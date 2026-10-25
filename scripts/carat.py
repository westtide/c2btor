# SPDX-License-Identifier: BSD-4-Clause
# SPDX-FileCopyrightText: 2026 C2BTOR contributors

"""Race the four fixed Carat configurations on one model."""
from contextlib import ExitStack
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
import time


# Workers 0, 1, 2 and 6 from Carat/scripts/portfolio_array.json.
CONFIGURATIONS = (
    ("0_cegar_ic3_ctg", ("-a", "ic3")),
    ("1_cegar_ic3", ("-a", "ic3", "--ctg_max_lvl", "0")),
    ("2_cegar_ic3_all", ("-a", "ic3", "--all", "--ctg_max_lvl", "0")),
    ("6_wlbmc", ("-a", "wlbmc", "-s", "kissat", "-k", "100")),
)


def classify(text, algorithm="ic3", returncode=None):
    verdicts = set(re.findall(r"^(Safe|Unsafe|Unknown)\s*$", text, re.M))
    if len(verdicts) != 1 or (returncode is not None and returncode != 0):
        return "Unknown"
    result = verdicts.pop()
    return "Unknown" if result == "Safe" and algorithm in {"wlbmc", "bmc"} else result


def _stop(processes):
    """Stop and reap our processes, including their process-group children."""
    # A pending task timeout must not interrupt kill/reap halfway through.
    previous = signal.pthread_sigmask(signal.SIG_BLOCK,
                                      {signal.SIGALRM, signal.SIGTERM, signal.SIGINT})
    try:
        for process in processes:
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
        deadline = time.monotonic() + 0.5
        for process in processes:
            try:
                process.wait(timeout=max(0, deadline - time.monotonic()))
            except subprocess.TimeoutExpired:
                pass
        for process in processes:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        for process in processes:
            process.wait()
    finally:
        signal.pthread_sigmask(signal.SIG_SETMASK, previous)


def race(carat, model, directory, deadline):
    """Keep the first completed decisive result and its standard counterexample.

    BenchExec accounts CPU and memory for the entire task process tree. The
    deadline is only a wall-time backstop; workers never receive separate
    900-second CPU allowances.
    """
    processes = []
    model, directory = Path(model).resolve(), Path(directory).resolve()
    with tempfile.TemporaryDirectory(prefix=".carat-", dir=directory) as temporary, ExitStack() as files:
        pending, failures = {}, []
        try:
            for name, options in CONFIGURATIONS:
                work = Path(temporary) / name
                work.mkdir()
                stdout = files.enter_context(tempfile.TemporaryFile(dir=temporary))
                stderr = files.enter_context(tempfile.TemporaryFile(dir=temporary))
                process = subprocess.Popen([str(carat), *options, "-w", str(work), str(model)],
                                           cwd=work, stdout=stdout, stderr=stderr, start_new_session=True)
                processes.append(process)
                pending[name] = (process, stdout, stderr, work, options[1])
            while pending:
                if time.monotonic() >= deadline:
                    raise TimeoutError("task wall-time limit reached")
                winners = []
                for name, (process, stdout, stderr, work, algorithm) in list(pending.items()):
                    code = process.poll()
                    if code is None:
                        continue
                    del pending[name]
                    stdout.seek(0)
                    # Read logs incrementally: even verbose workers cannot
                    # block on a full PIPE or force an unbounded RAM copy.
                    verdicts = {line.strip().decode() for line in stdout
                                if line.strip() in {b"Safe", b"Unsafe", b"Unknown"}}
                    result = classify("\n".join(verdicts), algorithm, code)
                    if result in {"Safe", "Unsafe"}:
                        winners.append((result, name, work))
                    else:
                        print(f"Carat {name}: {'crashed' if code else 'Unknown'}", file=sys.stderr)
                        if code:
                            failures.append(name)
                            stderr.seek(0, os.SEEK_END)
                            stderr.seek(max(0, stderr.tell() - 4000))
                            print(stderr.read().decode(errors="replace"), file=sys.stderr)
                if winners:
                    if len({result for result, _, _ in winners}) != 1:
                        raise ValueError("Carat workers returned conflicting Safe/Unsafe results")
                    result, name, work = winners[0]
                    if result == "Unsafe":
                        traces = list(work.glob("*.cexb"))
                        if len(traces) != 1 or not traces[0].stat().st_size:
                            raise ValueError(f"Carat {name}: Unsafe without exactly one nonempty standard counterexample")
                        traces[0].rename(directory / "model.cex")
                    return result, name
                if pending:
                    time.sleep(0.02)
            if len(failures) == len(CONFIGURATIONS):
                raise ValueError("all Carat workers crashed: " + ", ".join(failures))
            return "Unknown", None
        finally:
            _stop(processes)
