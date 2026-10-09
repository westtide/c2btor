#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Optional, Set


DEFAULT_SRC_ROOT = "test/simple_test_c"
DEFAULT_OUT_ROOT = "test/simple_test_btor2"
DEFAULT_RUNS_ROOT = "test/btor2_runs"
PREPROCESS_DIR_NAME = "__Preprocess"


def _default_related_dir(*, out_root: Path, replace_suffix: str, new_suffix: str) -> Path:
    name = out_root.name
    if replace_suffix and name.endswith(replace_suffix):
        return out_root.with_name(name[: -len(replace_suffix)] + new_suffix)
    return out_root.with_name(name + new_suffix)


@dataclass(frozen=True)
class Paths:
    repo_root: Path
    src_root: Path
    out_root: Path
    log_root: Path
    runs_root: Path
    preprocess_root: Path
    preprocess_csv: Path
    run_id: str
    run_dir: Path
    log_dir: Path
    files_path: Path
    results_csv: Path
    run_log: Path
    global_run_log: Path


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[2]


def _resolve_under(base: Path, p: str) -> Path:
    raw = Path(p).expanduser()
    return raw if raw.is_absolute() else (base / raw).resolve()


def _iter_sources(src_root: Path, exts: Iterable[str]) -> List[Path]:
    want = {e if e.startswith(".") else "." + e for e in exts}
    files: List[Path] = []
    for path in src_root.rglob("*"):
        if not path.is_file():
            continue
        if PREPROCESS_DIR_NAME in path.parts:
            continue
        if path.suffix in want:
            files.append(path)
    # Sort by relative path, case-insensitive, so directories like "array-*"
    # come before "Juliet_Test" even if case differs.
    files.sort(
        key=lambda p: (
            str(p.relative_to(src_root)).casefold(),
            str(p.relative_to(src_root)),
        )
    )

    # De-duplicate files with same relative stem (e.g. foo.c and foo.i) so the
    # later one does not overwrite/remove outputs of the earlier one.
    unique: List[Path] = []
    seen_stems = set()
    for path in files:
        stem_key = str(path.relative_to(src_root).with_suffix("")).casefold()
        if stem_key in seen_stems:
            continue
        seen_stems.add(stem_key)
        unique.append(path)
    return unique


def _normalize_case_to_source(rel_case: str) -> str:
    rel = rel_case.strip().replace("\\", "/")
    if not rel or rel.startswith("#"):
        return ""
    suffix = Path(rel).suffix.lower()
    if suffix == ".btor2":
        return str(Path(rel).with_suffix(".c"))
    if suffix not in (".c", ".i"):
        return rel + ".c"
    return rel


def _load_sources_from_cases(cases_file: Path, src_root: Path) -> tuple[List[Path], List[str]]:
    files: List[Path] = []
    missing: List[str] = []
    seen = set()
    with cases_file.open("r", encoding="utf-8") as handle:
        for raw in handle:
            rel = _normalize_case_to_source(raw)
            if not rel:
                continue
            key = rel.casefold()
            if key in seen:
                continue
            seen.add(key)
            full = src_root / rel
            if full.is_file():
                files.append(full)
            else:
                missing.append(rel)
    return files, missing


def _write_lines(path: Path, lines: Iterable[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as f:
        for line in lines:
            f.write(line)
            if not line.endswith("\n"):
                f.write("\n")


def _write_index_csv(path: Path, src_root: Path, files: List[Path]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as f:
        w = csv.writer(f)
        w.writerow(["index", "rel", "src_path"])
        for idx, p in enumerate(files):
            w.writerow([idx, str(p.relative_to(src_root)), str(p)])


def _replace_last_suffix(path: Path, new_suffix: str) -> Path:
    name = path.name
    if path.suffix:
        name = name[: -len(path.suffix)]
    return path.with_name(name + new_suffix)


def _case_yml_path(src_file: Path) -> Path:
    return _replace_last_suffix(src_file, ".yml")


def _read_svcomp_data_model(yml_path: Path) -> Optional[str]:
    if not yml_path.is_file():
        return None
    try:
        text = yml_path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return None

    match = re.search(r"(?m)^\s*data_model\s*:\s*([A-Za-z0-9_]+)\s*$", text)
    if match is None:
        return None
    return match.group(1).upper()


def _data_model_flag(data_model: Optional[str]) -> Optional[str]:
    if data_model == "ILP32":
        return "--32"
    if data_model == "LP64":
        return "--64"
    return None


def _has_explicit_data_model(cbmc_args: List[str]) -> bool:
    explicit = {
        "--16",
        "--32",
        "--64",
        "--LP64",
        "--ILP64",
        "--LLP64",
        "--ILP32",
        "--LP32",
    }
    return any(arg in explicit for arg in cbmc_args)


def _cbmc_args_for_source(cbmc_args: List[str], src_file: Path) -> List[str]:
    args = list(cbmc_args)
    if _has_explicit_data_model(args):
        return args

    flag = _data_model_flag(_read_svcomp_data_model(_case_yml_path(src_file)))
    if flag is not None:
        args.append(flag)
    return args


def _load_skip_stems(skip_path: Path) -> Set[str]:
    stems: Set[str] = set()
    if not skip_path.exists():
        return stems
    with skip_path.open("r", encoding="utf-8", errors="replace") as f:
        for raw in f:
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            # Support CSV rows like "rel,..." by taking first column.
            token = line.split(",", 1)[0].strip()
            token = token.replace("\\", "/")
            # Treat entries as relative paths and compare by stem.
            stem = str(Path(token).with_suffix("")).casefold()
            stems.add(stem)
    return stems


def _append_lines(path: Path, lines: Iterable[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as f:
        for line in lines:
            f.write(line)
            if not line.endswith("\n"):
                f.write("\n")


def _default_cbmc(repo_root: Path) -> Path:
    # Prefer in-repo build, fallback to PATH.
    in_repo = repo_root / "build" / "bin" / "c2btor"
    return in_repo if in_repo.exists() else Path("c2btor")


def _parse_cbmc_args(raw: str) -> List[str]:
    if not raw.strip():
        return []
    return shlex.split(raw)


def _add_default_cbmc_args(cbmc_args: List[str]) -> List[str]:
    # These defaults help the BTOR2 backend:
    # - --inline reduces FUNCTION_CALL instructions
    # - --no-signed-overflow-check removes overflow checks/assertions
    defaults = ["--inline", "--no-signed-overflow-check"]
    for flag in defaults:
        if flag not in cbmc_args:
            cbmc_args.append(flag)
    return cbmc_args


def _remove_flags(cbmc_args: List[str], flags: Iterable[str]) -> None:
    drop = set(flags)
    cbmc_args[:] = [arg for arg in cbmc_args if arg not in drop]


def _ensure_flag(cbmc_args: List[str], flag: str) -> None:
    if flag not in cbmc_args:
        cbmc_args.append(flag)


def _apply_check_settings(cbmc_args: List[str], args: argparse.Namespace) -> None:
    # Default behavior: disable pointer-related checks and built-in assertions.
    if args.pointer_check:
        _remove_flags(cbmc_args, ["--no-pointer-check"])
        _ensure_flag(cbmc_args, "--pointer-check")
    else:
        _remove_flags(cbmc_args, ["--pointer-check"])
        _ensure_flag(cbmc_args, "--no-pointer-check")

    if args.bounds_check:
        _remove_flags(cbmc_args, ["--no-bounds-check"])
        _ensure_flag(cbmc_args, "--bounds-check")
    else:
        _remove_flags(cbmc_args, ["--bounds-check"])
        _ensure_flag(cbmc_args, "--no-bounds-check")

    if args.pointer_primitive_check:
        _remove_flags(cbmc_args, ["--no-pointer-primitive-check"])
        _ensure_flag(cbmc_args, "--pointer-primitive-check")
    else:
        _remove_flags(cbmc_args, ["--pointer-primitive-check"])
        _ensure_flag(cbmc_args, "--no-pointer-primitive-check")

    if args.pointer_overflow_check:
        _ensure_flag(cbmc_args, "--pointer-overflow-check")
    else:
        _remove_flags(cbmc_args, ["--pointer-overflow-check", "--no-pointer-overflow-check"])

    if args.built_in_assertions:
        _remove_flags(cbmc_args, ["--no-built-in-assertions"])
    else:
        _ensure_flag(cbmc_args, "--no-built-in-assertions")

    if (
        args.goto_btor2_checks
        or args.pointer_check
        or args.bounds_check
        or args.pointer_primitive_check
        or args.pointer_overflow_check
        or args.built_in_assertions
    ):
        _ensure_flag(cbmc_args, "--goto-btor2-checks")


def _needs_malloc_fix(lines: List[str]) -> bool:
    pattern = re.compile(
        r"^\s*void\s*\*\s*malloc\s*\(\s*unsigned\s+int\s+size\s*\)\s*;\s*$"
    )
    for line in lines:
        if line.lstrip().startswith("//"):
            continue
        if pattern.match(line):
            return True
    return False


def _insert_stddef_include(lines: List[str]) -> List[str]:
    for line in lines:
        if line.strip() in ("#include <stddef.h>", "#include \"stddef.h\""):
            return lines

    out = list(lines)
    idx = 0
    in_block = False
    while idx < len(out):
        stripped = out[idx].lstrip()
        if in_block:
            if "*/" in stripped:
                in_block = False
            idx += 1
            continue
        if stripped.startswith("/*"):
            in_block = True
            idx += 1
            continue
        if stripped.startswith("//") or stripped == "" or stripped == "\n":
            idx += 1
            continue
        break

    out.insert(idx, "#include <stddef.h>\n")
    return out


def _comment_malloc_decl(lines: List[str]) -> List[str]:
    pattern = re.compile(
        r"^\s*void\s*\*\s*malloc\s*\(\s*unsigned\s+int\s+size\s*\)\s*;\s*$"
    )
    out: List[str] = []
    for line in lines:
        if line.lstrip().startswith("//") or not pattern.match(line):
            out.append(line)
            continue
        leading = line[: len(line) - len(line.lstrip())]
        body = line.lstrip().rstrip("\n")
        out.append(f"{leading}// {body}\n")
    return out


def _preprocess_source(
    *,
    src_file: Path,
    src_root: Path,
    preprocess_root: Path,
    preprocess_csv: Path,
) -> Path:
    try:
        content = src_file.read_text(encoding="utf-8")
    except Exception:
        return src_file

    lines = content.splitlines(keepends=True)
    if not _needs_malloc_fix(lines):
        return src_file

    processed = _comment_malloc_decl(lines)
    if src_file.suffix != ".i":
        processed = _insert_stddef_include(processed)
    processed_text = "".join(processed)

    rel = src_file.relative_to(src_root)
    orig_copy = preprocess_root / "original" / rel
    processed_copy = preprocess_root / "processed" / rel
    orig_copy.parent.mkdir(parents=True, exist_ok=True)
    processed_copy.parent.mkdir(parents=True, exist_ok=True)

    wrote = False
    if not orig_copy.exists():
        shutil.copy2(src_file, orig_copy)
        wrote = True

    if not processed_copy.exists() or processed_copy.read_text(
        encoding="utf-8"
    ) != processed_text:
        processed_copy.write_text(processed_text, encoding="utf-8")
        wrote = True

    if wrote:
        preprocess_csv.parent.mkdir(parents=True, exist_ok=True)
        file_exists = preprocess_csv.exists()
        with preprocess_csv.open("a", encoding="utf-8", newline="") as f:
            w = csv.writer(f)
            if not file_exists:
                w.writerow(
                    [
                        "timestamp",
                        "src_path",
                        "orig_copy",
                        "processed_copy",
                        "change",
                    ]
                )
            w.writerow(
                [
                    time.ctime(),
                    str(src_file),
                    str(orig_copy),
                    str(processed_copy),
                    "comment-malloc-unsigned-int"
                    + ("" if src_file.suffix == ".i" else ";add-stddef"),
                ]
            )

    return processed_copy


def _now_id() -> str:
    return time.strftime("%Y%m%d_%H%M%S", time.localtime())


CBMC_FAIL_PATTERNS = [
    re.compile(r"Failed to convert RHS expression"),
    re.compile(r"Failed to convert guard expression"),
    re.compile(r"Non-symbol LHS not fully supported"),
    re.compile(r"Unsupported expression for BTOR2"),
    re.compile(r"PARSING ERROR"),
    re.compile(r"CONVERSION ERROR"),
]


@dataclass(frozen=True)
class ConvertResult:
    idx: int
    total: int
    rel: str
    src_path: str
    out_path: str
    goto_path: str
    log_path: str
    status: str  # ok|timeout|error|empty_output|conversion_error|skipped
    exit_code: Optional[int]
    out_bytes: int
    goto_exit_code: Optional[int]
    goto_bytes: int
    elapsed_ms: int
    hint: str


def _run_cbmc_to_file(*, cmd: List[str], out_path: Path, timeout_sec: int) -> int:
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", encoding="utf-8", errors="replace") as f:
        f.write(f"CMD: {shlex.join(cmd)}\n")
        f.write(f"OUT: {out_path}\n")
        f.write(f"Started: {time.ctime()}\n")
        f.write("\n")
        f.flush()
        timeout = timeout_sec if timeout_sec and timeout_sec > 0 else None
        try:
            proc = subprocess.run(cmd, stdout=f, stderr=f, text=True, timeout=timeout)
            code = int(proc.returncode)
        except subprocess.TimeoutExpired:
            f.write(f"\n<TIMEOUT> exceeded {timeout_sec}s\n")
            code = 124
        except Exception as exc:
            f.write(f"\n<EXCEPTION> {exc}\n")
            code = 127
        f.write("\n")
        f.write(f"EXIT: {code}\n")
    return code


def _log_conversion_errors(log_path: Path) -> List[str]:
    try:
        text = log_path.read_text(encoding="utf-8", errors="replace")
    except Exception:
        return []
    hits: List[str] = []
    for pat in CBMC_FAIL_PATTERNS:
        if pat.search(text):
            hits.append(pat.pattern)
    return hits


def _convert_one(
    *,
    cbmc: str,
    cbmc_args: List[str],
    src_file: Path,
    src_root: Path,
    preprocess_root: Path,
    preprocess_csv: Path,
    out_root: Path,
    goto_root: Path,
    log_dir: Path,
    folder: str,
    force: bool,
    resume: bool,
    timeout_sec: int,
    idx: int,
    total: int,
) -> ConvertResult:
    actual_src = _preprocess_source(
        src_file=src_file,
        src_root=src_root,
        preprocess_root=preprocess_root,
        preprocess_csv=preprocess_csv,
    )
    rel = src_file.relative_to(src_root)
    rel_base = _replace_last_suffix(rel, "")
    out_path = out_root / Path(str(rel_base) + ".btor2")
    goto_path = goto_root / Path(str(rel_base) + ".goto")
    if folder:
        log_path = log_dir / folder / Path(str(rel_base) + ".log")
    else:
        log_path = log_dir / Path(str(rel_base) + ".log")
    tmp_out = out_path.with_suffix(out_path.suffix + ".tmp")
    tmp_goto = goto_path.with_suffix(goto_path.suffix + ".tmp")

    out_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.parent.mkdir(parents=True, exist_ok=True)
    goto_path.parent.mkdir(parents=True, exist_ok=True)

    goto_code: Optional[int] = None
    goto_bytes = 0
    try:
        goto_exists = goto_path.exists() and goto_path.stat().st_size > 0
    except Exception:
        goto_exists = False

    try:
        out_exists = out_path.exists() and out_path.stat().st_size > 0
        if resume and not force and out_exists and goto_exists:
            hint = "skipped: existing non-empty .btor2 and .goto"
            with log_path.open("w", encoding="utf-8", errors="replace") as log_f:
                log_f.write("CMD: <skipped>\n")
                log_f.write(f"SRC: {src_file}\n")
                log_f.write(f"OUT: {out_path} ({out_path.stat().st_size} bytes)\n")
                log_f.write(f"GOTO: {goto_path} ({goto_path.stat().st_size} bytes)\n")
                log_f.write(f"{hint}\n")
                log_f.write("EXIT: <skipped>\n")
            return ConvertResult(
                idx=idx,
                total=total,
                rel=str(rel),
                src_path=str(src_file),
                out_path=str(out_path),
                goto_path=str(goto_path),
                log_path=str(log_path),
                status="skipped",
                exit_code=None,
                out_bytes=int(out_path.stat().st_size),
                goto_exit_code=None,
                goto_bytes=int(goto_path.stat().st_size),
                elapsed_ms=0,
                hint=hint,
            )
    except Exception:
        pass

    case_cbmc_args = _cbmc_args_for_source(cbmc_args, src_file)
    goto_cmd = [cbmc, "--show-goto-functions", *case_cbmc_args, str(actual_src)]

    # Always (re)generate GOTO when missing/empty, or when forced.
    if force or not goto_exists:
        goto_code = _run_cbmc_to_file(
            cmd=goto_cmd, out_path=tmp_goto, timeout_sec=timeout_sec
        )
        try:
            ok_goto = goto_code == 0 and tmp_goto.exists() and tmp_goto.stat().st_size > 0
        except Exception:
            ok_goto = False
        if ok_goto:
            tmp_goto.replace(goto_path)
        else:
            try:
                tmp_goto.replace(goto_path)
            except Exception:
                # Keep at least some evidence.
                _append_lines(
                    goto_path,
                    [
                        "",
                        f"<FAILED TO WRITE GOTO OUTPUT> src={src_file}",
                        f"exit_code={goto_code}",
                    ],
                )
    try:
        if goto_path.exists():
            goto_bytes = int(goto_path.stat().st_size)
    except Exception:
        goto_bytes = 0

    cmd = [
        cbmc,
        "--goto-btor2",
        "--goto-btor2-out",
        str(tmp_out),
        *case_cbmc_args,
        str(actual_src),
    ]

    started = time.time()
    code: Optional[int] = None
    hint = ""
    with log_path.open("w", encoding="utf-8", errors="replace") as log_f:
        log_f.write(f"CMD: {shlex.join(cmd)}\n")
        log_f.write(f"SRC: {src_file}\n")
        log_f.write(f"OUT_TMP: {tmp_out}\n")
        log_f.write(f"GOTO: {goto_path}\n")
        log_f.write(f"Started: {time.ctime()}\n")
        log_f.write("\n")
        log_f.flush()
        timeout = timeout_sec if timeout_sec and timeout_sec > 0 else None
        try:
            proc = subprocess.run(
                cmd,
                stdout=log_f,
                stderr=log_f,
                text=True,
                timeout=timeout,
            )
            code = int(proc.returncode)
        except subprocess.TimeoutExpired:
            code = 124
            hint = f"timeout>{timeout_sec}s"
            log_f.write(f"\n<TIMEOUT> exceeded {timeout_sec}s\n")
        except Exception as exc:
            code = 127
            hint = f"exception: {exc}"
            log_f.write(f"\n<EXCEPTION> {exc}\n")
        finally:
            elapsed_ms = int((time.time() - started) * 1000)
            log_f.write("\n")
            log_f.write(f"EXIT: {code}\n")
            log_f.write(f"Elapsed: {elapsed_ms} ms\n")

    try:
        ok = code == 0 and tmp_out.exists() and tmp_out.stat().st_size > 0
    except OSError:
        ok = False

    log_errors = _log_conversion_errors(log_path)

    if code == 124:
        status = "timeout"
        hint = hint or f"timeout>{timeout_sec}s"
    elif code is not None and code not in (0, 124):
        status = "error"
        hint = hint or f"exit_code={code}"
    elif code == 0 and not ok:
        if log_errors:
            status = "conversion_error"
            hint = "log_errors=" + "|".join(log_errors)
        else:
            status = "empty_output"
            hint = "btor2_output_missing_or_empty"
    elif log_errors:
        status = "conversion_error"
        hint = "log_errors=" + "|".join(log_errors)
    else:
        status = "ok"
        hint = hint or ""

    if status == "ok":
        tmp_out.replace(out_path)
        out_bytes = int(out_path.stat().st_size) if out_path.exists() else 0
        return ConvertResult(
            idx=idx,
            total=total,
            rel=str(rel),
            src_path=str(src_file),
            out_path=str(out_path),
            goto_path=str(goto_path),
            log_path=str(log_path),
            status=status,
            exit_code=code,
            out_bytes=out_bytes,
            goto_exit_code=goto_code,
            goto_bytes=goto_bytes,
            elapsed_ms=int((time.time() - started) * 1000),
            hint=hint,
        )

    try:
        tmp_out.unlink(missing_ok=True)
    except Exception:
        pass
    try:
        out_path.unlink(missing_ok=True)
    except Exception:
        pass
    _append_lines(
        log_path,
        [
            f"conversion_status: {status}",
            f"exit_code: {code if code is not None else ''}",
        ],
    )
    out_bytes = int(out_path.stat().st_size) if out_path.exists() else 0
    return ConvertResult(
        idx=idx,
        total=total,
        rel=str(rel),
        src_path=str(src_file),
        out_path=str(out_path),
        goto_path=str(goto_path),
        log_path=str(log_path),
        status=status,
        exit_code=code,
        out_bytes=out_bytes,
        goto_exit_code=goto_code,
        goto_bytes=goto_bytes,
        elapsed_ms=int((time.time() - started) * 1000),
        hint=hint,
    )


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Convert C programs under a directory to BTOR2 using CBMC (sequential)."
    )
    parser.add_argument(
        "--src",
        "--src-root",
        dest="src_root",
        default=DEFAULT_SRC_ROOT,
        help=f"Root directory of input sources (default: {DEFAULT_SRC_ROOT})",
    )
    parser.add_argument(
        "--out",
        "--out-root",
        dest="out_root",
        default=DEFAULT_OUT_ROOT,
        help=f"Output directory for .btor2 files (default: {DEFAULT_OUT_ROOT})",
    )
    parser.add_argument(
        "--goto-dir",
        "--goto-root",
        dest="goto_root",
        default="",
        help="Output directory for per-file goto text dumps (default: derived from --out)",
    )
    parser.add_argument(
        "--log-dir",
        "--log-root",
        dest="log_root",
        default="",
        help="Output directory for per-file logs (default: derived from --out)",
    )
    parser.add_argument(
        "--runs-root",
        default=DEFAULT_RUNS_ROOT,
        help=f"Output directory for run summaries (default: {DEFAULT_RUNS_ROOT})",
    )
    parser.add_argument(
        "--run-id",
        default="",
        help="Optional run id used for summaries (default: timestamp)",
    )
    parser.add_argument(
        "--cases-file",
        default="",
        help="Optional file listing exact cases to convert, relative to --src-root.",
    )
    parser.add_argument(
        "--limit",
        type=int,
        default=None,
        help="Max number of input files to convert. Default: stop after 1000.",
    )
    parser.add_argument(
        "--ext",
        action="append",
        default=[".c", ".i"],
        help="File extension(s) to include (repeatable). Default: .c",
    )
    parser.add_argument(
        "--c2btor", "--cbmc", dest="cbmc",
        default="",
        help="Path to c2btor binary (default: repo build/bin/c2btor if present, else c2btor in PATH)",
    )
    parser.add_argument(
        "--cbmc-args",
        default=os.environ.get("CBMC_ARGS", ""),
        help="Extra args passed to cbmc (also supports CBMC_ARGS env var)",
    )
    parser.add_argument(
        "--goto-btor2-checks",
        dest="goto_btor2_checks",
        action="store_true",
        help="Run goto-check instrumentation before BTOR2 conversion",
    )
    parser.add_argument(
        "--pointer-check",
        dest="pointer_check",
        action="store_true",
        help="Enable CBMC pointer checks (default: off)",
    )
    parser.add_argument(
        "--no-pointer-check",
        dest="pointer_check",
        action="store_false",
        help="Disable CBMC pointer checks (default)",
    )
    parser.set_defaults(pointer_check=False)
    parser.add_argument(
        "--bounds-check",
        dest="bounds_check",
        action="store_true",
        help="Enable CBMC bounds checks (default: off)",
    )
    parser.add_argument(
        "--no-bounds-check",
        dest="bounds_check",
        action="store_false",
        help="Disable CBMC bounds checks (default)",
    )
    parser.set_defaults(bounds_check=False)
    parser.add_argument(
        "--pointer-primitive-check",
        dest="pointer_primitive_check",
        action="store_true",
        help="Enable CBMC pointer primitive checks (default: off)",
    )
    parser.add_argument(
        "--no-pointer-primitive-check",
        dest="pointer_primitive_check",
        action="store_false",
        help="Disable CBMC pointer primitive checks (default)",
    )
    parser.set_defaults(pointer_primitive_check=False)
    parser.add_argument(
        "--pointer-overflow-check",
        dest="pointer_overflow_check",
        action="store_true",
        help="Enable CBMC pointer overflow checks (default: off)",
    )
    parser.set_defaults(pointer_overflow_check=False)
    parser.add_argument(
        "--built-in-assertions",
        dest="built_in_assertions",
        action="store_true",
        help="Enable CBMC built-in library assertions (default: off)",
    )
    parser.add_argument(
        "--no-built-in-assertions",
        dest="built_in_assertions",
        action="store_false",
        help="Disable CBMC built-in library assertions (default)",
    )
    parser.set_defaults(built_in_assertions=False)
    parser.add_argument(
        "--force",
        action="store_true",
        help="Force re-run conversion (also ignores --resume)",
    )
    parser.add_argument(
        "--resume",
        action="store_true",
        help="Skip conversion if target .btor2 already exists and is non-empty",
    )
    parser.add_argument(
        "--progress-every",
        type=int,
        default=100,
        help="Print progress every N files (default: 100)",
    )
    parser.add_argument(
        "--start",
        type=int,
        default=0,
        help="Start index in the global sorted source list (0-based, default: 0)",
    )
    parser.add_argument(
        "--end",
        type=int,
        default=-1,
        help="End index (inclusive) in the global sorted source list (-1 means no upper bound)",
    )
    parser.add_argument(
        "--index-out",
        default="",
        help="Write global sorted source index CSV to this path",
    )
    parser.add_argument(
        "--index-only",
        action="store_true",
        help="Only write index CSV (requires --index-out), then exit",
    )
    parser.add_argument(
        "--skip-list",
        default="",
        help="Text/CSV file listing already-verified cases to skip (matched by relative stem)",
    )
    parser.add_argument(
        "--timeout-sec",
        type=int,
        default=0,
        help="Per-file timeout in seconds for each cbmc invocation (0 disables timeout, default: 0)",
    )
    args = parser.parse_args(argv)

    repo_root = _repo_root()
    src_root = _resolve_under(repo_root, args.src_root)
    preprocess_root = src_root / PREPROCESS_DIR_NAME
    preprocess_csv = preprocess_root / "preprocess.csv"
    out_root = _resolve_under(repo_root, args.out_root)
    goto_root = (
        _resolve_under(repo_root, args.goto_root)
        if args.goto_root.strip()
        else _default_related_dir(out_root=out_root, replace_suffix="_btor2", new_suffix="_goto")
    )
    log_root = (
        _resolve_under(repo_root, args.log_root)
        if args.log_root.strip()
        else _resolve_under(repo_root, "sv-log/cbmc")
    )
    runs_root = _resolve_under(repo_root, args.runs_root)
    run_id = args.run_id.strip() or _now_id()
    run_dir = runs_root / run_id
    log_dir = log_root

    if not src_root.is_dir():
        print(f"src root not found: {src_root}", file=sys.stderr)
        return 2

    folder = src_root.name

    cbmc_path = Path(args.cbmc).expanduser() if args.cbmc else _default_cbmc(repo_root)
    cbmc = str(cbmc_path)

    cbmc_args = _parse_cbmc_args(args.cbmc_args)
    cbmc_args = _add_default_cbmc_args(cbmc_args)
    _apply_check_settings(cbmc_args, args)

    cases_file = _resolve_under(repo_root, args.cases_file) if args.cases_file.strip() else None
    if cases_file:
        if not cases_file.is_file():
            print(f"cases file not found: {cases_file}", file=sys.stderr)
            return 2
        files, missing_cases = _load_sources_from_cases(cases_file, src_root)
    else:
        files = _iter_sources(src_root, args.ext)
        missing_cases = []
    if not files:
        print(f"no input files under {src_root} (exts={args.ext})", file=sys.stderr)
        return 2

    index_out: Optional[Path] = None
    if args.index_out.strip():
        index_out = _resolve_under(repo_root, args.index_out)
        _write_index_csv(index_out, src_root, files)
        print(f"wrote index: {index_out}")

    if args.index_only:
        if index_out is None:
            print("--index-only requires --index-out", file=sys.stderr)
            return 2
        return 0

    start = max(0, int(args.start))
    if start >= len(files):
        print(
            f"start index {start} out of range (total {len(files)})",
            file=sys.stderr,
        )
        return 2

    if args.end >= 0:
        end = min(int(args.end), len(files) - 1)
        if end < start:
            print(
                f"invalid range: start={start}, end={end} (inclusive)",
                file=sys.stderr,
            )
            return 2
        ranged = files[start : end + 1]
    else:
        end = -1
        ranged = files[start:]

    default_cap = 1000
    if args.limit is None:
        selected = ranged[: min(len(ranged), default_cap)]
    elif args.limit < 0:
        selected = ranged
    else:
        selected = ranged[: args.limit]

    skip_stems: Set[str] = set()
    skip_list_path: Optional[Path] = None
    if args.skip_list.strip():
        skip_list_path = _resolve_under(repo_root, args.skip_list)
        skip_stems = _load_skip_stems(skip_list_path)
        if skip_stems:
            selected = [
                p
                for p in selected
                if str(p.relative_to(src_root).with_suffix("")).casefold()
                not in skip_stems
            ]

    paths = Paths(
        repo_root=repo_root,
        src_root=src_root,
        out_root=out_root,
        log_root=log_root,
        runs_root=runs_root,
        preprocess_root=preprocess_root,
        preprocess_csv=preprocess_csv,
        run_id=run_id,
        run_dir=run_dir,
        log_dir=log_dir,
        files_path=run_dir / "files.txt",
        results_csv=run_dir / "results.csv",
        run_log=run_dir / "run.log",
        global_run_log=_resolve_under(repo_root, "test/btor2_run.log"),
    )

    run_dir.mkdir(parents=True, exist_ok=True)
    log_dir.mkdir(parents=True, exist_ok=True)
    goto_root.mkdir(parents=True, exist_ok=True)
    out_root.mkdir(parents=True, exist_ok=True)
    preprocess_root.mkdir(parents=True, exist_ok=True)

    _write_lines(paths.files_path, (str(p) for p in selected))

    started = time.time()
    meta = {
        "run_id": run_id,
        "started": time.ctime(),
        "src_root": str(paths.src_root),
        "out_root": str(paths.out_root),
        "goto_root": str(goto_root),
        "log_root": str(paths.log_root),
        "log_dir": str(log_dir),
        "preprocess_root": str(preprocess_root),
        "preprocess_csv": str(preprocess_csv),
        "cbmc": cbmc,
        "cbmc_args": cbmc_args,
        "goto_btor2_checks": bool(args.goto_btor2_checks),
        "pointer_check": bool(args.pointer_check),
        "bounds_check": bool(args.bounds_check),
        "pointer_primitive_check": bool(args.pointer_primitive_check),
        "pointer_overflow_check": bool(args.pointer_overflow_check),
        "built_in_assertions": bool(args.built_in_assertions),
        "limit": args.limit if args.limit is not None else default_cap,
        "start": start,
        "end": end,
        "index_out": str(index_out) if index_out else "",
        "skip_list": str(skip_list_path) if skip_list_path else "",
        "skip_count": len(skip_stems),
        "ext": args.ext,
        "cases_file": str(cases_file) if cases_file else "",
        "missing_cases": len(missing_cases),
        "resume": bool(args.resume),
        "force": bool(args.force),
        "timeout_sec": int(args.timeout_sec),
    }
    (run_dir / "meta.json").write_text(
        json.dumps(meta, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    _write_lines(paths.run_log, [f"Started: {meta['started']}", f"run_id: {run_id}"])
    _append_lines(
        paths.run_log,
        [
            f"Total files: {len(selected)}",
            f"Total discovered: {len(files)}",
            f"range: [{start}, {end if end >= 0 else 'end'}]",
            f"default_cap: {default_cap}" if args.limit is None else f"limit: {args.limit}",
            f"src_root: {paths.src_root}",
            f"out_root: {paths.out_root}",
            f"goto_root: {goto_root}",
            f"log_dir: {log_dir}",
            f"index_out: {index_out if index_out else ''}",
            f"skip_list: {skip_list_path if skip_list_path else ''}",
            f"skip_count: {len(skip_stems)}",
            f"cases_file: {cases_file if cases_file else ''}",
            f"missing_cases: {len(missing_cases)}",
            f"preprocess_root: {preprocess_root}",
            f"preprocess_csv: {preprocess_csv}",
            f"cbmc: {cbmc}",
            f"cbmc_args: {shlex.join(cbmc_args) if cbmc_args else ''}",
            f"goto_btor2_checks: {args.goto_btor2_checks}",
            f"pointer_check: {args.pointer_check}",
            f"bounds_check: {args.bounds_check}",
            f"pointer_primitive_check: {args.pointer_primitive_check}",
            f"pointer_overflow_check: {args.pointer_overflow_check}",
            f"built_in_assertions: {args.built_in_assertions}",
            f"resume: {args.resume}",
            f"force: {args.force}",
            f"timeout_sec: {args.timeout_sec}",
        ],
    )
    _append_lines(
        paths.global_run_log,
        [
            "========================================",
            f"[{time.ctime()}] run_id={run_id} total={len(selected)} src_root={paths.src_root}",
        ],
    )
    if missing_cases:
        _append_lines(
            paths.run_log,
            [f"missing_case: {rel}" for rel in missing_cases],
        )

    counts = {"ok": 0, "timeout": 0, "error": 0, "empty_output": 0, "conversion_error": 0, "skipped": 0}

    with paths.results_csv.open("w", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(
            f,
            fieldnames=[
                "idx",
                "total",
                "rel",
                "src_path",
                "out_path",
                "goto_path",
                "log_path",
                "status",
                "exit_code",
                "out_bytes",
                "goto_exit_code",
                "goto_bytes",
                "elapsed_ms",
                "hint",
            ],
        )
        w.writeheader()
        f.flush()

        for idx, src_file in enumerate(selected, start=1):
            res = _convert_one(
                cbmc=cbmc,
                cbmc_args=cbmc_args,
                src_file=src_file,
                src_root=src_root,
                preprocess_root=paths.preprocess_root,
                preprocess_csv=paths.preprocess_csv,
                out_root=out_root,
                goto_root=goto_root,
                log_dir=paths.log_dir,
                folder=folder,
                force=args.force,
                resume=args.resume,
                timeout_sec=args.timeout_sec,
                idx=idx,
                total=len(selected),
            )
            counts[res.status] = counts.get(res.status, 0) + 1

            w.writerow(
                {
                    "idx": res.idx,
                    "total": res.total,
                    "rel": res.rel,
                    "src_path": res.src_path,
                    "out_path": res.out_path,
                    "goto_path": res.goto_path,
                    "log_path": res.log_path,
                    "status": res.status,
                    "exit_code": "" if res.exit_code is None else str(res.exit_code),
                    "out_bytes": str(res.out_bytes),
                    "goto_exit_code": ""
                    if res.goto_exit_code is None
                    else str(res.goto_exit_code),
                    "goto_bytes": str(res.goto_bytes),
                    "elapsed_ms": str(res.elapsed_ms),
                    "hint": res.hint,
                }
            )
            f.flush()

            if args.progress_every > 0 and (
                idx % args.progress_every == 0 or idx == len(selected)
            ):
                elapsed = int(time.time() - started)
                ok = counts["ok"]
                fail = sum(v for k, v in counts.items() if k not in ("ok", "skipped"))
                skip = counts["skipped"]
                line = f"[{time.ctime()}] {idx}/{len(selected)} ok={ok} fail={fail} skip={skip} elapsed={elapsed}s"
                _append_lines(paths.run_log, [line])
                print(
                    f"[{idx}/{len(selected)}] ok={ok} fail={fail} skip={skip} elapsed={elapsed}s",
                    flush=True,
                )

    ok = counts["ok"]
    fail = sum(v for k, v in counts.items() if k not in ("ok", "skipped"))
    skip = counts["skipped"]
    _append_lines(paths.run_log, [f"Finished: {time.ctime()}"])
    _append_lines(
        paths.run_log,
        [f"Summary: ok={ok} timeout={counts['timeout']} error={counts['error']} "
         f"empty_output={counts['empty_output']} conversion_error={counts['conversion_error']} "
         f"skipped={skip} total={len(selected)}"],
    )
    _append_lines(
        paths.global_run_log,
        [f"[{time.ctime()}] run_id={run_id} ok={ok} fail={fail} skipped={skip}"],
    )
    (runs_root / "latest.txt").write_text(run_id + "\n", encoding="utf-8")

    print(f"run_id: {run_id}")
    print(f"run_dir: {run_dir}")
    print(f"out_root: {out_root}")
    print(f"log_dir: {log_dir}")
    print(f"folder: {folder}")
    print(f"results: {paths.results_csv}")
    print(f"ok={ok} timeout={counts['timeout']} error={counts['error']} "
          f"empty_output={counts['empty_output']} conversion_error={counts['conversion_error']} skipped={skip}")
    return 0 if fail == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
