"""rIC3 invocation shared by verification and regression runners."""
from functools import lru_cache
import subprocess


@lru_cache(maxsize=None)
def ric3_trace_options(binary):
    # rIC3 1.5.6 renamed --witness to --cex. Discover the CLI contract once
    # rather than tying a runner to a version string or a machine-specific path.
    help_text = subprocess.run([str(binary), 'check', '--help'], check=True,
                               capture_output=True, text=True, timeout=10).stdout
    return ['--cex', '--ui', 'false'] if '--cex' in help_text else ['--witness']


def ric3_command(binary, model, engine, timeout, bound=None):
    command = [str(binary), 'check', *ric3_trace_options(str(binary)), str(model),
               engine, '--time-limit', str(timeout)]
    if engine in {'bmc', 'wl-bmc', 'portfolio'} and bound is not None:
        command += ['--end', str(bound)]
    return command
