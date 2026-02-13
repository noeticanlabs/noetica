import subprocess
import sys


def run(cmd):
    print("$", " ".join(cmd))
    return subprocess.run(cmd, check=False).returncode


def main() -> int:
    rc = 0
    rc |= run([sys.executable, "ck0-coherence-kernel/tests/test_ck0_reference_model.py"])
    rc |= run([sys.executable, "nk0-noetica-kernel/tests/test_nk0_parse_type_run.py"])
    rc |= run([sys.executable, "nk0-noetica-kernel/tests/test_nk0_replay.py"])
    return 0 if rc == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
