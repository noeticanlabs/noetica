import subprocess
import sys
from pathlib import Path


def run(cmd):
    print("$", " ".join(cmd))
    return subprocess.run(cmd, check=False).returncode


def main() -> int:
    root = Path(__file__).resolve().parents[2]
    ck0_tests = [
        root / "ck0-coherence-kernel" / "tests" / "test_ck0_reference_model.py",
        root / "ck0-coherence-kernel" / "tests" / "test_ck0_negative_cases.py",
    ]
    nk0_tests = [
        root / "nk0-noetica-kernel" / "tests" / "test_nk0_parse_type_run.py",
        root / "nk0-noetica-kernel" / "tests" / "test_nk0_replay.py",
        root / "nk0-noetica-kernel" / "tests" / "test_nk0_negative_cases.py",
    ]
    missing = [p for p in (ck0_tests + nk0_tests) if not p.exists()]
    if missing:
        for p in missing:
            print(f"missing test file: {p}")
        return 2

    rc = 0
    for test_file in ck0_tests + nk0_tests:
        rc |= run([sys.executable, str(test_file)])
    return 0 if rc == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
