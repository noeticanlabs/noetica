import subprocess
import sys
from pathlib import Path


def run(cmd):
    print("$", " ".join(cmd))
    return subprocess.run(cmd, check=False).returncode


def main() -> int:
    root = Path(__file__).resolve().parents[2]
    coherence_tests = [
        root / "coherence-kernel" / "tests" / "test_ck0_reference_model.py",
        root / "coherence-kernel" / "tests" / "test_ck0_negative_cases.py",
    ]
    noetica_tests = [
        root / "noetica-kernel" / "tests" / "test_nk0_parse_type_run.py",
        root / "noetica-kernel" / "tests" / "test_nk0_replay.py",
        root / "noetica-kernel" / "tests" / "test_nk0_negative_cases.py",
    ]
    # NSC kernel tests will be added when implemented
    nsc_tests = []

    all_tests = coherence_tests + noetica_tests + nsc_tests
    missing = [p for p in all_tests if not p.exists()]
    if missing:
        for p in missing:
            print(f"missing test file: {p}")
        return 2

    rc = 0
    for test_file in all_tests:
        rc |= run([sys.executable, str(test_file)])

    return 0 if rc == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
