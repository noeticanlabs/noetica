import argparse
import json

from noetica_parser import parse_module
from noetica_typecheck import typecheck_module
# NSC runtime - this is the kernel boundary: Noetica emits, NSC executes
from nsc_kernel.nsc_runtime import run_function


def main() -> None:
    parser = argparse.ArgumentParser(description="NK-0 minimal CLI")
    parser.add_argument("module_file", help="Path to .nk module file")
    parser.add_argument("function", help="Function to invoke")
    parser.add_argument("--store", default="{}", help="Initial store as JSON object")
    parser.add_argument("--args", default="{}", help="Function args as JSON object")
    args = parser.parse_args()

    source = open(args.module_file, "r", encoding="utf-8").read()
    module = parse_module(source)
    typecheck_module(module)
    result, store, receipt = run_function(module, args.function, json.loads(args.store), json.loads(args.args))

    print(json.dumps({"result": result, "store": store, "receipt": receipt.__dict__}, indent=2))


if __name__ == "__main__":
    main()
