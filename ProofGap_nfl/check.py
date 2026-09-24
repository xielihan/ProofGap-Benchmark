#!/usr/bin/env python3
"""Check a user-supplied DSL proof without modifying the benchmark gap."""

from __future__ import annotations

import argparse
import configparser
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import subprocess
import sys
import tempfile
import time


PACKAGE_ROOT = Path(__file__).resolve().parent


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def native_binary() -> Path:
    machine = platform.machine().lower()
    if sys.platform.startswith("linux") and machine in {"x86_64", "amd64"}:
        return PACKAGE_ROOT / "bin/test_dsl"
    if sys.platform == "darwin" and machine in {"arm64", "aarch64"}:
        return PACKAGE_ROOT / "bin/test_dsl_macos_arm64"
    if sys.platform == "win32" and machine in {"x86_64", "amd64"}:
        return PACKAGE_ROOT / "bin/test_dsl_windows.exe"
    raise ValueError(
        f"No packaged verifier for {sys.platform}/{machine}; "
        "use --binary with a compatible test_dsl build."
    )


def proof_passes(returncode: int | None, result: object, stdout: str) -> bool:
    if returncode != 0 or not isinstance(result, dict):
        return False
    return (
        result.get("schema_version") == "test_dsl_structured_v2"
        and result.get("final_status") == "finish"
        and result.get("proof_finished") is True
        and result.get("proof_verified") is True
        and type(result.get("admit_count")) is int
        and result["admit_count"] == 0
        and type(result.get("split_gap_count")) is int
        and result["split_gap_count"] == 0
        and "dsl proof finished" in stdout
    )


def output_text(value: str | bytes | None) -> str:
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return value or ""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("gap", type=Path, help="benchmark gap.txt path")
    parser.add_argument("dsl", type=Path, help="user-generated DSL proof path")
    parser.add_argument("--timeout", type=float, default=120, help="seconds (default: 120)")
    parser.add_argument("--output-dir", type=Path, help="new directory for results and logs")
    parser.add_argument("--binary", type=Path, help="override the native test_dsl executable")
    args = parser.parse_args()
    if not math.isfinite(args.timeout) or args.timeout <= 0:
        parser.error("--timeout must be a finite positive number")

    # Resolve inputs relative to the caller, then use the package directory as
    # the verifier's working directory so the packaged settings are portable.
    try:
        gap, dsl = args.gap.resolve(), args.dsl.resolve()
        binary = args.binary.resolve() if args.binary else native_binary()
        for path in (gap, dsl, binary):
            if not path.is_file():
                raise ValueError(f"File not found: {path}")
        if os.name != "nt" and not os.access(binary, os.X_OK):
            raise ValueError(f"Verifier is not executable: {binary}")
        config = configparser.ConfigParser(interpolation=None)
        config.optionxform = str
        with (PACKAGE_ROOT / "settings.ini").open(encoding="utf-8") as handle:
            config.read_file(handle)
        theorem_lib = Path(config["THEOREM_LIBRARY"]["THMEOREM_LIB_SET"])
        if not theorem_lib.is_absolute():
            theorem_lib = PACKAGE_ROOT / theorem_lib
        theorem_lib = theorem_lib.resolve()
        if not theorem_lib.is_file():
            raise ValueError(f"Theorem library not found: {theorem_lib}")
        gap_text = gap.read_text(encoding="utf-8-sig")
        hashes = {"gap": sha256(gap), "dsl": sha256(dsl),
                  "binary": sha256(binary), "theorem_library": sha256(theorem_lib)}
        if args.output_dir:
            output = args.output_dir.resolve()
            output.mkdir(parents=True, exist_ok=False)
        else:
            runs = PACKAGE_ROOT / "verify"
            runs.mkdir(exist_ok=True)
            output = Path(tempfile.mkdtemp(prefix="run-", dir=runs))
    except (OSError, ValueError, KeyError, configparser.Error) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    # The parser expects nonblank lines. Normalize a temporary input only;
    # preserve the original gap's bytes and UTF-8 text.
    normalized = output / "gap.normalized.txt"
    normalized.write_text(
        "\n".join(line for line in gap_text.splitlines() if line.strip()) + "\n",
        encoding="utf-8",
    )
    config["ROOT_PATH"] = {"ROOT_PATH": PACKAGE_ROOT.as_posix()}
    config["THEOREM_LIBRARY"]["THMEOREM_LIB_SET"] = theorem_lib.as_posix()
    config["DSL_RESPONSES"] = {
        "DSL_ERROR_LOG": (output / "error_log.md").as_posix(),
        "DSL_EXECUTE_LOG": (output / "execute_log.md").as_posix(),
    }
    for name in ("error_log.md", "execute_log.md"):
        (output / name).write_text("", encoding="utf-8")
    settings = output / "settings.ini"
    with settings.open("w", encoding="utf-8") as handle:
        config.write(handle)
    result_path = output / "result.json"
    command = [str(binary), "--result-json", str(result_path), "-c", str(settings),
               str(normalized), str(dsl)]
    started = time.monotonic()
    returncode, stdout, stderr, execution_error = None, "", "", None
    timed_out = False
    try:
        process = subprocess.run(command, cwd=PACKAGE_ROOT, capture_output=True,
                                 text=True, encoding="utf-8", errors="replace",
                                 timeout=args.timeout, check=False)
        returncode, stdout, stderr = process.returncode, process.stdout, process.stderr
    except subprocess.TimeoutExpired as exc:
        timed_out = True
        stdout, stderr = output_text(exc.stdout), output_text(exc.stderr)
    except OSError as exc:
        execution_error = str(exc)
        stderr = execution_error
    elapsed = time.monotonic() - started
    (output / "stdout.txt").write_text(stdout, encoding="utf-8")
    (output / "stderr.txt").write_text(stderr, encoding="utf-8")
    result = None
    try:
        result = json.loads(result_path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        pass
    passed = not timed_out and not execution_error and proof_passes(returncode, result, stdout)
    status = "pass" if passed else "timeout" if timed_out else "error" if execution_error else "fail"
    summary = {
        "status": status, "passed": passed, "return_code": returncode,
        "timed_out": timed_out, "execution_error": execution_error,
        "duration_seconds": round(elapsed, 3), "gap": str(gap), "dsl": str(dsl),
        "binary": str(binary), "theorem_library": str(theorem_lib), "sha256": hashes,
        "final_status": result.get("final_status") if isinstance(result, dict) else None,
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(f"{status.upper()}: {output}")
    return 0 if passed else 2 if execution_error else 1


if __name__ == "__main__":
    raise SystemExit(main())
