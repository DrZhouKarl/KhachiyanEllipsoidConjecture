#!/usr/bin/env python3
"""Run fresh Lean checks and validate their output; see lean_guide.md."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_ENTRY = re.compile(
    r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$", re.M
)
INDEPENDENCE = Path("audit/Independence.lean")
STATEMENTS = Path("audit/StatementComparison.lean")


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args, cwd=ROOT):
    return subprocess.check_output(["git", *args], cwd=cwd, text=True).strip()


def check_axioms(source, output):
    expected = re.findall(r"^#print axioms (\S+)$", source, re.M)
    actual = AXIOM_ENTRY.findall(output)
    require(expected and len(set(expected)) == len(expected), "Empty or duplicate audit list")
    require([name for name, _ in actual] == expected, "Compiler/audit coverage mismatch")
    for name, axioms in actual:
        used = {item.strip() for item in axioms.split(",") if item.strip()}
        require(used <= ALLOWED_AXIOMS, f"Forbidden axioms for {name}: {used - ALLOWED_AXIOMS}")
    return len(actual)


def own_git_checkout():
    result = subprocess.run(["git", "rev-parse", "--show-toplevel"], cwd=ROOT,
                            stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True)
    return result.returncode == 0 and Path(result.stdout.strip()).resolve() == ROOT


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True,
                        help="New directory for actual command output and run.json")
    parser.add_argument("--require-cold", action="store_true",
                        help="Reject any preexisting project/dependency Lean build artifacts")
    args = parser.parse_args()
    output = args.output_dir.resolve()
    require(not output.exists(), f"Output directory already exists: {output}")
    versioned = own_git_checkout()
    if versioned:
        require(not git("status", "--porcelain", "--untracked-files=all"),
                "Verification requires a clean committed checkout")
    if args.require_cold:
        compiled = [p for p in (ROOT / ".lake").rglob("*")
                    if p.is_file() and any(part.endswith((".olean", ".ilean")) for part in p.parts)]
        require(not compiled, f"Preexisting Lean artifacts: {compiled[:3]}")
    manifest_path = ROOT / "lake-manifest.json"
    manifest = json.loads(manifest_path.read_text())
    packages = ROOT / manifest["packagesDir"]
    revisions = {}
    for package in manifest["packages"]:
        directory = packages / package["name"]
        require(package["type"] == "git", "Unsupported dependency type")
        head = git("rev-parse", "HEAD", cwd=directory)
        require(head == package["rev"], f"Dependency revision mismatch: {package['name']}")
        require(not git("status", "--porcelain", "--untracked-files=all", cwd=directory),
                f"Dirty dependency: {package['name']}")
        revisions[package["name"]] = head
    inputs = [ROOT / "Khachiyan.lean", *sorted((ROOT / "Khachiyan").glob("*.lean")),
              ROOT / INDEPENDENCE, ROOT / STATEMENTS, ROOT / "lakefile.lean",
              ROOT / "lake-manifest.json", ROOT / "lean-toolchain", Path(__file__).resolve()]
    source_before = {str(p.relative_to(ROOT)): digest(p) for p in inputs}
    output.mkdir(parents=True)
    env = os.environ.copy()
    for name in ["LEAN_PATH", "LEAN_SRC_PATH", "ELAN_TOOLCHAIN", "LAKE_HOME"]:
        env.pop(name, None)
    env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    env["GIT_TERMINAL_PROMPT"] = "0"
    record = {
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "commit": git("rev-parse", "HEAD") if versioned else None,
        "tree": git("rev-parse", "HEAD^{tree}") if versioned else None,
        "require_cold": args.require_cold,
        "dependencies": revisions, "manifest_sha256": digest(manifest_path),
        "commands": [], "success": False,
    }

    def save():
        (output / "run.json").write_text(json.dumps(record, indent=2) + "\n")

    def run(label, command):
        print(f"RUN {label}: {' '.join(command)}", flush=True)
        started = time.monotonic()
        log = output / f"{label}.log"
        with log.open("w") as stream:
            stream.write("$ " + " ".join(command) + "\n")
            stream.flush()
            result = subprocess.run(command, cwd=ROOT, env=env, stdout=stream,
                                    stderr=subprocess.STDOUT, text=True)
            stream.write(f"\nEXIT_CODE={result.returncode}\n")
        record["commands"].append({"command": command, "log": log.name,
                                   "exit_code": result.returncode,
                                   "seconds": round(time.monotonic() - started, 3),
                                   "sha256": digest(log)})
        save()
        require(result.returncode == 0, f"{label} failed; see {log}")
        print(f"PASS {label} ({record['commands'][-1]['seconds']} s)", flush=True)
        return log.read_text()

    try:
        save()
        run("lean-version", ["lean", "--version"])
        run("lake-version", ["lake", "--version"])
        prefix = subprocess.check_output(["lean", "--print-prefix"], cwd=ROOT,
                                         env=env, text=True).strip()
        search = run("lean-path", ["lake", "--no-cache", "env", "printenv", "LEAN_PATH"])
        paths = search.splitlines()[1].split(os.pathsep)
        for value in paths:
            resolved = (ROOT / value).resolve()
            require(resolved.is_relative_to(ROOT) or resolved.is_relative_to(Path(prefix)),
                    f"Lean search path escapes the checkout/toolchain: {resolved}")
        run("build", ["lake", "--no-cache", "--no-ansi", "build"])
        audit = run("axioms", ["lake", "--no-cache", "env", "lean", "Khachiyan/Audit.lean"])
        record["audit_entries"] = check_axioms((ROOT / "Khachiyan/Audit.lean").read_text(), audit)
        independent = run("independence", ["lake", "--no-cache", "env", "lean", str(INDEPENDENCE)])
        record["independent_entries"] = check_axioms((ROOT / INDEPENDENCE).read_text(), independent)
        require("PASS: the actual import closure excludes the M03/M04 route." in independent,
                "Missing independent import check")
        require("PASS: all transitive project proof dependencies belong to M01/M02 or the independent resolvent modules."
                in independent, "Missing transitive proof dependency check")
        statements = run("statements", ["lake", "--no-cache", "env", "lean", str(STATEMENTS)])
        require("PASS: primary M04 and independent M04R have identical hypotheses and conclusions after aligning implicit binders."
                in statements, "Missing final statement comparison")
        require(digest(manifest_path) == record["manifest_sha256"], "Manifest changed during verification")
        if versioned:
            require(not git("status", "--porcelain", "--untracked-files=all"), "Checkout changed during verification")
        require(all(digest(ROOT / name) == value for name, value in source_before.items()),
                "Proof, audit, configuration, or verification sources changed during verification")
        for package in manifest["packages"]:
            directory = packages / package["name"]
            require(git("rev-parse", "HEAD", cwd=directory) == package["rev"], "Dependency revision changed")
            require(not git("status", "--porcelain", "--untracked-files=all", cwd=directory),
                    f"Dependency changed during verification: {package['name']}")
        record["source_sha256"] = {str(p.relative_to(ROOT)): digest(p)
                                    for p in [ROOT / "Khachiyan.lean", *sorted((ROOT / "Khachiyan").glob("*.lean"))]}
        record["success"] = True
        print(f"PASS: fresh build; {record['audit_entries']} full and "
              f"{record['independent_entries']} independent audit entries", flush=True)
    except Exception as error:
        record["error"] = str(error)
        raise
    finally:
        record["finished_utc"] = datetime.now(timezone.utc).isoformat()
        save()


if __name__ == "__main__":
    main()
