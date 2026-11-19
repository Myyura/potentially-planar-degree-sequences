#!/usr/bin/env python3
"""Replay the local import closure with the Lean toolchain's kernel checker.

First run lake build in lean/. Run this script with Python 3.9 or later.
Additional positional arguments specify the root modules. The default root
is SparseBoundary. Replay never starts a build or modifies an object file.
"""
import argparse
import datetime
import functools
import hashlib
import os
from pathlib import Path
import re
import subprocess
import sys
import time

BUNDLE = Path(__file__).resolve().parent.parent
PROJECT = BUNDLE / "lean"
OBJECTS = PROJECT / ".lake" / "build" / "lib" / "lean"
IMPORT = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)$")
MODULE = re.compile(r"[A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)*")
BLOCK = re.compile(r"^\[\d+/\d+\] ")
SUCCESS = re.compile(r"^PASS ([\w.]+) exit=0 elapsed=[0-9.]+s$")


def utc_now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def relative_module(name, suffix):
    return Path(*name.split(".")).with_suffix(suffix)


def local_imports(roots):
    pending = list(roots)
    found = {}
    while pending:
        name = pending.pop()
        if name in found:
            continue
        source = PROJECT / relative_module(name, ".lean")
        if not MODULE.fullmatch(name) or not source.is_file():
            raise ValueError(f"Unknown local module {name}")
        dependencies = []
        for line in source.read_text().splitlines():
            match = IMPORT.match(line.split("--")[0])
            if match:
                for dependency in match.group(1).split():
                    if (PROJECT / relative_module(dependency, ".lean")).is_file():
                        dependencies.append(dependency)
        found[name] = dependencies
        pending.extend(dependencies)
    return found


def checksum(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_prior(path, version):
    if path is None:
        return {}
    lines = path.read_text().splitlines()
    if version not in lines:
        raise ValueError("The earlier log uses a different Lean toolchain.")
    results = {}
    section = []
    for line in lines:
        if BLOCK.match(line):
            section = [line]
        elif section:
            section.append(line)
            success = SUCCESS.fullmatch(line)
            if success:
                if (len(section) >= 4 and section[1].startswith("source sha256 ")
                        and section[2].startswith("olean  sha256 ")):
                    results[success[1]] = (section[1].split()[-1], section[2].split()[-1], section)
                section = []
    return results


def invocation(name, has_descendants, sysroot):
    # The CLI accepts namespace prefixes. For an aggregator, request only
    # that module through leanchecker's own public replay routine.
    if has_descendants:
        data = ("import LeanChecker\n#eval do\n"
                "  Lean.initSearchPath (← Lean.findSysroot)\n"
                f"  replayFromImports `{name}\n")
        return [sysroot / "bin" / "lean", "--stdin"], data, f"lean --stdin: replayFromImports {name}"
    return [sysroot / "bin" / "leanchecker", "-v", name], None, f"leanchecker -v {name}"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("roots", nargs="*", default=["SparseBoundary"])
    parser.add_argument("--log", type=Path, default=BUNDLE / "verification" / "kernel-primary.log")
    parser.add_argument("--reuse-log", type=Path, action="append", default=[],
                        help="reuse matching checks from an earlier local log (repeatable)")
    args = parser.parse_args()
    dependencies = local_imports(args.roots)
    modules = sorted(dependencies)
    setup = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=PROJECT, text=True)
    environment = dict(os.environ, LEAN_PATH=setup.strip())
    sysroot = Path(subprocess.check_output(["lean", "--print-prefix"], cwd=PROJECT, text=True).strip())
    version = subprocess.check_output([sysroot / "bin" / "lean", "--version"], text=True).strip()
    prior_logs = [read_prior(path, version) for path in args.reuse_log]
    digests = {}
    for name in modules:
        source = PROJECT / relative_module(name, ".lean")
        obj = OBJECTS / relative_module(name, ".olean")
        if not obj.is_file() or source.stat().st_mtime_ns > obj.stat().st_mtime_ns:
            sys.exit(f"Missing or outdated object file for {name}. Run lake build first.")
        digests[name] = (checksum(source), checksum(obj))

    @functools.lru_cache(maxsize=None)
    def reusable(index, name):
        earlier = prior_logs[index]
        return (name in earlier and earlier[name][:2] == digests[name]
                and all(reusable(index, dep) for dep in dependencies[name]))

    # Every reused entry must be justified by one internally consistent log.
    # An old object's imports cannot be discharged by records from a newer run.
    chosen = {}
    for name in modules:
        for index, earlier in enumerate(prior_logs):
            if reusable(index, name):
                chosen[name] = earlier[name][2]
                break
    reused = len(chosen)
    with args.log.open("w", buffering=1, encoding="utf-8") as log:
        def record(message):
            print(message, file=log, flush=True)

        record("Primary project kernel replay")
        record(version)
        record("UTC start " + utc_now())
        record("Roots " + ", ".join(args.roots))
        record(f"Local import closure: {len(modules)} modules")
        record(f"Reused {reused} prior checks with matching source, object, and local import closure.")
        for index, name in enumerate(modules, start=1):
            label = f"[{index}/{len(modules)}] "
            if name in chosen:
                section = chosen[name]
                record(BLOCK.sub(label, section[0]))
                for result in section[1:]:
                    record(result)
                continue
            has_descendants = any(other.startswith(name + ".") for other in modules)
            cmd, stdin, display = invocation(name, has_descendants, sysroot)
            record(label + display)
            record("source sha256 " + digests[name][0])
            record("olean  sha256 " + digests[name][1])
            record("started UTC " + utc_now())
            started = time.monotonic()
            proc = subprocess.run(cmd, cwd=PROJECT, env=environment, input=stdin,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            if proc.stdout:
                record(proc.stdout.rstrip())
            record(f"{'PASS' if proc.returncode == 0 else 'FAIL'} {name} exit={proc.returncode} elapsed={time.monotonic()-started:.2f}s")
            if proc.returncode:
                return proc.returncode
        for name in modules:
            final = (checksum(PROJECT / relative_module(name, ".lean")),
                     checksum(OBJECTS / relative_module(name, ".olean")))
            if digests[name] != final:
                record("FAIL changed during replay: " + name)
                return 1
        record(f"PASS final import closure: all {len(modules)} local modules")
        record("UTC finish " + utc_now())
    return 0


if __name__ == "__main__":
    sys.exit(main())
