#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
# SPDX-License-Identifier: MIT

import argparse
import concurrent.futures
import csv
import json
import os
import pathlib
import random
import re
import struct
import subprocess
import sys
import time

BASES = {
    "b3": 3,
    "b64": 0xFFFFFFFFFFFFFFC5,
    "bfull": 0x9E3779B97F4A7C15F39CC0605CEDC8341082276BF3A27251C9A8F3C6B5D2E2B7,
}

MODES = {
    "B": ("sweep", 1000, 1000, 0),
    "W2": ("sweep", -1, -1, 2),
    "W3": ("sweep", -1, -1, 3),
    "W4": ("sweep", -1, -1, 4),
    "W5": ("sweep", -1, -1, 5),
    "M": ("main", 0, 0, 0),
}

STEPS = re.compile(r"^STEPS\s+(\d[\d,]*)\s*$", re.MULTILINE)
TOTAL = re.compile(r"^TOTAL\s+(\d[\d,]*)\s", re.MULTILINE)
VARIABLE = re.compile(r"^VARIABLE\s+(\d[\d,]*)\s", re.MULTILINE)


def grid(name):
    if name == "pilot":
        return [(16, k) for k in (4, 8, 12)] + [(40, k) for k in (10, 20, 30)] + [(72, k) for k in (20, 40, 60)]
    if name == "short":
        lengths = list(range(9, 33))
        return [(n, k) for n in lengths for k in range(2, n + 1)]
    short = [9, 10, 11, 12, 13, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32]
    mid = [33, 34, 36, 38, 40, 44, 48, 52, 56, 60, 64]
    long = [65, 66, 68, 72, 76, 79]
    points = [(n, k) for n in short for k in range(2, n + 1)]
    for n in mid + long:
        ks = sorted(set(list(range(2, n + 1, 2)) + [n]))
        points += [(n, k) for k in ks]
    return points


def exponent(n, k):
    rng = random.Random(n * 1000 + k)
    bits = rng.sample(range(n - 1), k - 1)
    value = 1 << (n - 1)
    for bit in bits:
        value |= 1 << bit
    return value


def payload(mode, base, exp, reps):
    _, cutoff, short, width = MODES[mode]
    data = struct.pack("<iiii", cutoff, short, width, reps)
    data += base.to_bytes(32, "little") + exp.to_bytes(32, "little")
    framed = struct.pack("<Q", len(data)) + data
    framed += b"\0" * (-len(framed) % 8)
    return framed


def generate(args):
    work = pathlib.Path(args.work)
    inputs = work / "in"
    inputs.mkdir(parents=True, exist_ok=True)
    modes = args.modes.split(",")
    bases = args.bases.split(",")
    cases = []
    for mode in modes:
        cases.append({"id": f"zero-{mode}", "mode": mode, "base": "b3", "n": 0, "k": 0, "exp": "0", "reps": 0})
    for n, k in grid(args.grid):
        exp = exponent(n, k)
        for base in bases:
            for mode in modes:
                cases.append({"id": f"{base}-{n}-{k}-{mode}", "mode": mode, "base": base, "n": n, "k": k, "exp": hex(exp), "reps": 1})
    for case in cases:
        exp = int(case["exp"], 16)
        (inputs / f"{case['id']}.bin").write_bytes(payload(case["mode"], BASES[case["base"]], exp, case["reps"]))
    (work / "cases.json").write_text(json.dumps(cases))
    print(f"{len(cases)} cases")


def run_one(container, case):
    elf = MODES[case["mode"]][0]
    started = time.monotonic()
    proc = subprocess.run(
        ["docker", "exec", container, "ziskemu", "-e", f"/n/exp-{elf}", "-i", f"/n/in/{case['id']}.bin", "-X", "--no-thousands-sep"],
        capture_output=True, text=True)
    log = proc.stdout + proc.stderr
    steps = STEPS.search(log)
    total = TOTAL.search(log)
    variable = VARIABLE.search(log)
    base = BASES[case["base"]]
    expected = (case["reps"] * pow(base, int(case["exp"], 16), 1 << 256)) % (1 << 256)
    le = expected.to_bytes(32, "little").hex()
    be = expected.to_bytes(32, "big").hex()
    ok = le in log
    return {
        "id": case["id"], "mode": case["mode"], "base": case["base"], "n": case["n"], "k": case["k"],
        "steps": int(steps.group(1).replace(",", "")) if steps else -1,
        "total": int(total.group(1).replace(",", "")) if total else -1,
        "variable": int(variable.group(1).replace(",", "")) if variable else -1,
        "ok": ok, "rc": proc.returncode, "seconds": round(time.monotonic() - started, 3), "log": log if (not ok or steps is None) else "",
    }


def run(args):
    work = pathlib.Path(args.work)
    cases = json.loads((work / "cases.json").read_text())
    rows = []
    started = time.monotonic()
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for index, row in enumerate(pool.map(lambda case: run_one(args.container, case), cases)):
            rows.append(row)
            if index < 3 or row["log"]:
                print(json.dumps(row)[:4000])
            if index % 200 == 0:
                print(f"{index}/{len(cases)} {time.monotonic() - started:.0f}s", flush=True)
    with open(work / "results.csv", "w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=[key for key in rows[0] if key != "log"])
        writer.writeheader()
        for row in rows:
            writer.writerow({key: value for key, value in row.items() if key != "log"})
    bad = [row for row in rows if not row["ok"] or row["steps"] < 0]
    print(f"{len(rows)} runs in {time.monotonic() - started:.0f}s, {len(bad)} failed")
    zero = {row["mode"]: row["steps"] for row in rows if row["id"].startswith("zero-")}
    print("zero frames", zero)
    return 1 if bad else 0


def main():
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    gen = sub.add_parser("gen")
    gen.add_argument("--work", required=True)
    gen.add_argument("--grid", default="pilot")
    gen.add_argument("--modes", default="B,W2,W3,W4,W5,M")
    gen.add_argument("--bases", default="b3,b64,bfull")
    runner = sub.add_parser("run")
    runner.add_argument("--work", required=True)
    runner.add_argument("--container", required=True)
    runner.add_argument("--jobs", type=int, default=os.cpu_count())
    args = parser.parse_args()
    if args.command == "gen":
        generate(args)
        return 0
    return run(args)


if __name__ == "__main__":
    sys.exit(main())
