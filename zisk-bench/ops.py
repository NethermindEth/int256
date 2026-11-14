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

M256 = 1 << 256
BN254_P = 0x30644E72E131A029B85045B68181585D97816A916871CA8D3C208C16D87CFD47
BN254_R = 0x30644E72E131A029B85045B68181585D2833E84879B9709143E1F593F0000001
SECP_P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
SECP_N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
P251 = (1 << 251) + 17 * (1 << 192) + 1
P25519 = (1 << 255) - 19
P256P = 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
P256N = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
OPS = {"MUL": 1, "DIV": 2, "MOD": 3, "SMOD": 4, "SDIV": 5, "MULMOD": 6, "ADDMOD": 7, "EXP": 8}
STEPS = re.compile(r"^STEPS\s+(\d[\d,]*)\s*$", re.MULTILINE)
VARIABLE = re.compile(r"^VARIABLE\s+(\d[\d,]*)\s", re.MULTILINE)


def signed(x):
    return x - M256 if x >> 255 else x


def expected(op, a, b, m):
    if op == "MUL":
        return a * b % M256
    if op == "DIV":
        return a // b
    if op == "MOD":
        return a % b
    if op == "SMOD":
        x, y = signed(a), signed(b)
        r = abs(x) % abs(y)
        return (-r if x < 0 else r) % M256
    if op == "SDIV":
        x, y = signed(a), signed(b)
        q = abs(x) // abs(y)
        return (-q if (x < 0) != (y < 0) else q) % M256
    if op == "MULMOD":
        return a * b % m
    if op == "ADDMOD":
        return (a + b) % m
    if op == "EXP":
        return pow(a, b, M256)
    raise ValueError(op)


def cases():
    out = []
    for seed in range(3):
        rng = random.Random(seed)

        def r(bits):
            return rng.getrandbits(bits) | (1 << (bits - 1))

        def neg(x):
            return (M256 - x) % M256

        for x, y in [(256, 256), (128, 128), (64, 256), (192, 64)]:
            out.append(("MUL", f"{x}x{y}", r(x), r(y), 0))
        for x, y in [(256, 32), (256, 64), (256, 128), (256, 192), (256, 256), (192, 64), (192, 128), (128, 64), (128, 128), (100, 90), (64, 64), (64, 128)]:
            out.append(("DIV", f"{x}d{y}", r(x), r(y), 0))
            out.append(("MOD", f"{x}r{y}", r(x), r(y), 0))
        for name, y in [("wad", 10**18), ("ten", 10), ("u16", r(16))]:
            out.append(("DIV", f"256d{name}", r(256), y, 0))
            out.append(("MOD", f"256r{name}", r(256), y, 0))
            out.append(("DIV", f"200d{name}", r(200), y, 0))
        for name, mod in [("bn254r", BN254_R), ("bn254p", BN254_P), ("secpP", SECP_P), ("secpN", SECP_N)]:
            out.append(("MOD", f"256r{name}", r(256), mod, 0))
        for x, y in [(255, 255), (255, 128), (255, 64), (64, 64), (128, 64)]:
            for sx in (0, 1):
                for sy in (0, 1):
                    a, b = r(x - 1 if x == 255 else x), r(y - 1 if y == 255 else y)
                    a, b = (neg(a) if sx else a), (neg(b) if sy else b)
                    tag = f"{'-' if sx else '+'}{x}{'-' if sy else '+'}{y}"
                    out.append(("SMOD", tag, a, b, 0))
                    out.append(("SDIV", tag, a, b, 0))
        out.append(("SDIV", "min_d_-1", 1 << 255, M256 - 1, 0))
        for name, mod in [("m64", r(64)), ("m128", r(128)), ("m192", r(192)), ("m256", r(256)), ("bn254p", BN254_P), ("bn254r", BN254_R), ("secpP", SECP_P), ("secpN", SECP_N), ("p251", P251), ("p25519", P25519), ("p256p", P256P), ("p256n", P256N)]:
            out.append(("MULMOD", f"fullx{name}", r(256), r(256), mod))
            out.append(("MULMOD", f"redx{name}", rng.randrange(mod), rng.randrange(mod), mod))
        for name, mod in [("m64", r(64)), ("m128", r(128)), ("m256", r(256))]:
            out.append(("ADDMOD", f"full+{name}", r(256), r(256), mod))
        out.append(("EXP", "3^27bit", 3, r(27) | 1, 0))
        out.append(("EXP", "full^64bit", r(256) | 1, r(64), 0))
    rows = []
    for index, (op, shape, a, b, m) in enumerate(cases_unique(out)):
        rows.append({"case": f"{op}-{shape}-{index}", "op": op, "shape": shape, "a": hex(a), "b": hex(b), "m": hex(m)})
    return rows


def cases_unique(items):
    return items


def payload(op, a, b, m, reps):
    data = struct.pack("<ii", OPS[op], reps) + a.to_bytes(32, "little") + b.to_bytes(32, "little") + m.to_bytes(32, "little")
    framed = struct.pack("<Q", len(data)) + data
    return framed + b"\0" * (-len(framed) % 8)


def generate(args):
    work = pathlib.Path(args.work)
    (work / "in").mkdir(parents=True, exist_ok=True)
    rows = cases()
    rows.append({"case": "zero", "op": "MUL", "shape": "zero", "a": "0x0", "b": "0x0", "m": "0x0"})
    for row in rows:
        reps = 0 if row["case"] == "zero" else 1
        (work / "in" / f"{row['case']}.bin").write_bytes(payload(row["op"], int(row["a"], 16), int(row["b"], 16), int(row["m"], 16), reps))
    (work / "ops.json").write_text(json.dumps(rows))
    print(f"{len(rows)} cases")


def run_one(container, version, row):
    proc = subprocess.run(["docker", "exec", container, "ziskemu", "-e", f"/n/ops-{version}", "-i", f"/n/in/{row['case']}.bin", "-X", "--no-thousands-sep"], capture_output=True, text=True)
    log = proc.stdout + proc.stderr
    steps = STEPS.search(log)
    variable = VARIABLE.search(log)
    value = 0 if row["case"] == "zero" else expected(row["op"], int(row["a"], 16), int(row["b"], 16), int(row["m"], 16))
    ok = value.to_bytes(32, "little").hex() in log
    return {"version": version, "case": row["case"], "op": row["op"], "shape": row["shape"],
            "steps": int(steps.group(1).replace(",", "")) if steps else -1,
            "variable": int(variable.group(1).replace(",", "")) if variable else -1,
            "ok": ok, "log": "" if ok and steps else log[-3000:]}


def run(args):
    work = pathlib.Path(args.work)
    rows = json.loads((work / "ops.json").read_text())
    jobs = [(version, row) for version in args.versions.split() for row in rows]
    results = []
    started = time.monotonic()
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for result in pool.map(lambda job: run_one(args.container, *job), jobs):
            results.append(result)
            if result["log"]:
                print(json.dumps(result)[:3500])
    with open(work / "ops-results.csv", "w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=[key for key in results[0] if key != "log"])
        writer.writeheader()
        for result in results:
            writer.writerow({key: value for key, value in result.items() if key != "log"})
    bad = [result for result in results if not result["ok"] or result["steps"] < 0]
    print(f"{len(results)} runs in {time.monotonic() - started:.0f}s, {len(bad)} failed")
    return 1 if bad else 0


def main():
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    gen = sub.add_parser("gen")
    gen.add_argument("--work", required=True)
    runner = sub.add_parser("run")
    runner.add_argument("--work", required=True)
    runner.add_argument("--container", required=True)
    runner.add_argument("--versions", required=True)
    runner.add_argument("--jobs", type=int, default=os.cpu_count())
    args = parser.parse_args()
    if args.command == "gen":
        generate(args)
        return 0
    return run(args)


if __name__ == "__main__":
    sys.exit(main())
