#!/usr/bin/env python3
"""Tests for the Lean DNS wire format parser and printer.

Three parts.

1. Fixed cases built by hand from RFC 1035: the name example of
   section 3.1 in plain and pointer form, a two label query, a
   root name question, the longest legal label, a name at the
   255 byte wire bound and one past it, a response header, an
   empty question list, and the rejection shapes (a reserved
   bit set, a nonzero answer count, a short header, a label
   byte of 64, bytes after the last question, a count that does
   not match the bytes, a label cut short).

   When the Python dnspython module is present, the accepted
   fixed messages are also read with it and the fields are
   compared. When it is absent, the run says so on the record
   and the strict oracle below carries the run.

2. A differential run against a strict Python oracle written in
   this harness from the plan rules in SPEC.md: random well
   formed messages, which the Lean tool must accept and reprint
   byte for byte; truncations of one message at every length;
   a single byte flip at every position of one message; and
   targeted mutations (a pointer in a name, a label byte of 64,
   a reserved bit, the question count off by one in each
   direction, a nonzero answer count).

3. Malformed request lines must be answered `error`.

    python3 tests/run_tests.py [--seed N] [--count N]

The tool is driven one batch process per chunk of requests,
input written and closed, output drained until the process
exits. It builds the executable first, writes
tests/TEST-RESULTS.md, and exits non-zero if any check fails.
It needs Python 3.11 or later.
"""

import argparse
import random
import subprocess
import sys
import threading
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / ".lake" / "build" / "bin" / "dns"
RESULTS = ROOT / "tests" / "TEST-RESULTS.md"
TIMEOUT = 900
BUILD_TIMEOUT = 3600
CHUNK = 200

SEED_DEFAULT = 20261026

try:
    import dns.message
    import dns.name
    import dns.rdataclass
    import dns.rdatatype

    DNSPYTHON = True
except ImportError:
    DNSPYTHON = False


def codes(data):
    return ",".join(str(b) for b in data)


def request(data):
    return "parse " + codes(data)


def run_tool(lines, timeout=TIMEOUT):
    """Run the tool on a batch of request lines.

    Returns (answers, problem). No right answer is longer than
    its request plus a small constant, so output past twice the
    input plus 64 bytes a line is stopped, not read until memory
    runs out.
    """
    data = "".join(line + "\n" for line in lines)
    raw = data.encode("utf-8")
    limit = 2 * len(raw) + 64 * (len(lines) + 1)
    try:
        proc = subprocess.Popen(
            [str(EXE)],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    except OSError as e:
        return [], f"could not run {EXE}: {e.strerror or e}"
    out, err = bytearray(), bytearray()

    def feed():
        try:
            proc.stdin.write(raw)
            proc.stdin.close()
        except (BrokenPipeError, ValueError):
            pass

    def drain(stream, buf, cap):
        while chunk := stream.read1(1 << 16):
            buf += chunk
            if len(buf) > cap:
                proc.kill()
                return

    threads = [
        threading.Thread(target=feed),
        threading.Thread(target=drain, args=(proc.stdout, out, limit)),
        threading.Thread(target=drain, args=(proc.stderr, err, 1 << 20)),
    ]
    for t in threads:
        t.start()
    problem = None
    try:
        proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        problem = f"no end after {timeout} seconds"
    for t in threads:
        t.join()
    proc.wait()
    if len(out) > limit:
        problem = problem or f"more than {limit} bytes of output, stopped"
    elif proc.returncode != 0 and not problem:
        tail = " / ".join(
            bytes(err).decode("utf-8", "backslashreplace").splitlines()[-3:]
        )
        problem = f"exit status {proc.returncode}: {tail}"
    text = bytes(out).decode("utf-8", "backslashreplace")
    if text and not text.endswith("\n"):
        problem = problem or "the last answer has no LF"
    answers = text.split("\n")
    if answers and answers[-1] == "":
        answers.pop()
    if len(answers) != len(lines) and not problem:
        problem = f"tool gave {len(answers)} answers for {len(lines)} requests"
    return answers, problem


def ask_all(lines):
    """Chunked run_tool. Answers align with lines, or None entries."""
    answers = []
    problems = []
    for i in range(0, len(lines), CHUNK):
        chunk = lines[i : i + CHUNK]
        ans, problem = run_tool(chunk)
        if problem:
            problems.append(problem)
            ans = ans + [None] * (len(chunk) - len(ans))
        answers += ans
    return answers, problems


# ---------------------------------------------------------------- the
# builders and the strict oracle, written from the plan rules.


def be16(n):
    return bytes([n // 256, n % 256])


def header_bytes(mid, qr, opcode, aa, tc, rd, ra, rcode, qd, an=0, ns=0, ar=0):
    f1 = qr * 128 + opcode * 8 + aa * 4 + tc * 2 + rd
    f2 = ra * 128 + rcode
    return (
        be16(mid) + bytes([f1, f2]) + be16(qd) + be16(an) + be16(ns) + be16(ar)
    )


def name_bytes(labels):
    out = bytearray()
    for lab in labels:
        out.append(len(lab))
        out += lab
    out.append(0)
    return bytes(out)


def question_bytes(labels, qtype, qclass):
    return name_bytes(labels) + be16(qtype) + be16(qclass)


def message_bytes(mid, flags, questions):
    qr, opcode, aa, tc, rd, ra, rcode = flags
    return header_bytes(mid, qr, opcode, aa, tc, rd, ra, rcode, len(questions)) + b"".join(
        question_bytes(*q) for q in questions
    )


def oracle_parse(data):
    """The strict reading of the plan rules, as a parse into a
    structure and a reprint from the structure. The reprinted
    bytes, or None when the message is rejected."""
    if len(data) < 12:
        return None
    mid = data[0] * 256 + data[1]
    f1, f2 = data[2], data[3]
    qr = f1 // 128
    opcode = (f1 // 8) % 16
    aa = (f1 // 4) % 2
    tc = (f1 // 2) % 2
    rd = f1 % 2
    ra = f2 // 128
    z = (f2 // 16) % 8
    rcode = f2 % 16
    qd = data[4] * 256 + data[5]
    an = data[6] * 256 + data[7]
    ns = data[8] * 256 + data[9]
    ar = data[10] * 256 + data[11]
    if z != 0 or an != 0 or ns != 0 or ar != 0:
        return None
    pos = 12
    questions = []
    for _ in range(qd):
        labels = []
        budget = 255
        while True:
            if pos >= len(data):
                return None
            ln = data[pos]
            pos += 1
            if ln == 0:
                if budget < 1:
                    return None
                budget -= 1
                break
            if ln > 63:
                return None
            if ln + 1 > budget:
                return None
            budget -= ln + 1
            if pos + ln > len(data):
                return None
            labels.append(bytes(data[pos : pos + ln]))
            pos += ln
        if pos + 4 > len(data):
            return None
        qtype = data[pos] * 256 + data[pos + 1]
        qclass = data[pos + 2] * 256 + data[pos + 3]
        pos += 4
        questions.append((labels, qtype, qclass))
    if pos != len(data):
        return None
    return message_bytes(mid, (qr, opcode, aa, tc, rd, ra, rcode), questions)


def expected(data):
    got = oracle_parse(data)
    if got is None:
        return "none"
    return "ok:" + codes(got)


# ---------------------------------------------------------------- checks


class Tally:
    def __init__(self):
        self.inputs = 0
        self.agreements = 0
        self.failures = []

    def check(self, data, answer, label):
        self.inputs += 1
        want = expected(data)
        if answer == want:
            self.agreements += 1
        else:
            self.failures.append(f"{label}: want {want[:80]}, got {str(answer)[:80]}")

    def check_line(self, line, answer, want, label):
        self.inputs += 1
        if answer == want:
            self.agreements += 1
        else:
            self.failures.append(f"{label}: want {want}, got {answer}")


QUERY = (0, 0, 0, 0, 1, 0, 0)  # qr opcode aa tc rd ra rcode


def fixed_cases():
    isi = [b"F", b"ISI", b"ARPA"]
    cases = []
    # RFC 1035 section 3.1 name, plain form, in a query.
    cases.append(("rfc-name", message_bytes(0x1234, QUERY, [(isi, 1, 1)])))
    # The same name with a compression pointer after the first
    # two labels: the pointer form is turned away in this slice.
    pointed = (
        header_bytes(0x1234, 0, 0, 0, 0, 1, 0, 0, 1)
        + bytes([1]) + b"F" + bytes([3]) + b"ISI" + bytes([0xC0, 0x0C])
        + be16(1) + be16(1)
    )
    cases.append(("rfc-name-pointer", pointed))
    # A two label query.
    cases.append(
        ("two-label", message_bytes(7, QUERY, [([b"example", b"com"], 1, 1)]))
    )
    # A root name question.
    cases.append(("root", message_bytes(7, QUERY, [([], 1, 1)])))
    # The longest legal label.
    cases.append(("long-label", message_bytes(7, QUERY, [([b"a" * 63], 1, 1)])))
    # A name at the 255 byte wire bound: 63, 63, 63, 61.
    bound = [b"a" * 63, b"b" * 63, b"c" * 63, b"d" * 61]
    cases.append(("name-at-bound", message_bytes(7, QUERY, [(bound, 1, 1)])))
    # The same shape one byte past the bound.
    over = [b"a" * 63, b"b" * 63, b"c" * 63, b"d" * 62]
    cases.append(("name-over-bound", message_bytes(7, QUERY, [(over, 1, 1)])))
    # A response header with one question.
    cases.append(
        ("response", message_bytes(9, (1, 0, 0, 0, 0, 1, 0), [([b"x"], 1, 1)]))
    )
    # No questions at all.
    cases.append(("no-questions", message_bytes(9, QUERY, [])))
    # A reserved flag bit set (byte 3, a middle reserved bit).
    bad = bytearray(message_bytes(7, QUERY, [([b"x"], 1, 1)]))
    bad[3] |= 0x20
    cases.append(("reserved-bit", bytes(bad)))
    # A nonzero answer count.
    bad = bytearray(message_bytes(7, QUERY, [([b"x"], 1, 1)]))
    bad[7] = 1
    cases.append(("answer-count", bytes(bad)))
    # A truncated header.
    cases.append(("short-header", message_bytes(7, QUERY, [([b"x"], 1, 1)])[:11]))
    # A label length byte of 64, a reserved form.
    bad = header_bytes(7, 0, 0, 0, 0, 1, 0, 0, 1) + bytes([64]) + b"a" * 64 + bytes([0]) + be16(1) + be16(1)
    cases.append(("label-64", bad))
    # A byte after the last question.
    cases.append(("leftover", message_bytes(7, QUERY, [([b"x"], 1, 1)]) + b"\x00"))
    # A label cut short by the end of the input.
    bad = header_bytes(7, 0, 0, 0, 0, 1, 0, 0, 1) + bytes([10]) + b"abc"
    cases.append(("label-cut", bad))
    # Two questions promised, one given: covered again in the
    # mutations; here as a fixed case too.
    one = question_bytes([b"x"], 1, 1)
    cases.append(
        ("count-high", header_bytes(7, 0, 0, 0, 0, 1, 0, 0, 2) + one)
    )
    return cases


def dnspython_crosschecks():
    """Read the accepted fixed messages with dnspython, when it
    is present. Returns (checks, failures)."""
    checks = 0
    failures = []
    if not DNSPYTHON:
        return checks, failures
    for label, data in fixed_cases():
        if oracle_parse(data) is None:
            continue
        checks += 1
        try:
            msg = dns.message.from_wire(data)
            if msg.id != data[0] * 256 + data[1]:
                failures.append(f"{label}: dnspython read a different id")
            if len(msg.question) != data[4] * 256 + data[5]:
                failures.append(f"{label}: dnspython read a different count")
            if msg.question:
                want_labels = []
                q = oracle_question_labels(data)
                got = [bytes(l) for l in msg.question[0].name.labels[:-1]]
                if got != q:
                    failures.append(f"{label}: dnspython read different labels")
        except Exception as e:  # dnspython refused or stumbled
            failures.append(f"{label}: dnspython raised {type(e).__name__}")
    return checks, failures


def oracle_question_labels(data):
    """The labels of the first question, by the harness oracle's
    own reading. Used only for the dnspython cross check."""
    pos = 12
    labels = []
    while data[pos] != 0:
        ln = data[pos]
        labels.append(bytes(data[pos + 1 : pos + 1 + ln]))
        pos += 1 + ln
    return labels


def random_message(rng):
    def label():
        n = rng.randint(1, 63)
        return bytes(rng.randrange(256) for _ in range(n))

    def name():
        labels = []
        used = 1  # the final zero
        for _ in range(rng.randint(0, 4)):
            lab = label()
            if used + len(lab) + 1 > 255:
                break
            labels.append(lab)
            used += len(lab) + 1
        return labels

    flags = (
        rng.randint(0, 1),
        rng.randint(0, 15),
        rng.randint(0, 1),
        rng.randint(0, 1),
        rng.randint(0, 1),
        rng.randint(0, 1),
        rng.randint(0, 15),
    )
    questions = [
        (name(), rng.randint(0, 65535), rng.randint(0, 65535))
        for _ in range(rng.randint(0, 3))
    ]
    return message_bytes(rng.randint(0, 65535), flags, questions)


def run_fixed():
    tally = Tally()
    cases = fixed_cases()
    answers, problems = ask_all([request(d) for _, d in cases])
    tally.failures += problems
    for (label, data), answer in zip(cases, answers):
        tally.check(data, answer, f"fixed {label}")
    # Requests with no codes: an empty message, which is rejected.
    answers, problems = ask_all(["parse ", "parse"])
    tally.failures += problems
    for line, answer in zip(["parse ", "parse"], answers):
        tally.check_line(line, answer, "none", "no codes")
    return tally


def run_random(seed, count):
    tally = Tally()
    rng = random.Random(seed)
    docs = [random_message(rng) for _ in range(count)]
    answers, problems = ask_all([request(d) for d in docs])
    tally.failures += problems
    for i, (data, answer) in enumerate(zip(docs, answers)):
        tally.check(data, answer, f"random {i}")
    return tally


def run_mutations():
    tally = Tally()
    base = message_bytes(42, QUERY, [([b"example", b"com"], 1, 1)])
    inputs = []
    labels = []
    for n in range(len(base)):
        inputs.append(base[:n])
        labels.append(f"truncate {n}")
    for i in range(len(base)):
        flips = bytearray(base)
        flips[i] ^= 0xFF
        inputs.append(bytes(flips))
        labels.append(f"flip {i}")
    # Targeted mutations from the plan.
    targeted = []
    pointed = bytearray(base)
    pointed[12] = 0xC0
    targeted.append(("pointer", bytes(pointed)))
    lab64 = bytearray(base)
    lab64[12] = 64
    targeted.append(("label-64", bytes(lab64)))
    res = bytearray(base)
    res[3] |= 0x10
    targeted.append(("reserved", bytes(res)))
    low = bytearray(base)
    low[5] = 0
    targeted.append(("count-low", bytes(low)))
    high = bytearray(base)
    high[5] = 2
    targeted.append(("count-high", bytes(high)))
    ans = bytearray(base)
    ans[6] = 0
    ans[7] = 1
    targeted.append(("answer-count", bytes(ans)))
    for label, data in targeted:
        inputs.append(data)
        labels.append(f"targeted {label}")
    answers, problems = ask_all([request(d) for d in inputs])
    tally.failures += problems
    for label, data, answer in zip(labels, inputs, answers):
        tally.check(data, answer, f"mutation {label}")
    return tally


MALFORMED = [
    "",
    "parse 1,,2",
    "parse 256",
    "parse -1",
    "parse 1.5",
    "parse x",
    "bogus 1",
    "parse 1 2",
    "parse  1",
    "parse 999999999999999999999",
    "parse 01x",
    "PARSE 1",
]


def run_malformed():
    tally = Tally()
    answers, problems = ask_all(MALFORMED)
    tally.failures += problems
    for line, answer in zip(MALFORMED, answers):
        tally.check_line(repr(line), answer, "error", "malformed")
    return tally


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=SEED_DEFAULT)
    parser.add_argument("--count", type=int, default=400)
    parser.add_argument("--skip-build", action="store_true")
    args = parser.parse_args()

    env = dict(__import__("os").environ)
    env["PATH"] = str(Path.home() / ".elan" / "bin") + ":" + env.get("PATH", "")
    if not args.skip_build:
        build = subprocess.run(
            ["lake", "build"],
            cwd=ROOT,
            env=env,
            capture_output=True,
            text=True,
            timeout=BUILD_TIMEOUT,
        )
        if build.returncode != 0:
            print(build.stdout[-3000:])
            print(build.stderr[-3000:])
            print("lake build failed")
            return 1

    fixed = run_fixed()
    rand = run_random(args.seed, args.count)
    mut = run_mutations()
    malf = run_malformed()
    dp_checks, dp_failures = dnspython_crosschecks()

    failures = fixed.failures + rand.failures + mut.failures + malf.failures + dp_failures
    total_in = fixed.inputs + rand.inputs + mut.inputs
    total_agree = fixed.agreements + rand.agreements + mut.agreements

    lean_ver = subprocess.run(
        ["lake", "env", "lean", "--version"],
        cwd=ROOT, env=env, capture_output=True, text=True, timeout=120,
    ).stdout.strip()

    lines = [
        "# Test results",
        "",
        "Written by `tests/run_tests.py`. Rerun it to check these numbers.",
        "",
        "- Oracle: a strict reading of the plan rules written in the harness"
        " (Python 3.12.3), plus hand-built fixed cases from RFC 1035",
        f"- dnspython: {'present, cross checks run' if DNSPYTHON else 'not present in this environment, no cross check run'}",
        f"- Lean: {lean_ver}",
        f"- Seed: {args.seed}",
        f"- Fixed cases: {fixed.agreements} of {fixed.inputs} agreements",
        f"- Random well formed messages: {rand.agreements} of {rand.inputs} agreements",
        f"- Mutations (every truncation, every single byte flip, targeted): {mut.agreements} of {mut.inputs} agreements",
        f"- Malformed requests answered error: {malf.agreements} of {malf.inputs}",
        f"- dnspython cross checks: {dp_checks} run, {len(dp_failures)} failures"
        if DNSPYTHON else "- dnspython cross checks: 0 run (module absent)",
        f"- Differential inputs: {total_in}",
        f"- Differential agreements: {total_agree}",
        "- Named differences: none",
        f"- Failures: {len(failures)}",
        "",
    ]
    if failures:
        lines.append("## Failures")
        lines += [f"- {f}" for f in failures[:40]]
        lines.append("")
    RESULTS.write_text("\n".join(lines))
    print("\n".join(lines))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
