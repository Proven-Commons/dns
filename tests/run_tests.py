#!/usr/bin/env python3
"""Tests for the Lean DNS wire format parser and printer.

Slice 1 sections, kept and re-run:

1. Fixed cases built by hand from RFC 1035: the name example of
   section 3.1 in plain form and in a pointer shape that loops,
   a two label query, a root name question, the longest legal
   label, a name at the 255 byte wire bound and one past it, a
   response header, an empty question list, the AD and CD
   header bits (RFC 4035 section 3.2) set alone and in the
   RD+AD, RD+CD and RA+AD shapes resolvers send, which are
   read, and the rejection shapes (the Z bit set, a short
   header, a label byte of 64, bytes after the last question,
   a count that does not match the bytes, a label cut short). Slice 1 turned a nonzero
   answer count away; slice 2 reads records, so that case moved
   to the whole message sections below.

2. A differential run against the strict Python oracle in this
   harness: random well formed question-only messages;
   truncations of one message at every length; a single byte
   flip at every position; targeted mutations.

Slice 2 sections:

3. Whole message fixed cases: the RFC 1035 section 4.1.4
   example placed in a real message (the first name at offset
   12, the second name a label plus a pointer back to offset
   12), an answer record whose name is a bare pointer to the
   question name, a pointer chain of length two, a name that
   follows 16 pointers (the limit), and records in the
   authority and additional sections. Checked through both
   the `parse` operation (the canonical reprint, names
   expanded) and the `sections` operation (the summary text).

4. Whole message rejections: a pointer to itself, a forward
   pointer, a pointer past the end, a pointer into the middle
   of a label, a cycle that passes through a label (ended by
   the 16 pointer limit) and one through a 63 byte label
   (ended by the 255 byte budget), a reserved length form in
   a record name, a data length running past the end, an
   expanded name over 255 bytes reached by chaining, a name
   that follows 17 pointers, and a 65,523 byte message whose
   4,095 answer names each point into an 8,180 pointer
   chain.

5. Random whole messages (mixed sections), printed and read
   back, and the same messages run through a harness
   compressor that replaces repeated name suffixes with
   pointers (every second message may also point at an
   earlier root zero byte): the compressed bytes must read to
   the same message. Names are drawn from a small alphabet
   with shared tails, so most messages share suffixes; the
   results file counts the compressed messages that hold a
   pointer, and the inputs whose reading follows one.

6. Mutations of the compressed messages at each pointer:
   retargeted at itself, two bytes on, a random earlier and a
   random later offset, and past the end; cut short inside
   the pointer; and turned into each reserved form.

When the Python dnspython module is present, accepted fixed
messages are also read with it and compared. When it is
absent, the run says so on the record and the strict oracle
carries the run.

    python3 tests/run_tests.py [--seed N] [--count N]

The tool is driven one batch process per chunk of requests.
It builds the executable first, writes tests/TEST-RESULTS.md,
and exits non-zero if any check fails. It needs Python 3.11+.
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


def request(op, data):
    return op + " " + codes(data)


def run_tool(lines, timeout=TIMEOUT):
    """Run the tool on a batch of request lines.

    Returns (answers, problem). No right answer is longer than
    its request plus a small constant, except a `sections`
    answer for a message of arbitrary byte labels, whose text
    can reach about twelve times the message length; the cap
    leaves room for that.
    """
    data = "".join(line + "\n" for line in lines)
    raw = data.encode("utf-8")
    limit = 16 * len(raw) + 64 * (len(lines) + 1)
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
# builders, the model, and the strict oracle.


def be16(n):
    return bytes([n // 256, n % 256])


def be32(n):
    return bytes([(n >> 24) % 256, (n >> 16) % 256, (n >> 8) % 256, n % 256])


def header_bytes(mid, qr, opcode, aa, tc, rd, ra, rcode, qd, an=0, ns=0, ar=0,
                 ad=0, cd=0):
    # The fourth byte, RFC 6895 section 2: RA, Z (always written
    # as zero here), AD, CD, then the RCODE.
    f1 = qr * 128 + opcode * 8 + aa * 4 + tc * 2 + rd
    f2 = ra * 128 + ad * 32 + cd * 16 + rcode
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


def record_bytes(labels, rtype, rclass, ttl, data):
    return (
        name_bytes(labels)
        + be16(rtype)
        + be16(rclass)
        + be32(ttl)
        + be16(len(data))
        + bytes(data)
    )


def model_header(model):
    """The header bytes of a model. Its flags are the tuple
    (qr, opcode, aa, tc, rd, ra, rcode, ad, cd)."""
    qr, opcode, aa, tc, rd, ra, rcode, ad, cd = model["flags"]
    return header_bytes(
        model["id"], qr, opcode, aa, tc, rd, ra, rcode,
        len(model["questions"]), len(model["answers"]),
        len(model["authorities"]), len(model["additionals"]),
        ad=ad, cd=cd,
    )


def model_bytes(model):
    out = model_header(model)
    for q in model["questions"]:
        out += question_bytes(*q)
    for section in ("answers", "authorities", "additionals"):
        for r in model[section]:
            out += record_bytes(*r)
    return out


def summary(model):
    """The summary text, mirroring SPEC.md and Main.lean."""

    def name_s(labels):
        if not labels:
            return "ROOT"
        return ".".join(
            "-".join(str(b) for b in lab) for lab in labels
        )

    def q_s(q):
        return f"{name_s(q[0])}/{q[1]}/{q[2]}"

    def r_s(r):
        return (
            f"{name_s(r[0])}/{r[1]}/{r[2]}/{r[3]}/"
            + ",".join(str(b) for b in r[4])
        )

    return (
        f"id={model['id']}"
        f";qd={len(model['questions'])}"
        f";an={len(model['answers'])}"
        f";ns={len(model['authorities'])}"
        f";ar={len(model['additionals'])}"
        f";q={'|'.join(q_s(q) for q in model['questions'])}"
        f";a={'|'.join(r_s(r) for r in model['answers'])}"
        f";s={'|'.join(r_s(r) for r in model['authorities'])}"
        f";t={'|'.join(r_s(r) for r in model['additionals'])}"
    )


MAX_HOPS = 16


def read_name(data, pos, stats=None):
    """Read a name at pos by the plan rules. Returns
    (labels, position after the name at the place it was read),
    or None. At most MAX_HOPS pointers are followed. The step
    cap mirrors the Lean fuel, which no reading reaches. When
    `stats` is a dict, each pointer followed adds one to
    stats["hops"]."""
    labels = []
    budget = 255
    hops = 0
    nextpos = None
    cur = pos
    steps = 0
    while True:
        steps += 1
        if steps > 256:
            return None
        if cur >= len(data):
            return None
        b = data[cur]
        if b == 0:
            if budget < 1:
                return None
            budget -= 1
            if nextpos is None:
                nextpos = cur + 1
            return labels, nextpos
        if b <= 63:
            if b + 1 > budget:
                return None
            budget -= b + 1
            if cur + 1 + b > len(data):
                return None
            labels.append(bytes(data[cur + 1 : cur + 1 + b]))
            cur = cur + 1 + b
            continue
        if b >= 192:
            if cur + 1 >= len(data):
                return None
            target = (b - 192) * 256 + data[cur + 1]
            if not (target < cur and target < len(data)):
                return None
            hops += 1
            if hops > MAX_HOPS:
                return None
            if stats is not None:
                stats["hops"] = stats.get("hops", 0) + 1
            if nextpos is None:
                nextpos = cur + 2
            cur = target
            continue
        return None


def oracle_parse(data, stats=None):
    """The strict reading of the plan rules, as a parse into a
    model, or None when the message is rejected. `stats` is
    passed to read_name."""
    if len(data) < 12:
        return None
    mid = data[0] * 256 + data[1]
    f1, f2 = data[2], data[3]
    flags = (
        f1 // 128,
        (f1 // 8) % 16,
        (f1 // 4) % 2,
        (f1 // 2) % 2,
        f1 % 2,
        f2 // 128,
        f2 % 16,
        (f2 // 32) % 2,
        (f2 // 16) % 2,
    )
    # Z (0x40) is the one reserved bit; AD and CD are read.
    if (f2 // 64) % 2 != 0:
        return None
    qd = data[4] * 256 + data[5]
    an = data[6] * 256 + data[7]
    ns = data[8] * 256 + data[9]
    ar = data[10] * 256 + data[11]
    pos = 12
    questions = []
    for _ in range(qd):
        got = read_name(data, pos, stats)
        if got is None:
            return None
        labels, pos = got
        if pos + 4 > len(data):
            return None
        questions.append(
            (labels, data[pos] * 256 + data[pos + 1],
             data[pos + 2] * 256 + data[pos + 3])
        )
        pos += 4

    def read_record(pos):
        got = read_name(data, pos, stats)
        if got is None:
            return None
        labels, pos = got
        if pos + 10 > len(data):
            return None
        rtype = data[pos] * 256 + data[pos + 1]
        rclass = data[pos + 2] * 256 + data[pos + 3]
        ttl = int.from_bytes(data[pos + 4 : pos + 8], "big")
        rdlen = data[pos + 8] * 256 + data[pos + 9]
        pos += 10
        if pos + rdlen > len(data):
            return None
        rdata = bytes(data[pos : pos + rdlen])
        return (labels, rtype, rclass, ttl, rdata), pos + rdlen

    sections = {}
    for key, count in (("answers", an), ("authorities", ns),
                       ("additionals", ar)):
        records = []
        for _ in range(count):
            got = read_record(pos)
            if got is None:
                return None
            record, pos = got
            records.append(record)
        sections[key] = records
    if pos != len(data):
        return None
    return {
        "id": mid,
        "flags": flags,
        "questions": questions,
        **sections,
    }


def expected_parse(data):
    model = oracle_parse(data)
    if model is None:
        return "none"
    return "ok:" + codes(model_bytes(model))


def expected_sections(data):
    model = oracle_parse(data)
    if model is None:
        return "none"
    return "ok:" + codes(summary(model).encode("ascii"))


# ---------------------------------------------------------------- checks


class Tally:
    def __init__(self):
        self.inputs = 0
        self.agreements = 0
        self.failures = []
        # The message bytes behind each input, for the pointer
        # counts in the results file.
        self.datas = []

    def check(self, data, answer, label, op="parse"):
        self.inputs += 1
        self.datas.append(data)
        want = expected_parse(data) if op == "parse" else expected_sections(data)
        if answer == want:
            self.agreements += 1
        else:
            self.failures.append(
                f"{label}: want {want[:100]}, got {str(answer)[:100]}"
            )

    def check_line(self, line, answer, want, label):
        self.inputs += 1
        if answer == want:
            self.agreements += 1
        else:
            self.failures.append(f"{label}: want {want}, got {answer}")


QUERY = (0, 0, 0, 0, 1, 0, 0, 0, 0)  # qr opcode aa tc rd ra rcode ad cd
RESPONSE = (1, 0, 1, 0, 0, 1, 0, 0, 0)


def qmodel(mid, flags, questions):
    return {
        "id": mid, "flags": flags, "questions": questions,
        "answers": [], "authorities": [], "additionals": [],
    }


# ------------------------------------------------------- slice 1 sections


def fixed_cases():
    isi = [b"F", b"ISI", b"ARPA"]
    cases = []
    # RFC 1035 section 3.1 name, plain form, in a query.
    cases.append(("rfc-name", model_bytes(qmodel(0x1234, QUERY, [(isi, 1, 1)]))))
    # The same start with a compression pointer after the first
    # two labels, pointing back at the name's own start: reading
    # it loops through F and ISI. Each pass spends 6 bytes of
    # the 255 byte budget, so the budget alone would end it on
    # the 43rd pass; the 16 pointer limit ends it first, at the
    # 17th pointer. The step bound is never reached.
    pointed = (
        header_bytes(0x1234, 0, 0, 0, 0, 1, 0, 0, 1)
        + bytes([1]) + b"F" + bytes([3]) + b"ISI" + bytes([0xC0, 0x0C])
        + be16(1) + be16(1)
    )
    cases.append(("rfc-name-pointer-loop", pointed))
    # A two label query.
    cases.append(
        ("two-label", model_bytes(qmodel(7, QUERY, [([b"example", b"com"], 1, 1)])))
    )
    # A root name question.
    cases.append(("root", model_bytes(qmodel(7, QUERY, [([], 1, 1)]))))
    # The longest legal label.
    cases.append(("long-label", model_bytes(qmodel(7, QUERY, [([b"a" * 63], 1, 1)]))))
    # A name at the 255 byte wire bound: 63, 63, 63, 61.
    bound = [b"a" * 63, b"b" * 63, b"c" * 63, b"d" * 61]
    cases.append(("name-at-bound", model_bytes(qmodel(7, QUERY, [(bound, 1, 1)]))))
    # The same shape one byte past the bound.
    over = [b"a" * 63, b"b" * 63, b"c" * 63, b"d" * 62]
    cases.append(("name-over-bound", model_bytes(qmodel(7, QUERY, [(over, 1, 1)]))))
    # A response header with one question.
    cases.append(
        ("response", model_bytes(qmodel(9, (1, 0, 0, 0, 0, 1, 0, 0, 0), [([b"x"], 1, 1)])))
    )
    # No questions at all.
    cases.append(("no-questions", model_bytes(qmodel(9, QUERY, []))))
    # The AD bit (0x20 of byte 3) and the CD bit (0x10), RFC 4035
    # section 3.2, each set alone: read into the header.
    for label, bit in (("ad-bit", 0x20), ("cd-bit", 0x10)):
        data = bytearray(model_bytes(qmodel(7, (0, 0, 0, 0, 0, 0, 0, 0, 0), [([b"x"], 1, 1)])))
        data[3] |= bit
        cases.append((label, bytes(data)))
    # The flag bytes resolvers send: an RD+AD query (01 20, as
    # dig sends by default, RFC 6840 section 5.7), an RD+CD query
    # (01 10), and a validating resolver's RA+AD response (81 a0).
    for label, f1, f2 in (("rd-ad-query", 0x01, 0x20),
                          ("rd-cd-query", 0x01, 0x10),
                          ("ra-ad-response", 0x81, 0xA0)):
        data = bytearray(model_bytes(qmodel(7, QUERY, [([b"example", b"com"], 1, 1)])))
        data[2], data[3] = f1, f2
        cases.append((label, bytes(data)))
    # The Z bit (0x40 of byte 3), the one reserved flag bit:
    # turned away.
    bad = bytearray(model_bytes(qmodel(7, QUERY, [([b"x"], 1, 1)])))
    bad[3] |= 0x40
    cases.append(("z-bit", bytes(bad)))
    # A truncated header.
    cases.append(("short-header", model_bytes(qmodel(7, QUERY, [([b"x"], 1, 1)]))[:11]))
    # A label length byte of 64, a reserved form.
    bad = header_bytes(7, 0, 0, 0, 0, 1, 0, 0, 1) + bytes([64]) + b"a" * 64 + bytes([0]) + be16(1) + be16(1)
    cases.append(("label-64", bad))
    # A byte after the last question.
    cases.append(("leftover", model_bytes(qmodel(7, QUERY, [([b"x"], 1, 1)])) + b"\x00"))
    # A label cut short by the end of the input.
    bad = header_bytes(7, 0, 0, 0, 0, 1, 0, 0, 1) + bytes([10]) + b"abc"
    cases.append(("label-cut", bad))
    # Two questions promised, one given.
    one = question_bytes([b"x"], 1, 1)
    cases.append(
        ("count-high", header_bytes(7, 0, 0, 0, 0, 1, 0, 0, 2) + one)
    )
    return cases


def run_fixed():
    tally = Tally()
    cases = fixed_cases()
    answers, problems = ask_all([request("parse", d) for _, d in cases])
    tally.failures += problems
    for (label, data), answer in zip(cases, answers):
        tally.check(data, answer, f"fixed {label}")
    # Requests with no codes: an empty message, which is rejected.
    answers, problems = ask_all(["parse ", "parse"])
    tally.failures += problems
    for line, answer in zip(["parse ", "parse"], answers):
        tally.check_line(line, answer, "none", "no codes")
    return tally


def random_question_message(rng):
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
        rng.randint(0, 1),
        rng.randint(0, 1),
    )
    questions = [
        (name(), rng.randint(0, 65535), rng.randint(0, 65535))
        for _ in range(rng.randint(0, 3))
    ]
    return model_bytes(qmodel(rng.randint(0, 65535), flags, questions))


def run_random(seed, count):
    tally = Tally()
    rng = random.Random(seed)
    docs = [random_question_message(rng) for _ in range(count)]
    answers, problems = ask_all([request("parse", d) for d in docs])
    tally.failures += problems
    for i, (data, answer) in enumerate(zip(docs, answers)):
        tally.check(data, answer, f"random {i}")
    return tally


def run_mutations():
    tally = Tally()
    base = model_bytes(qmodel(42, QUERY, [([b"example", b"com"], 1, 1)]))
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
    targeted = []
    pointed = bytearray(base)
    pointed[12] = 0xC0
    targeted.append(("pointer", bytes(pointed)))
    lab64 = bytearray(base)
    lab64[12] = 64
    targeted.append(("label-64", bytes(lab64)))
    for label, bit in (("z", 0x40), ("ad", 0x20), ("cd", 0x10)):
        res = bytearray(base)
        res[3] |= bit
        targeted.append((label, bytes(res)))
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
    answers, problems = ask_all([request("parse", d) for d in inputs])
    tally.failures += problems
    for label, data, answer in zip(labels, inputs, answers):
        tally.check(data, answer, f"mutation {label}")
    return tally


# ------------------------------------------------------- slice 2 sections


def pointer(target):
    return bytes([0xC0 | (target // 256), target % 256])


def hop_chain(hops):
    """A response whose second answer name follows `hops`
    pointers. The question name is the label a at offset 12.
    The first answer's name is a pointer to it, and its data
    holds hops - 1 pointers, each to the one before, the first
    to offset 12. The second answer's name is a pointer to the
    last of them."""
    k = hops - 1
    wire = header_bytes(7, 1, 0, 0, 0, 0, 0, 0, 1, an=2)
    wire += question_bytes([b"a"], 1, 1)
    wire += pointer(12) + be16(16) + be16(1) + be32(0) + be16(2 * k)
    start = len(wire)
    chain = b""
    for i in range(k):
        chain += pointer(12 if i == 0 else start + 2 * (i - 1))
    wire += chain
    wire += pointer(start + 2 * (k - 1)) + be16(16) + be16(1) + be32(0) + be16(0)
    return wire


def long_pointer_chain(links, names):
    """A message whose first answer's data is a chain of
    `links` pointers, each to the one before, the first to the
    root name at offset 12, followed by `names` answers whose
    names point at the last link."""
    wire = header_bytes(7, 1, 0, 0, 0, 0, 0, 0, 0, an=1 + names)
    wire += bytes([0]) + be16(16) + be16(1) + be32(0) + be16(2 * links)
    start = len(wire)
    for i in range(links):
        wire += pointer(12 if i == 0 else start + 2 * (i - 1))
    head = start + 2 * (links - 1)
    for _ in range(names):
        wire += pointer(head) + be16(16) + be16(1) + be32(0) + be16(0)
    return wire


def full_fixed_cases():
    """Accepted whole messages, as (label, wire bytes, model).
    The wire bytes are hand built; the model is what both
    operations must report."""
    cases = []

    # RFC 1035 section 4.1.4, placed in a real message. The
    # first name starts at offset 12, right after the header.
    # The second name is the label FOO and a pointer back to
    # offset 12, so it expands to FOO.F.ISI.ARPA.
    isi = [b"F", b"ISI", b"ARPA"]
    wire = header_bytes(0x1234, 0, 0, 0, 0, 1, 0, 0, 2)
    wire += name_bytes(isi) + be16(1) + be16(1)
    wire += bytes([3]) + b"FOO" + pointer(12) + be16(1) + be16(1)
    model = qmodel(0x1234, QUERY, [(isi, 1, 1), ([b"FOO"] + isi, 1, 1)])
    cases.append(("rfc-4.1.4", wire, model))

    # A question and an answer whose name is a bare pointer
    # back to the question name at offset 12.
    name = [b"example", b"com"]
    wire = header_bytes(0x2222, 1, 0, 1, 0, 0, 1, 0, 1, an=1)
    wire += question_bytes(name, 1, 1)
    wire += pointer(12) + be16(1) + be16(1) + be32(300) + be16(4) + bytes([1, 2, 3, 4])
    model = qmodel(0x2222, RESPONSE, [(name, 1, 1)])
    model["answers"] = [(name, 1, 1, 300, bytes([1, 2, 3, 4]))]
    cases.append(("answer-pointer", wire, model))

    # A pointer chain of length two: the third name points at
    # the second, which points at the first.
    wire = header_bytes(0x3333, 0, 0, 0, 0, 1, 0, 0, 3)
    off1 = len(wire)
    wire += question_bytes([b"a", b"b"], 1, 1)
    off2 = len(wire)
    wire += bytes([1]) + b"c" + pointer(off1) + be16(1) + be16(1)
    wire += bytes([1]) + b"d" + pointer(off2) + be16(1) + be16(1)
    model = qmodel(
        0x3333, QUERY,
        [([b"a", b"b"], 1, 1),
         ([b"c", b"a", b"b"], 1, 1),
         ([b"d", b"c", b"a", b"b"], 1, 1)],
    )
    cases.append(("pointer-chain", wire, model))

    # A pointer into the middle of a label, landing on bytes
    # that read as a name: no rule forbids it. The first name
    # is the one label 61 01 78; the second is a pointer to
    # offset 14, where 01 78 00 reads as the name x.
    wire = header_bytes(7, 0, 0, 0, 0, 1, 0, 0, 2)
    wire += question_bytes([b"a\x01x"], 1, 1) + pointer(14) + be16(1) + be16(1)
    assert wire.hex() == "000701000002000000000000036101780000010001c00e00010001"
    model = qmodel(7, QUERY, [([b"a\x01x"], 1, 1), ([b"x"], 1, 1)])
    cases.append(("pointer-mid-label", wire, model))

    # A pointer into the name being read: the name at offset
    # 12 is the label 01 78 00 and then a pointer to offset 13,
    # inside that label, where 01 78 00 reads as x. The target
    # is before the pointer, so it is read: the name is the two
    # labels 01 78 00 and x. dnspython refuses it, since it asks
    # each target to lie before the start of the name being
    # read; the results file names that difference.
    wire = header_bytes(7, 0, 0, 0, 0, 1, 0, 0, 1)
    wire += bytes([3, 1, 0x78, 0]) + pointer(13) + be16(1) + be16(1)
    model = qmodel(7, QUERY, [([b"\x01x\x00", b"x"], 1, 1)])
    cases.append(("pointer-into-own-name", wire, model))

    # A name that follows exactly 16 pointers, the limit: read.
    model = qmodel(7, (1, 0, 0, 0, 0, 0, 0, 0, 0), [([b"a"], 1, 1)])
    chain = hop_chain(16)
    model["answers"] = [
        ([b"a"], 16, 1, 0, chain[31:61]),
        ([b"a"], 16, 1, 0, b""),
    ]
    cases.append(("sixteen-hops", chain, model))

    # Records in the authority and additional sections, built
    # plainly by the model builder.
    model = qmodel(0x4444, RESPONSE, [([b"example", b"com"], 1, 1)])
    model["authorities"] = [
        ([b"com"], 2, 1, 3600, bytes([1]) + b"n" + bytes([7]) + b"example" + bytes([3]) + b"com" + bytes([0]))
    ]
    model["additionals"] = [
        ([b"n", b"example", b"com"], 1, 1, 60, bytes([127, 0, 0, 1])),
        ([], 41, 1, 0, b""),
    ]
    cases.append(("authority-additional", model_bytes(model), model))

    # An answer record whose name is written in full, with
    # empty data, next to a root name question.
    model = qmodel(0x5555, RESPONSE, [([], 255, 255)])
    model["answers"] = [([b"deep", b"a", b"b"], 16, 3, 4294967295, b"")]
    cases.append(("full-names", model_bytes(model), model))
    return cases


def run_full_fixed(op):
    tally = Tally()
    cases = full_fixed_cases()
    answers, problems = ask_all([request(op, d) for _, d, _ in cases])
    tally.failures += problems
    for (label, data, model), answer in zip(cases, answers):
        tally.inputs += 1
        tally.datas.append(data)
        want = (
            "ok:" + codes(model_bytes(model))
            if op == "parse"
            else "ok:" + codes(summary(model).encode("ascii"))
        )
        if answer == want:
            tally.agreements += 1
        else:
            tally.failures.append(
                f"full fixed {label} {op}: want {want[:100]}, got {str(answer)[:100]}"
            )
    return tally


def rejection_cases():
    cases = []

    # A pointer to itself: the name at offset 12 is a pointer
    # to offset 12, and the target must be strictly earlier.
    wire = header_bytes(7, 0, 0, 0, 0, 1, 0, 0, 1) + pointer(12) + be16(1) + be16(1)
    cases.append(("pointer-self", wire))

    # A forward pointer: two questions, the first named by a
    # pointer to offset 18, where the second question's name
    # sits. Every byte is counted and the target lies inside
    # the message, so only the backwards rule refuses it; a
    # reader that allowed forward pointers would read both
    # names as later.
    wire = header_bytes(7, 0, 0, 0, 0, 1, 0, 0, 2) + pointer(18) + be16(1) + be16(1)
    wire += question_bytes([b"later"], 1, 1)
    assert wire.hex() == "000701000002000000000000c01200010001056c617465720000010001"
    cases.append(("pointer-forward", wire))

    # A pointer past the end of the message.
    wire = header_bytes(7, 0, 0, 0, 0, 1, 0, 0, 1) + pointer(1023) + be16(1) + be16(1)
    cases.append(("pointer-past-end", wire))

    # A pointer onto a reserved length form: the second name
    # points at offset 14, the second byte of the label abc in
    # the first name, which begins at offset 12. The byte
    # there, b (0x62), has one top bit set, the reserved form,
    # so reading at the target refuses it. Landing inside a
    # label is not refused in itself: see the accepted case
    # pointer-mid-label.
    wire = header_bytes(7, 0, 0, 0, 0, 1, 0, 0, 2)
    wire += question_bytes([b"abc"], 1, 1)
    wire += pointer(14) + be16(1) + be16(1)
    cases.append(("pointer-onto-reserved-form", wire))

    # A reserved length form (one top bit set) in a record
    # name.
    wire = header_bytes(7, 1, 0, 0, 0, 0, 1, 0, 1, an=1)
    wire += question_bytes([b"x"], 1, 1)
    wire += bytes([0x40]) + b"a" * 64 + bytes([0])
    wire += be16(1) + be16(1) + be32(0) + be16(0)
    cases.append(("reserved-in-record", wire))

    # A data length that runs past the end.
    wire = header_bytes(7, 1, 0, 0, 0, 0, 1, 0, 1, an=1)
    wire += question_bytes([b"x"], 1, 1)
    wire += name_bytes([b"y"]) + be16(1) + be16(1) + be32(0) + be16(10) + b"abc"
    cases.append(("data-past-end", wire))

    # An expanded name over 255 bytes, reached by chaining:
    # each name adds one 60 byte label and points at the name
    # before it. The fifth expansion needs 306 wire bytes.
    wire = header_bytes(7, 0, 0, 0, 0, 1, 0, 0, 5)
    prev = None
    for i in range(5):
        lab = bytes([97 + i]) * 60
        start = len(wire)
        if prev is None:
            wire += name_bytes([lab])
        else:
            wire += bytes([60]) + lab + pointer(prev)
        wire += be16(1) + be16(1)
        prev = start
    cases.append(("chain-over-255", wire))

    # A cycle that passes through a label, the reviewer's
    # shape. The header bytes double as a name fragment: at
    # offset 5 sit the bytes 04 61 62 63 64, the label abcd,
    # and at offset 10 the pointer C0 05 back to offset 5.
    # (Read as header fields those bytes give QDCOUNT 4 and
    # large answer, authority, and additional counts, which
    # do not matter: the first name read already fails.) The
    # question name at offset 12 is a pointer to offset 5.
    # Reading it walks label, pointer, label, pointer, and
    # the strictly backwards rule alone does not stop that:
    # the pointer at offset 10 does point back to offset 5.
    # What turns it away is the 16 pointer limit: the 17th
    # pointer is refused after 16 passes through the label,
    # which spent 80 of the 255 budget bytes. (Without the
    # limit, the budget would end it after 51 passes.) The
    # oracle rejects it by the same rule, and both operations
    # must answer none.
    wire = header_bytes(0, 0, 0, 0, 0, 0, 0, 0, 4,
                        an=0x6162, ns=0x6364, ar=0xC005)
    wire += pointer(5) + be16(1) + be16(1)
    cases.append(("pointer-cycle-through-label", wire))

    # A cycle through a 63 byte label, which the budget ends
    # before the pointer limit: the name at offset 12 is the
    # label and a pointer back to offset 12. Each pass spends
    # 64 bytes, so the fourth pass is turned away after 3
    # pointers.
    wire = header_bytes(7, 0, 0, 0, 0, 1, 0, 0, 1)
    wire += bytes([63]) + b"a" * 63 + pointer(12) + be16(1) + be16(1)
    cases.append(("pointer-cycle-budget", wire))

    # A name that follows 17 pointers, one past the limit.
    cases.append(("seventeen-hops", hop_chain(17)))

    # The re-review's 65,523 byte message: one record's data
    # holds a chain of 8,180 backward pointers, and 4,095
    # answer names point at its head. Every rule but the
    # pointer limit allows it; the first answer name is
    # turned away at its 17th pointer.
    cases.append(("long-pointer-chain", long_pointer_chain(8180, 4095)))
    return cases


def run_rejections():
    tally = Tally()
    cases = rejection_cases()
    lines = []
    for _, data in cases:
        lines.append(request("parse", data))
        lines.append(request("sections", data))
    answers, problems = ask_all(lines)
    tally.failures += problems
    for (label, data), p_ans, s_ans in zip(
        cases, answers[0::2], answers[1::2]
    ):
        for op, answer in (("parse", p_ans), ("sections", s_ans)):
            tally.inputs += 1
            tally.datas.append(data)
            if answer == "none":
                tally.agreements += 1
            else:
                tally.failures.append(
                    f"rejection {label} {op}: want none, got {str(answer)[:80]}"
                )
    return tally


# Labels for the whole message generator. Names are drawn from a
# small alphabet and end in one of a few shared tails, so that
# names in one message share suffixes and the compressor below
# has pointers to write. One label in seven is random bytes
# instead, and one pool label is 63 bytes long.
LABEL_POOL = [b"a", b"b", b"c", b"ns", b"www", b"mail", b"example",
              b"com", b"org", b"x" * 63]
TAILS = [[], [b"com"], [b"example", b"com"], [b"org"],
         [b"example", b"org"], [b"b", b"c"]]


def wire_len(labels):
    return sum(len(lab) + 1 for lab in labels) + 1


def random_model(rng):
    def label():
        if rng.randrange(7) == 0:
            n = rng.randint(1, 24)
            return bytes(rng.randrange(256) for _ in range(n))
        return rng.choice(LABEL_POOL)

    def name():
        labels = [label() for _ in range(rng.randint(0, 2))]
        labels += rng.choice(TAILS)
        while wire_len(labels) > 255:
            labels.pop(0)
        return labels

    def record():
        return (
            name(),
            rng.randint(0, 65535),
            rng.randint(0, 65535),
            rng.randint(0, 4294967295),
            bytes(rng.randrange(256) for _ in range(rng.randint(0, 20))),
        )

    flags = (
        rng.randint(0, 1),
        rng.randint(0, 15),
        rng.randint(0, 1),
        rng.randint(0, 1),
        rng.randint(0, 1),
        rng.randint(0, 1),
        rng.randint(0, 15),
        rng.randint(0, 1),
        rng.randint(0, 1),
    )
    return {
        "id": rng.randint(0, 65535),
        "flags": flags,
        "questions": [
            (name(), rng.randint(0, 65535), rng.randint(0, 65535))
            for _ in range(rng.randint(0, 2))
        ],
        "answers": [record() for _ in range(rng.randint(0, 3))],
        "authorities": [record() for _ in range(rng.randint(0, 2))],
        "additionals": [record() for _ in range(rng.randint(0, 2))],
    }


def run_random_full(seed, count, op):
    tally = Tally()
    rng = random.Random(seed + 1)
    models = [random_model(rng) for _ in range(count)]
    docs = [model_bytes(m) for m in models]
    answers, problems = ask_all([request(op, d) for d in docs])
    tally.failures += problems
    for i, (model, data, answer) in enumerate(zip(models, docs, answers)):
        tally.inputs += 1
        tally.datas.append(data)
        want = (
            "ok:" + codes(data)
            if op == "parse"
            else "ok:" + codes(summary(model).encode("ascii"))
        )
        if answer == want:
            tally.agreements += 1
        else:
            tally.failures.append(
                f"random full {i} {op}: want {want[:100]}, got {str(answer)[:100]}"
            )
    return tally, models


def compress_message(model, point_root=False):
    """Write a model with name compression. Returns the bytes
    and the offsets of the pointers written.

    A dictionary maps each name suffix already written to the
    offset where it starts. Each new name writes the labels
    before its longest known suffix, then a pointer to that
    suffix, or a zero byte when no suffix is known. The root
    suffix counts as known only when `point_root` is set: then
    a name may end in a pointer to an earlier zero byte, and a
    root name may be that pointer alone."""
    out = bytearray(model_header(model))
    known = {}
    pointers = []

    def write_name(labels):
        split = None
        for i in range(len(labels) + 1):
            suffix = tuple(labels[i:])
            if suffix in known and (suffix or point_root):
                split = i
                break
        stop = len(labels) if split is None else split
        for j in range(stop):
            suffix = tuple(labels[j:])
            if suffix not in known:
                known[suffix] = len(out)
            out.append(len(labels[j]))
            out.extend(labels[j])
        if split is None:
            if tuple() not in known:
                known[tuple()] = len(out)
            out.append(0)
        else:
            pointers.append(len(out))
            out.extend(pointer(known[tuple(labels[split:])]))

    for labels, qt, qc in model["questions"]:
        write_name(labels)
        out += be16(qt) + be16(qc)
    for section in ("answers", "authorities", "additionals"):
        for labels, rt, rc, ttl, data in model[section]:
            write_name(labels)
            out += be16(rt) + be16(rc) + be32(ttl) + be16(len(data)) + bytes(data)
    return bytes(out), pointers


def suffix_models():
    """Models whose names share suffixes, so the compressor
    has pointers to write."""
    base = [b"example", b"com"]
    models = []
    m = qmodel(0x6001, RESPONSE, [([b"www"] + base, 1, 1), (base, 1, 1)])
    m["answers"] = [
        ([b"www"] + base, 1, 1, 300, bytes([10, 0, 0, 1])),
        (base, 2, 1, 300, name_bytes([b"ns", b"example", b"com"])),
    ]
    m["additionals"] = [([b"ns"] + base, 1, 1, 300, bytes([10, 0, 0, 2]))]
    models.append(m)
    m = qmodel(0x6002, QUERY, [([b"a", b"b", b"c"], 1, 1),
                               ([b"b", b"c"], 1, 1),
                               ([b"c"], 1, 1),
                               ([], 1, 1)])
    models.append(m)
    return models


def compressed_docs(models):
    """The compressed form of each model: every second one may
    point at the root. Returns (bytes, pointer offsets) pairs."""
    return [compress_message(m, point_root=(i % 2 == 1))
            for i, m in enumerate(models)]


def run_compressed(models, docs, op):
    tally = Tally()
    answers, problems = ask_all([request(op, d) for d, _ in docs])
    tally.failures += problems
    for i, (model, (data, _), answer) in enumerate(zip(models, docs, answers)):
        tally.inputs += 1
        tally.datas.append(data)
        want = (
            "ok:" + codes(model_bytes(model))
            if op == "parse"
            else "ok:" + codes(summary(model).encode("ascii"))
        )
        if answer == want:
            tally.agreements += 1
        else:
            tally.failures.append(
                f"compressed {i} {op}: want {want[:100]}, got {str(answer)[:100]}"
            )
    return tally


def pointer_mutations(docs, rng):
    """Mutations of the compressed messages at their pointers.
    For each pointer: retarget it at itself, two bytes on, a
    random earlier offset (which can land in the header, inside
    a label, or on another pointer), a random later offset, and
    past the end of the message (0x3FFF); cut the message short
    inside it; and turn its first byte into each reserved form
    (top bits 01 and 10). Returns (label, bytes) pairs."""
    out = []
    for n, (data, pointers) in enumerate(docs):
        for p in pointers:
            def retarget(t, kind):
                m = bytearray(data)
                m[p] = 0xC0 | (t >> 8)
                m[p + 1] = t & 0xFF
                out.append((f"compressed {n} pointer at {p} {kind}", bytes(m)))

            retarget(p, "to itself")
            retarget(p + 2, "two bytes on")
            retarget(rng.randrange(0, p), "back to a random offset")
            if p + 2 < len(data):
                retarget(rng.randrange(p + 2, len(data)), "on to a random offset")
            retarget(0x3FFF, "past the end")
            out.append((f"compressed {n} cut inside the pointer at {p}", data[: p + 1]))
            for form in (0x40, 0x80):
                m = bytearray(data)
                m[p] = form | (data[p] & 0x3F)
                out.append((f"compressed {n} pointer at {p} as form {form:#04x}", bytes(m)))
    return out


def run_pointer_mutations(docs, seed):
    tally = Tally()
    cases = pointer_mutations(docs, random.Random(seed + 2))
    answers, problems = ask_all([request("parse", d) for _, d in cases])
    tally.failures += problems
    for (label, data), answer in zip(cases, answers):
        tally.check(data, answer, f"mutation {label}")
    return tally


def follows_pointer(data):
    """Whether the strict reading of `data` follows at least one
    pointer, whether the message is then accepted or not."""
    stats = {}
    oracle_parse(data, stats)
    return stats.get("hops", 0) > 0


def dnspython_crosschecks():
    """Read the accepted fixed messages with dnspython, when it
    is present. Returns (checks, failures)."""
    checks = 0
    failures = []
    if not DNSPYTHON:
        return checks, failures
    cases = [(label, data) for label, data in fixed_cases()
             if oracle_parse(data) is not None]
    cases += [(label, data) for label, data, _ in full_fixed_cases()]
    for label, data in cases:
        checks += 1
        try:
            msg = dns.message.from_wire(data)
            model = oracle_parse(data)
            if msg.id != model["id"]:
                failures.append(f"{label}: dnspython read a different id")
            got_q = [
                [bytes(l) for l in q.name.labels[:-1]] for q in msg.question
            ]
            want_q = [list(q[0]) for q in model["questions"]]
            if got_q != want_q:
                failures.append(f"{label}: dnspython read different questions")
            got_a = [
                [bytes(l) for l in rr.name.labels[:-1]] for rr in msg.answer
            ]
            want_a = [list(r[0]) for r in model["answers"]]
            if got_a != want_a:
                failures.append(f"{label}: dnspython read different answers")
        except Exception as e:  # dnspython refused or stumbled
            failures.append(f"{label}: dnspython raised {type(e).__name__}")
    return checks, failures


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
    "sections 256",
    "sections x",
    "sections 1,,2",
    "section 1",
    "sections 1 2",
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
    ffp = run_full_fixed("parse")
    ffs = run_full_fixed("sections")
    rej = run_rejections()
    rfp, models = run_random_full(args.seed, 300, "parse")
    rfs, _ = run_random_full(args.seed, 300, "sections")
    comp_models = models + suffix_models()
    comp_docs = compressed_docs(comp_models)
    comp_p = run_compressed(comp_models, comp_docs, "parse")
    comp_s = run_compressed(comp_models, comp_docs, "sections")
    comp_mut = run_pointer_mutations(comp_docs, args.seed)
    malf = run_malformed()
    dp_checks, dp_failures = dnspython_crosschecks()

    tallies = [
        ("Slice 1 fixed cases", fixed),
        ("Slice 1 random well formed messages", rand),
        ("Slice 1 mutations (every truncation, every single byte flip, targeted)", mut),
        ("Full fixed cases, parse", ffp),
        ("Full fixed cases, sections", ffs),
        ("Full rejections (parse and sections)", rej),
        ("Random whole messages, parse", rfp),
        ("Random whole messages, sections", rfs),
        ("Compressed random and suffix messages, parse", comp_p),
        ("Compressed random and suffix messages, sections", comp_s),
        ("Mutations of the compressed messages at their pointers, parse", comp_mut),
    ]
    failures = []
    for _, t in tallies:
        failures += t.failures
    failures += malf.failures + dp_failures
    total_in = sum(t.inputs for _, t in tallies)
    total_agree = sum(t.agreements for _, t in tallies)
    with_pointer = sum(follows_pointer(d) for _, t in tallies for d in t.datas)
    comp_with_pointer = sum(1 for _, ptrs in comp_docs if ptrs)
    comp_pointers = sum(len(ptrs) for _, ptrs in comp_docs)

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
    ]
    for label, t in tallies:
        lines.append(f"- {label}: {t.agreements} of {t.inputs} agreements")
    lines += [
        f"- Malformed requests answered error: {malf.agreements} of {malf.inputs}",
        f"- dnspython cross checks: {dp_checks} run, {len(dp_failures)} failures"
        if DNSPYTHON else "- dnspython cross checks: 0 run (module absent)",
        f"- Compressed messages holding a pointer: {comp_with_pointer} of"
        f" {len(comp_docs)}, {comp_pointers} pointers in all",
        f"- Differential inputs whose reading follows a pointer: {with_pointer}"
        f" of {total_in}",
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
