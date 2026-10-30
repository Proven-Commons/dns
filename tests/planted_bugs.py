#!/usr/bin/env python3
"""Planted bugs: does a wrong parser get caught?

Each planted bug is a small change to the code under proof in
`Dns/Parse.lean` or `Dns/Value.lean`. For each one, this script
copies the project to a scratch directory, makes the change,
builds the library and the tool, and then asks two things:

1. Which statements of `Dns/Spec.lean` are false for the changed
   code. A single-input statement is checked as written. A
   statement over every input cannot be checked that way, so it
   is checked on the instances listed in INSTANCES below: a
   false instance shows the statement false for the changed
   code, and a true one does not show that it holds. Each check
   is written twice, as the proposition and as its negation,
   and `decide +kernel` must prove exactly one of the two.
2. How many failures `tests/run_tests.py` records against the
   changed tool, and, when dnspython can be imported, how many
   differences its judges cannot name.

The unchanged code is run first, as the baseline: every check
must hold there, and the tests must record no failure.

    python3 tests/planted_bugs.py

It writes tests/PLANTED-BUGS.md and exits non-zero if the
baseline fails or a planted bug is caught by nothing. It needs
Python 3.11+ and the Lean toolchain on PATH (or in ~/.elan/bin).
"""

import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RECORD = ROOT / "tests" / "PLANTED-BUGS.md"
SKIP = {".lake", ".git", "__pycache__"}

# Each bug: (name, what it changes, [(file, old text, new text)]).
BUGS = [
    ("forward-pointers", "a pointer may aim forward",
     [("Dns/Parse.lean",
       "if 0 < hops ∧ target < pointerPosition ∧ target < full.length then",
       "if 0 < hops ∧ target < full.length then")]),
    ("no-hop-limit", "no limit on the pointers a name follows",
     [("Dns/Parse.lean",
       "if 0 < hops ∧ target < pointerPosition ∧ target < full.length then",
       "if target < pointerPosition ∧ target < full.length then")]),
    ("hops-15", "the limit is 15 pointers, not 16",
     [("Dns/Parse.lean", "def maxHops : Nat := 16", "def maxHops : Nat := 15")]),
    ("hops-reset-at-label",
     "the pointer count starts again after each label",
     [("Dns/Parse.lean",
       "match parseNameGo fuel full (budget - (b.toNat + 1)) hops",
       "match parseNameGo fuel full (budget - (b.toNat + 1)) 16")]),
    ("budget-reset-at-jump",
     "the 255 byte budget starts again at each pointer",
     [("Dns/Parse.lean",
       "match parseNameGo fuel full budget (hops - 1)",
       "match parseNameGo fuel full 255 (hops - 1)")]),
    ("ad-cd-refused", "AD and CD are refused, as Z is",
     [("Dns/Parse.lean",
       "    if (f2.toNat / 64) % 2 = 0 then",
       "    if (f2.toNat / 16) % 8 = 0 then")]),
    ("z-accepted", "a set Z bit is not refused",
     [("Dns/Parse.lean", "    if (f2.toNat / 64) % 2 = 0 then", "    if True then")]),
    ("ad-cd-swapped-in-parseHeader",
     "AD and CD swapped in the header reader and in the printer",
     [("Dns/Parse.lean",
       "f2.toNat / 128, (f2.toNat / 32) % 2, (f2.toNat / 16) % 2,",
       "f2.toNat / 128, (f2.toNat / 16) % 2, (f2.toNat / 32) % 2,"),
      ("Dns/Value.lean",
       "(h.ra * 128 + h.ad * 32 + h.cd * 16 + h.rcode).toUInt8",
       "(h.ra * 128 + h.cd * 32 + h.ad * 16 + h.rcode).toUInt8")]),
    ("ad-cd-swapped-in-parse",
     "AD and CD swapped by parse after the header reader, and in the"
     " printer",
     [("Dns/Parse.lean",
       "if rest = [] then some ⟨h, qs, answers, authorities, additionals⟩ else none",
       "if rest = [] then some ⟨{ h with ad := h.cd, cd := h.ad }, qs, answers,"
       " authorities, additionals⟩ else none"),
      ("Dns/Value.lean",
       "(h.ra * 128 + h.ad * 32 + h.cd * 16 + h.rcode).toUInt8",
       "(h.ra * 128 + h.cd * 32 + h.ad * 16 + h.rcode).toUInt8")]),
    ("answers-authorities-swapped",
     "the answer and authority sections swapped in parse and in the"
     " printer",
     [("Dns/Parse.lean",
       "if rest = [] then some ⟨h, qs, answers, authorities, additionals⟩ else none",
       "if rest = [] then some ⟨h, qs, authorities, answers, additionals⟩ else none"),
      ("Dns/Value.lean",
       "  printHeader m.header m.questions.length m.answers.length\n"
       "      m.authorities.length m.additionals.length ++\n"
       "    printQuestions m.questions ++ printRecords m.answers ++\n"
       "    printRecords m.authorities ++ printRecords m.additionals",
       "  printHeader m.header m.questions.length m.authorities.length\n"
       "      m.answers.length m.additionals.length ++\n"
       "    printQuestions m.questions ++ printRecords m.authorities ++\n"
       "    printRecords m.answers ++ printRecords m.additionals")]),
]

# Instances of the statements over every input, each written as
# a closed proposition that `decide +kernel` settles. The first
# word names the statement it is an instance of.
INSTANCES = [
    ("Dns.Spec.parse_print", "parse (print mAD) = some mAD"),
    ("Dns.Spec.parse_print", "parse (print mCD) = some mCD"),
    ("Dns.Spec.parse_print", "parse (print mRecords) = some mRecords"),
    ("Dns.Spec.parse_print_question_only", "parse (print mQ) = some mQ"),
    ("Dns.Spec.parse_reads_header",
     "(parse ([0, 7, 1, 32, 0, 0, 0, 0, 0, 0, 0, 0] : List UInt8)).map"
     " (fun m => (m.header.rd, m.header.ad, m.header.cd)) = some (1, 1, 0)"),
    ("Dns.Spec.parse_reads_header",
     "(parse ([0, 7, 1, 16, 0, 0, 0, 0, 0, 0, 0, 0] : List UInt8)).map"
     " (fun m => (m.header.rd, m.header.ad, m.header.cd)) = some (1, 0, 1)"),
    ("Dns.Spec.parse_reads_header",
     "(parse ([0, 7, 129, 160, 0, 0, 0, 0, 0, 0, 0, 0] : List UInt8)).map"
     " (fun m => (m.header.qr, m.header.rd, m.header.ra, m.header.ad,"
     " m.header.cd)) = some (1, 1, 1, 1, 0)"),
    ("Dns.Spec.parse_reads_header",
     "(parse ([0, 7, 128, 128, 0, 1, 0, 1, 0, 0, 0, 0, 1, 120, 0, 0, 1, 0, 1,"
     " 1, 121, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0] : List UInt8)).map"
     " (fun m => (m.questions.length, m.answers.length, m.authorities.length,"
     " m.additionals.length)) = some (1, 1, 0, 0)"),
    ("Dns.Spec.parseHeader_fields",
     "(parseHeader ([0, 7, 1, 32, 0, 0, 0, 0, 0, 0, 0, 0] : List UInt8)).map"
     " (fun x => (x.1.ad, x.1.cd)) = some (1, 0)"),
    ("Dns.Spec.parseHeader_fields",
     "(parseHeader ([0, 7, 1, 16, 0, 0, 0, 0, 0, 0, 0, 0] : List UInt8)).map"
     " (fun x => (x.1.ad, x.1.cd)) = some (0, 1)"),
    ("Dns.Spec.rejects_z_bit",
     "parse ([0, 7, 1, 64, 0, 0, 0, 0, 0, 0, 0, 0] : List UInt8) = none"),
    ("Dns.Spec.rejects_z_bit",
     "parse ([0, 7, 129, 224, 0, 0, 0, 0, 0, 0, 0, 0] : List UInt8) = none"),
]

MESSAGES = """
def mAD : Message :=
  { header := { id := 7, qr := 0, opcode := 0, aa := 0, tc := 0,
                rd := 1, ra := 0, ad := 1, cd := 0, rcode := 0 },
    questions := [{ name := [[120]], qtype := 1, qclass := 1 }],
    answers := [], authorities := [], additionals := [] }

def mCD : Message :=
  { header := { id := 7, qr := 0, opcode := 0, aa := 0, tc := 0,
                rd := 1, ra := 0, ad := 0, cd := 1, rcode := 0 },
    questions := [{ name := [[120]], qtype := 1, qclass := 1 }],
    answers := [], authorities := [], additionals := [] }

def mQ : Message :=
  { header := { id := 9, qr := 0, opcode := 2, aa := 0, tc := 1,
                rd := 1, ra := 0, ad := 1, cd := 1, rcode := 3 },
    questions := [{ name := [[97], [98, 99]], qtype := 28, qclass := 1 },
                  { name := [], qtype := 2, qclass := 3 }],
    answers := [], authorities := [], additionals := [] }

def mRecords : Message :=
  { header := { id := 300, qr := 1, opcode := 0, aa := 1, tc := 0,
                rd := 1, ra := 1, ad := 0, cd := 0, rcode := 0 },
    questions := [{ name := [[120]], qtype := 1, qclass := 1 }],
    answers := [{ name := [[120]], type := 1, rclass := 1, ttl := 60,
                  data := [1, 2, 3, 4] }],
    authorities := [{ name := [[121]], type := 2, rclass := 1, ttl := 7,
                      data := [] },
                    { name := [], type := 6, rclass := 1, ttl := 0,
                      data := [5] }],
    additionals := [] }
"""


def env():
    e = dict(os.environ)
    e["PATH"] = str(Path.home() / ".elan" / "bin") + ":" + e.get("PATH", "")
    return e


def check_file():
    """The Lean file that checks every single-input statement as
    written and every instance above. Each check N is written
    twice: check_N states the proposition and refute_N its
    negation, both by `decide +kernel`, so exactly one of them
    must go through. Returns the text and the statement each
    numbered check belongs to."""
    spec = (ROOT / "Dns" / "Spec.lean").read_text()
    props = []
    for m in re.finditer(r"^theorem (Dns\.Spec\.\w+) :\n(.*?):= sorry", spec, re.S | re.M):
        props.append((m.group(1), m.group(2).strip()))
    props += INSTANCES
    lines = ["import Dns", "", "open Dns", "", MESSAGES]
    owners = []
    for owner, prop in props:
        owners.append(owner)
        n = len(owners)
        lines.append(f"theorem check_{n} :\n    {prop} := by decide +kernel\n")
        lines.append(f"theorem refute_{n} :\n    ¬ ({prop}) := by decide +kernel\n")
    return "\n".join(lines), owners


def copy_project(dest):
    for path in ROOT.rglob("*"):
        rel = path.relative_to(ROOT)
        if any(part in SKIP for part in rel.parts) or rel == Path("tests/PLANTED-BUGS.md"):
            continue
        target = dest / rel
        if path.is_dir():
            target.mkdir(parents=True, exist_ok=True)
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(path, target)


def run_one(work, changes, check_text, owners):
    """Apply `changes` in `work`, build, check, test. Returns
    (build error or None, statements refuted, test record lines)."""
    for f, old, new in changes:
        p = work / f
        s = p.read_text()
        if s.count(old) != 1:
            raise SystemExit(f"planted bug does not apply: {f}: {old[:60]}")
        p.write_text(s.replace(old, new))
    build = subprocess.run(["lake", "build", "Dns", "dns"], cwd=work, env=env(),
                           capture_output=True, text=True, timeout=3600)
    if build.returncode != 0:
        return (build.stdout + build.stderr)[-500:], [], {}
    (work / "PlantedCheck.lean").write_text(check_text)
    chk = subprocess.run(["lake", "env", "lean", "PlantedCheck.lean"], cwd=work,
                         env=env(), capture_output=True, text=True, timeout=3600)
    out = chk.stdout + chk.stderr
    starts = [(i + 1, m.group(1), int(m.group(2)))
              for i, line in enumerate(check_text.splitlines())
              if (m := re.match(r"theorem (check|refute)_(\d+) :", line))]
    failed = set()
    for m in re.finditer(r"PlantedCheck\.lean:(\d+):\d+: error", out):
        line = int(m.group(1))
        at = [(kind, n) for start, kind, n in starts if start <= line]
        if not at:
            return out[-800:], [], {}
        failed.add(at[-1])
    refuted = []
    for n, owner in enumerate(owners, start=1):
        holds = ("check", n) not in failed
        fails = ("refute", n) not in failed
        if holds == fails:
            return f"check {n} ({owner}) is neither proved nor refuted", [], {}
        if fails and owner not in refuted:
            refuted.append(owner)
    subprocess.run([sys.executable, "tests/run_tests.py", "--skip-build"], cwd=work,
                   env=env(), capture_output=True, text=True, timeout=3600)
    record = {}
    results = work / "tests" / "TEST-RESULTS.md"
    text = results.read_text() if results.exists() else ""
    for key in ("Inputs", "Failures"):
        m = re.search(rf"^- {key}: (\d+)", text, re.M)
        record[key] = int(m.group(1)) if m else None
    record["unnamed"] = sum(int(n) for n in re.findall(r"(\d+) unnamed$", text, re.M))
    record["judged"] = "unnamed" in text
    return None, refuted, record


def main():
    check_text, owners = check_file()
    rows = []
    bad = []
    with tempfile.TemporaryDirectory() as tmp:
        base = Path(tmp) / "base"
        base.mkdir()
        copy_project(base)
        for name, what, changes in [("baseline", "the code as it is", [])] + BUGS:
            work = Path(tmp) / name
            shutil.copytree(base, work)
            err, refuted, rec = run_one(work, changes, check_text, owners)
            shutil.rmtree(work)
            if err:
                bad.append(f"{name}: build or check did not run: {err}")
                rows.append((name, what, "did not run", "", ""))
                continue
            caught_by_tests = (rec["Failures"] or 0) > 0
            if name == "baseline":
                if refuted or caught_by_tests or rec["unnamed"]:
                    bad.append(f"baseline: refuted {refuted}, record {rec}")
            elif not refuted and not caught_by_tests:
                bad.append(f"{name}: caught by nothing")
            rows.append((
                name, what,
                ", ".join(f"`{r}`" for r in refuted) or "none",
                f"{rec['Failures']} of {rec['Inputs']}",
                str(rec["unnamed"]) if rec["judged"] else "not run",
            ))
            print(name, refuted, rec, flush=True)
    single = sum(1 for o in owners if o not in {i[0] for i in INSTANCES})
    lines = [
        "# Planted bugs",
        "",
        "Written by `python3 tests/planted_bugs.py`. Each planted bug is a small",
        "change to the code under proof, made in a scratch copy of the project.",
        "For each, the script lists the statements of `Dns/Spec.lean` that are false",
        "for the changed code, and the failures `tests/run_tests.py` records",
        "against the changed tool. Rerun it to check these rows.",
        "",
        f"- Single-input statements checked as written: {single}",
        f"- Instances of the statements over every input: {len(INSTANCES)}"
        " (a false instance refutes its statement; a true one proves nothing)",
        "- Each check is decided both ways with `decide +kernel`: the proposition"
        " and its negation, exactly one of which must go through.",
        "- dnspython: " + ("judges ran" if rows and rows[0][4] != "not run"
                           else "not installed, so the judges did not run"),
        "",
        "| Planted bug | What changes | Statements refuted | Test failures"
        " | Unnamed dnspython differences |",
        "|---|---|---|---|---|",
    ]
    for r in rows:
        lines.append("| " + " | ".join(r) + " |")
    lines.append("")
    if bad:
        lines += ["## Problems", ""] + [f"- {b}" for b in bad] + [""]
    RECORD.write_text("\n".join(lines))
    print("\n".join(lines))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
