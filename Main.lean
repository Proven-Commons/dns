/-
  Command line front end, used by the tests.

  Reads one request per line and prints one answer per line. A
  request is an operation and its input as comma-separated
  decimal byte codes.

    parse 0,0,1,0,...      prints  ok:0,0,1,0,... or none
    sections 0,0,1,0,...   prints  ok:105,100,61,... or none

  Two operations take the byte codes of a DNS message. `parse`
  answers `ok:` and the byte codes of the canonical reprint of
  the parsed message. `sections` answers `ok:` and the byte
  codes of the summary text SPEC.md defines: the identifier,
  the header flags, the four section counts, and the entries
  of the four sections, with every name expanded. Both answer `none` when
  the message is rejected.

  A request is an operation, then optionally one space and its
  numbers; with no numbers after the space, the input is empty.
  A malformed request prints `error`: any other line, an unknown
  operation, a number that is not plain decimal digits, or a
  code above 255, which no byte holds. A line may end in LF or
  CR LF; nothing else around a request is ignored.

  The parsing and printing here call `Dns.parse` and `Dns.print`
  directly. The line handling is covered by the tests, not by a
  proof.
-/

import Dns

open Dns

/-- A number in plain decimal digits. Longer numbers than any
    byte code are refused before they are converted, since that
    takes time quadratic in their length. -/
def number (t : String) : Option Nat :=
  let ds := t.toList
  if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
  else t.toNat?

/-- The comma-separated numbers in `s`. -/
def numbers (s : String) : Option (List Nat) :=
  if s.isEmpty then some [] else (s.splitOn ",").mapM number

/-- The numbers as bytes. A number above 255 is not a byte, and
    makes the request malformed. -/
def toBytes (ns : List Nat) : Option (List UInt8) :=
  ns.mapM fun n => if n < 256 then some n.toUInt8 else none

def showCodes (bs : List UInt8) : String :=
  ",".intercalate (bs.map fun b => toString b.toNat)

/-- A name in the summary encoding: the word `ROOT` for the
    root, or the labels in order, full stops between them, each
    label written as its byte codes split by hyphens. -/
def showName (nm : Name) : String :=
  if nm.isEmpty then "ROOT"
  else ".".intercalate
    (nm.map fun l => "-".intercalate (l.map fun b => toString b.toNat))

/-- One question in the summary encoding. -/
def showQuestion (q : Question) : String :=
  showName q.name ++ "/" ++ toString q.qtype ++ "/" ++ toString q.qclass

/-- One record in the summary encoding. Its data is written as
    byte codes split by commas. -/
def showRecord (r : Record) : String :=
  showName r.name ++ "/" ++ toString r.type ++ "/" ++ toString r.rclass ++
    "/" ++ toString r.ttl ++ "/" ++ showCodes r.data

/-- The summary of a message, in the encoding SPEC.md states:
    the identifier, the header flags in the order of the third
    and fourth header bytes, the four section counts, and the
    entries of the four sections in order. -/
def summary (m : Message) : String :=
  "id=" ++ toString m.header.id ++
    ";qr=" ++ toString m.header.qr ++
    ";opcode=" ++ toString m.header.opcode ++
    ";aa=" ++ toString m.header.aa ++
    ";tc=" ++ toString m.header.tc ++
    ";rd=" ++ toString m.header.rd ++
    ";ra=" ++ toString m.header.ra ++
    ";ad=" ++ toString m.header.ad ++
    ";cd=" ++ toString m.header.cd ++
    ";rcode=" ++ toString m.header.rcode ++
    ";qd=" ++ toString m.questions.length ++
    ";an=" ++ toString m.answers.length ++
    ";ns=" ++ toString m.authorities.length ++
    ";ar=" ++ toString m.additionals.length ++
    ";q=" ++ "|".intercalate (m.questions.map showQuestion) ++
    ";a=" ++ "|".intercalate (m.answers.map showRecord) ++
    ";s=" ++ "|".intercalate (m.authorities.map showRecord) ++
    ";t=" ++ "|".intercalate (m.additionals.map showRecord)

/-- The byte codes of a summary text. Every character the
    summary uses is plain ASCII, so each code is one byte. -/
def stringCodes (s : String) : List UInt8 :=
  s.toList.map fun c => c.toNat.toUInt8

/-- The answer to one request, or `none` when the request is
    malformed. -/
def answer (op : String) (ns : List Nat) : Option String :=
  match op with
  | "parse" =>
    match toBytes ns with
    | none => none
    | some bs =>
      match parse bs with
      | some v => some ("ok:" ++ showCodes (print v))
      | none => some "none"
  | "sections" =>
    match toBytes ns with
    | none => none
    | some bs =>
      match parse bs with
      | some v => some ("ok:" ++ showCodes (stringCodes (summary v)))
      | none => some "none"
  | _ => none

/-- The answer to one line: an operation, then optionally one
    space and its numbers. -/
def request (line : String) : Option String :=
  match line.splitOn " " with
  | [op] => answer op []
  | [op, arg] => numbers arg >>= answer op
  | _ => none

/-- The line without its line ending: LF, or CR LF. -/
def chomp (line : String) : String :=
  let cs := line.toList
  if cs.getLast? = some '\n' then
    let cs := cs.dropLast
    String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
  else line

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let line := chomp line
    stdout.putStrLn ((request line).getD "error")
