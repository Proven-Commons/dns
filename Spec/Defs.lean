/-
  The definitions the statements in `Spec.lean` use besides the
  code under proof: well formedness of a message, which states
  the wire bounds each field must fit, and the expanded wire
  length of a name it uses. They give the statements their
  meaning, and the parser and printer do not use them, so they
  are part of the specification, with `Spec.lean` and
  `SPEC.md`, not of the code (`bar.toml` lists the code).
-/

import Dns

namespace Spec

open Dns

/-- The wire length of an expanded name: one length byte per
    label, the label bytes, and the final zero byte. -/
def wireLen : Name → Nat
  | [] => 1
  | l :: ls => (l.length + 1) + wireLen ls

/-- A well formed header: the identifier fits two bytes, each
    single flag field is 0 or 1, and the opcode and the RCODE
    fit four bits. -/
def WFHeader (h : Header) : Prop :=
  h.id < 65536 ∧ h.qr ≤ 1 ∧ h.opcode < 16 ∧ h.aa ≤ 1 ∧ h.tc ≤ 1 ∧
    h.rd ≤ 1 ∧ h.ra ≤ 1 ∧ h.ad ≤ 1 ∧ h.cd ≤ 1 ∧ h.rcode < 16

/-- A well formed expanded name: every label holds 1 to 63
    bytes, and the expanded wire length fits the 255 byte
    bound. -/
def WFName (nm : Name) : Prop :=
  (∀ l ∈ nm, 1 ≤ l.length ∧ l.length ≤ 63) ∧ wireLen nm ≤ 255

/-- A well formed question: QTYPE and QCLASS fit two bytes, and
    its name is well formed. -/
def WFQuestion (q : Question) : Prop :=
  q.qtype < 65536 ∧ q.qclass < 65536 ∧ WFName q.name

/-- A well formed record: type and class fit two bytes, TTL
    fits four bytes, its name is well formed, and its data
    length fits two bytes. -/
def WFRecord (r : Record) : Prop :=
  r.type < 65536 ∧ r.rclass < 65536 ∧ r.ttl < 4294967296 ∧
    WFName r.name ∧ r.data.length < 65536

/-- A well formed message: a well formed header, well formed
    entries in all four sections, and each section count fits
    two bytes. -/
def WF (m : Message) : Prop :=
  WFHeader m.header ∧
    (∀ q ∈ m.questions, WFQuestion q) ∧
    (∀ r ∈ m.answers, WFRecord r) ∧
    (∀ r ∈ m.authorities, WFRecord r) ∧
    (∀ r ∈ m.additionals, WFRecord r) ∧
    m.questions.length < 65536 ∧ m.answers.length < 65536 ∧
    m.authorities.length < 65536 ∧ m.additionals.length < 65536

end Spec
