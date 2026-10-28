/-
  The round trip proof: for every well formed message, parsing
  its printed form gives the same message back.

  The statement proved here is `parse_print`. A matching
  statement in a spec file still has to be added by a reviewer,
  so this file builds on its own, in the same shape as the png
  proofs.

  The steps: two printed bytes read back as the value they were
  printed from; the printed flag bytes decode to the fields they
  were printed from; a printed name reads back as the name, with
  whatever follows untouched; one printed question reads back; a
  printed question list reads back whole; then the header at the
  top level.
-/

import Dns

namespace Dns.Proofs

open Dns

/-- A byte printed from a number reads back as the number modulo
    256. -/
theorem toUInt8_toNat (n : Nat) : (n.toUInt8).toNat = n % 256 := rfl

/-- Two bytes printed from a value below 2^16 read back as the
    value. -/
theorem u16_be16 (n : Nat) (h : n < 65536) :
    u16 (n / 256).toUInt8 n.toUInt8 = n := by
  simp only [u16, toUInt8_toNat]
  omega

/-- Reading two bytes off the front of a printed value and what
    follows it. -/
theorem getU16_be16 (n : Nat) (h : n < 65536) (r : List UInt8) :
    getU16 (be16 n ++ r) = some (n, r) := by
  show getU16 ((n / 256).toUInt8 :: n.toUInt8 :: r) = some (n, r)
  show some (u16 (n / 256).toUInt8 n.toUInt8, r) = some (n, r)
  rw [u16_be16 n h]

/-- The value the first flag byte was printed from. -/
theorem flags1_toNat {h : Header} (hq : h.qr ≤ 1) (ho : h.opcode < 16)
    (ha : h.aa ≤ 1) (ht : h.tc ≤ 1) (hr : h.rd ≤ 1) :
    (flags1 h).toNat =
      h.qr * 128 + h.opcode * 8 + h.aa * 4 + h.tc * 2 + h.rd := by
  have hb : h.qr * 128 + h.opcode * 8 + h.aa * 4 + h.tc * 2 + h.rd < 256 := by
    omega
  simp only [flags1, toUInt8_toNat, Nat.mod_eq_of_lt hb]

/-- The printed first flag byte decodes to the fields it was
    printed from. -/
theorem flags1_decode {h : Header} (hq : h.qr ≤ 1) (ho : h.opcode < 16)
    (ha : h.aa ≤ 1) (ht : h.tc ≤ 1) (hr : h.rd ≤ 1) :
    (flags1 h).toNat / 128 = h.qr ∧
    ((flags1 h).toNat / 8) % 16 = h.opcode ∧
    ((flags1 h).toNat / 4) % 2 = h.aa ∧
    ((flags1 h).toNat / 2) % 2 = h.tc ∧
    (flags1 h).toNat % 2 = h.rd := by
  rw [flags1_toNat hq ho ha ht hr]
  omega

/-- The value the second flag byte was printed from. -/
theorem flags2_toNat {h : Header} (ha : h.ra ≤ 1) (hr : h.rcode < 16) :
    (flags2 h).toNat = h.ra * 128 + h.rcode := by
  have hb : h.ra * 128 + h.rcode < 256 := by omega
  simp only [flags2, toUInt8_toNat, Nat.mod_eq_of_lt hb]

/-- The printed second flag byte decodes to the fields it was
    printed from, and its reserved bits read as zero. -/
theorem flags2_decode {h : Header} (ha : h.ra ≤ 1) (hr : h.rcode < 16) :
    (flags2 h).toNat / 128 = h.ra ∧
    (flags2 h).toNat % 16 = h.rcode ∧
    ((flags2 h).toNat / 16) % 8 = 0 := by
  rw [flags2_toNat ha hr]
  omega

/-- The printed length of a name is its wire length. -/
theorem printName_length : ∀ (nm : Name), (printName nm).length = wireLen nm
  | [] => rfl
  | l :: ls => by
    simp only [printName, wireLen, List.length_append, List.length_cons]
    rw [printName_length ls]

/-- One step of the name reader on a byte and what follows it,
    stated for rewriting. -/
theorem parseNameGo_step (fuel budget : Nat) (b : UInt8) (rest : List UInt8) :
    parseNameGo (fuel + 1) budget (b :: rest) =
      if b = 0 then
        if 1 ≤ budget then some ([], rest) else none
      else if b.toNat ≤ 63 then
        if b.toNat + 1 ≤ budget then
          if (rest.take b.toNat).length = b.toNat then
            match parseNameGo fuel (budget - (b.toNat + 1)) (rest.drop b.toNat) with
            | some (ls, rest') => some (rest.take b.toNat :: ls, rest')
            | none => none
          else none
        else none
      else none := rfl

/-- A printed name reads back as the name, over any bytes that
    follow it, given the wire budget and enough fuel. -/
theorem parseNameGo_printName (nm : Name) (budget fuel : Nat)
    (rest : List UInt8)
    (hl : ∀ l ∈ nm, 1 ≤ l.length ∧ l.length ≤ 63)
    (hw : wireLen nm ≤ budget)
    (hf : (printName nm).length < fuel) :
    parseNameGo fuel budget (printName nm ++ rest) = some (nm, rest) := by
  induction nm generalizing budget fuel rest with
  | nil =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by
      have : (printName ([] : Name)).length = 1 := rfl
      omega⟩
    have hw1 : 1 ≤ budget := hw
    show parseNameGo (f + 1) budget ((0 : UInt8) :: rest) = some ([], rest)
    rw [parseNameGo_step, if_pos rfl, if_pos hw1]
  | cons l ls ih =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by
      have h1 : (printName (l :: ls)).length ≥ 1 := by
        simp [printName]
      omega⟩
    have hl1 : 1 ≤ l.length ∧ l.length ≤ 63 := hl l (by simp)
    have hls : ∀ x ∈ ls, 1 ≤ x.length ∧ x.length ≤ 63 :=
      fun x hx => hl x (List.mem_cons_of_mem l hx)
    have hbn : l.length.toUInt8.toNat = l.length := by
      rw [toUInt8_toNat]
      omega
    have key : printName (l :: ls) ++ rest
        = l.length.toUInt8 :: (l ++ (printName ls ++ rest)) := by
      simp [printName, List.append_assoc]
    rw [key, parseNameGo_step, hbn]
    have hb0 : ¬ (l.length.toUInt8 : UInt8) = 0 := by
      intro hcon
      have hz : l.length.toUInt8.toNat = 0 := by
        rw [hcon]
        rfl
      omega
    have hbud : l.length + 1 ≤ budget := by
      have hw' : wireLen (l :: ls) = l.length + 1 + wireLen ls := rfl
      omega
    rw [if_neg hb0, if_pos hl1.2, if_pos hbud]
    have htake : (l ++ (printName ls ++ rest)).take l.length = l :=
      List.take_left
    have hdrop : (l ++ (printName ls ++ rest)).drop l.length
        = printName ls ++ rest := List.drop_left
    have hlen : ((l ++ (printName ls ++ rest)).take l.length).length
        = l.length := by rw [htake]
    rw [if_pos hlen, hdrop]
    have hwls : wireLen ls ≤ budget - (l.length + 1) := by
      have hw' : wireLen (l :: ls) = l.length + 1 + wireLen ls := rfl
      omega
    have hfls : (printName ls).length < f := by
      have e1 := printName_length (l :: ls)
      have e2 := printName_length ls
      simp only [printName, List.length_append, List.length_cons] at hf
      omega
    rw [ih (budget - (l.length + 1)) f rest hls hwls hfls, htake]

/-- The name reader at the top level, stated for rewriting. -/
theorem parseName_step (bs : List UInt8) :
    parseName bs = parseNameGo (bs.length + 1) 255 bs := rfl

/-- One step of the question reader, stated for rewriting. -/
theorem parseQuestion_step (bs : List UInt8) :
    parseQuestion bs = (parseName bs).bind fun (nm, rest) =>
      (getU16 rest).bind fun (qt, rest) =>
      (getU16 rest).bind fun (qc, rest) => some (⟨nm, qt, qc⟩, rest) := rfl

/-- One printed question reads back as the question, over any
    bytes that follow it. -/
theorem parseQuestion_printQuestion {q : Question} (hw : WFQuestion q)
    (rest : List UInt8) :
    parseQuestion (printQuestion q ++ rest) = some (q, rest) := by
  obtain ⟨hqt, hqc, hl, hwl⟩ := hw
  have key : printQuestion q ++ rest
      = printName q.name ++ (be16 q.qtype ++ (be16 q.qclass ++ rest)) := by
    simp [printQuestion, List.append_assoc]
  have hfuel : (printName q.name).length
      < (printName q.name ++ (be16 q.qtype ++ (be16 q.qclass ++ rest))).length + 1 := by
    simp only [List.length_append, be16, List.length_cons, List.length_nil]
    omega
  have hname := parseNameGo_printName q.name 255
    ((printName q.name ++ (be16 q.qtype ++ (be16 q.qclass ++ rest))).length + 1)
    (be16 q.qtype ++ (be16 q.qclass ++ rest)) hl hwl hfuel
  rw [key]
  simp only [parseQuestion_step, parseName_step, hname, Option.bind_some]
  rw [getU16_be16 q.qtype hqt]
  simp only [Option.bind_some]
  rw [getU16_be16 q.qclass hqc]
  simp only [Option.bind_some]

/-- A printed question list reads back whole, over any bytes
    that follow it. -/
theorem parseQuestions_printQuestions (qs : List Question)
    (rest : List UInt8)
    (hw : ∀ q ∈ qs, WFQuestion q) :
    parseQuestions qs.length (printQuestions qs ++ rest) = some (qs, rest) := by
  induction qs generalizing rest with
  | nil => rfl
  | cons q qs ih =>
    have hq : WFQuestion q := hw q (by simp)
    have hqs : ∀ x ∈ qs, WFQuestion x :=
      fun x hx => hw x (List.mem_cons_of_mem q hx)
    have key : printQuestions (q :: qs) ++ rest
        = printQuestion q ++ (printQuestions qs ++ rest) := by
      simp [printQuestions, List.append_assoc]
    show parseQuestions (qs.length + 1)
        (printQuestions (q :: qs) ++ rest) = some (q :: qs, rest)
    rw [key]
    show (parseQuestion (printQuestion q ++ (printQuestions qs ++ rest)) >>=
      fun (q', rest) => parseQuestions qs.length rest >>= fun (qs', rest') =>
      some (q' :: qs', rest')) = some (q :: qs, rest)
    rw [parseQuestion_printQuestion hq (printQuestions qs ++ rest)]
    show (parseQuestions qs.length (printQuestions qs ++ rest) >>=
      fun (qs', rest') => some (q :: qs', rest')) = some (q :: qs, rest)
    rw [ih rest hqs]
    rfl

/-- The printed header reads back as the header and the count
    it was printed with, over any bytes that follow it. -/
theorem parseHeader_step (i1 i2 f1 f2 q1 q2 a1 a2 n1 n2 r1 r2 : UInt8)
    (rest : List UInt8) :
    parseHeader (i1 :: i2 :: f1 :: f2 ::
      q1 :: q2 :: a1 :: a2 :: n1 :: n2 :: r1 :: r2 :: rest) =
      if (f2.toNat / 16) % 8 = 0 ∧ u16 a1 a2 = 0 ∧
          u16 n1 n2 = 0 ∧ u16 r1 r2 = 0 then
        some (⟨u16 i1 i2, f1.toNat / 128, (f1.toNat / 8) % 16,
          (f1.toNat / 4) % 2, (f1.toNat / 2) % 2, f1.toNat % 2,
          f2.toNat / 128, f2.toNat % 16⟩, u16 q1 q2, rest)
      else none := rfl

/-- A printed header reads back as the header and its count. -/
theorem parseHeader_printHeader {h : Header} (hw : WFHeader h)
    {qd : Nat} (hqd : qd < 65536) (rest : List UInt8) :
    parseHeader (printHeader h qd ++ rest) = some (h, qd, rest) := by
  obtain ⟨hid, hqr, hop, haa, htc, hrd, hra, hrc⟩ := hw
  have key : printHeader h qd ++ rest =
      (h.id / 256).toUInt8 :: h.id.toUInt8 :: flags1 h :: flags2 h ::
      (qd / 256).toUInt8 :: qd.toUInt8 ::
      0 :: 0 :: 0 :: 0 :: 0 :: 0 :: rest := by
    simp [printHeader, be16]
  rw [key, parseHeader_step]
  obtain ⟨d1, d2, d3, d4, d5⟩ := flags1_decode hqr hop haa htc hrd
  obtain ⟨e1, e2, e3⟩ := flags2_decode hra hrc
  have hz : u16 (0 : UInt8) 0 = 0 := rfl
  rw [if_pos ⟨e3, hz, hz, hz⟩,
    u16_be16 h.id hid, u16_be16 qd hqd,
    d1, d2, d3, d4, d5, e1, e2]

/-- The round trip: parsing the printed form of a well formed
    message gives the message back. -/
theorem parse_print {m : Message} (hw : WF m) : parse (print m) = some m := by
  obtain ⟨hh, hq, hlen⟩ := hw
  have key : print m
      = printHeader m.header m.questions.length ++ printQuestions m.questions := rfl
  rw [key]
  show (parseHeader (printHeader m.header m.questions.length ++
      printQuestions m.questions) >>= fun (h, qd, rest) =>
    parseQuestions qd rest >>= fun (qs, rest') =>
    if rest' = [] then some ⟨h, qs⟩ else none) = some m
  rw [parseHeader_printHeader hh hlen]
  show (parseQuestions m.questions.length (printQuestions m.questions) >>=
    fun (qs, rest') => if rest' = [] then some ⟨m.header, qs⟩ else none) =
    some m
  have kh : (printQuestions m.questions)
      = printQuestions m.questions ++ [] := (List.append_nil _).symm
  rw [kh, parseQuestions_printQuestions m.questions [] hq]
  show (if ([] : List UInt8) = [] then
    some ⟨m.header, m.questions⟩ else none) = some m
  rw [if_pos rfl]

end Dns.Proofs
