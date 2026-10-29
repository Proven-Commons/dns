/-
  The round trip proof: for every well formed whole message,
  parsing its printed form gives the same message back.

  The statement proved here is `parse_print`. It covers all
  four sections. A question-only corollary,
  `parse_print_question_only`, states the first slice's result
  for messages whose other three sections are empty.

  The printed form holds no compression. Its names therefore
  take the label steps of the name reader, never the pointer
  step. The name lemma is stated for any whole-message context:
  only the suffix at the front matters on those steps, and the
  name and the bytes after it come back unchanged.
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

/-- Four bytes printed from a value below 2^32 read back as the
    value. -/
theorem u32_be32 (n : Nat) (h : n < 4294967296) :
    u32 (n / 16777216).toUInt8 (n / 65536).toUInt8
      (n / 256).toUInt8 n.toUInt8 = n := by
  simp only [u32, toUInt8_toNat]
  omega

/-- Reading four bytes off the front of a printed value and
    what follows it. -/
theorem getU32_be32 (n : Nat) (h : n < 4294967296) (r : List UInt8) :
    getU32 (be32 n ++ r) = some (n, r) := by
  show getU32 ((n / 16777216).toUInt8 :: (n / 65536).toUInt8 ::
    (n / 256).toUInt8 :: n.toUInt8 :: r) = some (n, r)
  show some (u32 (n / 16777216).toUInt8 (n / 65536).toUInt8
    (n / 256).toUInt8 n.toUInt8, r) = some (n, r)
  rw [u32_be32 n h]

/-- Taking a printed byte list from the front of itself and
    what follows it. -/
theorem takeBytes_append (data rest : List UInt8) :
    takeBytes data.length (data ++ rest) = some (data, rest) := by
  unfold takeBytes
  rw [if_pos (by simp)]
  simp [List.take_left, List.drop_left]

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
theorem flags2_toNat {h : Header} (ha : h.ra ≤ 1) (had : h.ad ≤ 1)
    (hcd : h.cd ≤ 1) (hr : h.rcode < 16) :
    (flags2 h).toNat = h.ra * 128 + h.ad * 32 + h.cd * 16 + h.rcode := by
  have hb : h.ra * 128 + h.ad * 32 + h.cd * 16 + h.rcode < 256 := by omega
  simp only [flags2, toUInt8_toNat, Nat.mod_eq_of_lt hb]

/-- The printed second flag byte decodes to the fields it was
    printed from, and its Z bit reads as zero. -/
theorem flags2_decode {h : Header} (ha : h.ra ≤ 1) (had : h.ad ≤ 1)
    (hcd : h.cd ≤ 1) (hr : h.rcode < 16) :
    (flags2 h).toNat / 128 = h.ra ∧
    ((flags2 h).toNat / 32) % 2 = h.ad ∧
    ((flags2 h).toNat / 16) % 2 = h.cd ∧
    (flags2 h).toNat % 16 = h.rcode ∧
    ((flags2 h).toNat / 64) % 2 = 0 := by
  rw [flags2_toNat ha had hcd hr]
  omega

/-- The printed length of a name is its wire length. -/
theorem printName_length : ∀ (nm : Name), (printName nm).length = wireLen nm
  | [] => rfl
  | l :: ls => by
    simp only [printName, wireLen, List.length_append, List.length_cons]
    rw [printName_length ls]

/-- One step of the name reader on a byte and what follows it,
    stated for rewriting. -/
theorem parseNameGo_step (fuel : Nat) (full : List UInt8) (budget : Nat)
    (b : UInt8) (rest : List UInt8) :
    parseNameGo (fuel + 1) full budget (b :: rest) =
      if b = 0 then
        if 1 ≤ budget then some ([], rest, budget - 1) else none
      else if b.toNat ≤ 63 then
        if b.toNat + 1 ≤ budget then
          if (rest.take b.toNat).length = b.toNat then
            match parseNameGo fuel full (budget - (b.toNat + 1))
                (rest.drop b.toNat) with
            | some (ls, rest', remaining) =>
              some (rest.take b.toNat :: ls, rest', remaining)
            | none => none
          else none
        else none
      else if 192 ≤ b.toNat then
        match rest with
        | [] => none
        | c :: after =>
          if (b.toNat - 192) * 256 + c.toNat <
                full.length - (b :: c :: after).length ∧
              (b.toNat - 192) * 256 + c.toNat < full.length then
            match parseNameGo fuel full budget
                (full.drop ((b.toNat - 192) * 256 + c.toNat)) with
            | some (ls, _, remaining) => some (ls, after, remaining)
            | none => none
          else none
      else none := rfl

/-- A printed name reads back as the name, over any bytes that
    follow it, given the expanded wire budget and enough fuel.
    The whole-message context does not matter on these steps:
    a printed name holds no pointer byte. The remaining budget
    is the starting budget minus the name's wire length. -/
theorem parseNameGo_printName (nm : Name) (full : List UInt8)
    (budget fuel : Nat) (rest : List UInt8)
    (hl : ∀ l ∈ nm, 1 ≤ l.length ∧ l.length ≤ 63)
    (hw : wireLen nm ≤ budget)
    (hf : (printName nm).length < fuel) :
    parseNameGo fuel full budget (printName nm ++ rest) =
      some (nm, rest, budget - wireLen nm) := by
  induction nm generalizing budget fuel rest with
  | nil =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by
      have : (printName ([] : Name)).length = 1 := rfl
      omega⟩
    have hw1 : 1 ≤ budget := hw
    show parseNameGo (f + 1) full budget ((0 : UInt8) :: rest) =
      some ([], rest, budget - 1)
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
    have hrem : budget - (l.length + 1) - wireLen ls =
        budget - wireLen (l :: ls) := by
      have hw' : wireLen (l :: ls) = l.length + 1 + wireLen ls := rfl
      omega
    rw [ih (budget - (l.length + 1)) f rest hls hwls hfls, htake, hrem]

/-- The top level in-message name reader on a printed name. -/
theorem parseNameIn_printName (full : List UInt8) (nm : Name)
    (rest : List UInt8)
    (hl : ∀ l ∈ nm, 1 ≤ l.length ∧ l.length ≤ 63)
    (hw : wireLen nm ≤ 255) :
    parseNameIn full (printName nm ++ rest) =
      some (nm, rest, 255 - wireLen nm) := by
  unfold parseNameIn
  apply parseNameGo_printName nm full 255 (full.length + 257) rest hl hw
  have hlen : (printName nm).length = wireLen nm := printName_length nm
  omega

/-- The in-message name reader at the top level, stated for
    rewriting. -/
theorem parseNameIn_step (full bs : List UInt8) :
    parseNameIn full bs =
      parseNameGo (full.length + 257) full 255 bs := rfl

/-- One step of the question reader, stated for rewriting. -/
theorem parseQuestionIn_step (full bs : List UInt8) :
    parseQuestionIn full bs = (parseNameIn full bs).bind fun (nm, rest, _) =>
      (getU16 rest).bind fun (qt, rest) =>
      (getU16 rest).bind fun (qc, rest) => some (⟨nm, qt, qc⟩, rest) := rfl

/-- One printed question reads back as the question, over any
    bytes that follow it. -/
theorem parseQuestionIn_printQuestion {q : Question} (hw : WFQuestion q)
    (full rest : List UInt8) :
    parseQuestionIn full (printQuestion q ++ rest) = some (q, rest) := by
  obtain ⟨hqt, hqc, hl, hwl⟩ := hw
  have key : printQuestion q ++ rest
      = printName q.name ++ (be16 q.qtype ++ (be16 q.qclass ++ rest)) := by
    simp [printQuestion, List.append_assoc]
  have hname := parseNameIn_printName full q.name
    (be16 q.qtype ++ (be16 q.qclass ++ rest)) hl hwl
  rw [key]
  simp only [parseQuestionIn_step, hname, Option.bind_some]
  rw [getU16_be16 q.qtype hqt]
  simp only [Option.bind_some]
  rw [getU16_be16 q.qclass hqc]
  simp only [Option.bind_some]

/-- A printed question list reads back whole, over any bytes
    that follow it. -/
theorem parseQuestionsIn_printQuestions (qs : List Question)
    (full rest : List UInt8)
    (hw : ∀ q ∈ qs, WFQuestion q) :
    parseQuestionsIn qs.length full (printQuestions qs ++ rest) =
      some (qs, rest) := by
  induction qs generalizing rest with
  | nil => rfl
  | cons q qs ih =>
    have hq : WFQuestion q := hw q (by simp)
    have hqs : ∀ x ∈ qs, WFQuestion x :=
      fun x hx => hw x (List.mem_cons_of_mem q hx)
    have key : printQuestions (q :: qs) ++ rest
        = printQuestion q ++ (printQuestions qs ++ rest) := by
      simp [printQuestions, List.append_assoc]
    show parseQuestionsIn (qs.length + 1) full
        (printQuestions (q :: qs) ++ rest) = some (q :: qs, rest)
    rw [key]
    show (parseQuestionIn full (printQuestion q ++ (printQuestions qs ++ rest)) >>=
      fun (q', rest) => parseQuestionsIn qs.length full rest >>= fun (qs', rest') =>
      some (q' :: qs', rest')) = some (q :: qs, rest)
    rw [parseQuestionIn_printQuestion hq full (printQuestions qs ++ rest)]
    show (parseQuestionsIn qs.length full (printQuestions qs ++ rest) >>=
      fun (qs', rest') => some (q :: qs', rest')) = some (q :: qs, rest)
    rw [ih rest hqs]
    rfl

/-- One step of the record reader, stated for rewriting. -/
theorem parseRecordIn_step (full bs : List UInt8) :
    parseRecordIn full bs = (parseNameIn full bs).bind fun (nm, rest, _) =>
      (getU16 rest).bind fun (rt, rest) =>
      (getU16 rest).bind fun (rc, rest) =>
      (getU32 rest).bind fun (ttl, rest) =>
      (getU16 rest).bind fun (rdlen, rest) =>
      (takeBytes rdlen rest).bind fun (data, rest) =>
      some (⟨nm, rt, rc, ttl, data⟩, rest) := rfl

/-- One printed record reads back as the record, over any bytes
    that follow it. -/
theorem parseRecordIn_printRecord {r : Record} (hw : WFRecord r)
    (full rest : List UInt8) :
    parseRecordIn full (printRecord r ++ rest) = some (r, rest) := by
  have hrt : r.type < 65536 := hw.1
  have hrc : r.rclass < 65536 := hw.2.1
  have httl : r.ttl < 4294967296 := hw.2.2.1
  have hl : ∀ l ∈ r.name, 1 ≤ l.length ∧ l.length ≤ 63 := hw.2.2.2.1.1
  have hwl : wireLen r.name ≤ 255 := hw.2.2.2.1.2
  have hdata : r.data.length < 65536 := hw.2.2.2.2
  have key : printRecord r ++ rest
      = printName r.name ++ (be16 r.type ++ (be16 r.rclass ++
        (be32 r.ttl ++ (be16 r.data.length ++ (r.data ++ rest))))) := by
    simp [printRecord, List.append_assoc]
  have hname := parseNameIn_printName full r.name
    (be16 r.type ++ (be16 r.rclass ++
      (be32 r.ttl ++ (be16 r.data.length ++ (r.data ++ rest))))) hl hwl
  rw [key]
  simp only [parseRecordIn_step, hname, Option.bind_some]
  rw [getU16_be16 r.type hrt]
  simp only [Option.bind_some]
  rw [getU16_be16 r.rclass hrc]
  simp only [Option.bind_some]
  rw [getU32_be32 r.ttl httl]
  simp only [Option.bind_some]
  rw [getU16_be16 r.data.length hdata]
  simp only [Option.bind_some]
  rw [takeBytes_append r.data rest]
  simp only [Option.bind_some]

/-- A printed record list reads back whole, over any bytes that
    follow it. -/
theorem parseRecordsIn_printRecords (rs : List Record)
    (full rest : List UInt8)
    (hw : ∀ r ∈ rs, WFRecord r) :
    parseRecordsIn rs.length full (printRecords rs ++ rest) =
      some (rs, rest) := by
  induction rs generalizing rest with
  | nil => rfl
  | cons r rs ih =>
    have hr : WFRecord r := hw r (by simp)
    have hrs : ∀ x ∈ rs, WFRecord x :=
      fun x hx => hw x (List.mem_cons_of_mem r hx)
    have key : printRecords (r :: rs) ++ rest
        = printRecord r ++ (printRecords rs ++ rest) := by
      simp [printRecords, List.append_assoc]
    show parseRecordsIn (rs.length + 1) full
        (printRecords (r :: rs) ++ rest) = some (r :: rs, rest)
    rw [key]
    show (parseRecordIn full (printRecord r ++ (printRecords rs ++ rest)) >>=
      fun (r', rest) => parseRecordsIn rs.length full rest >>= fun (rs', rest') =>
      some (r' :: rs', rest')) = some (r :: rs, rest)
    rw [parseRecordIn_printRecord hr full (printRecords rs ++ rest)]
    show (parseRecordsIn rs.length full (printRecords rs ++ rest) >>=
      fun (rs', rest') => some (r :: rs', rest')) = some (r :: rs, rest)
    rw [ih rest hrs]
    rfl

/-- One step of the header reader, stated for rewriting. -/
theorem parseHeader_step (i1 i2 f1 f2 q1 q2 a1 a2 n1 n2 r1 r2 : UInt8)
    (rest : List UInt8) :
    parseHeader (i1 :: i2 :: f1 :: f2 ::
      q1 :: q2 :: a1 :: a2 :: n1 :: n2 :: r1 :: r2 :: rest) =
      if (f2.toNat / 64) % 2 = 0 then
        some (⟨u16 i1 i2, f1.toNat / 128, (f1.toNat / 8) % 16,
          (f1.toNat / 4) % 2, (f1.toNat / 2) % 2, f1.toNat % 2,
          f2.toNat / 128, (f2.toNat / 32) % 2, (f2.toNat / 16) % 2,
          f2.toNat % 16⟩,
          u16 q1 q2, u16 a1 a2, u16 n1 n2, u16 r1 r2, rest)
      else none := rfl

/-- A printed header reads back as the header and the counts it
    was printed with, over any bytes that follow it. -/
theorem parseHeader_printHeader {h : Header} (hw : WFHeader h)
    {qd an ns ar : Nat} (hqd : qd < 65536) (han : an < 65536)
    (hns : ns < 65536) (har : ar < 65536) (rest : List UInt8) :
    parseHeader (printHeader h qd an ns ar ++ rest) =
      some (h, qd, an, ns, ar, rest) := by
  obtain ⟨hid, hqr, hop, haa, htc, hrd, hra, had, hcd, hrc⟩ := hw
  have key : printHeader h qd an ns ar ++ rest =
      (h.id / 256).toUInt8 :: h.id.toUInt8 :: flags1 h :: flags2 h ::
      (qd / 256).toUInt8 :: qd.toUInt8 ::
      (an / 256).toUInt8 :: an.toUInt8 ::
      (ns / 256).toUInt8 :: ns.toUInt8 ::
      (ar / 256).toUInt8 :: ar.toUInt8 :: rest := by
    simp [printHeader, be16]
  rw [key, parseHeader_step]
  obtain ⟨d1, d2, d3, d4, d5⟩ := flags1_decode hqr hop haa htc hrd
  obtain ⟨e1, e2, e3, e4, e5⟩ := flags2_decode hra had hcd hrc
  rw [if_pos e5,
    u16_be16 h.id hid, u16_be16 qd hqd, u16_be16 an han,
    u16_be16 ns hns, u16_be16 ar har,
    d1, d2, d3, d4, d5, e1, e2, e3, e4]

/-- The whole message round trip: parsing the printed form of a
    well formed message gives the message back. -/
theorem parse_print {m : Message} (hw : WF m) : parse (print m) = some m := by
  obtain ⟨hh, hq, ha, hs, ht, hqlen, halen, hslen, htlen⟩ := hw
  have key : print m
      = printHeader m.header m.questions.length m.answers.length
          m.authorities.length m.additionals.length ++
        (printQuestions m.questions ++ (printRecords m.answers ++
          (printRecords m.authorities ++ printRecords m.additionals))) := by
    simp [print, List.append_assoc]
  rw [key]
  show (parseHeader (printHeader m.header m.questions.length m.answers.length
      m.authorities.length m.additionals.length ++
      (printQuestions m.questions ++ (printRecords m.answers ++
        (printRecords m.authorities ++ printRecords m.additionals)))) >>=
      fun (h, qd, an, ns, ar, rest) =>
    parseQuestionsIn qd (printHeader m.header m.questions.length m.answers.length
        m.authorities.length m.additionals.length ++
        (printQuestions m.questions ++ (printRecords m.answers ++
          (printRecords m.authorities ++ printRecords m.additionals)))) rest >>=
      fun (qs, rest) =>
    parseRecordsIn an (printHeader m.header m.questions.length m.answers.length
        m.authorities.length m.additionals.length ++
        (printQuestions m.questions ++ (printRecords m.answers ++
          (printRecords m.authorities ++ printRecords m.additionals)))) rest >>=
      fun (answers, rest) =>
    parseRecordsIn ns (printHeader m.header m.questions.length m.answers.length
        m.authorities.length m.additionals.length ++
        (printQuestions m.questions ++ (printRecords m.answers ++
          (printRecords m.authorities ++ printRecords m.additionals)))) rest >>=
      fun (authorities, rest) =>
    parseRecordsIn ar (printHeader m.header m.questions.length m.answers.length
        m.authorities.length m.additionals.length ++
        (printQuestions m.questions ++ (printRecords m.answers ++
          (printRecords m.authorities ++ printRecords m.additionals)))) rest >>=
      fun (additionals, rest) =>
    if rest = [] then some ⟨h, qs, answers, authorities, additionals⟩ else none) =
    some m
  rw [parseHeader_printHeader hh hqlen halen hslen htlen]
  show (parseQuestionsIn m.questions.length (printHeader m.header m.questions.length m.answers.length
        m.authorities.length m.additionals.length ++
        (printQuestions m.questions ++ (printRecords m.answers ++
          (printRecords m.authorities ++ printRecords m.additionals))))
      (printQuestions m.questions ++ (printRecords m.answers ++
        (printRecords m.authorities ++ printRecords m.additionals))) >>=
      fun (qs, rest) =>
    parseRecordsIn m.answers.length (printHeader m.header m.questions.length m.answers.length
        m.authorities.length m.additionals.length ++
        (printQuestions m.questions ++ (printRecords m.answers ++
          (printRecords m.authorities ++ printRecords m.additionals)))) rest >>= fun (answers, rest) =>
    parseRecordsIn m.authorities.length (printHeader m.header m.questions.length m.answers.length
        m.authorities.length m.additionals.length ++
        (printQuestions m.questions ++ (printRecords m.answers ++
          (printRecords m.authorities ++ printRecords m.additionals)))) rest >>= fun (authorities, rest) =>
    parseRecordsIn m.additionals.length (printHeader m.header m.questions.length m.answers.length
        m.authorities.length m.additionals.length ++
        (printQuestions m.questions ++ (printRecords m.answers ++
          (printRecords m.authorities ++ printRecords m.additionals)))) rest >>= fun (additionals, rest) =>
    if rest = [] then
      some ⟨m.header, qs, answers, authorities, additionals⟩ else none) = some m
  rw [parseQuestionsIn_printQuestions m.questions (printHeader m.header m.questions.length m.answers.length
        m.authorities.length m.additionals.length ++
        (printQuestions m.questions ++ (printRecords m.answers ++
          (printRecords m.authorities ++ printRecords m.additionals))))
    (printRecords m.answers ++
      (printRecords m.authorities ++ printRecords m.additionals)) hq]
  show (parseRecordsIn m.answers.length (printHeader m.header m.questions.length m.answers.length
        m.authorities.length m.additionals.length ++
        (printQuestions m.questions ++ (printRecords m.answers ++
          (printRecords m.authorities ++ printRecords m.additionals))))
      (printRecords m.answers ++
        (printRecords m.authorities ++ printRecords m.additionals)) >>=
      fun (answers, rest) =>
    parseRecordsIn m.authorities.length (printHeader m.header m.questions.length m.answers.length
        m.authorities.length m.additionals.length ++
        (printQuestions m.questions ++ (printRecords m.answers ++
          (printRecords m.authorities ++ printRecords m.additionals)))) rest >>= fun (authorities, rest) =>
    parseRecordsIn m.additionals.length (printHeader m.header m.questions.length m.answers.length
        m.authorities.length m.additionals.length ++
        (printQuestions m.questions ++ (printRecords m.answers ++
          (printRecords m.authorities ++ printRecords m.additionals)))) rest >>= fun (additionals, rest) =>
    if rest = [] then
      some ⟨m.header, m.questions, answers, authorities, additionals⟩ else none) =
    some m
  rw [parseRecordsIn_printRecords m.answers (printHeader m.header m.questions.length m.answers.length
        m.authorities.length m.additionals.length ++
        (printQuestions m.questions ++ (printRecords m.answers ++
          (printRecords m.authorities ++ printRecords m.additionals))))
    (printRecords m.authorities ++ printRecords m.additionals) ha]
  show (parseRecordsIn m.authorities.length (printHeader m.header m.questions.length m.answers.length
        m.authorities.length m.additionals.length ++
        (printQuestions m.questions ++ (printRecords m.answers ++
          (printRecords m.authorities ++ printRecords m.additionals))))
      (printRecords m.authorities ++ printRecords m.additionals) >>=
      fun (authorities, rest) =>
    parseRecordsIn m.additionals.length (printHeader m.header m.questions.length m.answers.length
        m.authorities.length m.additionals.length ++
        (printQuestions m.questions ++ (printRecords m.answers ++
          (printRecords m.authorities ++ printRecords m.additionals)))) rest >>= fun (additionals, rest) =>
    if rest = [] then
      some ⟨m.header, m.questions, m.answers, authorities, additionals⟩
      else none) = some m
  rw [parseRecordsIn_printRecords m.authorities (printHeader m.header m.questions.length m.answers.length
        m.authorities.length m.additionals.length ++
        (printQuestions m.questions ++ (printRecords m.answers ++
          (printRecords m.authorities ++ printRecords m.additionals))))
    (printRecords m.additionals) hs]
  have kh : (printRecords m.additionals)
      = printRecords m.additionals ++ [] := (List.append_nil _).symm
  show (parseRecordsIn m.additionals.length (printHeader m.header m.questions.length m.answers.length
        m.authorities.length m.additionals.length ++
        (printQuestions m.questions ++ (printRecords m.answers ++
          (printRecords m.authorities ++ printRecords m.additionals))))
      (printRecords m.additionals) >>= fun (additionals, rest) =>
    if rest = [] then
      some ⟨m.header, m.questions, m.answers, m.authorities, additionals⟩
      else none) = some m
  rw [kh]
  rw [parseRecordsIn_printRecords m.additionals (printHeader m.header m.questions.length m.answers.length
        m.authorities.length m.additionals.length ++
        (printQuestions m.questions ++ (printRecords m.answers ++
          (printRecords m.authorities ++ (printRecords m.additionals ++ []))))) [] ht]
  show (if ([] : List UInt8) = [] then
    some ⟨m.header, m.questions, m.answers, m.authorities, m.additionals⟩
    else none) = some m
  rw [if_pos rfl]

/-- The first slice's question-only result, as a corollary of
    the whole message theorem. -/
theorem parse_print_question_only {h : Header} {qs : List Question}
    (hh : WFHeader h) (hq : ∀ q ∈ qs, WFQuestion q)
    (hlen : qs.length < 65536) :
    parse (print ⟨h, qs, [], [], []⟩) = some ⟨h, qs, [], [], []⟩ := by
  apply parse_print
  exact ⟨hh, hq,
    by intro r hr; simp at hr,
    by intro r hr; simp at hr,
    by intro r hr; simp at hr,
    hlen, by simp, by simp, by simp⟩

end Dns.Proofs
