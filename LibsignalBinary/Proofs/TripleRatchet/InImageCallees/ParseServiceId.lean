/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImage.Uuid
import ProofLib.SepLogic.WPp

/-!
# Verification of `ServiceId::parse_from_service_id_string`

Proves that `ServiceId::parse_from_service_id_string` checks for an optional `"PNI:"` prefix
followed by a 36-byte hyphenated UUID via `<uuid::Uuid>::try_parse`, matching
`parseSidCodeSpec` and `parseSidCodeStackSpec`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr

namespace ParseServiceId

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

gen_decodes libsignalSessionCode_tree libsignalSessionBin [(ls_off% "<libsignal_core::address::ServiceId>::parse_from_service_id_string") → (ls_off% "<libsignal_core::address::ServiceId>::parse_from_service_id_string" + 208)]

local elab "parseServiceId_fetches " b:term:max C:term:max ctl:term:max abs:term:max
    hfn:term:max off:term:max len:term:max : tactic => open Lean Meta Elab Tactic in do
  let offLit := Syntax.mkNumLit (toString (← CryptoVerification.CodeLayout.evalNat off "parseServiceId_fetches "))
  let k0Lit := Syntax.mkNumLit "0"
  let lenLit := Syntax.mkNumLit (toString (← CryptoVerification.CodeLayout.evalNat len "parseServiceId_fetches "))
  let hfnId : Ident ← if hfn.raw.isIdent then pure ⟨hfn.raw⟩ else do
    let g ← getMainGoal
    let c? ← g.withContext do
      tryCatchRuntimeEx (do
        let e := (← instantiateMVars (← Term.elabTermAndSynthesize hfn none)).consumeMData
        return if e.isConst then some e.constName! else none) (fun _ => pure none)
    match c? with
    | some c => pure (mkCIdentFrom hfn c)
    | none =>
      let id := mkIdent `_hfn_layout
      evalTactic (← `(tactic| have $id := $hfn))
      pure id
  evalTactic (← `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode libsignalSessionBin $b (Rust.withPanics (tripleRatchetExterns $C $ctl $abs)) $hfnId:ident $offLit:num $k0Lit:num $lenLit:num))

def uuidWord0 (u : List.Vector (BitVec 8) 16) : BitVec 64 :=
  pack64 (u.toList.getD 0 0#8) (u.toList.getD 1 0#8) (u.toList.getD 2 0#8) (u.toList.getD 3 0#8)
    (u.toList.getD 4 0#8) (u.toList.getD 5 0#8) (u.toList.getD 6 0#8) (u.toList.getD 7 0#8)

def uuidWord1 (u : List.Vector (BitVec 8) 16) : BitVec 64 :=
  pack64 (u.toList.getD 8 0#8) (u.toList.getD 9 0#8) (u.toList.getD 10 0#8) (u.toList.getD 11 0#8)
    (u.toList.getD 12 0#8) (u.toList.getD 13 0#8) (u.toList.getD 14 0#8) (u.toList.getD 15 0#8)

theorem pointsToBytes_uuid (a : BitVec 64) (u : List.Vector (BitVec 8) 16) :
    (a ↦ₛ u.toList) = ((a ↦₆₄ uuidWord0 u) ∗ ((a + 8#64) ↦₆₄ uuidWord1 u)) := by
  have hlen : u.toList.length = 16 := u.toList_length
  have hsplit : u.toList = (u.toList.drop 0).take 8 ++ (u.toList.drop 8).take 8 := by
    have hd : (u.toList.drop 8).length ≤ 8 := by simp [hlen]
    simp only [List.drop_zero, List.take_of_length_le hd, List.take_append_drop]
  conv => lhs; rw [hsplit]
  rw [pointsToBytes_append]
  have ht8 : ((u.toList.drop 0).take 8).length = 8 := by simp [hlen]
  rw [ht8, pointsToBytes_take8_eq_pointsTo64 a u.toList 0 (by omega),
    pointsToBytes_take8_eq_pointsTo64 (a + 8#64) u.toList 8 (by omega)]
  rfl

theorem memRegion_17_none_split (out : BitVec 64) :
    memRegion out 17 = (∃∗ b0 : BitVec 8, out ↦₈ b0) ∗ memRegion (out + 1#64) 16 := by
  rw [ProofLib.memRegion_split' (b := out) (n := 1) (k := 16)
        (b' := out + 1#64) rfl rfl (by decide),
      memRegion_one out]

theorem memRegion_out1_16_split (out : BitVec 64) :
    memRegion (out + 1#64) 16 =
      (∃∗ w0 : BitVec 64, (out + 1#64) ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (out + 9#64) ↦₆₄ w1) := by
  rw [ProofLib.memRegion_split' (b := out + 1#64) (n := 8) (k := 8)
        (b' := out + 9#64) rfl (by bv_arith) (by decide),
      memRegion_eight (out + 1#64), memRegion_eight (out + 9#64)]

theorem stackAt_parseSid_split (sp : BitVec 64) :
    stackAt sp parseSidStack =
      stackAt (sp - 80#64) uuidTryParseStack ∗
      (∃∗ q0 : BitVec 64, (sp - 80#64) ↦₆₄ q0) ∗
      (∃∗ q1 : BitVec 64, (sp - 72#64) ↦₆₄ q1) ∗
      memRegion (sp - 64#64) 32 ∗
      (∃∗ s29 : BitVec 64, (sp - 32#64) ↦₆₄ s29) ∗
      (∃∗ s30 : BitVec 64, (sp - 24#64) ↦₆₄ s30) ∗
      (∃∗ s19 : BitVec 64, (sp - 16#64) ↦₆₄ s19) ∗
      memRegion (sp - 8#64) 8 := by
  have hbot : sp - BitVec.ofNat 64 (0x50 + uuidTryParseStack) =
      sp - 80#64 - BitVec.ofNat 64 uuidTryParseStack := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  show stackAt sp (0x50 + uuidTryParseStack) = _
  rw [ProofLib.stackAt_split_bottom sp 0x50 uuidTryParseStack (by decide), hbot]
  congr 1
  simp only [stackAt]
  rw [show BitVec.ofNat 64 0x50 = 80#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 8) (k := 72)
        (b' := sp - 72#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 72#64) (n := 8) (k := 64)
        (b' := sp - 64#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64) (n := 32) (k := 32)
        (b' := sp - 32#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 32#64) (n := 8) (k := 24)
        (b' := sp - 24#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 24#64) (n := 8) (k := 16)
        (b' := sp - 16#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 16#64) (n := 8) (k := 8)
        (b' := sp - 8#64) rfl (by bv_arith) (by decide),
      memRegion_eight (sp - 80#64), memRegion_eight (sp - 72#64),
      memRegion_eight (sp - 32#64), memRegion_eight (sp - 24#64),
      memRegion_eight (sp - 16#64)]

theorem stackAt_parseSidFrame_split (sp : BitVec 64) :
    stackAt sp parseSidFrameStack =
      (∃∗ q0 : BitVec 64, (sp - 80#64) ↦₆₄ q0) ∗
      (∃∗ q1 : BitVec 64, (sp - 72#64) ↦₆₄ q1) ∗
      memRegion (sp - 64#64) 32 ∗
      (∃∗ s29 : BitVec 64, (sp - 32#64) ↦₆₄ s29) ∗
      (∃∗ s30 : BitVec 64, (sp - 24#64) ↦₆₄ s30) ∗
      (∃∗ s19 : BitVec 64, (sp - 16#64) ↦₆₄ s19) ∗
      memRegion (sp - 8#64) 8 := by
  simp only [stackAt, parseSidFrameStack]
  rw [show BitVec.ofNat 64 0x50 = 80#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 8) (k := 72)
        (b' := sp - 72#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 72#64) (n := 8) (k := 64)
        (b' := sp - 64#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64) (n := 32) (k := 32)
        (b' := sp - 32#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 32#64) (n := 8) (k := 24)
        (b' := sp - 24#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 24#64) (n := 8) (k := 16)
        (b' := sp - 16#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 16#64) (n := 8) (k := 8)
        (b' := sp - 8#64) rfl (by bv_arith) (by decide),
      memRegion_eight (sp - 80#64), memRegion_eight (sp - 72#64),
      memRegion_eight (sp - 32#64), memRegion_eight (sp - 24#64),
      memRegion_eight (sp - 16#64)]

theorem stackAt_parseSid_eq_frame (sp : BitVec 64) :
    stackAt sp parseSidStack =
      stackAt (sp - 80#64) uuidTryParseStack ∗ stackAt sp parseSidFrameStack := by
  have hbot : sp - BitVec.ofNat 64 (0x50 + uuidTryParseStack) =
      sp - 80#64 - BitVec.ofNat 64 uuidTryParseStack := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  show stackAt sp (0x50 + uuidTryParseStack) = _
  rw [ProofLib.stackAt_split_bottom sp 0x50 uuidTryParseStack (by decide), hbot]

theorem memRegion_sp64_none_split (sp : BitVec 64) :
    memRegion (sp - 64#64) 32 =
      (∃∗ tag : BitVec 32, (sp - 64#64) ↦₃₂ tag) ∗ memRegion (sp - 60#64) 28 := by
  rw [ProofLib.memRegion_split' (b := sp - 64#64) (n := 4) (k := 28)
        (b' := sp - 60#64) rfl (by bv_arith) (by decide),
      memRegion_four (sp - 64#64)]

theorem memRegion_sp64_some_split (sp : BitVec 64) :
    memRegion (sp - 64#64) 32 =
      (∃∗ tag : BitVec 32, (sp - 64#64) ↦₃₂ tag) ∗
      (∃∗ u0 : BitVec 64, (sp - 60#64) ↦₆₄ u0) ∗
      (∃∗ u1 : BitVec 64, (sp - 52#64) ↦₆₄ u1) ∗
      memRegion (sp - 44#64) 12 := by
  rw [ProofLib.memRegion_split' (b := sp - 64#64) (n := 4) (k := 28)
        (b' := sp - 60#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 60#64) (n := 8) (k := 20)
        (b' := sp - 52#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 52#64) (n := 8) (k := 12)
        (b' := sp - 44#64) rfl (by bv_arith) (by decide),
      memRegion_four (sp - 64#64), memRegion_eight (sp - 60#64), memRegion_eight (sp - 52#64)]

theorem serviceIdParse_of_lt_4 (bs : List (BitVec 8)) (h : bs.length < 4) :
    serviceIdParse uuidTryParse bs = none := by
  unfold serviceIdParse tryParseHyphenated hyphenatedLength
  split
  · split
    · exfalso; simp at *; omega
    · rfl
  · split
    · exfalso; omega
    · rfl

theorem toNat_lt_of_ult {x : BitVec 64} {n : Nat} (h : x.toNat = n) (hult : x.ult 4#64 = true) :
    n < 4 :=
  h ▸ BitVec.lt_def.mp (BitVec.ult_iff_lt.mp hult)

theorem le_of_not_ult {x : BitVec 64} {n : Nat} (h : x.toNat = n) (hult : ¬x.ult 4#64 = true) :
    4 ≤ n := by
  have : ¬x.toNat < 4 := fun hlt => hult (BitVec.ult_iff_lt.mpr (BitVec.lt_def.mpr hlt))
  omega

theorem exists_cons4_of_le {bs : List (BitVec 8)} (h : 4 ≤ bs.length) :
    ∃ b0 b1 b2 b3 bs', bs = b0 :: b1 :: b2 :: b3 :: bs' := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, bs'⟩⟩⟩⟩
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · exact ⟨b0, b1, b2, b3, bs', rfl⟩

theorem pointsToBytes_cons4 (p : BitVec 64) (b0 b1 b2 b3 : BitVec 8) (bs' : List (BitVec 8)) :
    (p ↦ₛ (b0 :: b1 :: b2 :: b3 :: bs')) =
      (p ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ ((p + 4#64) ↦ₛ bs') := by
  change (p ↦ₛ ([b0, b1, b2, b3] ++ bs')) = _
  rw [pointsToBytes_append, pointsToBytes4_eq_pointsTo32]
  rfl

namespace ExtractAppendFacts

theorem extractLsb'_append_zero {w1 w2 : Nat} (hi : BitVec w1) (lo : BitVec w2) :
    (hi ++ lo).extractLsb' 0 w2 = lo := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'; simp [BitVec.getLsbD_append, hi']

theorem extractLsb'_append_step {w1 w2 : Nat} (hi : BitVec w1) (lo : BitVec w2)
    (s k : Nat) (h : w2 ≤ s) :
    (hi ++ lo).extractLsb' s k = hi.extractLsb' (s - w2) k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'
  have hnot : ¬(s + i < w2) := by omega
  have hsub : s - w2 + i = s + i - w2 := by omega
  simp [BitVec.getLsbD_append, hi', hnot, hsub]

theorem extractLsb'_append_8 {w1 : Nat} (hi : BitVec w1) (lo : BitVec 8) :
    (hi ++ lo).extractLsb' 8 8 = hi.extractLsb' 0 8 :=
  extractLsb'_append_step hi lo 8 8 (by decide)

theorem extractLsb'_append_16 {w1 : Nat} (hi : BitVec w1) (lo : BitVec 8) :
    (hi ++ lo).extractLsb' 16 8 = hi.extractLsb' 8 8 :=
  extractLsb'_append_step hi lo 16 8 (by decide)

theorem extractLsb'_append_24 {w1 : Nat} (hi : BitVec w1) (lo : BitVec 8) :
    (hi ++ lo).extractLsb' 24 8 = hi.extractLsb' 16 8 :=
  extractLsb'_append_step hi lo 24 8 (by decide)

theorem extractLsb'_zero_self {w : Nat} (x : BitVec w) :
    x.extractLsb' 0 w = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'; simp [hi']

theorem append4_eq_iff (b0 b1 b2 b3 c0 c1 c2 c3 : BitVec 8) :
    b3 ++ b2 ++ b1 ++ b0 = c3 ++ c2 ++ c1 ++ c0 ↔
      b0 = c0 ∧ b1 = c1 ∧ b2 = c2 ∧ b3 = c3 := by
  constructor
  · intro h
    have h0 := congrArg (fun v => v.extractLsb' 0 8) h
    have h1 := congrArg (fun v => v.extractLsb' 8 8) h
    have h2 := congrArg (fun v => v.extractLsb' 16 8) h
    have h3 := congrArg (fun v => v.extractLsb' 24 8) h
    simp only [extractLsb'_append_zero, extractLsb'_append_8,
      extractLsb'_append_16, extractLsb'_append_24,
      extractLsb'_zero_self] at h0 h1 h2 h3
    exact ⟨h0, h1, h2, h3⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl

end ExtractAppendFacts

theorem isPrefixOf_pniPrefix_cons4 (b0 b1 b2 b3 : BitVec 8) (bs' : List (BitVec 8)) :
    pniPrefix.isPrefixOf (b0 :: b1 :: b2 :: b3 :: bs') =
      ((b3 ++ b2 ++ b1 ++ b0) == 0x3a494e50#32) := by
  rw [pniPrefix_word, Bool.eq_iff_iff]
  simp only [List.isPrefixOf, Bool.and_true, Bool.and_eq_true, beq_iff_eq]
  rw [show (0x3a494e50#32 : BitVec 32) = 0x3a#8 ++ 0x49#8 ++ 0x4e#8 ++ 0x50#8 by rfl,
    ExtractAppendFacts.append4_eq_iff]
  exact ⟨fun ⟨h0, h1, h2, h3⟩ => ⟨h0.symm, h1.symm, h2.symm, h3.symm⟩,
    fun ⟨h0, h1, h2, h3⟩ => ⟨h0.symm, h1.symm, h2.symm, h3.symm⟩⟩

theorem drop_pniPrefix_cons4 (b0 b1 b2 b3 : BitVec 8) (bs' : List (BitVec 8)) :
    (b0 :: b1 :: b2 :: b3 :: bs').drop pniPrefix.length = bs' := by
  rw [pniPrefix_word]; rfl

theorem serviceIdParse_cons4_pni (b0 b1 b2 b3 : BitVec 8)
    (bs' : List (BitVec 8)) (hpni : b3 ++ b2 ++ b1 ++ b0 = 0x3a494e50#32) :
    serviceIdParse uuidTryParse (b0 :: b1 :: b2 :: b3 :: bs') =
      if bs'.length = 36 then (uuidTryParse bs').map (fun u => (true, u)) else none := by
  unfold serviceIdParse tryParseHyphenated hyphenatedLength
  have hpni' : pniPrefix.isPrefixOf (b0 :: b1 :: b2 :: b3 :: bs') = true := by
    rw [isPrefixOf_pniPrefix_cons4, hpni]; rfl
  rw [hpni', drop_pniPrefix_cons4]
  split
  · split <;> rfl
  · contradiction

theorem serviceIdParse_cons4_aci (b0 b1 b2 b3 : BitVec 8)
    (bs' : List (BitVec 8)) (hpni : b3 ++ b2 ++ b1 ++ b0 ≠ 0x3a494e50#32) :
    serviceIdParse uuidTryParse (b0 :: b1 :: b2 :: b3 :: bs') =
      if (b0 :: b1 :: b2 :: b3 :: bs').length = 36 then
        (uuidTryParse (b0 :: b1 :: b2 :: b3 :: bs')).map (fun u => (false, u))
      else none := by
  unfold serviceIdParse tryParseHyphenated hyphenatedLength
  have hpni' : pniPrefix.isPrefixOf (b0 :: b1 :: b2 :: b3 :: bs') = false := by
    rw [isPrefixOf_pniPrefix_cons4, beq_eq_false_iff_ne]
    exact hpni
  rw [hpni']
  split
  · contradiction
  · split <;> rfl

theorem length_ne_36_of_ne_40 {x : BitVec 64} {b0 b1 b2 b3 : BitVec 8} {bs' : List (BitVec 8)}
    (h : x.toNat = (b0 :: b1 :: b2 :: b3 :: bs').length) (hne : x ≠ 40#64) :
    bs'.length ≠ 36 := by
  intro h36
  apply hne
  apply BitVec.eq_of_toNat_eq
  simp only [List.length_cons] at h
  change x.toNat = 40
  omega

theorem length_eq_36_of_eq_40 {x : BitVec 64} {b0 b1 b2 b3 : BitVec 8} {bs' : List (BitVec 8)}
    (h : x.toNat = (b0 :: b1 :: b2 :: b3 :: bs').length) (hx : x = 40#64) :
    bs'.length = 36 := by
  rw [hx] at h
  simp only [List.length_cons] at h
  change 40 = bs'.length + 1 + 1 + 1 + 1 at h
  omega

theorem length_ne_36_of_ne_36 {x : BitVec 64} {bs : List (BitVec 8)}
    (h : x.toNat = bs.length) (hne : x ≠ 36#64) :
    bs.length ≠ 36 := by
  intro h36
  apply hne
  apply BitVec.eq_of_toNat_eq
  change x.toNat = 36
  omega

theorem length_eq_36_of_eq_36 {x : BitVec 64} {bs : List (BitVec 8)}
    (h : x.toNat = bs.length) (hx : x = 36#64) :
    bs.length = 36 := by
  rw [hx] at h
  exact h.symm

theorem uuidResultAt_sp64_none (sp : BitVec 64) :
    uuidResultAt (sp - 64#64) none =
      ((sp - 64#64) ↦₃₂ 6#32) ∗ memRegion (sp - 60#64) 28 := by
  simp only [uuidResultAt, uuidErrParseOther]
  have h60 : sp - 64#64 + 4#64 = sp - 60#64 := by bv_arith
  rw [h60]

theorem uuidResultAt_sp64_some (sp : BitVec 64) (u : List.Vector (BitVec 8) 16) :
    uuidResultAt (sp - 64#64) (some u) =
      ((sp - 64#64) ↦₃₂ 0xFFFFFFFF#32) ∗
      ((sp - 60#64) ↦₆₄ uuidWord0 u) ∗
      ((sp - 52#64) ↦₆₄ uuidWord1 u) ∗
      memRegion (sp - 44#64) 12 := by
  simp only [uuidResultAt, uuidOkTag]
  have h60 : sp - 64#64 + 4#64 = sp - 60#64 := by bv_arith
  have h44 : sp - 64#64 + 20#64 = sp - 44#64 := by bv_arith
  have h52 : sp - 60#64 + 8#64 = sp - 52#64 := by bv_arith
  rw [h60, h44, pointsToBytes_uuid (sp - 60#64) u, h52]
  ac_rfl

theorem parseSidResultAt_some_eq (out : BitVec 64) (pni : Bool) (u : List.Vector (BitVec 8) 16) :
    parseSidResultAt out (some (pni, u)) =
      (out ↦₈ kindByte pni) ∗
      ((out + 1#64) ↦₆₄ uuidWord0 u) ∗
      ((out + 9#64) ↦₆₄ uuidWord1 u) := by
  simp only [parseSidResultAt, pointsToBytes_uuid (out + 1#64) u]
  have h9 : out + 1#64 + 8#64 = out + 9#64 := by bv_arith
  rw [h9]

theorem uuidTryParse_ok_at_of_contract {α : Type} (b : BitVec 64)
    (H : String → Option (State → State)) {spec : Spec α}
    (huuid : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr uuidTryParseName) spec)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff uuidTryParseName := by
      fnoff_eq) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr name + BitVec.ofNat 64 k) spec := by
  have hrel :
      (libsignalSessionCode.rebase b H).fnAddr name + BitVec.ofNat 64 k =
        (libsignalSessionCode.rebase b H).fnAddr uuidTryParseName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, BitVec.add_assoc, ← BitVec.ofNat_add, hk]
  rwa [hrel]

theorem uuidTryParseStack_of_spec {P : Program} {addr : BitVec 64}
    (hookStack : Nat)
    (h : subroutine_ok P addr (uuidTryParseSpec uuidTryParse)) :
    subroutine_ok P addr (uuidTryParseStackSpec hookStack) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨ (uuidTryParseSpec uuidTryParse).pre x s0 ∗ (stackAt s0.sp hookStack ∗ R) := by
    simp only [uuidTryParseStackSpec, uuidTryParseSpec, sepConj_assoc] at hpre ⊢
    exact hpre
  refine h.mono_outcome x (stackAt s0.sp hookStack ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    simp only [uuidTryParseStackSpec, uuidTryParseSpec, sepConj_assoc] at hpost ⊢
    exact hpost
  · simp only [uuidTryParseSpec, satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · simp only [uuidTryParseSpec, satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · simp only [uuidTryParseSpec, satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1

theorem parseSid_ok_of_contract_stack (b : BitVec 64)
    (H : String → Option (State → State)) (hookStack : Nat := 0)
    (huuid_entry : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr uuidTryParseName)
      (uuidTryParseStackSpec hookStack)) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr parseSidName)
      (parseSidCodeStackSpec hookStack) := by
  simp only [parseSidCodeStackSpec, parseSidSpec, uuidTryParseStackSpec, uuidTryParseSpec] at huuid_entry ⊢
  have hfn : libsignalSessionCode.fnOff parseSidName = num% (ls_off% "<libsignal_core::address::ServiceId>::parse_from_service_id_string") :=
    (ls_lemma% fnOff "<libsignal_core::address::ServiceId>::parse_from_service_id_string")
  have huuid := uuidTryParse_ok_at_of_contract b H huuid_entry parseSidName (num% (ls_off% "<uuid::Uuid>::try_parse" - ls_off% "<libsignal_core::address::ServiceId>::parse_from_service_id_string"))
    (by simp only [arm64_norm])
  code_fetches CryptoVerification.libsignalSessionCode libsignalSessionBin
    b H (ls_lemma% fnOff "<libsignal_core::address::ServiceId>::parse_from_service_id_string") (num% (ls_off% "<libsignal_core::address::ServiceId>::parse_from_service_id_string")) 212
  clear hfn huuid_entry
  dsimp only [parseSidName, BitVec.ofNat_eq_ofNat] at huuid ⊢
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr
    "<libsignal_core::address::ServiceId>::parse_from_service_id_string" = entry
  wp_init x s0
  examples_hide_fetches
  obtain ⟨p, bs, out⟩ := x
  dsimp only at *
  rw [memRegion_17_none_split out, stackAt_parseSidFrame_split s0.sp]
  wp_pull_exists
  wp_steps
  wp_if hlt4
  · rw [serviceIdParse_of_lt_4 bs (toNat_lt_of_ult h_2 hlt4), parseSidResultAt]
    wp_steps
    wp_done
  · obtain ⟨b0, b1, b2, b3, bs', rfl⟩ := exists_cons4_of_le (le_of_not_ult h_2 hlt4)
    rw [pointsToBytes_cons4 p b0 b1 b2 b3 bs']
    wp_steps
    wp_if hpni
    · rw [serviceIdParse_cons4_pni b0 b1 b2 b3 bs' hpni]
      wp_steps
      wp_if hlen40
      · have hne36 := length_ne_36_of_ne_40 h_2 hlen40
        simp only [hne36, ↓reduceIte, parseSidResultAt]
        wp_steps
        wp_done
      · have heq36 := length_eq_36_of_eq_40 h_2 hlen40
        simp only [heq36, ↓reduceIte]
        wp_steps
        wp_call huuid (p + 4#64, bs', s0.sp - 64#64)
        cases hparse : uuidTryParse bs' with
        | none =>
          rw [uuidResultAt_sp64_none s0.sp, memRegion_sp64_none_split s0.sp]
          dsimp only [Option.map, parseSidResultAt]
          wp_steps
          wp_done
        | some u =>
          rw [uuidResultAt_sp64_some s0.sp u, memRegion_sp64_some_split s0.sp,
              memRegion_out1_16_split out]
          dsimp only [Option.map]
          rw [parseSidResultAt_some_eq out true u]
          wp_pull_exists
          wp_steps
          wp_done
    · rw [serviceIdParse_cons4_aci b0 b1 b2 b3 bs' hpni, ← pointsToBytes_cons4 p b0 b1 b2 b3 bs']
      wp_steps
      wp_if hlen36
      · have hne36 := length_ne_36_of_ne_36 h_2 hlen36
        simp only [hne36, ↓reduceIte, parseSidResultAt]
        wp_steps
        wp_done
      · have heq36 := length_eq_36_of_eq_36 h_2 hlen36
        simp only [heq36, ↓reduceIte]
        wp_steps
        wp_call huuid (p, b0 :: b1 :: b2 :: b3 :: bs', s0.sp - 64#64)
        cases hparse : uuidTryParse (b0 :: b1 :: b2 :: b3 :: bs') with
        | none =>
          rw [uuidResultAt_sp64_none s0.sp, memRegion_sp64_none_split s0.sp]
          dsimp only [Option.map, parseSidResultAt]
          wp_steps
          wp_done
        | some u =>
          rw [uuidResultAt_sp64_some s0.sp u, memRegion_sp64_some_split s0.sp,
              memRegion_out1_16_split out]
          dsimp only [Option.map]
          rw [parseSidResultAt_some_eq out false u]
          wp_pull_exists
          wp_steps
          wp_done

theorem parseSid_ok_of_contract (b : BitVec 64)
    (H : String → Option (State → State))
    (huuid : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr uuidTryParseName)
      (uuidTryParseSpec uuidTryParse)) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr parseSidName)
      (parseSidCodeSpec uuidTryParse) := by
  have h0 := parseSid_ok_of_contract_stack b H uuidTryParseStack
    (uuidTryParseStack_of_spec uuidTryParseStack huuid)
  have hspec : parseSidCodeStackSpec uuidTryParseStack = parseSidCodeSpec uuidTryParse := by
    simp only [parseSidCodeStackSpec, parseSidCodeSpec, stackAt_parseSid_eq_frame]
  rwa [hspec] at h0

/-- `parseSid_ok_aux` on any `libsignalSessionCode.rebase b H` whose `<uuid::Uuid>::try_parse`
meets the in-image `uuidTryParseCodeSpec uuidTryParse` (e.g. `Stage2Contracts.uuid_try_parse`). -/
theorem parseSid_ok_of_code (b : BitVec 64) (H : String → Option (State → State))
    (huuid_entry : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr uuidTryParseName)
      (uuidTryParseCodeSpec uuidTryParse)) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr parseSidName)
      (parseSidCodeSpec uuidTryParse) := by
  simp only [parseSidCodeSpec, parseSidSpec]
  have hfn : libsignalSessionCode.fnOff parseSidName = num% (ls_off% "<libsignal_core::address::ServiceId>::parse_from_service_id_string") :=
    (ls_lemma% fnOff "<libsignal_core::address::ServiceId>::parse_from_service_id_string")
  have huuid := uuidTryParse_ok_at_of_contract b H huuid_entry parseSidName
    (num% (ls_off% "<uuid::Uuid>::try_parse" - ls_off% "<libsignal_core::address::ServiceId>::parse_from_service_id_string")) (by simp only [arm64_norm])
  code_fetches CryptoVerification.libsignalSessionCode libsignalSessionBin
    b H (ls_lemma% fnOff "<libsignal_core::address::ServiceId>::parse_from_service_id_string") (num% (ls_off% "<libsignal_core::address::ServiceId>::parse_from_service_id_string")) 212
  clear hfn huuid_entry
  dsimp only [parseSidName, BitVec.ofNat_eq_ofNat] at huuid ⊢
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr
    "<libsignal_core::address::ServiceId>::parse_from_service_id_string" = entry
  wp_init x s0
  examples_hide_fetches
  obtain ⟨p, bs, out⟩ := x
  dsimp only at *
  rw [memRegion_17_none_split out, stackAt_parseSid_split s0.sp]
  wp_pull_exists
  wp_steps
  wp_if hlt4
  · rw [serviceIdParse_of_lt_4 bs (toNat_lt_of_ult h_2 hlt4), parseSidResultAt]
    wp_steps
    wp_done
  · obtain ⟨b0, b1, b2, b3, bs', rfl⟩ := exists_cons4_of_le (le_of_not_ult h_2 hlt4)
    rw [pointsToBytes_cons4 p b0 b1 b2 b3 bs']
    wp_steps
    wp_if hpni
    · rw [serviceIdParse_cons4_pni b0 b1 b2 b3 bs' hpni]
      wp_steps
      wp_if hlen40
      · have hne36 := length_ne_36_of_ne_40 h_2 hlen40
        simp only [hne36, ↓reduceIte, parseSidResultAt]
        wp_steps
        wp_done
      · have heq36 := length_eq_36_of_eq_40 h_2 hlen40
        simp only [heq36, ↓reduceIte]
        wp_steps
        wp_call huuid (p + 4#64, bs', s0.sp - 64#64)
        cases hparse : uuidTryParse bs' with
        | none =>
          rw [uuidResultAt_sp64_none s0.sp, memRegion_sp64_none_split s0.sp]
          dsimp only [Option.map, parseSidResultAt]
          wp_steps
          wp_done
        | some u =>
          rw [uuidResultAt_sp64_some s0.sp u, memRegion_sp64_some_split s0.sp,
              memRegion_out1_16_split out]
          dsimp only [Option.map]
          rw [parseSidResultAt_some_eq out true u]
          wp_pull_exists
          wp_steps
          wp_done
    · rw [serviceIdParse_cons4_aci b0 b1 b2 b3 bs' hpni, ← pointsToBytes_cons4 p b0 b1 b2 b3 bs']
      wp_steps
      wp_if hlen36
      · have hne36 := length_ne_36_of_ne_36 h_2 hlen36
        simp only [hne36, ↓reduceIte, parseSidResultAt]
        wp_steps
        wp_done
      · have heq36 := length_eq_36_of_eq_36 h_2 hlen36
        simp only [heq36, ↓reduceIte]
        wp_steps
        wp_call huuid (p, b0 :: b1 :: b2 :: b3 :: bs', s0.sp - 64#64)
        cases hparse : uuidTryParse (b0 :: b1 :: b2 :: b3 :: bs') with
        | none =>
          rw [uuidResultAt_sp64_none s0.sp, memRegion_sp64_none_split s0.sp]
          dsimp only [Option.map, parseSidResultAt]
          wp_steps
          wp_done
        | some u =>
          rw [uuidResultAt_sp64_some s0.sp u, memRegion_sp64_some_split s0.sp,
              memRegion_out1_16_split out]
          dsimp only [Option.map]
          rw [parseSidResultAt_some_eq out false u]
          wp_pull_exists
          wp_steps
          wp_done

theorem parseSid_ok_aux_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr parseSidName)
      (parseSidCodeSpec uuidTryParse) :=
  parseSid_ok_of_code b (Rust.withPanics (trTrapExterns C abs))
    (by
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
        uuidTryParse_ok_at_trap b C abs uuidTryParseName 0 (Nat.add_zero _))

theorem parseSid_ok_aux (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr parseSidName)
      (parseSidCodeSpec uuidTryParse) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr parseSidName]
  exact subroutine_ok_kit_of_trTrap (parseSid_ok_aux_trap b C abs)

end ParseServiceId

/-- Contract-backed `ServiceId::parse_from_service_id_string` (`0x3e4c0`) with caller-supplied
`uuidTryParseStackSpec parse hookStack`. -/
theorem parseSid_ok_of_contract_stack (b : BitVec 64)
    (H : String → Option (State → State)) (hookStack : Nat := 0)
    (huuid : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr uuidTryParseName)
      (uuidTryParseStackSpec hookStack)) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr parseSidName)
      (parseSidCodeStackSpec hookStack) :=
  ParseServiceId.parseSid_ok_of_contract_stack b H hookStack huuid

/-- Contract-backed `ServiceId::parse_from_service_id_string` (`0x3e4c0`) with caller-supplied
`uuidTryParseSpec parse`. -/
theorem parseSid_ok_of_contract (b : BitVec 64)
    (H : String → Option (State → State))
    (huuid : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr uuidTryParseName)
      (uuidTryParseSpec uuidTryParse)) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr parseSidName)
      (parseSidCodeSpec uuidTryParse) :=
  ParseServiceId.parseSid_ok_of_contract b H huuid

theorem parseSid_ok_ext (b : BitVec 64) (C : Crypto) (A : RustHeap.RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hC : Stage2Contracts b C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr parseSidName)
      (parseSidCodeSpec uuidTryParse) :=
  ParseServiceId.parseSid_ok_of_code b (Rust.withPanics ext) hC.uuid_try_parse

theorem parseSid_ok_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr parseSidName)
      (parseSidCodeSpec uuidTryParse) :=
  ParseServiceId.parseSid_ok_of_code b (Rust.withPanics (trTrapExterns C abs))
    (by
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
        uuidTryParse_ok_at_trap b C abs uuidTryParseName 0 (Nat.add_zero _))

theorem parseSid_ok (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr parseSidName)
      (parseSidCodeSpec uuidTryParse) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr parseSidName]
  exact subroutine_ok_kit_of_trTrap (parseSid_ok_trap b C abs)

namespace ParseServiceId

private abbrev ImgCallInv (img : Obj.Image) (s : State) : Prop :=
  img.FrozenLoaded s ∧ s.symtab = img.symtab

private theorem ImgCallInv.of_steps {img : Obj.Image} {prog : Program} {s s' : State}
    (h : ImgCallInv img s) (hs : Steps prog s s') : ImgCallInv img s' :=
  ⟨h.1.of_keepsFrozen hs.keepsFrozen, hs.symtab_eq.trans h.2⟩

private theorem SepWP.seq_inImage {prog : Program} {img : Obj.Image} {mid target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (h : SepWP prog mid s P (fun sm Pm => ImgCallInv img sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post := by
  unfold SepWP
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨hoom, hfalse⟩⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', out⟩ :=
      (hnext (hinv.of_steps hsteps)).elim hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', out⟩
  · exact ⟨sm, hsteps, Or.inr ⟨hoom, hfalse⟩⟩

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem frozenLoaded_setMem (img : Obj.Image) (s : State) (m : Memory) :
    img.FrozenLoaded (s.setMem m) = img.FrozenLoaded (State.setMem default m) := by
  simp only [Obj.Image.frozenLoaded_iff]; rfl

theorem parseSid_ok_of_contract_stack_inImage (img : Obj.Image)
    (H : String → Option (State → State)) (hookStack : Nat := 0)
    (huuid_entry : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr uuidTryParseName)
      ((uuidTryParseStackSpec hookStack).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr parseSidName)
      ((parseSidCodeStackSpec hookStack).inImage img) := by
  unfold Spec.inImage at huuid_entry ⊢
  simp only [parseSidCodeStackSpec, parseSidSpec, uuidTryParseStackSpec, uuidTryParseSpec] at huuid_entry ⊢
  have hfn : libsignalSessionCode.fnOff parseSidName = num% (ls_off% "<libsignal_core::address::ServiceId>::parse_from_service_id_string") :=
    (ls_lemma% fnOff "<libsignal_core::address::ServiceId>::parse_from_service_id_string")
  have huuid := uuidTryParse_ok_at_of_contract img.base H huuid_entry parseSidName (num% (ls_off% "<uuid::Uuid>::try_parse" - ls_off% "<libsignal_core::address::ServiceId>::parse_from_service_id_string"))
    (by simp only [arm64_norm])
  code_fetches CryptoVerification.libsignalSessionCode libsignalSessionBin
    img.base H (ls_lemma% fnOff "<libsignal_core::address::ServiceId>::parse_from_service_id_string") (num% (ls_off% "<libsignal_core::address::ServiceId>::parse_from_service_id_string")) 212
  clear hfn huuid_entry
  dsimp only [parseSidName, BitVec.ofNat_eq_ofNat] at huuid ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr
    "<libsignal_core::address::ServiceId>::parse_from_service_id_string" = entry
  wp_init x s0
  examples_hide_fetches
  obtain ⟨p, bs, out⟩ := x
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  rw [memRegion_17_none_split out, stackAt_parseSidFrame_split s0.sp]
  wp_pull_exists
  apply SepWP.seq_inImage (mid := entry + bv% (16)) hinv0
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  rintro ⟨hF1, hsym1⟩
  simp only [frozenLoaded_setMem, arm64_norm] at hF1 hsym1
  wp_steps
  wp_if hlt4
  · rw [serviceIdParse_of_lt_4 bs (toNat_lt_of_ult h_4 hlt4), parseSidResultAt]
    wp_steps
    wp_done
  · obtain ⟨b0, b1, b2, b3, bs', rfl⟩ := exists_cons4_of_le (le_of_not_ult h_4 hlt4)
    rw [pointsToBytes_cons4 p b0 b1 b2 b3 bs']
    wp_steps
    wp_if hpni
    · rw [serviceIdParse_cons4_pni b0 b1 b2 b3 bs' hpni]
      wp_steps
      wp_if hlen40
      · have hne36 := length_ne_36_of_ne_40 h_4 hlen40
        simp only [hne36, ↓reduceIte, parseSidResultAt]
        wp_steps
        wp_done
      · have heq36 := length_eq_36_of_eq_40 h_4 hlen40
        simp only [heq36, ↓reduceIte]
        wp_steps
        wp_call huuid (p + 4#64, bs', s0.sp - 64#64)
        cases hparse : uuidTryParse bs' with
        | none =>
          rw [uuidResultAt_sp64_none s0.sp, memRegion_sp64_none_split s0.sp]
          dsimp only [Option.map, parseSidResultAt]
          wp_steps
          wp_done
        | some u =>
          rw [uuidResultAt_sp64_some s0.sp u, memRegion_sp64_some_split s0.sp,
              memRegion_out1_16_split out]
          dsimp only [Option.map]
          rw [parseSidResultAt_some_eq out true u]
          wp_pull_exists
          wp_steps
          wp_done
    · rw [serviceIdParse_cons4_aci b0 b1 b2 b3 bs' hpni, ← pointsToBytes_cons4 p b0 b1 b2 b3 bs']
      wp_steps
      wp_if hlen36
      · have hne36 := length_ne_36_of_ne_36 h_4 hlen36
        simp only [hne36, ↓reduceIte, parseSidResultAt]
        wp_steps
        wp_done
      · have heq36 := length_eq_36_of_eq_36 h_4 hlen36
        simp only [heq36, ↓reduceIte]
        wp_steps
        wp_call huuid (p, b0 :: b1 :: b2 :: b3 :: bs', s0.sp - 64#64)
        cases hparse : uuidTryParse (b0 :: b1 :: b2 :: b3 :: bs') with
        | none =>
          rw [uuidResultAt_sp64_none s0.sp, memRegion_sp64_none_split s0.sp]
          dsimp only [Option.map, parseSidResultAt]
          wp_steps
          wp_done
        | some u =>
          rw [uuidResultAt_sp64_some s0.sp u, memRegion_sp64_some_split s0.sp,
              memRegion_out1_16_split out]
          dsimp only [Option.map]
          rw [parseSidResultAt_some_eq out false u]
          wp_pull_exists
          wp_steps
          wp_done

end ParseServiceId

/-- Contract-backed `ServiceId::parse_from_service_id_string` (`0x3e4c0`) with caller-supplied
`(uuidTryParseStackSpec parse hookStack).inImage img`. -/
theorem parseSid_ok_of_contract_stack_inImage (img : Obj.Image)
    (H : String → Option (State → State)) (hookStack : Nat := 0)
    (huuid : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr uuidTryParseName)
      ((uuidTryParseStackSpec hookStack).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr parseSidName)
      ((parseSidCodeStackSpec hookStack).inImage img) :=
  ParseServiceId.parseSid_ok_of_contract_stack_inImage img H hookStack huuid

/-! ## Relocatable per-block proofs (`[LibsignalPlacement]`) -/

namespace ParseServiceId

theorem parseSid_placed_ok_of_contract_stack [LibsignalPlacement]
    (H : String → Option (State → State)) (hookStack : Nat := 0)
    (huuid_entry : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H)
      (blkPl_252).base
      (withLsCodeLoaded lsmpl (uuidTryParseStackSpec hookStack))) :
    subroutine_ok ((blkPC_206).rebase (blkPl_206).base H)
      (blkPl_206).base
      (withLsCodeLoaded lsmpl (parseSidCodeStackSpec hookStack)) := by
  have huuid := ls_subroutine_ok_of_block (callerProg := (blkPC_206).rebase (blkPl_206).base H) huuid_entry
  change subroutine_ok _ (lsmpl.base 252) _ at huuid
  unfold withLsCodeLoaded at huuid ⊢
  simp only [parseSidCodeStackSpec, parseSidSpec, uuidTryParseStackSpec, uuidTryParseSpec] at huuid ⊢
  clear huuid_entry
  wp_init x s0
  obtain ⟨p, bs, out⟩ := x
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hlen_eq : (s0.readReg64 (Reg.gpr 1#5)).toNat = bs.length := by assumption
  rw [memRegion_17_none_split out, stackAt_parseSidFrame_split s0.sp]
  wp_pull_exists
  apply sepWP_seq_lscl hcl0 (mid := (blkPl_206).base + bv% (16))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  wp_steps
  wp_if hlt4
  · rw [serviceIdParse_of_lt_4 bs (toNat_lt_of_ult hlen_eq hlt4), parseSidResultAt]
    wp_steps
    wp_done
  · obtain ⟨b0, b1, b2, b3, bs', rfl⟩ := exists_cons4_of_le (le_of_not_ult hlen_eq hlt4)
    rw [pointsToBytes_cons4 p b0 b1 b2 b3 bs']
    wp_steps
    wp_if hpni
    · rw [serviceIdParse_cons4_pni b0 b1 b2 b3 bs' hpni]
      wp_steps
      wp_if hlen40
      · have hne36 := length_ne_36_of_ne_40 hlen_eq hlen40
        simp only [hne36, ↓reduceIte, parseSidResultAt]
        wp_steps
        wp_done
      · have heq36 := length_eq_36_of_eq_40 hlen_eq hlen40
        simp only [heq36, ↓reduceIte]
        wp_steps
        wp_call huuid (p + 4#64, bs', s0.sp - 64#64)
        cases hparse : uuidTryParse bs' with
        | none =>
          rw [uuidResultAt_sp64_none s0.sp, memRegion_sp64_none_split s0.sp]
          dsimp only [Option.map, parseSidResultAt]
          wp_steps
          wp_done
        | some u =>
          rw [uuidResultAt_sp64_some s0.sp u, memRegion_sp64_some_split s0.sp,
              memRegion_out1_16_split out]
          dsimp only [Option.map]
          rw [parseSidResultAt_some_eq out true u]
          wp_pull_exists
          wp_steps
          wp_done
    · rw [serviceIdParse_cons4_aci b0 b1 b2 b3 bs' hpni, ← pointsToBytes_cons4 p b0 b1 b2 b3 bs']
      wp_steps
      wp_if hlen36
      · have hne36 := length_ne_36_of_ne_36 hlen_eq hlen36
        simp only [hne36, ↓reduceIte, parseSidResultAt]
        wp_steps
        wp_done
      · have heq36 := length_eq_36_of_eq_36 hlen_eq hlen36
        simp only [heq36, ↓reduceIte]
        wp_steps
        wp_call huuid (p, b0 :: b1 :: b2 :: b3 :: bs', s0.sp - 64#64)
        cases hparse : uuidTryParse (b0 :: b1 :: b2 :: b3 :: bs') with
        | none =>
          rw [uuidResultAt_sp64_none s0.sp, memRegion_sp64_none_split s0.sp]
          dsimp only [Option.map, parseSidResultAt]
          wp_steps
          wp_done
        | some u =>
          rw [uuidResultAt_sp64_some s0.sp u, memRegion_sp64_some_split s0.sp,
              memRegion_out1_16_split out]
          dsimp only [Option.map]
          rw [parseSidResultAt_some_eq out false u]
          wp_pull_exists
          wp_steps
          wp_done

end ParseServiceId

/-- Relocatable `ServiceId::parse_from_service_id_string` (Block `206`) with caller-supplied
`withLsCodeLoaded lsmpl (uuidTryParseStackSpec hookStack)` on Block `252`. -/
theorem parseSid_placed_ok_of_contract_stack [LibsignalPlacement]
    (H : String → Option (State → State)) (hookStack : Nat := 0)
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H)
      (blkPl_252).base
      (withLsCodeLoaded lsmpl (uuidTryParseStackSpec hookStack))) :
    subroutine_ok ((blkPC_206).rebase (blkPl_206).base H)
      (blkPl_206).base
      (withLsCodeLoaded lsmpl (parseSidCodeStackSpec hookStack)) :=
  ParseServiceId.parseSid_placed_ok_of_contract_stack H hookStack huuid

/-- Relocatable `ServiceId::parse_from_service_id_string` (Block `206`) with caller-supplied
plain `uuidTryParseStackSpec hookStack` on Block `252`. -/
theorem parseSid_placed_ok_of_plain_contract_stack [LibsignalPlacement]
    (H : String → Option (State → State)) (hookStack : Nat := 0)
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H)
      (blkPl_252).base
      (uuidTryParseStackSpec hookStack)) :
    subroutine_ok ((blkPC_206).rebase (blkPl_206).base H)
      (blkPl_206).base
      (withLsCodeLoaded lsmpl (parseSidCodeStackSpec hookStack)) :=
  ParseServiceId.parseSid_placed_ok_of_contract_stack H hookStack
    (subroutine_ok_withLsCodeLoaded_of_plain huuid)

/-- Relocatable `ServiceId::parse_from_service_id_string` (Block `206`) with caller-supplied
`withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse)` on Block `252`. -/
theorem parseSid_placed_ok_of_code [LibsignalPlacement]
    (H : String → Option (State → State))
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H)
      (blkPl_252).base
      (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse))) :
    subroutine_ok ((blkPC_206).rebase (blkPl_206).base H)
      (blkPl_206).base
      (withLsCodeLoaded lsmpl (parseSidCodeSpec uuidTryParse)) := by
  have h0 := ParseServiceId.parseSid_placed_ok_of_contract_stack H uuidTryParseStack huuid
  have hspec : parseSidCodeStackSpec uuidTryParseStack = parseSidCodeSpec uuidTryParse := by
    simp only [parseSidCodeStackSpec, parseSidCodeSpec, ParseServiceId.stackAt_parseSid_eq_frame]
  rwa [hspec] at h0

/-- Relocatable `ServiceId::parse_from_service_id_string` (Block `206`) with caller-supplied
`uuidTryParseSpec uuidTryParse` on Block `252`. -/
theorem parseSid_placed_ok_of_contract [LibsignalPlacement]
    (H : String → Option (State → State))
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H)
      (blkPl_252).base
      (uuidTryParseSpec uuidTryParse)) :
    subroutine_ok ((blkPC_206).rebase (blkPl_206).base H)
      (blkPl_206).base
      (withLsCodeLoaded lsmpl (parseSidCodeSpec uuidTryParse)) :=
  parseSid_placed_ok_of_code H
    (subroutine_ok_withLsCodeLoaded_of_plain
      (ParseServiceId.uuidTryParseStack_of_spec uuidTryParseStack huuid))

end CryptoVerification.LibsignalTripleRatchet
