/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccount
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
public import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244

/-!
# Relocatable Contracts for `<IdentityKey>::is_same_account` (Block `17`)

Proves `isSameAccountDistinctRawSpec` and `isSameAccountDistinctSpec` on Block `17` under
`[LibsignalPlacement]`, covering both `localIk ≠ remoteIk` and `localIk = remoteIk ∧ DistinctSid`
via Blocks `212` (`<PublicKey as PartialEq>::eq`) and `206` (`parse_from_service_id_string`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.WireEntries

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalSession.FindReceiverChainIndex

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Stack and Callee Adapters (Blocks `212` and `206`) -/

private theorem stackAt_parseSidStack_eq_publicKeyEq_placed (sp : BitVec 64) :
    stackAt sp parseSidStack =
      memRegion (sp - 16#64) 16 ∗
      memRegion (sp - 16#64 - 48#64) 48 ∗
      memRegion (sp - 272#64) 208 := by
  simp only [stackAt, parseSidStack, uuidTryParseStack]
  have h64 : sp - 16#64 - 48#64 = sp - 64#64 := by bv_omega
  rw [h64,
      show (80 + 192 : Nat) = 272 from rfl,
      show BitVec.ofNat 64 272 = 272#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 272#64) (b' := sp - 64#64) (N := 272) (n := 208) (k := 64)
        (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64) (b' := sp - 16#64) (N := 64) (n := 48) (k := 16)
        (by decide) (by bv_omega) (by decide)]
  ac_rfl

private def publicKeyEqMem80PlacedSpec :
    Spec (BitVec 64 × PublicKey × BitVec 64 × PublicKey × BitVec 64) where
  pre := fun (p1, pk1, p2, pk2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp⌝ ∗
    (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
    stackAt sp parseSidStack
  post := fun (p1, pk1, p2, pk2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if pk1 == pk2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
    (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
    stackAt sp parseSidStack

private theorem publicKeyEqMem80_placed_ok [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hEq : subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
      (withLsCodeLoaded lsmpl publicKeyEqMemSpec)) :
    subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
      (withLsCodeLoaded lsmpl publicKeyEqMem80PlacedSpec) := by
  refine subroutine_ok_map hEq ?_
  rintro ⟨p1, pk1, p2, pk2, sp⟩ R s0 hpre
  refine ⟨(p1, pk1, p2, pk2, sp), memRegion (sp - 272#64) 208 ∗ R, ?_, ?_⟩
  · simp only [publicKeyEqMemSpec, publicKeyEqMem80PlacedSpec,
      stackAt_parseSidStack_eq_publicKeyEq_placed sp] at hpre ⊢
    exact Satisfies.of_eq hpre (by ac_rfl)
  · intro sf hpost
    simp only [publicKeyEqMemSpec, publicKeyEqMem80PlacedSpec,
      stackAt_parseSidStack_eq_publicKeyEq_placed sp] at hpost ⊢
    exact Satisfies.of_eq hpost (by ac_rfl)

private theorem memRegion_17_eq_cells_placed (a : BitVec 64) :
    memRegion a 17 =
      ∃∗ b0 : BitVec 8, ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        (a ↦₈ b0) ∗ ((a + 1#64) ↦₆₄ w0) ∗ ((a + 9#64) ↦₆₄ w1) := by
  rw [show (17 : Nat) = 1 + (8 + 8) by decide,
    memRegion_split a 1 (8 + 8) (by decide),
    memRegion_split (a + 1#64) 8 8 (by decide),
    memRegion_one a, ProofLib.memRegion_eight (a + 1#64),
    ProofLib.memRegion_eight (a + 1#64 + 8#64)]
  have h9 : a + 1#64 + 8#64 = a + 9#64 := by bv_arith
  rw [h9, sepExists_sepConj_left]
  refine congrArg sepExists (funext fun b0 => ?_)
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine congrArg sepExists (funext fun w0 => ?_)
  rw [sepExists_sepConj_right, sepExists_sepConj_right]

private theorem pointsTo_17_entails_memRegion_placed (a : BitVec 64)
    (b0 : BitVec 8) (w0 w1 : BitVec 64) :
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₆₄ w0) ∗ ((a + 9#64) ↦₆₄ w1)) ⊢ memRegion a 17 := by
  rw [memRegion_17_eq_cells_placed a]
  exact Entails.sepExists_right b0 (Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.refl _)))

private theorem memRegion_16_out_split_placed (a : BitVec 64) :
    memRegion (a + 1#64) 16 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ((a + 1#64) ↦₆₄ w0) ∗ ((a + 9#64) ↦₆₄ w1) := by
  rw [show (16 : Nat) = 8 + 8 by decide, memRegion_split (a + 1#64) 8 8 (by decide)]
  have h9 : a + 1#64 + BitVec.ofNat 64 8 = a + 9#64 := by bv_arith
  rw [h9, ProofLib.memRegion_eight (a + 1#64), ProofLib.memRegion_eight (a + 9#64),
    sepExists_sepConj_left]
  refine congrArg sepExists (funext fun w0 => ?_)
  rw [sepExists_sepConj_right]

private theorem parseSidResultAt_entails_rel_cells_placed (out : BitVec 64)
    (res : Option (Bool × List.Vector (BitVec 8) 16)) :
    parseSidResultAt out res ⊢
      ∃∗ b0 : BitVec 8, ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        ⌜SidCellsRel res b0 w0 w1⌝ ∗
        (out ↦₈ b0) ∗ ((out + 1#64) ↦₆₄ w0) ∗ ((out + 9#64) ↦₆₄ w1) := by
  cases res with
  | none =>
    simp only [parseSidResultAt, SidCellsRel, memRegion_16_out_split_placed,
      sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro w0
    apply Entails.sepExists_elim; intro w1
    refine Entails.sepExists_right 2#8 (Entails.sepExists_right w0 (Entails.sepExists_right w1 ?_))
    exact Entails.pure_right rfl (Entails.of_eq (by ac_rfl))
  | some val =>
    rcases val with ⟨pni, uuid⟩
    rw [ParseServiceId.parseSidResultAt_some_eq out pni uuid]
    exact Entails.sepExists_right (kindByte pni)
      (Entails.sepExists_right (ParseServiceId.uuidWord0 uuid)
        (Entails.sepExists_right (ParseServiceId.uuidWord1 uuid)
          (Entails.pure_right ⟨rfl, rfl, rfl⟩ (Entails.refl _))))

private abbrev ParseSidRelPlacedGhost :=
  BitVec 64 × List (BitVec 8) × BitVec 64 × BitVec 8 × BitVec 64 × BitVec 64

private def parseSidRelPlacedSpec (parse : UuidParser) : Spec ParseSidRelPlacedGhost where
  pre := fun (p, bs, out, b0, w0, w1) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ s.readReg64 .x8 = out⌝ ∗
      (p ↦ₛ bs) ∗ (out ↦₈ b0) ∗ ((out + 1#64) ↦₆₄ w0) ∗ ((out + 9#64) ↦₆₄ w1) ∗
      stackAt s.sp parseSidStack
  post := fun (p, bs, out, _, _, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (p ↦ₛ bs) ∗
      (∃∗ b0' : BitVec 8, ∃∗ w0' : BitVec 64, ∃∗ w1' : BitVec 64,
        ⌜SidCellsRel (serviceIdParse parse bs) b0' w0' w1'⌝ ∗
        (out ↦₈ b0') ∗ ((out + 1#64) ↦₆₄ w0') ∗ ((out + 9#64) ↦₆₄ w1')) ∗
      stackAt s0.sp parseSidStack

private theorem parseSidRel_placed_ok [LibsignalPlacement] {parse : UuidParser}
    {H : String → Option (State → State)}
    (hParse : subroutine_ok ((blkPC_206).rebase (blkPl_206).base H) (blkPl_206).base
      (withLsCodeLoaded lsmpl (parseSidCodeSpec parse))) :
    subroutine_ok ((blkPC_206).rebase (blkPl_206).base H) (blkPl_206).base
      (withLsCodeLoaded lsmpl (parseSidRelPlacedSpec parse)) := by
  refine subroutine_ok_map hParse ?_
  rintro ⟨p, bs, out, b0, w0, w1⟩ R s0 hpre
  refine ⟨(p, bs, out), R, ?_, fun sf hpost => ?_⟩
  · simp only [parseSidRelPlacedSpec, parseSidCodeSpec, parseSidSpec] at hpre ⊢
    have hm : s0.mem ⊨ ((out ↦₈ b0) ∗ ((out + 1#64) ↦₆₄ w0) ∗ ((out + 9#64) ↦₆₄ w1)) ∗
        (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧ s0.readReg64 .x8 = out⌝ ∗
          ⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗
          (p ↦ₛ bs) ∗ stackAt s0.sp parseSidStack ∗ R) :=
      Satisfies.of_eq hpre (by ac_rfl)
    have hm' :=
      Arm64.Satisfies.mono (sepConj_mono_left (pointsTo_17_entails_memRegion_placed out b0 w0 w1)) hm
    exact Satisfies.of_eq hm' (by ac_rfl)
  · simp only [parseSidCodeSpec, parseSidSpec, parseSidRelPlacedSpec] at hpost ⊢
    have hm : sf.mem ⊨ parseSidResultAt out (serviceIdParse parse bs) ∗
        (⌜sf.trace = s0.trace⌝ ∗ (p ↦ₛ bs) ∗ stackAt s0.sp parseSidStack ∗ R) :=
      Satisfies.of_eq hpost (by ac_rfl)
    have hm' :=
      Arm64.Satisfies.mono (sepConj_mono_left (parseSidResultAt_entails_rel_cells_placed out _)) hm
    exact Satisfies.of_eq hm' (by ac_rfl)

private theorem stackAt_isSameAccountDistinct_split_placed (sp : BitVec 64) :
    stackAt sp isSameAccountDistinctStack =
      stackAt (sp - 80#64) parseSidStack ∗
      memRegion (sp - 80#64) 12 ∗
      (∃∗ b0 : BitVec 8, ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        ((sp - 68#64) ↦₈ b0) ∗ ((sp - 67#64) ↦₆₄ w0) ∗ ((sp - 59#64) ↦₆₄ w1)) ∗
      memRegion (sp - 51#64) 3 ∗
      ProofLib.cells (sp - 48#64) 6 := by
  simp only [stackAt, isSameAccountDistinctStack, parseSidStack, uuidTryParseStack]
  rw [show (80 + (80 + 192) : Nat) = 352 from rfl,
      show (80 + 192 : Nat) = 272 from rfl,
      show BitVec.ofNat 64 352 = 352#64 from rfl,
      show BitVec.ofNat 64 272 = 272#64 from rfl,
      show sp - 80#64 - 272#64 = sp - 352#64 by bv_arith,
      show (352 : Nat) = 272 + (12 + (17 + (3 + 8 * 6))) by decide,
      memRegion_split (sp - 352#64) 272 (12 + (17 + (3 + 8 * 6))) (by decide),
      memRegion_split (sp - 352#64 + 272#64) 12 (17 + (3 + 8 * 6)) (by decide),
      memRegion_split (sp - 352#64 + 272#64 + 12#64) 17 (3 + 8 * 6) (by decide),
      memRegion_split (sp - 352#64 + 272#64 + 12#64 + 17#64) 3 (8 * 6) (by decide),
      ProofLib.memRegion_cells _ 6 (by decide),
      memRegion_17_eq_cells_placed]
  have h1 : sp - 352#64 + 272#64 = sp - 80#64 := by bv_arith
  have h2 : sp - 80#64 + 12#64 = sp - 68#64 := by bv_arith
  have h3 : sp - 68#64 + 1#64 = sp - 67#64 := by bv_arith
  have h4 : sp - 68#64 + 9#64 = sp - 59#64 := by bv_arith
  have h5 : sp - 68#64 + 17#64 = sp - 51#64 := by bv_arith
  have h6 : sp - 51#64 + 3#64 = sp - 48#64 := by bv_arith
  rw [h1, h2, h3, h4, h5, h6]

private theorem pack64_inj_placed (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (h : pack64 a0 a1 a2 a3 a4 a5 a6 a7 = pack64 b0 b1 b2 b3 b4 b5 b6 b7) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 ∧ a5 = b5 ∧ a6 = b6 ∧ a7 = b7 := by
  unfold pack64 at h
  exact ⟨
    calc a0 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 0 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 0 8 := congrArg _ h
      _ = b0 := by unfold pack64; bv_bits,
    calc a1 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 8 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 8 8 := congrArg _ h
      _ = b1 := by unfold pack64; bv_bits,
    calc a2 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 16 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 16 8 := congrArg _ h
      _ = b2 := by unfold pack64; bv_bits,
    calc a3 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 24 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 24 8 := congrArg _ h
      _ = b3 := by unfold pack64; bv_bits,
    calc a4 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 32 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 32 8 := congrArg _ h
      _ = b4 := by unfold pack64; bv_bits,
    calc a5 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 40 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 40 8 := congrArg _ h
      _ = b5 := by unfold pack64; bv_bits,
    calc a6 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 48 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 48 8 := congrArg _ h
      _ = b6 := by unfold pack64; bv_bits,
    calc a7 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 56 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 56 8 := congrArg _ h
      _ = b7 := by unfold pack64; bv_bits⟩

private theorem uuid_eq_of_uuidWords_eq_placed {u1 u2 : List.Vector (BitVec 8) 16}
    (hw0 : ParseServiceId.uuidWord0 u1 = ParseServiceId.uuidWord0 u2)
    (hw1 : ParseServiceId.uuidWord1 u1 = ParseServiceId.uuidWord1 u2) :
    u1 = u2 := by
  rcases u1 with ⟨l1, hl1⟩
  rcases u2 with ⟨l2, hl2⟩
  rcases l1 with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7,
    _ | ⟨a8, _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, _ | ⟨a12, _ | ⟨a13, _ | ⟨a14, _ | ⟨a15,
      _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try cases hl1
  rcases l2 with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
      _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try cases hl2
  simp only [ParseServiceId.uuidWord0, ParseServiceId.uuidWord1, List.Vector.toList, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hw0 hw1
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := pack64_inj_placed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw0
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := pack64_inj_placed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw1
  rfl

private theorem kindByte_inj_placed {p1 p2 : Bool} (h : kindByte p1 = kindByte p2) : p1 = p2 := by
  cases p1 <;> cases p2 <;> revert h <;> decide

private theorem sidCellsRel_ne_of_distinct_placed {parse : UuidParser} {bs1 bs2 : List (BitVec 8)}
    {b0_1 b0_2 : BitVec 8} {w0_1 w1_1 w0_2 w1_2 : BitVec 64}
    (hDist : DistinctSid parse bs1 bs2)
    (hrel1 : SidCellsRel (serviceIdParse parse bs1) b0_1 w0_1 w1_1)
    (hrel2 : SidCellsRel (serviceIdParse parse bs2) b0_2 w0_2 w1_2)
    (hb1 : b0_1 ≠ 2#8) (hb2 : b0_2 ≠ 2#8) (hkind : b0_1 = b0_2) :
    w0_1 = w0_2 ∧ w1_1 = w1_2 → False := by
  rintro ⟨hw0, hw1⟩
  cases hs1 : serviceIdParse parse bs1 with
  | none => rw [hs1, SidCellsRel] at hrel1; exact hb1 hrel1
  | some v1 =>
    rcases v1 with ⟨p1, u1⟩
    rw [hs1, SidCellsRel] at hrel1
    rcases hrel1 with ⟨hb0_1, hw0_1, hw1_1⟩
    cases hs2 : serviceIdParse parse bs2 with
    | none => rw [hs2, SidCellsRel] at hrel2; exact hb2 hrel2
    | some v2 =>
      rcases v2 with ⟨p2, u2⟩
      rw [hs2, SidCellsRel] at hrel2
      rcases hrel2 with ⟨hb0_2, hw0_2, hw1_2⟩
      have hp : p1 = p2 := kindByte_inj_placed (hb0_1.symm.trans (hkind.trans hb0_2))
      have hu : u1 = u2 := uuid_eq_of_uuidWords_eq_placed
        (hw0_1.symm.trans (hw0.trans hw0_2))
        (hw1_1.symm.trans (hw1.trans hw1_2))
      subst hp hu
      exact hDist (p1, u1) hs1 hs2

private theorem cond_uuid_words_ne_placed {w0_1 w1_1 w0_2 w1_2 : BitVec 64}
    (hne : w0_1 = w0_2 ∧ w1_1 = w1_2 → False) :
    (if (w0_1 == w0_2) = true then w1_1 != w1_2 else true) = true := by
  by_cases h0 : (w0_1 == w0_2) = true
  · simp only [h0, ↓reduceIte, bne_iff_ne]
    intro h1
    exact hne ⟨of_decide_eq_true h0, h1⟩
  · simp only [h0, Bool.false_eq_true, ↓reduceIte]

private theorem sidCellsRel_b0_cases_placed {o : Option (Bool × List.Vector (BitVec 8) 16)}
    {b0 : BitVec 8} {w0 w1 : BitVec 64} (h : SidCellsRel o b0 w0 w1) :
    b0 = 0#8 ∨ b0 = 1#8 ∨ b0 = 2#8 := by
  cases o with
  | none => right; right; exact h
  | some v => rcases v with ⟨p, _⟩; rcases h with ⟨rfl, _, _⟩; cases p <;> simp [kindByte]

/-! ## `isSameAccountDistinctRaw_placed_ok` (Block `17`) -/

/-- Block `17` (`<IdentityKey>::is_same_account`) meets `isSameAccountDistinctRawSpec parse`
under `[LibsignalPlacement]`, given `subroutine_ok` for Block `212` (`publicKeyEqMemSpec`)
and Block `206` (`parseSidCodeSpec parse`). -/
theorem isSameAccountDistinctRaw_placed_ok_of_callees [LibsignalPlacement] {parse : UuidParser}
    {H : String → Option (State → State)}
    (hEq : subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
      (withLsCodeLoaded lsmpl publicKeyEqMemSpec))
    (hParse : subroutine_ok ((blkPC_206).rebase (blkPl_206).base H) (blkPl_206).base
      (withLsCodeLoaded lsmpl (parseSidCodeSpec parse))) :
    subroutine_ok ((blkPC_17).rebase (blkPl_17).base H) (blkPl_17).base
      (withLsCodeLoaded lsmpl (isSameAccountDistinctRawSpec parse)) := by
  simp only [withLsCodeLoaded, isSameAccountDistinctRawSpec]
  have hEq0 : subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (lsmpl.base 212)
      (withLsCodeLoaded lsmpl publicKeyEqMem80PlacedSpec) :=
    publicKeyEqMem80_placed_ok hEq
  have hEq' := ls_subroutine_ok_cl_of_block (callerProg := (blkPC_17).rebase (blkPl_17).base H) hEq0
  simp only [withLsCl, publicKeyEqMem80PlacedSpec] at hEq'
  have hParse0 : subroutine_ok ((blkPC_206).rebase (blkPl_206).base H) (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidRelPlacedSpec parse)) :=
    parseSidRel_placed_ok hParse
  have hParse' := ls_subroutine_ok_cl_of_block (callerProg := (blkPC_17).rebase (blkPl_17).base H) hParse0
  simp only [withLsCl, parseSidRelPlacedSpec] at hParse'
  wp_init x s0
  obtain ⟨localIkA, localIk, localAddr, localNamePtr, localNameBytes,
    remoteIkA, remoteIk, remoteAddr, remoteNamePtr, remoteNameBytes⟩ := x
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = localIkA := by assumption
  have hx1 : s0.readReg64 (Reg.gpr 1#5) = localAddr := by assumption
  have hx2 : s0.readReg64 (Reg.gpr 2#5) = remoteIkA := by assumption
  have hx3 : s0.readReg64 (Reg.gpr 3#5) = remoteAddr := by assumption
  have h_or : localIk ≠ remoteIk ∨ DistinctSid parse localNameBytes remoteNameBytes := by assumption
  subst hx0 hx1 hx2 hx3
  rw [stackAt_isSameAccountDistinct_split_placed s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro b0_init
  apply SepWP.exists_elim; intro w0_init
  apply SepWP.exists_elim; intro w1_init
  cells_unfold
  wp_pull_exists
  wp_steps_lscl (lsmpl.base 212)
  wp_call hEq' (s0.readReg64 (Reg.gpr 0#5), localIk.publicKey,
    s0.readReg64 (Reg.gpr 2#5), remoteIk.publicKey, s0.sp - 80#64)
  by_cases hpk : (localIk.publicKey == remoteIk.publicKey) = true
  · have hik_eq : localIk = remoteIk := by
      cases localIk; cases remoteIk
      have hpk' := of_decide_eq_true hpk
      subst hpk'; rfl
    have hDist : DistinctSid parse localNameBytes remoteNameBytes :=
      h_or.resolve_left (not_not.mpr hik_eq)
    simp only [hpk, ↓reduceIte] at *
    wp_steps_lscl (lsmpl.base 206)
    wp_call hParse'
    wp_steps
    wp_if hb0
    · wp_steps_lscl (lsmpl.base 206)
      wp_call hParse'
      wp_steps
      wp_if hb1
      · wp_steps
        wp_done
      · wp_steps
        wp_if hb01
        · wp_steps
          wp_done
        · wp_steps
          have hrel1 : SidCellsRel (serviceIdParse parse localNameBytes) _ _ _ := ‹_›
          have hrel2 : SidCellsRel (serviceIdParse parse remoteNameBytes) _ _ _ := ‹_›
          have hne := cond_uuid_words_ne_placed (sidCellsRel_ne_of_distinct_placed hDist hrel1 hrel2
            (by revert hb0; rcases sidCellsRel_b0_cases_placed hrel1 with rfl | rfl | rfl <;> decide)
            (by revert hb1; rcases sidCellsRel_b0_cases_placed hrel2 with rfl | rfl | rfl <;> decide)
            (by revert hb01; rcases sidCellsRel_b0_cases_placed hrel1 with rfl | rfl | rfl <;>
                rcases sidCellsRel_b0_cases_placed hrel2 with rfl | rfl | rfl <;> decide))
          wp_done
    · wp_steps
      wp_done
  · simp only [hpk, Bool.false_eq_true, ↓reduceIte] at *
    wp_steps
    wp_done

theorem isSameAccountDistinctRaw_placed_ok_of_parse [LibsignalPlacement] {parse : UuidParser}
    {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook)
    (hParse : subroutine_ok ((blkPC_206).rebase (blkPl_206).base H) (blkPl_206).base
      (withLsCodeLoaded lsmpl (parseSidCodeSpec parse))) :
    subroutine_ok ((blkPC_17).rebase (blkPl_17).base H) (blkPl_17).base
      (withLsCodeLoaded lsmpl (isSameAccountDistinctRawSpec parse)) :=
  isSameAccountDistinctRaw_placed_ok_of_callees (publicKeyEqMem_placed_ok h_bb) hParse

theorem isSameAccountDistinctRaw_placed_ok [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook)
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H) (blkPl_252).base
      (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse))) :
    subroutine_ok ((blkPC_17).rebase (blkPl_17).base H) (blkPl_17).base
      (withLsCodeLoaded lsmpl (isSameAccountDistinctRawSpec uuidTryParse)) :=
  isSameAccountDistinctRaw_placed_ok_of_parse h_bb (parseSid_placed_ok_of_code H huuid)

theorem isSameAccountDistinctRaw_placed_ok_of_contract [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook)
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H) (blkPl_252).base
      (uuidTryParseSpec uuidTryParse)) :
    subroutine_ok ((blkPC_17).rebase (blkPl_17).base H) (blkPl_17).base
      (withLsCodeLoaded lsmpl (isSameAccountDistinctRawSpec uuidTryParse)) :=
  isSameAccountDistinctRaw_placed_ok_of_parse h_bb (parseSid_placed_ok_of_contract H huuid)

/-! ## `isSameAccountEqDistinct_placed_ok` (Block `17`) -/

private def vecU8BufRest_placed (A : RustAlloc) (cap ptr : BitVec 64) (n : Nat) : SepProp :=
  if cap = 0 then emp
  else A.live ptr cap.toNat 1 ∗ memRegion (ptr + BitVec.ofNat 64 n) (cap.toNat - n)

private theorem vecU8At_buf_eq_placed (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) :
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
      (ptr ↦ₛ bs) ∗ vecU8BufRest_placed A cap ptr bs.length := by
  unfold vecU8BufRest_placed
  by_cases hcap : cap = 0
  · subst hcap
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hle)
    subst hbs
    simp [pointsToBytes_nil]
  · simp only [hcap, ite_false]
    ac_rfl

private theorem vecU8At_expose_placed (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ vecU8BufRest_placed A cap ptr bs.length := by
  unfold vecU8At vecHeader
  trans (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      if cap = 0 then emp
      else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)))
  · ac_rfl
  · simp only [pure_sepConj]
    congr 1
    funext h
    apply propext
    refine and_congr_right fun ⟨hle, _, _⟩ => ?_
    rw [vecU8At_buf_eq_placed A cap ptr bs hle]

private def addrRest_placed (A : RustAlloc) (g : AddrGhost) (a : BitVec 64) : SepProp :=
  (a ↦₆₄ g.name.cap) ∗ vecU8BufRest_placed A g.name.cap g.name.ptr g.name.bytes.length ∗
    ((a + 24#64) ↦₈ g.device) ∗ memRegion (a + 0x19#64) 7

private theorem protocolAddressAt_expose_placed (A : RustAlloc) (g : AddrGhost) (a : BitVec 64) :
    protocolAddressAt A g a =
      ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
        ((a + 8#64) ↦₆₄ g.name.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
        (g.name.ptr ↦ₛ g.name.bytes) ∗
        addrRest_placed A g a := by
  unfold protocolAddressAt vecGhostAt addrRest_placed
  rw [vecU8At_expose_placed]
  ac_rfl

/-- Lift any `subroutine_ok prog entry (withLsCodeLoaded lsmpl (isSameAccountDistinctRawSpec parse))`
to `withLsCodeLoaded lsmpl (isSameAccountDistinctSpec A parse)`. -/
theorem isSameAccountEqDistinct_of_raw_placed [LibsignalPlacement] {prog : Program}
    {entry : BitVec 64} {parse : UuidParser} (A : RustAlloc)
    (hraw : subroutine_ok prog entry (withLsCodeLoaded lsmpl (isSameAccountDistinctRawSpec parse))) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl (isSameAccountDistinctSpec A parse)) := by
  refine subroutine_ok_map hraw ?_
  rintro ⟨localIkA, localIk, locA, loc, remoteIkA, remoteIk, remA, rem⟩ R s0 hpre
  simp only [isSameAccountDistinctSpec, protocolAddressAt_expose_placed] at hpre
  have hpre' : s0.mem ⊨
      ⌜s0.readReg64 .x0 = localIkA ∧ s0.readReg64 .x1 = locA ∧
        s0.readReg64 .x2 = remoteIkA ∧ s0.readReg64 .x3 = remA ∧
        (localIk ≠ remoteIk ∨ DistinctSid parse loc.name.bytes rem.name.bytes)⌝ ∗
      (⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗
        (⌜loc.name.bytes.length ≤ loc.name.cap.toNat ∧ loc.name.cap.toNat < 2 ^ 63 ∧
          loc.name.ptr ≠ 0⌝ ∗
          (⌜rem.name.bytes.length ≤ rem.name.cap.toNat ∧ rem.name.cap.toNat < 2 ^ 63 ∧
            rem.name.ptr ≠ 0⌝ ∗
            ((localIkA ↦ₛ localIk.publicKey.bytes.toList) ∗
             ((locA + 8#64) ↦₆₄ loc.name.ptr) ∗
             ((locA + 16#64) ↦₆₄ BitVec.ofNat 64 loc.name.bytes.length) ∗
             (loc.name.ptr ↦ₛ loc.name.bytes) ∗
             (remoteIkA ↦ₛ remoteIk.publicKey.bytes.toList) ∗
             ((remA + 8#64) ↦₆₄ rem.name.ptr) ∗
             ((remA + 16#64) ↦₆₄ BitVec.ofNat 64 rem.name.bytes.length) ∗
             (rem.name.ptr ↦ₛ rem.name.bytes) ∗
             stackAt s0.sp isSameAccountDistinctStack ∗
             addrRest_placed A loc locA ∗ addrRest_placed A rem remA ∗ R)))) :=
    Satisfies.of_eq hpre (by ac_rfl)
  rw [satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx1, hx2, hx3, hdist⟩, hpre'⟩
  rw [satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨hcl, hpre'⟩
  rw [satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨hloc_pure, hpre'⟩
  rw [satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨hrem_pure, hm⟩
  refine ⟨⟨localIkA, localIk, locA, loc.name.ptr, loc.name.bytes,
    remoteIkA, remoteIk, remA, rem.name.ptr, rem.name.bytes⟩,
    addrRest_placed A loc locA ∗ addrRest_placed A rem remA ∗ R, ?_, fun sf hpost => ?_⟩
  · simp only [isSameAccountDistinctRawSpec]
    have hloc_lt : loc.name.bytes.length < 2 ^ 64 := by omega
    have hrem_lt : rem.name.bytes.length < 2 ^ 64 := by omega
    have hm' : s0.mem ⊨
        ⌜s0.readReg64 .x0 = localIkA ∧ s0.readReg64 .x1 = locA ∧
          s0.readReg64 .x2 = remoteIkA ∧ s0.readReg64 .x3 = remA ∧
          loc.name.bytes.length < 2 ^ 64 ∧ rem.name.bytes.length < 2 ^ 64 ∧
          (localIk ≠ remoteIk ∨ DistinctSid parse loc.name.bytes rem.name.bytes)⌝ ∗
        (⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗
          ((localIkA ↦ₛ localIk.publicKey.bytes.toList) ∗
           ((locA + 8#64) ↦₆₄ loc.name.ptr) ∗
           ((locA + 16#64) ↦₆₄ BitVec.ofNat 64 loc.name.bytes.length) ∗
           (loc.name.ptr ↦ₛ loc.name.bytes) ∗
           (remoteIkA ↦ₛ remoteIk.publicKey.bytes.toList) ∗
           ((remA + 8#64) ↦₆₄ rem.name.ptr) ∗
           ((remA + 16#64) ↦₆₄ BitVec.ofNat 64 rem.name.bytes.length) ∗
           (rem.name.ptr ↦ₛ rem.name.bytes) ∗
           stackAt s0.sp isSameAccountDistinctStack ∗
           addrRest_placed A loc locA ∗ addrRest_placed A rem remA ∗ R)) := by
      rw [satisfies_pure_sepConj]
      refine ⟨⟨hx0, hx1, hx2, hx3, hloc_lt, hrem_lt, hdist⟩, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨hcl, hm⟩
    exact Satisfies.of_eq hm' (by ac_rfl)
  · simp only [isSameAccountDistinctRawSpec, isSameAccountDistinctSpec,
      protocolAddressAt_expose_placed] at hpost ⊢
    have hpost' : sf.mem ⊨
        ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ sf.trace = s0.trace⌝ ∗
        ((localIkA ↦ₛ localIk.publicKey.bytes.toList) ∗
         ((locA + 8#64) ↦₆₄ loc.name.ptr) ∗
         ((locA + 16#64) ↦₆₄ BitVec.ofNat 64 loc.name.bytes.length) ∗
         (loc.name.ptr ↦ₛ loc.name.bytes) ∗
         (remoteIkA ↦ₛ remoteIk.publicKey.bytes.toList) ∗
         ((remA + 8#64) ↦₆₄ rem.name.ptr) ∗
         ((remA + 16#64) ↦₆₄ BitVec.ofNat 64 rem.name.bytes.length) ∗
         (rem.name.ptr ↦ₛ rem.name.bytes) ∗
         stackAt s0.sp isSameAccountDistinctStack ∗
         addrRest_placed A loc locA ∗ addrRest_placed A rem remA ∗ R) :=
      Satisfies.of_eq hpost (by ac_rfl)
    rw [satisfies_pure_sepConj] at hpost'
    rcases hpost' with ⟨hret, hpost'⟩
    have hpost'' : sf.mem ⊨
        ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ sf.trace = s0.trace⌝ ∗
        (⌜loc.name.bytes.length ≤ loc.name.cap.toNat ∧ loc.name.cap.toNat < 2 ^ 63 ∧
          loc.name.ptr ≠ 0⌝ ∗
          (⌜rem.name.bytes.length ≤ rem.name.cap.toNat ∧ rem.name.cap.toNat < 2 ^ 63 ∧
            rem.name.ptr ≠ 0⌝ ∗
            ((localIkA ↦ₛ localIk.publicKey.bytes.toList) ∗
             ((locA + 8#64) ↦₆₄ loc.name.ptr) ∗
             ((locA + 16#64) ↦₆₄ BitVec.ofNat 64 loc.name.bytes.length) ∗
             (loc.name.ptr ↦ₛ loc.name.bytes) ∗
             (remoteIkA ↦ₛ remoteIk.publicKey.bytes.toList) ∗
             ((remA + 8#64) ↦₆₄ rem.name.ptr) ∗
             ((remA + 16#64) ↦₆₄ BitVec.ofNat 64 rem.name.bytes.length) ∗
             (rem.name.ptr ↦ₛ rem.name.bytes) ∗
             stackAt s0.sp isSameAccountDistinctStack ∗
             addrRest_placed A loc locA ∗ addrRest_placed A rem remA ∗ R))) := by
      rw [satisfies_pure_sepConj]
      refine ⟨hret, ?_⟩
      rw [satisfies_pure_sepConj]
      refine ⟨hloc_pure, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨hrem_pure, hpost'⟩
    exact Satisfies.of_eq hpost'' (by ac_rfl)

theorem isSameAccountEqDistinct_placed_ok_of_callees [LibsignalPlacement] {parse : UuidParser}
    (A : RustAlloc) {H : String → Option (State → State)}
    (hEq : subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
      (withLsCodeLoaded lsmpl publicKeyEqMemSpec))
    (hParse : subroutine_ok ((blkPC_206).rebase (blkPl_206).base H) (blkPl_206).base
      (withLsCodeLoaded lsmpl (parseSidCodeSpec parse))) :
    subroutine_ok ((blkPC_17).rebase (blkPl_17).base H) (blkPl_17).base
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpec A parse)) :=
  isSameAccountEqDistinct_of_raw_placed A (isSameAccountDistinctRaw_placed_ok_of_callees hEq hParse)

theorem isSameAccountEqDistinct_placed_ok_of_parse [LibsignalPlacement] {parse : UuidParser}
    (A : RustAlloc) {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook)
    (hParse : subroutine_ok ((blkPC_206).rebase (blkPl_206).base H) (blkPl_206).base
      (withLsCodeLoaded lsmpl (parseSidCodeSpec parse))) :
    subroutine_ok ((blkPC_17).rebase (blkPl_17).base H) (blkPl_17).base
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpec A parse)) :=
  isSameAccountEqDistinct_of_raw_placed A (isSameAccountDistinctRaw_placed_ok_of_parse h_bb hParse)

theorem isSameAccountEqDistinct_placed_ok [LibsignalPlacement]
    (A : RustAlloc) {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook)
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H) (blkPl_252).base
      (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse))) :
    subroutine_ok ((blkPC_17).rebase (blkPl_17).base H) (blkPl_17).base
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpec A uuidTryParse)) :=
  isSameAccountEqDistinct_of_raw_placed A (isSameAccountDistinctRaw_placed_ok h_bb huuid)

theorem isSameAccountEqDistinct_placed_ok_of_contract [LibsignalPlacement]
    (A : RustAlloc) {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook)
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H) (blkPl_252).base
      (uuidTryParseSpec uuidTryParse)) :
    subroutine_ok ((blkPC_17).rebase (blkPl_17).base H) (blkPl_17).base
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpec A uuidTryParse)) :=
  isSameAccountEqDistinct_of_raw_placed A (isSameAccountDistinctRaw_placed_ok_of_contract h_bb huuid)

/-! ## Cross-Block Caller Transfers (`lsmpl.base 17`) -/

theorem isSameAccountDistinctRaw_placed_ok_at [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_bb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook)
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H) (blkPl_252).base
      (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse)))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctRawSpec uuidTryParse)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg)
    (isSameAccountDistinctRaw_placed_ok h_bb huuid) hi

theorem isSameAccountDistinctRaw_placed_cl_ok_at [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_bb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook)
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H) (blkPl_252).base
      (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse)))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 17)
      (withLsCl lsmpl (isSameAccountDistinctRawSpec uuidTryParse)) :=
  ls_subroutine_ok_cl_of_block (callerProg := callerProg)
    (isSameAccountDistinctRaw_placed_ok h_bb huuid) hi

theorem isSameAccountEqDistinct_placed_ok_at [LibsignalPlacement]
    (A : RustAlloc) {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_bb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook)
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H) (blkPl_252).base
      (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse)))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpec A uuidTryParse)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg)
    (isSameAccountEqDistinct_placed_ok A h_bb huuid) hi

theorem isSameAccountEqDistinct_placed_cl_ok_at [LibsignalPlacement]
    (A : RustAlloc) {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_bb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook)
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H) (blkPl_252).base
      (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse)))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 17)
      (withLsCl lsmpl (isSameAccountDistinctSpec A uuidTryParse)) :=
  ls_subroutine_ok_cl_of_block (callerProg := callerProg)
    (isSameAccountEqDistinct_placed_ok A h_bb huuid) hi

end CryptoVerification.E2E.Pqxdh.WireEntries
