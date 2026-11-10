/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize
public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.DefsBudget
public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.MergeFieldsBudget
public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.MergeLoopBudget
public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.PostBudget
public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.VarintKeyBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `PreKeyRecord::deserialize` Proof

Proves `preKeyRecord_deserialize_placed_ok` (`preKeyDeserializePlacedSpec`, Block `65`) under
`[LibsignalPlacement]` and `PortDepsPlaced M A lim H` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`
under `FitsEnv`).
-/

@[expose] public section

set_option autoImplicit false

open CryptoGames.LibsignalSession (SignalProtocolError)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalProtoCodec (WireType decodeKey decodeVarint mergeBytes mergeUint32 recursionLimit skipField)
open CryptoVerification.LibsignalTripleRatchet (KindNoHeap LibsignalCodeRoLoaded decodeErrorAt decodeErrorAtStackLen extract_withLsCodeRoLoaded smallRootStack)
open CryptoVerification.LibsignalTripleRatchet.Prost (BytesMergeCapOk BytesMergeGhost Int32MergeGhost SkipFieldGhost bytesMergeCapOk_mono bytesMergeStackX int32MergeStackX skipFieldStackX sliceCursorAt)
open CryptoVerification.LibsignalTripleRatchet.Wire (SepWPp cons_len_bv64_ne_zero decodeKey_suffix entails_of_eq key_and7_eq_wt key_and7_ule6_of_ge key_and7_ule6_of_lt key_lsr32_eq_zero_of_lt key_lsr32_ne_zero_of_ge key_tag32_eq_zero_of_lt1 key_tag32_ne_zero_of_ge1 key_tag32_zeroExtend64_eq mergeBytes_suffix mergeUint32_suffix pointsTo64_pair_entails_memRegion16 setWidth32_ofNat64 setWidth8_ofNat64 skipField_suffix sliceCursorAfter_entails_memRegion stackAt_sub_split)
open CryptoVerification.LibsignalTripleRatchetRepr (speWord)
open CryptoVerification.RecordCodecs (PreKeyRecord PreKeyRecordStructure decodeFieldsLoop skipUnknown)
open CryptoVerification.RecordCodecs.Placed (blkPl_65 lsProg_65)
open CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers (PkEpilogueStatePlaced PkLoopRegs pkAfterVarintMem pkCalleeSavedAt pkDecodeKey_err_entails pkDeserialize_eq_of_decodeLoop pkEmptyHeaders_entails_loopOf pkErrMem_of_loopOf pkLoopMem pkLoopOut pkMemRegion48_split8 pkMemRegion48_split_112_120_128 pkMemRegion64_unpack pkMergeField_suffix pkStack_smallRoot_split pkStruct56_unpack_init pkSubStack pkSubStack_split pk_tag_ge4_conds preKeyStructAt_entails_loopOf preKeyStructAt_entails_of preKeyStructAt_split_id preKeyStructAt_split_priv preKeyStructAt_split_pub preKeyStructLoopOf preKeyStructLoopOf_entails_of preKeyStructLoopOf_mono preKeyStructOf)
open CryptoVerification.RustHeap (vecHeader vecU8At)

namespace LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserializeBudget

open Arm64 ProofLib.ProgramReflection
open ProofLib hiding SepWPp
open CryptoVerification.LibsignalTripleRatchet.Wire renaming SepWP.done -> sepWPDoneWire
open scoped CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecsBinary (DecodeGhost preKeyResultAt sepWPp_of_sepWP_lscro)
open scoped CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (Int32MergeEnv SkipFieldEnv)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (BytesMergeEnv)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget
  (PortDepsPlaced RecordCodecIterEnv RecordCodecLoopEnv mergeBytes_len_bound
   fitsEnv_recordCodecLoop_head fitsEnv_recordCodecLoop_bytesHead
   fitsEnv_recordCodecLoop_tail fitsEnv_recordCodecLoop_bytesTail fitsEnv_recordCodecLoop_mono_fuel
   preKeyDeserializeRawSpec preKeyDeserializePlacedSpec
   noPanicQp sepWPp_frame_noPanic sepWPp_mono_post sepWPp_call_noPanic_lscro)
open LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.DefsBudget
  (pk_int32Merge_placed_ok pk_skipField_placed_ok pk_bytesMerge_placed_ok
   pkEpilogueMem pkEpiloguePostPlaced pkEpiloguePostPlaced_prepend_iter
   pkEpiloguePostPlaced_prepend_bytes pkEpiloguePostPlaced_mono_fuel)
open LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.VarintKeyBudget (pkAdvanceCursor_placed)
open LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.PostBudget
  (fast_empty_174_placed_wp epilogue_224_placed_wp)
open LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.MergeFieldsBudget (post_err_1d0_placed_wp)
open LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.MergeLoopBudget
  (post_ok_23c_placed_wp decodeErrorFrom_1c8_placed_wp decodeErrorFrom_1c4_placed_wp
   decodeErrorPush_2cc_placed_wp decodeVarint_080_placed_cps)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

section PkSetMemSimp
@[local arm64_norm ↓, local wp_norm ↓] private theorem sp_setMem_pk (s : State) (m : Memory) : (s.setMem m).sp = s.sp := rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem pc_setMem_pk (s : State) (m : Memory) : (s.setMem m).pc = s.pc := rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem status_setMem_pk (s : State) (m : Memory) : (s.setMem m).status = s.status := rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem trace_setMem_pk (s : State) (m : Memory) : (s.setMem m).trace = s.trace := rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem readReg64_setMem_pk (s : State) (m : Memory) (r : Reg) : (s.setMem m).readReg64 r = s.readReg64 r := rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem readReg32_setMem_pk (s : State) (m : Memory) (r : Reg) : (s.setMem m).readReg32 r = s.readReg32 r := rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem readReg_setMem_pk (s : State) (m : Memory) (w : Width) (r : Reg) : (s.setMem m).readReg w r = s.readReg w r := rfl
end PkSetMemSimp

local macro "mk_pk_regs " h:term:max : term => `(
  ⟨by simpa [arm64_norm] using ($h).sp, by simpa [arm64_norm] using ($h).x29,
   by simpa [speWord, arm64_norm] using ($h).x22, by simpa [arm64_norm] using ($h).x20,
   by simpa [arm64_norm] using ($h).x19_eq,
   ⟨by simpa [arm64_norm] using ($h).saved.x24, by simpa [arm64_norm] using ($h).saved.x25,
    by simpa [arm64_norm] using ($h).saved.x26, by simpa [arm64_norm] using ($h).saved.x27,
    by simpa [arm64_norm] using ($h).saved.x28⟩⟩)

/-! ## 1. Key Decode & Field Merge CPS Lemmas (Block `65`) -/

theorem decodeKey_tail_0e0_placed_cps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H) {s0 s : State} {sp' x19 ptr key : BitVec 64}
    {bs rest : List (BitVec 8)} {m : PreKeyRecordStructure} {out : Except SignalProtocolError PreKeyRecord}
    (hdv : decodeVarint bs = some (key, rest)) (hpc : s.pc = (blkPl_65).base + bv% (224)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s) (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = key)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (fuel + 1) maxLen))
    (hcont : ∀ (tag : ℕ) (wt : WireType) (s1 : State), decodeKey bs = some ((tag, wt), rest) →
      s1.pc = (blkPl_65).base + bv% (252) → s1.status = .Running → PkLoopRegs s0 sp' x19 s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      s1.readReg64 .x8 = BitVec.ofNat 64 wt.toNat → s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1
        (pkAfterVarintMem (A.atState lim st s1) sp' x19 ptr bs rest bs.length m)
        (pkEpiloguePostPlaced A lim st (fuel + 1) maxLen s0 sp' x19 ptr bs out) (noPanicQp s0))
    (hnone : decodeKey bs = none → out = .error .invalidProtobufEncoding) :
    SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (pkAfterVarintMem (A.atState lim st s) sp' x19 ptr bs rest bs.length m)
      (pkEpiloguePostPlaced A lim st (fuel + 1) maxLen s0 sp' x19 ptr bs out) (noPanicQp s0) := by
  have h0 : s.readReg64 (Reg.gpr 0#5) = key := hx0
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h22 : s.readReg64 (Reg.gpr 22#5) = 0x8000000000000002#64 := hregs.x22
  have hloop_eq : ∀ s', preKeyStructLoopOf (A.atState lim st s') = preKeyStructLoopOf A.repAlloc := fun _ => rfl
  by_cases hkey32 : 2 ^ 32 ≤ key.toNat
  · have hdk : decodeKey bs = none := by unfold decodeKey; rw [hdv]; simp only [hkey32, ↓reduceIte]
    have hcbnz := key_lsr32_ne_zero_of_ge key hkey32
    unfold pkAfterVarintMem; rw [hloop_eq, pkMemRegion48_split_112_120_128 sp']; dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w1 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w0 => ?_
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (452)) ?_
    wp_steps_sync_pool ((blkPl_65).base + bv% (452))
    refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre ?_
      (decodeErrorFrom_1c4_placed_wp d (st := st) (fuel := fuel) (maxLen := maxLen)
        (w0 := w0) (mErr := m) (hnone hdk) (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (mk_pk_regs hregs)
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 (by simpa [arm64_norm] using htr)
        (by simp [KindNoHeap, arm64_norm]) hFit)
    refine Entails.trans ?_ (pkDecodeKey_err_entails (A.atState lim st _) sp' x19 ptr w0 key bs rest bs.length m)
    rw [hloop_eq]; dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]; apply entails_of_eq; try simp only [arm64_norm]; sep_ac_rfl
  · have hkey_lt : key.toNat < 2 ^ 32 := by omega
    have hcbnz := key_lsr32_eq_zero_of_lt key hkey_lt
    cases hwt : CryptoVerification.LibsignalProtoCodec.WireType.ofNat? (key.toNat % 8) with
    | none =>
      have hdk : decodeKey bs = none := by unfold decodeKey; rw [hdv]; simp only [hkey32, ↓reduceIte, hwt]
      have hge6 : 6 ≤ key.toNat % 8 := (CryptoVerification.LibsignalTripleRatchet.Wire.WireType.ofNat?_eq_none_iff (key.toNat % 8) (by omega)).mp hwt
      have hbcs := key_and7_ule6_of_ge key hge6
      unfold pkAfterVarintMem; rw [hloop_eq, pkMemRegion48_split_112_120_128 sp']; dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w1 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w0 => ?_
      refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (456)) ?_
      wp_steps_sync_pool ((blkPl_65).base + bv% (456))
      refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
      refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre ?_
        (decodeErrorFrom_1c8_placed_wp d (st := st) (fuel := fuel) (maxLen := maxLen)
          (kind := 0x8000000000000003#64) (mErr := m) (hnone hdk) (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          (mk_pk_regs hregs) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hcrl1 (by simpa [arm64_norm] using htr) (by simp [KindNoHeap]) hFit)
      refine Entails.trans ?_
        (pkDecodeKey_err_entails (A.atState lim st _) sp' x19 ptr 0x8000000000000003#64 (key &&& 7#64) bs rest bs.length m)
      rw [hloop_eq]; dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]; apply entails_of_eq; try simp only [arm64_norm]; sep_ac_rfl
    | some wt =>
      have hlt6 : key.toNat % 8 < 6 := CryptoVerification.LibsignalTripleRatchet.Wire.WireType.lt_six_of_ofNat?_eq_some hwt
      have hbcs := key_and7_ule6_of_lt key hlt6
      by_cases htag0 : key.toNat / 8 < 1
      · have hdk : decodeKey bs = none := by unfold decodeKey; rw [hdv]; simp only [hkey32, ↓reduceIte, hwt, htag0]
        have hcbz := key_tag32_eq_zero_of_lt1 key hkey_lt htag0
        unfold pkAfterVarintMem; rw [hloop_eq, pkMemRegion48_split8 sp', ProofLib.memRegion_eight (sp' + 112#64)]
        dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w0 => ?_
        refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (452)) ?_; wp_steps
        refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
        refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre ?_
          (decodeErrorFrom_1c4_placed_wp d (st := st) (fuel := fuel) (maxLen := maxLen)
            (w0 := w0) (mErr := m) (hnone hdk) (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (mk_pk_regs hregs)
            (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 (by simpa [arm64_norm] using htr)
            (by simp [KindNoHeap, arm64_norm]) hFit)
        refine Entails.trans (sepConj_mono (sliceCursorAfter_entails_memRegion (sp' + 40#64) ptr bs rest)
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left (preKeyStructLoopOf_entails_of A.repAlloc (sp' + 56#64) bs.length m)))))) ?_
        apply entails_of_eq; simp only [arm64_norm, sepConj_assoc]
      · have hdk : decodeKey bs = some ((key.toNat / 8, wt), rest) := by
          unfold decodeKey; rw [hdv]; simp only [hkey32, ↓reduceIte, hwt, htag0]
        have hcbz := key_tag32_ne_zero_of_ge1 key hkey_lt htag0
        unfold pkAfterVarintMem; rw [hloop_eq]; dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]
        refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (252)) ?_; wp_steps
        refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
        refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre ?_
          (hcont (key.toNat / 8) wt _ hdk (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (mk_pk_regs hregs)
            (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 (by simpa [arm64_norm] using htr)
            (by simp [arm64_norm]; exact key_and7_eq_wt key hwt)
            (by simpa [arm64_norm] using key_tag32_zeroExtend64_eq key hkey_lt))
        apply entails_of_eq; unfold pkAfterVarintMem; rw [hloop_eq]; dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]; simp only [arm64_norm]

theorem decodeKey_080_placed_cps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H) {s0 s : State} {sp' x19 ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : PreKeyRecordStructure} {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (blkPl_65).base + bv% (128)) (hrun : s.status = .Running) (hregs : PkLoopRegs s0 sp' x19 s)
    (hx23 : s.readReg64 .x23 = sp' + 40#64) (hx21 : s.readReg64 .x21 = sp' + 48#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlen : (b0 :: bs1).length < 2 ^ 63) (hFit : FitsEnv M lim st (RecordCodecLoopEnv (fuel + 1) maxLen))
    (hcont : ∀ (tag : ℕ) (wt : WireType) (rest : List (BitVec 8)) (s1 : State),
      decodeKey (b0 :: bs1) = some ((tag, wt), rest) → s1.pc = (blkPl_65).base + bv% (252) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      s1.readReg64 .x8 = BitVec.ofNat 64 wt.toNat → s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1
        (pkAfterVarintMem (A.atState lim st s1) sp' x19 ptr (b0 :: bs1) rest (b0 :: bs1).length m)
        (pkEpiloguePostPlaced A lim st (fuel + 1) maxLen s0 sp' x19 ptr (b0 :: bs1) out) (noPanicQp s0))
    (hnone : decodeKey (b0 :: bs1) = none → out = .error .invalidProtobufEncoding) :
    SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (pkLoopMem (A.atState lim st s) sp' x19 ptr (b0 :: bs1) m)
      (pkEpiloguePostPlaced A lim st (fuel + 1) maxLen s0 sp' x19 ptr (b0 :: bs1) out) (noPanicQp s0) :=
  decodeVarint_080_placed_cps d hpc hrun hregs hx23 hx21 hx2 hsp hcrl htr hlen hFit
    (fun key rest s1 hdv hpc1 hrun1 hregs1 hsp1 hcrl1 htr1 hx0_1 =>
      decodeKey_tail_0e0_placed_cps d hdv hpc1 hrun1 hregs1 hsp1 hcrl1 htr1 hx0_1 hFit
        (fun tag wt s2 hdk => hcont tag wt rest s2 hdk) hnone)
    (fun hdv_none => hnone (by simp [decodeKey, hdv_none]))

theorem mergeId_114_placed_cps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H)
    {s0 s : State} {sp' x19 ptr : BitVec 64} {wt : WireType} {bs : List (BitVec 8)}
    {m : PreKeyRecordStructure} {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (blkPl_65).base + bv% (276)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (fuel + 2) maxLen))
    (hcont : ∀ (v : BitVec 32) (rest : List (BitVec 8)) (st1 : M.σ) (s1 : State),
      mergeUint32 wt bs = some (v, rest) → FitsEnv M lim st1 (RecordCodecLoopEnv fuel maxLen) →
      s1.pc = (blkPl_65).base + bv% (112) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1
        (pkAfterVarintMem (A.atState lim st1 s1) sp' x19 ptr bs rest rest.length { m with id := v })
        (pkEpiloguePostPlaced A lim st1 fuel maxLen s0 sp' x19 ptr bs out) (noPanicQp s0))
    (hnone : mergeUint32 wt bs = none → out = .error .invalidProtobufEncoding) :
    SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (pkLoopMem (A.atState lim st s) sp' x19 ptr bs m)
      (pkEpiloguePostPlaced A lim st (fuel + 2) maxLen s0 sp' x19 ptr bs out) (noPanicQp s0) := by
  have hloop_eq : ∀ (st' : M.σ) (s' : State),
      preKeyStructLoopOf (A.atState lim st' s') = preKeyStructLoopOf A.repAlloc := fun _ _ => rfl
  unfold pkLoopMem; rw [hloop_eq]; unfold preKeyStructLoopOf; dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_pure_left_comm, sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun g => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hg => ?_
  rw [preKeyStructAt_split_id A.repAlloc g sp' m]; simp only [sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (pointsTo32_entails_memRegion (sp' + 104#64) m.id))))) ?_
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h20 : s.readReg64 (Reg.gpr 20#5) = sp' + 56#64 := hregs.x20
  have h8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 wt.toNat := hx8
  have hstack := stackAt_sub_split sp' int32MergeStackX (skipFieldStackX 100)
  simp only [hstack]
  refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 8) ?_; wp_steps
  refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
  let xInt : Int32MergeGhost := ⟨wt, sp' + 104#64, sp' + 184#64, sp' + 40#64, ptr, bs⟩
  have hFit_call : FitsEnv M lim st (Int32MergeEnv xInt) :=
    fitsEnv_recordCodecLoop_head (fun _ => LibsignalBinary.Proofs.RecordCodecs.DepsBudget.RecordCodecIterEnv.of_int32Merge)
      (fitsEnv_recordCodecLoop_mono_fuel (by omega : fuel + 1 ≤ fuel + 2) hFit)
  refine sepWPp_call_noPanic_lscro (xInt, st) (pk_int32Merge_placed_ok d)
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (by simp [arm64_norm] : _ = (blkPl_65).base + bv% (292)) (by simpa [arm64_norm] using htr)
    (T := memRegion (sp' + 104#64) 4 ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
      sliceCursorAt (sp' + 40#64) ptr bs ∗ A.pool lim st s ∗ stackAt sp' int32MergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 56#64 + 48#64 = sp' + 104#64 ∧ sp' + 160#64 + 24#64 = sp' + 184#64 ∧
      bs.length < 9223372036854775808 ∧ FitsEnv M lim st (Int32MergeEnv xInt))
    (by cases wt <;> simp [LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget.int32MergeSpecX, LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget.int32MergeSpecGen, xInt, hsp_eq, CryptoVerification.LibsignalProtoCodec.WireType.toNat, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, by bv_omega, by bv_omega, hlen, hFit_call⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  have hregs2 : PkLoopRegs s0 sp' x19 s2 := CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.PkLoopRegs.of_calleeSaved (mk_pk_regs hregs) hsp2 hcs2
  dsimp only [LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget.int32MergeSpecX, LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget.int32MergeSpecGen, xInt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun evs₁ => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun htr2 => ?_
  simp only [sepConj_pure_left_comm]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hevs₁ => ?_
  have hiter₁ : RecordCodecIterEnv maxLen evs₁ := LibsignalBinary.Proofs.RecordCodecs.DepsBudget.RecordCodecIterEnv.of_int32Merge hevs₁
  have hFit1 : FitsEnv M lim (M.stepEvents evs₁ st) (RecordCodecLoopEnv (fuel + 1) maxLen) :=
    fitsEnv_recordCodecLoop_tail hiter₁ hFit
  cases hm : mergeUint32 wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩; dsimp only
    obtain ⟨k, hkl, hrest⟩ := mergeUint32_suffix hm
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    simp only [sepConj_pure_left_comm, sepConj_assoc]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hx0_0 => ?_
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (112)) ?_; wp_steps
    refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
    refine sepWPp_mono_post
      (CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre ?_
        (hcont v rest (M.stepEvents evs₁ st) _ hm
          (fitsEnv_recordCodecLoop_mono_fuel (by omega : fuel ≤ fuel + 1) hFit1)
          (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) (mk_pk_regs hregs2)
          (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
          hcrl3 (by simpa [arm64_norm] using htr2.trans htr)))
      (fun sf Pf h => pkEpiloguePostPlaced_prepend_iter hiter₁ (pkEpiloguePostPlaced_mono_fuel (by omega) h))
    have hstruct : (((sp' + 104#64) ↦₃₂ v) ∗ memRegion (sp' + 108#64) 4) ∗
        (vecU8At A.repAlloc (sp' + 56#64) g.pub.cap g.pub.ptr m.publicKey ∗
          vecU8At A.repAlloc (sp' + 80#64) g.priv.cap g.priv.ptr m.privateKey) ⊢
        preKeyStructLoopOf A.repAlloc (sp' + 56#64) rest.length { m with id := v } := by
      refine Entails.trans ?_
        (preKeyStructAt_entails_loopOf A.repAlloc g (sp' + 56#64) rest.length { m with id := v } (hg.mono hrest_le))
      rw [preKeyStructAt_split_id A.repAlloc g sp' { m with id := v }]; exact Entails.refl _
    unfold pkAfterVarintMem; rw [hloop_eq]; dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]
    simp only [hstack, hsp_eq, arm64_norm]; simp only [sepConj_assoc] at hstruct
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstruct))))
    apply entails_of_eq; sep_ac_rfl
  | none =>
    dsimp only; have hout := hnone hm
    simp only [sepConj_pure_left_comm, sepConj_assoc]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hx0_ne => ?_
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs2.x29
    rw [pkMemRegion48_split8 sp', ProofLib.memRegion_eight (sp' + 112#64), ProofLib.memRegion_four (sp' + 104#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w0 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun vErr => ?_
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (716)) ?_
    wp_steps_sync_pool ((blkPl_65).base + bv% (716))
    refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
    refine sepWPp_mono_post
      (CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre ?_
        (decodeErrorPush_2cc_placed_wp d (st := M.stepEvents evs₁ st) (fuel := fuel) (maxLen := maxLen)
          (err := s2.readReg64 (Reg.gpr 0#5)) (mErr := { m with id := vErr }) hout
          (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) (mk_pk_regs hregs2)
          (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
          hcrl3 (by simpa [arm64_norm] using htr2.trans htr) (by simp [arm64_norm]) hx0_ne hFit1))
      (fun sf Pf h => pkEpiloguePostPlaced_prepend_iter hiter₁ h)
    have hstruct : (((sp' + 104#64) ↦₃₂ vErr) ∗ memRegion (sp' + 108#64) 4) ∗
        (vecU8At A.repAlloc (sp' + 56#64) g.pub.cap g.pub.ptr m.publicKey ∗
          vecU8At A.repAlloc (sp' + 80#64) g.priv.cap g.priv.ptr m.privateKey) ⊢
        preKeyStructOf A.repAlloc (sp' + 56#64) { m with id := vErr } := by
      refine Entails.trans ?_ (preKeyStructAt_entails_of A.repAlloc g (sp' + 56#64) { m with id := vErr })
      rw [preKeyStructAt_split_id A.repAlloc g sp' { m with id := vErr }]; exact Entails.refl _
    simp only [hstack, hsp_eq, arm64_norm]; simp only [sepConj_assoc] at hstruct
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstruct)))))))
    apply entails_of_eq; sep_ac_rfl

theorem mergePublicKey_05c_placed_cps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H)
    {s0 s : State} {sp' x19 ptr : BitVec 64} {wt : WireType} {bs : List (BitVec 8)}
    {m : PreKeyRecordStructure} {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (blkPl_65).base + bv% (92)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63) (hlen_max : bs.length ≤ maxLen)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (2 * bs.length + 4) maxLen))
    (hcont : ∀ (v rest : List (BitVec 8)) (st1 : M.σ) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      FitsEnv M lim st1 (RecordCodecLoopEnv (2 * rest.length + 2) maxLen) →
      s1.pc = (blkPl_65).base + bv% (112) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1
        (pkAfterVarintMem (A.atState lim st1 s1) sp' x19 ptr bs rest rest.length { m with publicKey := v })
        (pkEpiloguePostPlaced A lim st1 (2 * rest.length + 2) maxLen s0 sp' x19 ptr bs out) (noPanicQp s0))
    (hnone : mergeBytes wt bs = none → out = .error .invalidProtobufEncoding) :
    SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (pkLoopMem (A.atState lim st s) sp' x19 ptr bs m)
      (pkEpiloguePostPlaced A lim st (2 * bs.length + 4) maxLen s0 sp' x19 ptr bs out) (noPanicQp s0) := by
  have hloop_eq : ∀ (st' : M.σ) (s' : State),
      preKeyStructLoopOf (A.atState lim st' s') = preKeyStructLoopOf A.repAlloc := fun _ _ => rfl
  unfold pkLoopMem; rw [hloop_eq]; unfold preKeyStructLoopOf; dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_pure_left_comm, sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun g => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hg => ?_
  rw [preKeyStructAt_split_pub A.repAlloc g sp' m]
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 wt.toNat := hx8
  have hstack := stackAt_sub_split sp' bytesMergeStackX (skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 7) ?_; wp_steps
  refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
  let xBm : BytesMergeGhost :=
    ⟨wt, sp' + 56#64, g.pub.cap, g.pub.ptr, m.publicKey, sp' + 184#64, sp' + 40#64, ptr, bs⟩
  have hFit_call : FitsEnv M lim st (BytesMergeEnv xBm) :=
    fitsEnv_recordCodecLoop_bytesHead hlen_max (by omega : 2 * bs.length + 1 ≤ 2 * bs.length + 4) hFit
  refine sepWPp_call_noPanic_lscro (xBm, st) (pk_bytesMerge_placed_ok d)
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (by simp [arm64_norm] : _ = (blkPl_65).base + bv% (108)) (by simpa [arm64_norm] using htr)
    (T := vecU8At A.repAlloc (sp' + 56#64) g.pub.cap g.pub.ptr m.publicKey ∗
      ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
      sliceCursorAt (sp' + 40#64) ptr bs ∗ A.pool lim st s ∗ stackAt sp' bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 56#64 = sp' + 56#64 ∧ sp' + 160#64 + 24#64 = sp' + 184#64 ∧
      bs.length < 9223372036854775808 ∧ BytesMergeCapOk g.pub.cap bs.length ∧
      FitsEnv M lim st (BytesMergeEnv xBm))
    (by cases wt <;> simp [LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeRawSpecX, LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeRawSpecGen,
      LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bmPreBoundBudget, xBm, hsp_eq, CryptoVerification.LibsignalProtoCodec.WireType.toNat, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, rfl, by bv_omega, hlen, hg.pub, hFit_call⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  have hregs2 : PkLoopRegs s0 sp' x19 s2 := CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.PkLoopRegs.of_calleeSaved (mk_pk_regs hregs) hsp2 hcs2
  dsimp only [LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeRawSpecX, LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeRawSpecGen, xBm]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun evs₁ => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun htr2 => ?_
  rw [sepConj_pure_left_comm]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hevs₁ => ?_
  cases hm : mergeBytes wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩; dsimp only [LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bmPostVec]
    have hlen_bound := mergeBytes_len_bound hm
    have hbud_some : (2 * rest.length + 2) + 2 * v.length + 1 ≤ 2 * bs.length + 4 := by omega
    have hFit_rest : FitsEnv M lim (M.stepEvents evs₁ st) (RecordCodecLoopEnv (2 * rest.length + 2) maxLen) :=
      fitsEnv_recordCodecLoop_bytesTail hm hlen_max hevs₁
        (fitsEnv_recordCodecLoop_mono_fuel hbud_some hFit)
    obtain ⟨k, hkl, hrest, _⟩ := mergeBytes_suffix hm
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun cap' => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun ptr' => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hx0_0 => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hcap' => ?_
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (112)) ?_; wp_steps
    refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
    refine sepWPp_mono_post
      (CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre ?_
        (hcont v rest (M.stepEvents evs₁ st) _ hm hFit_rest
          (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) (mk_pk_regs hregs2)
          (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
          hcrl3 (by simpa [arm64_norm] using htr2.trans htr)))
      (fun sf Pf h => pkEpiloguePostPlaced_mono_fuel hbud_some (pkEpiloguePostPlaced_prepend_bytes hm hlen_max hevs₁ h))
    have hstruct : vecU8At A.repAlloc (sp' + 56#64) cap' ptr' v ∗
        (vecU8At A.repAlloc (sp' + 80#64) g.priv.cap g.priv.ptr m.privateKey ∗
          ((sp' + 104#64) ↦₃₂ m.id) ∗ memRegion (sp' + 108#64) 4) ⊢
        preKeyStructLoopOf A.repAlloc (sp' + 56#64) rest.length { m with publicKey := v } := by
      refine Entails.trans ?_
        (preKeyStructAt_entails_loopOf A.repAlloc { g with pub := ⟨cap', ptr'⟩ } (sp' + 56#64)
          rest.length { m with publicKey := v } ⟨hcap', bytesMergeCapOk_mono hg.priv hrest_le⟩)
      rw [preKeyStructAt_split_pub A.repAlloc { g with pub := ⟨cap', ptr'⟩ } sp' { m with publicKey := v }]
      exact Entails.refl _
    unfold pkAfterVarintMem; rw [hloop_eq]; dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]
    simp only [hstack, hsp_eq, arm64_norm]
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstruct))))
    apply entails_of_eq; sep_ac_rfl
  | none =>
    dsimp only; have hout := hnone hm
    simp only [sepConj_pure_left_comm, sepConj_assoc]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hx0_ne => ?_
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs2.x29
    rw [pkMemRegion48_split8 sp', ProofLib.memRegion_eight (sp' + 112#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w0 => ?_
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (716)) ?_
    wp_steps_sync_pool ((blkPl_65).base + bv% (716))
    refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
    have hiter₁ : RecordCodecIterEnv maxLen evs₁ :=
      LibsignalBinary.Proofs.RecordCodecs.DepsBudget.RecordCodecIterEnv.of_bytesMergeErr (x := xBm) hm hevs₁
    have hFit1 : FitsEnv M lim (M.stepEvents evs₁ st) (RecordCodecLoopEnv (2 * bs.length + 2 + 1) maxLen) :=
      fitsEnv_recordCodecLoop_tail hiter₁ (fitsEnv_recordCodecLoop_mono_fuel (by omega) hFit)
    refine sepWPp_mono_post
      (CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre ?_
        (decodeErrorPush_2cc_placed_wp d (st := M.stepEvents evs₁ st) (fuel := 2 * bs.length + 2) (maxLen := maxLen)
          (err := s2.readReg64 (Reg.gpr 0#5)) (mErr := m) hout
          (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) (mk_pk_regs hregs2)
          (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
          hcrl3 (by simpa [arm64_norm] using htr2.trans htr) (by simp [arm64_norm]) hx0_ne hFit1))
      (fun sf Pf h => pkEpiloguePostPlaced_mono_fuel (by omega) (pkEpiloguePostPlaced_prepend_iter hiter₁ h))
    have hstruct : vecU8At A.repAlloc (sp' + 56#64) g.pub.cap g.pub.ptr m.publicKey ∗
        (vecU8At A.repAlloc (sp' + 80#64) g.priv.cap g.priv.ptr m.privateKey ∗
          ((sp' + 104#64) ↦₃₂ m.id) ∗ memRegion (sp' + 108#64) 4) ⊢
        preKeyStructOf A.repAlloc (sp' + 56#64) m := by
      rw [← preKeyStructAt_split_pub A.repAlloc g sp' m]
      exact preKeyStructAt_entails_of A.repAlloc g (sp' + 56#64) m
    simp only [hstack, hsp_eq, arm64_norm]
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstruct)))))))
    apply entails_of_eq; sep_ac_rfl

theorem mergePrivateKey_12c_placed_cps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H)
    {s0 s : State} {sp' x19 ptr : BitVec 64} {wt : WireType} {bs : List (BitVec 8)}
    {m : PreKeyRecordStructure} {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (blkPl_65).base + bv% (300)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63) (hlen_max : bs.length ≤ maxLen)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (2 * bs.length + 4) maxLen))
    (hcont : ∀ (v rest : List (BitVec 8)) (st1 : M.σ) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      FitsEnv M lim st1 (RecordCodecLoopEnv (2 * rest.length + 2) maxLen) →
      s1.pc = (blkPl_65).base + bv% (112) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1
        (pkAfterVarintMem (A.atState lim st1 s1) sp' x19 ptr bs rest rest.length { m with privateKey := v })
        (pkEpiloguePostPlaced A lim st1 (2 * rest.length + 2) maxLen s0 sp' x19 ptr bs out) (noPanicQp s0))
    (hnone : mergeBytes wt bs = none → out = .error .invalidProtobufEncoding) :
    SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (pkLoopMem (A.atState lim st s) sp' x19 ptr bs m)
      (pkEpiloguePostPlaced A lim st (2 * bs.length + 4) maxLen s0 sp' x19 ptr bs out) (noPanicQp s0) := by
  have hloop_eq : ∀ (st' : M.σ) (s' : State),
      preKeyStructLoopOf (A.atState lim st' s') = preKeyStructLoopOf A.repAlloc := fun _ _ => rfl
  unfold pkLoopMem; rw [hloop_eq]; unfold preKeyStructLoopOf; dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_pure_left_comm, sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun g => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hg => ?_
  rw [preKeyStructAt_split_priv A.repAlloc g sp' m]
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h20 : s.readReg64 (Reg.gpr 20#5) = sp' + 56#64 := hregs.x20
  have h8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 wt.toNat := hx8
  have hstack := stackAt_sub_split sp' bytesMergeStackX (skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 7) ?_; wp_steps
  refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
  let xBm : BytesMergeGhost :=
    ⟨wt, sp' + 80#64, g.priv.cap, g.priv.ptr, m.privateKey, sp' + 184#64, sp' + 40#64, ptr, bs⟩
  have hFit_call : FitsEnv M lim st (BytesMergeEnv xBm) :=
    fitsEnv_recordCodecLoop_bytesHead hlen_max (by omega : 2 * bs.length + 1 ≤ 2 * bs.length + 4) hFit
  refine sepWPp_call_noPanic_lscro (xBm, st) (pk_bytesMerge_placed_ok d)
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (by simp [arm64_norm] : _ = (blkPl_65).base + bv% (316)) (by simpa [arm64_norm] using htr)
    (T := vecU8At A.repAlloc (sp' + 80#64) g.priv.cap g.priv.ptr m.privateKey ∗
      ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
      sliceCursorAt (sp' + 40#64) ptr bs ∗ A.pool lim st s ∗ stackAt sp' bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 56#64 + 24#64 = sp' + 80#64 ∧ sp' + 160#64 + 24#64 = sp' + 184#64 ∧
      bs.length < 9223372036854775808 ∧ BytesMergeCapOk g.priv.cap bs.length ∧
      FitsEnv M lim st (BytesMergeEnv xBm))
    (by cases wt <;> simp [LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeRawSpecX, LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeRawSpecGen,
      LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bmPreBoundBudget, xBm, hsp_eq, CryptoVerification.LibsignalProtoCodec.WireType.toNat, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, by bv_omega, by bv_omega, hlen, hg.priv, hFit_call⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  have hregs2 : PkLoopRegs s0 sp' x19 s2 := CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.PkLoopRegs.of_calleeSaved (mk_pk_regs hregs) hsp2 hcs2
  dsimp only [LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeRawSpecX, LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeRawSpecGen, xBm]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun evs₁ => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun htr2 => ?_
  rw [sepConj_pure_left_comm]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hevs₁ => ?_
  cases hm : mergeBytes wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩; dsimp only [LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bmPostVec]
    have hlen_bound := mergeBytes_len_bound hm
    have hbud_some : (2 * rest.length + 2) + 2 * v.length + 1 ≤ 2 * bs.length + 4 := by omega
    have hFit_rest : FitsEnv M lim (M.stepEvents evs₁ st) (RecordCodecLoopEnv (2 * rest.length + 2) maxLen) :=
      fitsEnv_recordCodecLoop_bytesTail hm hlen_max hevs₁
        (fitsEnv_recordCodecLoop_mono_fuel hbud_some hFit)
    obtain ⟨k, hkl, hrest, _⟩ := mergeBytes_suffix hm
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun cap' => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun ptr' => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hx0_0 => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hcap' => ?_
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (112)) ?_; wp_steps
    refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
    refine sepWPp_mono_post
      (CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre ?_
        (hcont v rest (M.stepEvents evs₁ st) _ hm hFit_rest
          (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) (mk_pk_regs hregs2)
          (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
          hcrl3 (by simpa [arm64_norm] using htr2.trans htr)))
      (fun sf Pf h => pkEpiloguePostPlaced_mono_fuel hbud_some (pkEpiloguePostPlaced_prepend_bytes hm hlen_max hevs₁ h))
    have hstruct : vecU8At A.repAlloc (sp' + 80#64) cap' ptr' v ∗
        (vecU8At A.repAlloc (sp' + 56#64) g.pub.cap g.pub.ptr m.publicKey ∗
          ((sp' + 104#64) ↦₃₂ m.id) ∗ memRegion (sp' + 108#64) 4) ⊢
        preKeyStructLoopOf A.repAlloc (sp' + 56#64) rest.length { m with privateKey := v } := by
      refine Entails.trans ?_
        (preKeyStructAt_entails_loopOf A.repAlloc { g with priv := ⟨cap', ptr'⟩ } (sp' + 56#64)
          rest.length { m with privateKey := v } ⟨bytesMergeCapOk_mono hg.pub hrest_le, hcap'⟩)
      rw [preKeyStructAt_split_priv A.repAlloc { g with priv := ⟨cap', ptr'⟩ } sp' { m with privateKey := v }]
      exact Entails.refl _
    unfold pkAfterVarintMem; rw [hloop_eq]; dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]
    simp only [hstack, hsp_eq, arm64_norm]
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstruct))))
    apply entails_of_eq; sep_ac_rfl
  | none =>
    dsimp only; have hout := hnone hm
    simp only [sepConj_pure_left_comm, sepConj_assoc]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hx0_ne => ?_
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs2.x29
    rw [pkMemRegion48_split8 sp', ProofLib.memRegion_eight (sp' + 112#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w0 => ?_
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (716)) ?_
    wp_steps_sync_pool ((blkPl_65).base + bv% (716))
    refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
    have hiter₁ : RecordCodecIterEnv maxLen evs₁ :=
      LibsignalBinary.Proofs.RecordCodecs.DepsBudget.RecordCodecIterEnv.of_bytesMergeErr (x := xBm) hm hevs₁
    have hFit1 : FitsEnv M lim (M.stepEvents evs₁ st) (RecordCodecLoopEnv (2 * bs.length + 2 + 1) maxLen) :=
      fitsEnv_recordCodecLoop_tail hiter₁ (fitsEnv_recordCodecLoop_mono_fuel (by omega) hFit)
    refine sepWPp_mono_post
      (CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre ?_
        (decodeErrorPush_2cc_placed_wp d (st := M.stepEvents evs₁ st) (fuel := 2 * bs.length + 2) (maxLen := maxLen)
          (err := s2.readReg64 (Reg.gpr 0#5)) (mErr := m) hout
          (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) (mk_pk_regs hregs2)
          (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
          hcrl3 (by simpa [arm64_norm] using htr2.trans htr) (by simp [arm64_norm]) hx0_ne hFit1))
      (fun sf Pf h => pkEpiloguePostPlaced_mono_fuel (by omega) (pkEpiloguePostPlaced_prepend_iter hiter₁ h))
    have hstruct : vecU8At A.repAlloc (sp' + 80#64) g.priv.cap g.priv.ptr m.privateKey ∗
        (vecU8At A.repAlloc (sp' + 56#64) g.pub.cap g.pub.ptr m.publicKey ∗
          ((sp' + 104#64) ↦₃₂ m.id) ∗ memRegion (sp' + 108#64) 4) ⊢
        preKeyStructOf A.repAlloc (sp' + 56#64) m := by
      rw [← preKeyStructAt_split_priv A.repAlloc g sp' m]
      exact preKeyStructAt_entails_of A.repAlloc g (sp' + 56#64) m
    simp only [hstack, hsp_eq, arm64_norm]
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstruct)))))))
    apply entails_of_eq; sep_ac_rfl

theorem mergeSkipField_144_placed_cps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H)
    {s0 s : State} {sp' x19 ptr : BitVec 64} {tag : ℕ} {wt : WireType} {bs : List (BitVec 8)}
    {m : PreKeyRecordStructure} {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (blkPl_65).base + bv% (324)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 wt.toNat)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag) (htag_lt : tag < 2 ^ 32)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (fuel + 2) maxLen))
    (hcont : ∀ (rest : List (BitVec 8)) (st1 : M.σ) (s1 : State),
      skipField (2 * bs.length + 2) 100 tag wt bs = some rest →
      FitsEnv M lim st1 (RecordCodecLoopEnv fuel maxLen) →
      s1.pc = (blkPl_65).base + bv% (112) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1
        (pkAfterVarintMem (A.atState lim st1 s1) sp' x19 ptr bs rest rest.length m)
        (pkEpiloguePostPlaced A lim st1 fuel maxLen s0 sp' x19 ptr bs out) (noPanicQp s0))
    (hnone : skipField (2 * bs.length + 2) 100 tag wt bs = none → out = .error .invalidProtobufEncoding) :
    SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (pkLoopMem (A.atState lim st s) sp' x19 ptr bs m)
      (pkEpiloguePostPlaced A lim st (fuel + 2) maxLen s0 sp' x19 ptr bs out) (noPanicQp s0) := by
  have hloop_eq : ∀ (st' : M.σ) (s' : State),
      preKeyStructLoopOf (A.atState lim st' s') = preKeyStructLoopOf A.repAlloc := fun _ _ => rfl
  unfold pkLoopMem; rw [hloop_eq]; dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 wt.toNat := hx8
  have h1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 tag := hx1
  refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 1) ?_; wp_steps
  refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
  let xSk : SkipFieldGhost := ⟨wt, tag, 100, sp' + 184#64, sp' + 40#64, ptr, bs⟩
  have hFit_call : FitsEnv M lim st (SkipFieldEnv xSk) :=
    fitsEnv_recordCodecLoop_head (fun _ => LibsignalBinary.Proofs.RecordCodecs.DepsBudget.RecordCodecIterEnv.of_skipField)
      (fitsEnv_recordCodecLoop_mono_fuel (by omega : fuel + 1 ≤ fuel + 2) hFit)
  refine sepWPp_call_noPanic_lscro (xSk, st) (pk_skipField_placed_ok d)
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (by simp [arm64_norm] : _ = (blkPl_65).base + bv% (340)) (by simpa [arm64_norm] using htr)
    (T := ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗ sliceCursorAt (sp' + 40#64) ptr bs ∗
      A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      (BitVec.ofNat 64 tag).setWidth 32 = BitVec.ofNat 32 tag ∧ tag < 4294967296 ∧
      sp' + 160#64 + 24#64 = sp' + 184#64 ∧
      (100#64 : BitVec 64).setWidth 32 = 100#32 ∧ 100 < 4294967296 ∧
      bs.length < 9223372036854775808 ∧ FitsEnv M lim st (SkipFieldEnv xSk))
    (by cases wt <;> simp [LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget.skipFieldSpecX, LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget.skipFieldSpecGen, xSk, hsp_eq, h1, CryptoVerification.LibsignalProtoCodec.WireType.toNat, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, setWidth32_ofNat64 tag, htag_lt, by bv_omega, rfl, by decide, hlen, hFit_call⟩
    (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  have hregs2 : PkLoopRegs s0 sp' x19 s2 := CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.PkLoopRegs.of_calleeSaved (mk_pk_regs hregs) hsp2 hcs2
  have hsp2_eq : s2.sp = sp' := hregs2.sp
  dsimp only [LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget.skipFieldSpecX, LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget.skipFieldSpecGen, xSk]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun evs₁ => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun htr2 => ?_
  simp only [sepConj_pure_left_comm]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hevs₁ => ?_
  have hiter₁ : RecordCodecIterEnv maxLen evs₁ := LibsignalBinary.Proofs.RecordCodecs.DepsBudget.RecordCodecIterEnv.of_skipField hevs₁
  have hFit1 : FitsEnv M lim (M.stepEvents evs₁ st) (RecordCodecLoopEnv (fuel + 1) maxLen) :=
    fitsEnv_recordCodecLoop_tail hiter₁ hFit
  cases hs : skipField (2 * bs.length + 2) 100 tag wt bs with
  | some rest =>
    dsimp only; obtain ⟨k, hkl, hrest⟩ := skipField_suffix hs
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    simp only [sepConj_pure_left_comm, sepConj_assoc]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hx0_0 => ?_
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (112)) ?_; wp_steps
    refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
    refine sepWPp_mono_post
      (CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre ?_
        (hcont rest (M.stepEvents evs₁ st) _ hs
          (fitsEnv_recordCodecLoop_mono_fuel (by omega : fuel ≤ fuel + 1) hFit1)
          (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) (mk_pk_regs hregs2)
          (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
          hcrl3 (by simpa [arm64_norm] using htr2.trans htr)))
      (fun sf Pf h => pkEpiloguePostPlaced_prepend_iter hiter₁ (pkEpiloguePostPlaced_mono_fuel (by omega) h))
    unfold pkAfterVarintMem; rw [hloop_eq]; dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]
    simp only [hsp_eq, arm64_norm]
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (preKeyStructLoopOf_mono A.repAlloc (sp' + 56#64) m hrest_le)))))
    apply entails_of_eq; sep_ac_rfl
  | none =>
    dsimp only; have hout := hnone hs
    simp only [sepConj_pure_left_comm, sepConj_assoc]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hx0_ne => ?_
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (464)) ?_; wp_steps
    refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
    refine sepWPp_mono_post
      (CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre ?_
        (post_err_1d0_placed_wp d (st := M.stepEvents evs₁ st) (fuel := fuel + 1) (maxLen := maxLen)
          (err := s2.readReg64 (Reg.gpr 0#5)) (mErr := m) hout
          ⟨by simp [hsp2_eq, arm64_norm],
           by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
           hcrl3, by simp [htr2, htr, arm64_norm],
           ⟨by simpa [arm64_norm] using hregs2.saved.x24, by simpa [arm64_norm] using hregs2.saved.x25,
            by simpa [arm64_norm] using hregs2.saved.x26, by simpa [arm64_norm] using hregs2.saved.x27,
            by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
          (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) (by simp [arm64_norm])
          (by simpa [arm64_norm] using hregs2.x19_eq) (by simpa [speWord, arm64_norm] using hregs2.x22)))
      (fun sf Pf h => pkEpiloguePostPlaced_prepend_iter hiter₁ h)
    have herr_mem := pkErrMem_of_loopOf (A.atState lim (M.stepEvents evs₁ st) s2)
      sp' x19 ptr (s2.readReg64 (Reg.gpr 0#5)) 0 bs.length m bs
    have hstruct_eq : preKeyStructOf (A.atState lim (M.stepEvents evs₁ st) s2) = preKeyStructOf A.repAlloc := rfl
    have hdec_eq : decodeErrorAtStackLen (A.atState lim (M.stepEvents evs₁ st) s2) =
        decodeErrorAtStackLen A.repAlloc := rfl
    have hdecAt_eq : decodeErrorAt (A.atState lim (M.stepEvents evs₁ st) s2) = decodeErrorAt A.repAlloc := rfl
    rw [hloop_eq, hstruct_eq, hdec_eq, hdecAt_eq] at herr_mem
    dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState] at herr_mem; simp only [hsp_eq, arm64_norm]
    refine Entails.trans ?_ herr_mem; apply entails_of_eq; sep_ac_rfl

/-! ## 2. Tag Dispatch, Decode Loop, Prologue, and Root Proof (Block `65`) -/

theorem dispatch_tag_0fc_placed_cps [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {sp' x19 : BitVec 64} {tag : ℕ} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_65).base + bv% (252)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_ge : 1 ≤ tag) (htag_lt : tag < 2 ^ 32)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (h1 : tag = 1 → ∀ s1 : State, s1.pc = (blkPl_65).base + bv% (276) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.readReg64 .x8 = s.readReg64 .x8 → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1 P Q Qp)
    (h2 : tag = 2 → ∀ s1 : State, s1.pc = (blkPl_65).base + bv% (92) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.readReg64 .x8 = s.readReg64 .x8 → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1 P Q Qp)
    (h3 : tag = 3 → ∀ s1 : State, s1.pc = (blkPl_65).base + bv% (300) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.readReg64 .x8 = s.readReg64 .x8 → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1 P Q Qp)
    (h4 : 4 ≤ tag → ∀ s1 : State, s1.pc = (blkPl_65).base + bv% (324) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.readReg64 .x8 = s.readReg64 .x8 →
      s1.readReg64 .x1 = BitVec.ofNat 64 tag → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1 P Q Qp) :
    SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s P Q Qp :=
  CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.dispatch_tag_0fc_placed_cps
    hpc hrun hregs hx1 htag_ge htag_lt hsp hcrl htr h1 h2 h3 h4

theorem mergeField_0fc_placed_cps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H)
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {tag : ℕ} {wt : WireType} {bs : List (BitVec 8)}
    {m : PreKeyRecordStructure} {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (blkPl_65).base + bv% (252)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 wt.toNat)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag) (htag_ge : 1 ≤ tag) (htag_lt : tag < 2 ^ 32)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63) (hlen_max : bs.length ≤ maxLen)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (2 * bs.length + 4) maxLen))
    (hcont : ∀ (m' : PreKeyRecordStructure) (rest : List (BitVec 8)) (st1 : M.σ) (s1 : State),
      CryptoVerification.RecordCodecs.PreKeyRecordStructure.mergeField m tag wt bs = some (m', rest) →
      FitsEnv M lim st1 (RecordCodecLoopEnv (2 * rest.length + 2) maxLen) →
      s1.pc = (blkPl_65).base + bv% (112) → s1.status = .Running → PkLoopRegs s0 sp' x19 s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1
        (pkAfterVarintMem (A.atState lim st1 s1) sp' x19 ptr bs rest rest.length m')
        (pkEpiloguePostPlaced A lim st1 (2 * rest.length + 2) maxLen s0 sp' x19 ptr bs out) (noPanicQp s0))
    (hnone : CryptoVerification.RecordCodecs.PreKeyRecordStructure.mergeField m tag wt bs = none → out = .error .invalidProtobufEncoding) :
    SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (pkLoopMem (A.atState lim st s) sp' x19 ptr bs m)
      (pkEpiloguePostPlaced A lim st (2 * bs.length + 4) maxLen s0 sp' x19 ptr bs out) (noPanicQp s0) := by
  have hloop_eq : ∀ s', preKeyStructLoopOf (A.atState lim st s') = preKeyStructLoopOf A.repAlloc := fun _ => rfl
  rcases tag with _ | _ | _ | _ | n
  · omega
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 1#64 := hx1
    unfold pkLoopMem; rw [hloop_eq]; dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (276)) ?_; wp_steps
    refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (by apply entails_of_eq; unfold pkLoopMem; rw [hloop_eq]; dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]; simp only [arm64_norm])
      (mergeId_114_placed_cps (fuel := 2 * bs.length + 2) (m := m) d (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (mk_pk_regs hregs)
        (by simpa [arm64_norm] using hx8) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 htr hlen hFit
        (fun v rest st1 s2 hm hFit1 hpc2 hrun2 hregs2 hsp2 hcrl2 htr2 => by
          obtain ⟨k, _, hrest⟩ := mergeUint32_suffix hm
          have hle : 2 * rest.length + 2 ≤ 2 * bs.length + 2 := by rw [hrest, List.length_drop]; omega
          exact sepWPp_mono_post
            (hcont { m with id := v } rest st1 s2 (by simp [CryptoVerification.RecordCodecs.PreKeyRecordStructure.mergeField, hm])
              (fitsEnv_recordCodecLoop_mono_fuel hle hFit1) hpc2 hrun2 hregs2 hsp2 hcrl2 htr2)
            (fun _ _ h => pkEpiloguePostPlaced_mono_fuel hle h))
        (fun hm => hnone (by simp [CryptoVerification.RecordCodecs.PreKeyRecordStructure.mergeField, hm])))
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 2#64 := hx1
    unfold pkLoopMem; rw [hloop_eq]; dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (92)) ?_; wp_steps
    refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (by apply entails_of_eq; unfold pkLoopMem; rw [hloop_eq]; dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]; simp only [arm64_norm])
      (mergePublicKey_05c_placed_cps d (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (mk_pk_regs hregs)
        (by simpa [arm64_norm] using hx8) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 htr hlen hlen_max hFit
        (fun v rest st1 s2 hm => hcont { m with publicKey := v } rest st1 s2 (by simp [CryptoVerification.RecordCodecs.PreKeyRecordStructure.mergeField, hm]))
        (fun hm => hnone (by simp [CryptoVerification.RecordCodecs.PreKeyRecordStructure.mergeField, hm])))
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 3#64 := hx1
    unfold pkLoopMem; rw [hloop_eq]; dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (300)) ?_; wp_steps
    refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (by apply entails_of_eq; unfold pkLoopMem; rw [hloop_eq]; dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]; simp only [arm64_norm])
      (mergePrivateKey_12c_placed_cps d (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (mk_pk_regs hregs)
        (by simpa [arm64_norm] using hx8) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 htr hlen hlen_max hFit
        (fun v rest st1 s2 hm => hcont { m with privateKey := v } rest st1 s2 (by simp [CryptoVerification.RecordCodecs.PreKeyRecordStructure.mergeField, hm]))
        (fun hm => hnone (by simp [CryptoVerification.RecordCodecs.PreKeyRecordStructure.mergeField, hm])))
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (n + 4) := hx1
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩ := pk_tag_ge4_conds (n + 4) (by omega) htag_lt
    unfold pkLoopMem; rw [hloop_eq]; dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (324)) ?_; wp_steps
    refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (by apply entails_of_eq; unfold pkLoopMem; rw [hloop_eq]; dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]; simp only [arm64_norm])
      (mergeSkipField_144_placed_cps (fuel := 2 * bs.length + 2) (m := m) d (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (mk_pk_regs hregs)
        (by simpa [arm64_norm] using hx8) (by simpa [arm64_norm] using hx1') htag_lt
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 htr hlen hFit
        (fun rest st1 s2 hs hFit1 hpc2 hrun2 hregs2 hsp2 hcrl2 htr2 => by
          obtain ⟨k, _, hrest⟩ := skipField_suffix hs
          have hle : 2 * rest.length + 2 ≤ 2 * bs.length + 2 := by rw [hrest, List.length_drop]; omega
          exact sepWPp_mono_post
            (hcont m rest st1 s2 (by simp [CryptoVerification.RecordCodecs.PreKeyRecordStructure.mergeField, skipUnknown, recursionLimit, hs])
              (fitsEnv_recordCodecLoop_mono_fuel hle hFit1) hpc2 hrun2 hregs2 hsp2 hcrl2 htr2)
            (fun _ _ h => pkEpiloguePostPlaced_mono_fuel hle h))
        (fun hs => hnone (by simp [CryptoVerification.RecordCodecs.PreKeyRecordStructure.mergeField, skipUnknown, recursionLimit, hs])))

theorem loopHeader_070_empty_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} {s0 s : State} {sp' x19 ptr : BitVec 64} {m : PreKeyRecordStructure}
    {out : Except SignalProtocolError PreKeyRecord} (hok : out = .ok ⟨m⟩)
    (hpc : s.pc = (blkPl_65).base + bv% (112)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace) :
    SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (pkLoopMem (A.atState lim st s) sp' x19 ptr [] m)
      (pkEpiloguePostPlaced A lim st fuel maxLen s0 sp' x19 ptr [] out) (noPanicQp s0) := by
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have hloop_eq : preKeyStructLoopOf (A.atState lim st s) = preKeyStructLoopOf A.repAlloc := rfl
  unfold pkLoopMem sliceCursorAt; rw [hloop_eq]; dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]
  simp only [sepConj_assoc]
  refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (572)) ?_; wp_steps
  refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre ?_
    (post_ok_23c_placed_wp (st := st) (fuel := fuel) (maxLen := maxLen)
      (sp' := sp') (x19 := x19) (ptr := ptr) (m := m) (bs := []) (out := out) hok
      ⟨by simpa [arm64_norm] using hregs.sp, by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
       hcrl1, by simp [htr, arm64_norm], ⟨by simpa [arm64_norm] using hregs.saved.x24,
        by simpa [arm64_norm] using hregs.saved.x25, by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27, by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simpa [arm64_norm] using hregs.x19_eq) (by simpa [arm64_norm] using hregs.x20))
  have h16 := pointsTo64_pair_entails_memRegion16 (sp' + 40#64) ptr
    (BitVec.ofNat 64 ([] : List (BitVec 8)).length)
  have hof := preKeyStructLoopOf_entails_of A.repAlloc (sp' + 56#64) ([] : List (BitVec 8)).length m
  rw [← sepConj_assoc ((sp' + 40#64) ↦₆₄ ptr)
    ((sp' + 40#64 + 8#64) ↦₆₄ BitVec.ofNat 64 ([] : List (BitVec 8)).length)]
  refine Entails.trans
    (sepConj_mono h16 (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left hof))))) ?_
  apply entails_of_eq; simp only [arm64_norm]; sep_ac_rfl

theorem loopHeader_070_cons_placed_cps [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {sp' x19 ptr : BitVec 64} {b0 : BitVec 8} {bs1 : List (BitVec 8)} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_65).base + bv% (112)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace) (hlen : (b0 :: bs1).length < 2 ^ 63)
    (hcont : ∀ s1 : State, s1.pc = (blkPl_65).base + bv% (128) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.readReg64 .x23 = sp' + 40#64 → s1.readReg64 .x21 = sp' + 48#64 →
      s1.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1
        (sliceCursorAt (sp' + 40#64) ptr (b0 :: bs1) ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗ F) Q Qp) :
    SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (sliceCursorAt (sp' + 40#64) ptr (b0 :: bs1) ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗ F) Q Qp :=
  CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.loopHeader_070_cons_placed_cps
    hpc hrun hregs hsp hcrl htr hlen hcont

theorem decodeLoop_080_step_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H)
    {s0 s : State} {sp' x19 ptr : BitVec 64} {st : M.σ}
    {fuel : ℕ} {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : PreKeyRecordStructure}
    (ih : ∀ {st : M.σ} {s : State} {ptr : BitVec 64} {bs : List (BitVec 8)} {m : PreKeyRecordStructure},
      FitsEnv M lim st (RecordCodecLoopEnv (2 * bs.length + 2) maxLen) →
      s.pc = (blkPl_65).base + bv% (112) → s.status = .Running → PkLoopRegs s0 sp' x19 s →
      s.spAligned = true → LibsignalCodeRoLoaded lsmpl s.mem → s.trace = s0.trace →
      bs.length ≤ fuel → bs.length ≤ maxLen → bs.length < 2 ^ 63 →
      SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
        (pkLoopMem (A.atState lim st s) sp' x19 ptr bs m)
        (pkEpiloguePostPlaced A lim st (2 * bs.length + 2) maxLen s0 sp' x19 ptr bs
          (pkLoopOut (decodeFieldsLoop CryptoVerification.RecordCodecs.PreKeyRecordStructure.mergeField fuel m bs))) (noPanicQp s0))
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (2 * (b0 :: bs1).length + 2) maxLen))
    (hpc : s.pc = (blkPl_65).base + bv% (128)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s) (hx23 : s.readReg64 .x23 = sp' + 40#64)
    (hx21 : s.readReg64 .x21 = sp' + 48#64) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hfuel : (b0 :: bs1).length ≤ fuel + 1) (hlen_max : (b0 :: bs1).length ≤ maxLen)
    (hlen : (b0 :: bs1).length < 2 ^ 63) :
    SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (pkLoopMem (A.atState lim st s) sp' x19 ptr (b0 :: bs1) m)
      (pkEpiloguePostPlaced A lim st (2 * (b0 :: bs1).length + 2) maxLen s0 sp' x19 ptr (b0 :: bs1)
        (pkLoopOut (decodeFieldsLoop CryptoVerification.RecordCodecs.PreKeyRecordStructure.mergeField (fuel + 1) m (b0 :: bs1))))
      (noPanicQp s0) := by
  have hbf1 : 2 * (b0 :: bs1).length + 2 = (2 * (b0 :: bs1).length + 1) + 1 := rfl
  rw [hbf1] at hFit ⊢
  refine decodeKey_080_placed_cps d hpc hrun hregs hx23 hx21 hx2 hsp hcrl htr hlen hFit
    (fun tag wt rest1 s1 hdk hpc1 hrun1 hregs1 hsp1 hcrl1 htr1 hx8_1 hx1_1 => ?_)
    (fun hdk_none => by simp [decodeFieldsLoop, pkLoopOut, hdk_none])
  obtain ⟨k1, hk1_pos, hk1_le, hrest1_eq, htag_lt, htag_ge⟩ := decodeKey_suffix hdk
  have hrest1_len : rest1.length = (b0 :: bs1).length - k1 := by simp [hrest1_eq]
  have hbud1 : 2 * rest1.length + 4 ≤ (2 * (b0 :: bs1).length + 1) + 1 := by omega
  unfold pkAfterVarintMem; refine pkAdvanceCursor_placed ⟨k1, hk1_le, hrest1_eq⟩ ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (preKeyStructLoopOf_mono (A.atState lim st s1) (sp' + 56#64)
        (m := rest1.length) (n := (b0 :: bs1).length) m (by omega)))))) ?_
  change SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1
    (pkLoopMem (A.atState lim st s1) sp' x19 (ptr + BitVec.ofNat 64 ((b0 :: bs1).length - rest1.length)) rest1 m) _ _
  refine sepWPp_mono_post
    (mergeField_0fc_placed_cps d hpc1 hrun1 hregs1 hx8_1 hx1_1 htag_ge htag_lt hsp1 hcrl1 htr1
      (by omega) (by omega) (fitsEnv_recordCodecLoop_mono_fuel hbud1 hFit)
      (fun m' rest2 st1 s2 hmf hFit1 hpc2 hrun2 hregs2 hsp2 hcrl2 htr2 => ?_)
      (fun hmf_none => by simp [decodeFieldsLoop, pkLoopOut, hdk, hmf_none]))
    (fun _ _ h => pkEpiloguePostPlaced_mono_fuel hbud1 h)
  obtain ⟨k2, hk2_le, hrest2_eq⟩ := pkMergeField_suffix hmf
  have hrest2_len : rest2.length = rest1.length - k2 := by simp [hrest2_eq]
  unfold pkAfterVarintMem; refine pkAdvanceCursor_placed ⟨k2, hk2_le, hrest2_eq⟩ ?_
  have hloop_eq : decodeFieldsLoop CryptoVerification.RecordCodecs.PreKeyRecordStructure.mergeField (fuel + 1) m (b0 :: bs1) =
      decodeFieldsLoop CryptoVerification.RecordCodecs.PreKeyRecordStructure.mergeField fuel m' rest2 := by simp [decodeFieldsLoop, hdk, hmf]
  rw [hloop_eq]; exact ih hFit1 hpc2 hrun2 hregs2 hsp2 hcrl2 htr2 (by omega) (by omega) (by omega)

theorem decodeLoop_070_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H) {s0 : State} {sp' x19 : BitVec 64} :
    ∀ (fuel : ℕ) {st : M.σ} {s : State} {ptr : BitVec 64} {bs : List (BitVec 8)} {m : PreKeyRecordStructure},
      FitsEnv M lim st (RecordCodecLoopEnv (2 * bs.length + 2) maxLen) →
      s.pc = (blkPl_65).base + bv% (112) → s.status = .Running → PkLoopRegs s0 sp' x19 s →
      s.spAligned = true → LibsignalCodeRoLoaded lsmpl s.mem → s.trace = s0.trace →
      bs.length ≤ fuel → bs.length ≤ maxLen → bs.length < 2 ^ 63 →
      SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
        (pkLoopMem (A.atState lim st s) sp' x19 ptr bs m)
        (pkEpiloguePostPlaced A lim st (2 * bs.length + 2) maxLen s0 sp' x19 ptr bs
          (pkLoopOut (decodeFieldsLoop CryptoVerification.RecordCodecs.PreKeyRecordStructure.mergeField fuel m bs))) (noPanicQp s0)
  | 0, _st, s, _ptr, bs, _m, _hFit, hpc, hrun, hregs, hsp, hcrl, htr, hfuel, _, _ => by
    cases bs with
    | nil => exact loopHeader_070_empty_placed_wp rfl hpc hrun hregs hsp hcrl htr
    | cons _ _ => simp at hfuel
  | fuel + 1, st, s, ptr, bs, m, hFit, hpc, hrun, hregs, hsp, hcrl, htr, hfuel, hlen_max, hlen => by
    cases bs with
    | nil => exact loopHeader_070_empty_placed_wp rfl hpc hrun hregs hsp hcrl htr
    | cons b0 bs1 =>
      have hloop_eq : ∀ s', preKeyStructLoopOf (A.atState lim st s') = preKeyStructLoopOf A.repAlloc := fun _ => rfl
      have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
      obtain ⟨hc_eq, hc_ne⟩ := cons_len_bv64_ne_zero b0 bs1 hlen
      unfold pkLoopMem sliceCursorAt; rw [hloop_eq]; dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]
      simp only [sepConj_assoc]
      refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (128)) ?_; wp_steps
      refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
      refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre ?_
        (decodeLoop_080_step_placed_wp d (decodeLoop_070_placed_wp d fuel) hFit
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (mk_pk_regs hregs)
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hcrl1 (by simpa [arm64_norm] using htr) hfuel hlen_max hlen)
      apply entails_of_eq; unfold pkLoopMem sliceCursorAt; rw [hloop_eq]
      dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]; simp only [arm64_norm, sepConj_assoc]

theorem prologue_000_to_224_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H) {x : DecodeGhost} {s0 : State}
    (hlt : x.bytes.length < 2 ^ 32) (hpc : s0.pc = (blkPl_65).base) (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = x.bytesA) (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (2 * x.bytes.length + 3) x.bytes.length)) :
    SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 56 ∗ stackAt s0.sp smallRootStack ∗ A.pool lim st s0)
      (fun sm Pm => PkEpilogueStatePlaced s0 (s0.sp - 224#64) sm ∧
        (Pm ⊢ pkEpilogueMem A lim st (2 * x.bytes.length + 3) x.bytes.length
            (s0.sp - 224#64) x.ret x.bytesA x.bytes (CryptoVerification.RecordCodecs.PreKeyRecord.deserialize x.bytes) sm ∗
          pkCalleeSavedAt (s0.sp - 224#64) s0 ∗
          memRegion (s0.sp - 224#64 - BitVec.ofNat 64 pkSubStack) (pkSubStack - skipFieldStackX 100)))
      (noPanicQp s0) := by
  set sp' := s0.sp - 224#64
  have hstk1 := pkStack_smallRoot_split s0.sp; have hstk2 := pkSubStack_split sp'
  have h160 : memRegion sp' 160 = memRegion sp' 40 ∗ memRegion (sp' + 40#64) 16 ∗
      memRegion (sp' + 56#64) 56 ∗ memRegion (sp' + 112#64) 48 := by
    rw [show (160 : Nat) = 40 + (16 + (56 + 48)) by decide,
      ProofLib.memRegion_split sp' 40 120 (by decide),
      ProofLib.memRegion_split (sp' + 40#64) 16 104 (by decide),
      ProofLib.memRegion_split (sp' + 40#64 + 16#64) 56 48 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h16 : memRegion (sp' + 40#64) 16 =
      (∃∗ u0 : BitVec 64, (sp' + 40#64) ↦₆₄ u0) ∗ (∃∗ u1 : BitVec 64, (sp' + 48#64) ↦₆₄ u1) := by
    rw [ProofLib.memRegion_split (sp' + 40#64) 8 8 (by decide),
      ProofLib.memRegion_eight, ProofLib.memRegion_eight]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (P' := memRegion (sp' + 160#64) 64 ∗ memRegion (sp' + 56#64) 56 ∗ memRegion (sp' + 40#64) 16 ∗
      (memRegion sp' 40 ∗ memRegion (sp' + 112#64) 48 ∗ memRegion x.ret 56 ∗ (x.bytesA ↦ₛ x.bytes) ∗
        A.pool lim st s0 ∗ stackAt sp' (skipFieldStackX 100) ∗
        memRegion (sp' - BitVec.ofNat 64 pkSubStack) (pkSubStack - skipFieldStackX 100)))
    (by rw [hstk1]; dsimp only [sp'] at hstk2 h160 ⊢; rw [hstk2, h160]; apply entails_of_eq; sep_ac_rfl) ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (sepConj_mono (pkMemRegion64_unpack (sp' + 160#64))
      (sepConj_mono (pkStruct56_unpack_init (sp' + 56#64)) (Entails.refl _))) ?_
  rw [h16]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun u1 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun u0 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun s6w => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun s5w => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun s4w =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun s3w => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun s2w => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun s1w =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun s0w => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun c7 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun c6 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun c5 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun c4 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun c3 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun c2 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun c1 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun c0 => ?_
  dsimp only [sp']
  have h0 : s0.readReg64 (Reg.gpr 0#5) = x.bytesA := hx0
  have h1 : s0.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 x.bytes.length := hx1
  have h8 : s0.readReg64 (Reg.gpr 8#5) = x.ret := hx8
  cases hbs : x.bytes with
  | nil =>
    have h1_nil : s0.readReg64 (Reg.gpr 1#5) = 0#64 := by simpa [hbs] using h1
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (372)) ?_
    wp_steps_sync_pool ((blkPl_65).base + bv% (372))
    refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
    set F_saved := pkCalleeSavedAt sp' s0 ∗
      memRegion (sp' - BitVec.ofNat 64 pkSubStack) (pkSubStack - skipFieldStackX 100)
    have h16_pack := pointsTo64_pair_entails_memRegion16 (sp' + 40#64) x.bytesA 0#64
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre ?_
      (sepWPp_frame_noPanic (F := F_saved)
        (fast_empty_174_placed_wp (st := st) (fuel := 2 * ([] : List (BitVec 8)).length + 3)
          (maxLen := ([] : List (BitVec 8)).length)
          (sp' := sp') (x19 := x.ret) (ptr := x.bytesA) (out := CryptoVerification.RecordCodecs.PreKeyRecord.deserialize []) rfl
          ⟨by dsimp only [sp']; simp [arm64_norm], by simpa [State.spAligned, arm64_norm] using hsp, hcrl1,
           by simp [arm64_norm],
           ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩⟩
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [arm64_norm])
          (by dsimp only [sp']; simp [bv_sub_add_lit, arm64_norm]))
        (fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, sepConj_mono_left hentf⟩))
    dsimp only [F_saved, pkCalleeSavedAt, vecHeader, sp'] at h16_pack ⊢
    simp only [bv_sub_add_lit, BitVec.sub_sub, BitVec.reduceAdd, arm64_norm, sepConj_assoc] at h16_pack ⊢
    rw [← sepConj_assoc ((s0.sp - 184#64) ↦₆₄ x.bytesA) ((s0.sp - 176#64) ↦₆₄ 0#64)]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h16_pack)))))))))))))))))) ?_
    apply entails_of_eq; sep_ac_rfl
  | cons b0 bs1 =>
    have hlen63 : (b0 :: bs1).length < 2 ^ 63 := by simp [hbs, List.length_cons] at hlt ⊢; omega
    obtain ⟨hc_eq, hc_ne⟩ := cons_len_bv64_ne_zero b0 bs1 hlen63
    have h1_cons : s0.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (b0 :: bs1).length := by simpa [hbs] using h1
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (128)) ?_
    wp_steps_sync_pool ((blkPl_65).base + bv% (128))
    refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
    set F_saved := pkCalleeSavedAt sp' s0 ∗
      memRegion (sp' - BitVec.ofNat 64 pkSubStack) (pkSubStack - skipFieldStackX 100)
    have hloop0 := pkEmptyHeaders_entails_loopOf A.repAlloc sp' (b0 :: bs1).length
    have hdes : CryptoVerification.RecordCodecs.PreKeyRecord.deserialize (b0 :: bs1) =
        pkLoopOut (decodeFieldsLoop CryptoVerification.RecordCodecs.PreKeyRecordStructure.mergeField (bs1.length + 1)
          CryptoVerification.RecordCodecs.PreKeyRecordStructure.empty (b0 :: bs1)) := by
      rw [pkDeserialize_eq_of_decodeLoop (b0 :: bs1)]; simp only [List.length_cons]
      cases decodeFieldsLoop CryptoVerification.RecordCodecs.PreKeyRecordStructure.mergeField (bs1.length + 1)
        CryptoVerification.RecordCodecs.PreKeyRecordStructure.empty (b0 :: bs1) <;> rfl
    rw [hdes]; rw [hbs] at hFit
    have hFit_loop : FitsEnv M lim st (RecordCodecLoopEnv (2 * (b0 :: bs1).length + 2) (b0 :: bs1).length) :=
      fitsEnv_recordCodecLoop_mono_fuel (by omega) hFit
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre ?_
      (sepWPp_frame_noPanic (F := F_saved)
        (decodeLoop_080_step_placed_wp d (sp' := sp') (x19 := x.ret) (ptr := x.bytesA)
          (b0 := b0) (bs1 := bs1) (m := CryptoVerification.RecordCodecs.PreKeyRecordStructure.empty)
          (decodeLoop_070_placed_wp d bs1.length) hFit_loop
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          ⟨by dsimp only [sp']; simp [arm64_norm], by dsimp only [sp']; simp [bv_sub_add_lit, arm64_norm],
           by simp [arm64_norm], by dsimp only [sp']; simp [bv_sub_add_lit, arm64_norm], by simp [arm64_norm],
           ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
            by simp [arm64_norm], by simp [arm64_norm]⟩⟩
          (by dsimp only [sp']; simp [bv_sub_add_lit, arm64_norm])
          (by dsimp only [sp']; simp [bv_sub_add_lit, arm64_norm]) (by simp [arm64_norm])
          (by simpa [State.spAligned, arm64_norm] using hsp) hcrl1 (by simp [arm64_norm])
          (by simp) (Nat.le_refl _) hlen63)
        (fun sf Pf h => by
          have h' := pkEpiloguePostPlaced_mono_fuel
            (by omega : 2 * (b0 :: bs1).length + 2 ≤ 2 * (b0 :: bs1).length + 3) h
          exact ⟨h'.1, sepConj_mono_left h'.2⟩))
    have hloop_eq : ∀ s', preKeyStructLoopOf (A.atState lim st s') = preKeyStructLoopOf A.repAlloc := fun _ => rfl
    unfold pkLoopMem sliceCursorAt; rw [hloop_eq]
    dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState, F_saved, pkCalleeSavedAt, vecHeader, sp'] at hloop0 ⊢
    simp only [bv_sub_add_lit, BitVec.sub_sub, BitVec.reduceAdd, arm64_norm, sepConj_assoc] at hloop0 ⊢
    have hloop0L : (((((((s0.sp - 168#64) ↦₆₄ 0#64 ∗ (s0.sp - 160#64) ↦₆₄ 1#64) ∗
        (s0.sp - 152#64) ↦₆₄ 0#64) ∗ (s0.sp - 144#64) ↦₆₄ 0#64) ∗
        (s0.sp - 136#64) ↦₆₄ 1#64) ∗ (s0.sp - 128#64) ↦₆₄ 0#64) ∗
        (s0.sp - 120#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 116#64) 4 ⊢
        preKeyStructLoopOf A.repAlloc (s0.sp - 168#64) (b0 :: bs1).length CryptoVerification.RecordCodecs.PreKeyRecordStructure.empty := by
      simpa only [sepConj_assoc] using hloop0
    rw [← sepConj_assoc ((s0.sp - 168#64) ↦₆₄ 0#64),
      ← sepConj_assoc (((s0.sp - 168#64) ↦₆₄ 0#64) ∗ _),
      ← sepConj_assoc ((((s0.sp - 168#64) ↦₆₄ 0#64) ∗ _) ∗ _),
      ← sepConj_assoc (((((s0.sp - 168#64) ↦₆₄ 0#64) ∗ _) ∗ _) ∗ _),
      ← sepConj_assoc ((((((s0.sp - 168#64) ↦₆₄ 0#64) ∗ _) ∗ _) ∗ _) ∗ _),
      ← sepConj_assoc (((((((s0.sp - 168#64) ↦₆₄ 0#64) ∗ _) ∗ _) ∗ _) ∗ _) ∗ _),
      ← sepConj_assoc ((((((((s0.sp - 168#64) ↦₆₄ 0#64) ∗ _) ∗ _) ∗ _) ∗ _) ∗ _) ∗ _)]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hloop0L (Entails.refl _))))))))))) ?_
    apply entails_of_eq; sep_ac_rfl

/-- Relocatable `PreKeyRecord::deserialize` (Block `65`) meets `preKeyDeserializePlacedSpec`
under `[LibsignalPlacement]` and `PortDepsPlaced M A lim H` (`onPanic = ⌜False⌝`,
`onOom = ⌜False⌝` under `FitsEnv`). -/
theorem preKeyRecord_deserialize_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_65 H) (blkPl_65).base (preKeyDeserializePlacedSpec A lim) := by
  refine subroutine_ok.of_codeLoaded fun ⟨x, st⟩ R s0 hpc hrun hpre hsp hL => ?_
  have ⟨hcrl0, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [preKeyDeserializeRawSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1_nat, hlt, hx8, hFit⟩, hmem⟩
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length := by
    rw [← hx1_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hmem' : s0.mem ⊨
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 56 ∗ stackAt s0.sp smallRootStack ∗ A.pool lim st s0) ∗ R := by
    ac_nf at hmem ⊢
  have h1 := prologue_000_to_224_placed_wp d (x := x) hlt hpc hrun hsp hcrl0 hx0 hx1 hx8 hFit
  have hfull : SepWPp (lsProg_65 H) (s0.readReg64 .x30) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 56 ∗ stackAt s0.sp smallRootStack ∗ A.pool lim st s0)
      (fun sf Pf => sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (preKeyDeserializePlacedSpec A lim).post (x, st) s0 sf)) (noPanicQp s0) := by
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.bind h1 fun sm Pm hpcm hrunm ⟨hstm, hentm⟩ =>
      CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre hentm (epilogue_224_placed_wp (A := A) (lim := lim) (st := st) (x := x) hstm hpcm hrunm)
  obtain ⟨sf, hsteps, ⟨hpc_f, hrun_f, Pf, hmf, ⟨hsp_f, hcs_f, hent_f⟩, hv_f⟩ | ⟨_, _, _, hqp⟩ | ⟨_, hoom⟩⟩ :=
    hfull R hmem' hL
  · refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
    exact Or.inl ⟨⟨hpc_f, hsp_f, hrun_f⟩, ⟨hsp_f, hcs_f hv_f⟩,
      Satisfies.mono (sepConj_mono_left hent_f) hmf⟩
  · exact hqp.elim
  · exact (not_satisfies_false_sepConj hoom).elim

end LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserializeBudget
