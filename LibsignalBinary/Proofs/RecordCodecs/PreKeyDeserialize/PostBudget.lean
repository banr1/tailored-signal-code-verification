/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.DefsBudget
public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.Post
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `PreKeyRecord::deserialize` Result Packing and Deallocation

`RustCliAllocBudget`-threaded result packing and `Vec<u8>` / `DecodeError` cleanup helpers for
`PreKeyRecord::deserialize` (Block `65`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.PostBudget

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification CryptoVerification.RecordCodecs CryptoVerification.RecordCodecs.Placed
open CryptoVerification.RecordCodecsBinary (DecodeGhost preKeyResultAt sepWPp_of_sepWP_lscro)
open CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers
  (PkEpilogueStatePlaced PreKeyGhost pkCalleeSavedAt pkSubStack pkStack_smallRoot_unsplit
   pkMemRegion40_unpack pkMemRegion40_pack pkMemRegion56_unpack pkMemRegion160_pack
   pkStruct56_pack pkRecordOk56_intro emp_entails_two_vecU8Buf_zero
   status_setPC_pre status_setMem_pre trace_setPC_pre trace_setMem_pre
   sp_setPC_pre sp_setMem_pre pc_setPC_pre pc_setMem_pre readReg64_setPC_pre readReg64_setMem_pre
   readReg32_setPC_pre readReg32_setMem_pre readReg_setPC_pre readReg_setMem_pre)
open LibsignalBinary.Heap
open LibsignalBinary.Proofs.Placed.BudgetPoolSync
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget
open LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.DefsBudget

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

open scoped CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers

theorem pack_tail_190_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} {s0 s : State} {sp' x19 ptr w0 w1 : BitVec 64} {pad32 : BitVec 32}
    {g : PreKeyGhost} {m : PreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Except SignalProtocolError PreKeyRecord} (hok : out = .ok ⟨m⟩)
    (hst : PkEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_65).base + bv% (400)) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19) (hx8 : s.readReg64 .x8 = g.pub.cap)
    (hx0 : s.readReg64 .x0 = g.pub.ptr) (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 m.publicKey.length)
    (hx9 : s.readReg64 .x9 = g.priv.cap) (hx11 : s.readReg64 .x11 = g.priv.ptr) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      ((sp' ↦₆₄ w0) ∗ ((sp' + 8#64) ↦₆₄ w1) ∗ ((sp' + 16#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
        ((sp' + 24#64) ↦₆₄ (pad32 ++ m.id)) ∗ memRegion (sp' + 32#64) 8 ∗ memRegion (sp' + 40#64) 16 ∗
        memRegion (sp' + 56#64) 56 ∗ memRegion (sp' + 112#64) 48 ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        memRegion x19 56 ∗ vecU8Buf A.repAlloc g.pub.cap g.pub.ptr m.publicKey ∗
        vecU8Buf A.repAlloc g.priv.cap g.priv.ptr m.privateKey ∗ (ptr ↦ₛ bs) ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePostPlaced A lim st fuel maxLen s0 sp' x19 ptr bs out) (noPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcrl, htr, hsaved⟩
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (pkMemRegion56_unpack x19))))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun r0 => Wire.SepWPp.exists_pre fun r1 =>
    Wire.SepWPp.exists_pre fun r2 => Wire.SepWPp.exists_pre fun r3 =>
    Wire.SepWPp.exists_pre fun r4 => Wire.SepWPp.exists_pre fun r5 => Wire.SepWPp.exists_pre fun r6 => ?_
  have h19 : s.readReg64 (Reg.gpr 19#5) = x19 := hx19
  have h8 : s.readReg64 (Reg.gpr 8#5) = g.pub.cap := hx8
  have h0 : s.readReg64 (Reg.gpr 0#5) = g.pub.ptr := hx0
  have h10 : s.readReg64 (Reg.gpr 10#5) = BitVec.ofNat 64 m.publicKey.length := hx10
  have h9 : s.readReg64 (Reg.gpr 9#5) = g.priv.cap := hx9
  have h11 : s.readReg64 (Reg.gpr 11#5) = g.priv.ptr := hx11
  refine sepWPp_of_sepWP_end_noPanic_lscro hcrl ?_
  wp_steps_sync_pool ((blkPl_65).base + bv% (548))
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcrl1
  refine ⟨⟨by simp [hsp_eq, arm64_norm], by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
    hcrl1, by simp [htr, arm64_norm],
    ⟨by simpa [arm64_norm] using hsaved.x24, by simpa [arm64_norm] using hsaved.x25,
     by simpa [arm64_norm] using hsaved.x26, by simpa [arm64_norm] using hsaved.x27,
     by simpa [arm64_norm] using hsaved.x28⟩⟩, ?_⟩
  have h40 := pkMemRegion40_pack sp' (BitVec.ofNat 64 m.privateKey.length) (pad32 ++ m.id)
    (BitVec.ofNat 64 m.privateKey.length) (pad32 ++ m.id)
  unfold pkEpilogueMem
  simp only [arm64_norm]
  refine Entails.sepExists_right [] ?_
  rw [pure_true_emp (PkSubEnv.of_loop .nil), emp_sepConj, AllocCostModel.stepEvents_nil]
  refine Entails.trans ?_
    (sepConj_mono (pkMemRegion160_pack sp')
      (sepConj_mono_right (sepConj_mono_left (pkRecordOk56_intro A.repAlloc g x19 m pad32 hok))))
  refine Entails.trans ?_ (sepConj_mono_left (sepConj_mono_left h40))
  apply entails_of_eq; ac_rfl

theorem fast_empty_174_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} {s0 s : State} {sp' x19 ptr : BitVec 64}
    {out : Except SignalProtocolError PreKeyRecord}
    (hok : out = .ok ⟨PreKeyRecordStructure.empty⟩) (hst : PkEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_65).base + bv% (372)) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19) (hx20 : s.readReg64 .x20 = sp' + 56#64) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (memRegion sp' 40 ∗ memRegion (sp' + 40#64) 16 ∗ vecHeader (sp' + 56#64) 0#64 1#64 0#64 ∗
        vecHeader (sp' + 80#64) 0#64 1#64 0#64 ∗ ((sp' + 104#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 108#64) 4 ∗
        memRegion (sp' + 112#64) 48 ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗ memRegion x19 56 ∗
        (ptr ↦ₛ ([] : List (BitVec 8))) ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePostPlaced A lim st fuel maxLen s0 sp' x19 ptr [] out) (noPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcrl, htr, hsaved⟩
  refine Wire.SepWPp.mono_pre
    (sepConj_mono (pkMemRegion40_unpack sp') (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left (memRegion_four_entails (sp' + 108#64)))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun pad32 => Wire.SepWPp.exists_pre fun w0 =>
    Wire.SepWPp.exists_pre fun w1 => Wire.SepWPp.exists_pre fun w2 => Wire.SepWPp.exists_pre fun w3 => ?_
  have hp104 : ((sp' + 104#64) ↦₃₂ 0#32) ∗ ((sp' + 108#64) ↦₃₂ pad32) =
      ((sp' + 104#64) ↦₆₄ (pad32 ++ 0#32)) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair (sp' + 104#64) 0#32 pad32
  refine Wire.SepWPp.mono_pre
    (P' := (sp' ↦₆₄ w0) ∗ ((sp' + 8#64) ↦₆₄ w1) ∗ ((sp' + 16#64) ↦₆₄ w2) ∗ ((sp' + 24#64) ↦₆₄ w3) ∗
      memRegion (sp' + 32#64) 8 ∗ memRegion (sp' + 40#64) 16 ∗ ((sp' + 56#64) ↦₆₄ 0#64) ∗ ((sp' + 64#64) ↦₆₄ 1#64) ∗
      ((sp' + 72#64) ↦₆₄ 0#64) ∗ ((sp' + 80#64) ↦₆₄ 0#64) ∗ ((sp' + 88#64) ↦₆₄ 1#64) ∗ ((sp' + 96#64) ↦₆₄ 0#64) ∗
      ((sp' + 104#64) ↦₆₄ (pad32 ++ 0#32)) ∗ memRegion (sp' + 112#64) 48 ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
      memRegion x19 56 ∗ (ptr ↦ₛ ([] : List (BitVec 8))) ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
    (by dsimp only [vecHeader]; rw [← sepConj_assoc ((sp' + 104#64) ↦₃₂ 0#32), hp104]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; exact Entails.refl _) ?_
  have h19 : s.readReg64 (Reg.gpr 19#5) = x19 := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = sp' + 56#64 := hx20
  refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (400)) ?_
  wp_steps_sync_pool ((blkPl_65).base + bv% (400))
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
  refine Wire.SepWPp.mono_pre ?_
    (pack_tail_190_placed_wp (g := ⟨⟨0#64, 1#64⟩, ⟨0#64, 1#64⟩⟩) (m := PreKeyRecordStructure.empty)
      (w0 := w0) (w1 := w1) (pad32 := pad32) hok
      ⟨by simp [hsp_eq, arm64_norm], by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp, hcrl1,
       by simp [htr, arm64_norm], ⟨by simpa [arm64_norm] using hsaved.x24, by simpa [arm64_norm] using hsaved.x25,
        by simpa [arm64_norm] using hsaved.x26, by simpa [arm64_norm] using hsaved.x27, by simpa [arm64_norm] using hsaved.x28⟩⟩
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [h19, arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [PreKeyRecordStructure.empty, arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]))
  simp only [PreKeyRecordStructure.empty, arm64_norm]
  have h56 : ((sp' + 56#64) ↦₆₄ 0#64) ∗ ((sp' + 64#64) ↦₆₄ 1#64) ∗ ((sp' + 72#64) ↦₆₄ 0#64) ∗
      ((sp' + 80#64) ↦₆₄ 0#64) ∗ ((sp' + 88#64) ↦₆₄ 1#64) ∗ ((sp' + 96#64) ↦₆₄ 0#64) ∗
      ((sp' + 104#64) ↦₆₄ (pad32 ++ 0#32)) ⊢ memRegion (sp' + 56#64) 56 := by
    rw [← hp104]
    simpa [vecHeader, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      pkStruct56_pack sp' 0#64 1#64 0#64 0#64 1#64 0#64 0#32 pad32
  rw [← emp_sepConj (A.pool lim st _ ∗ stackAt sp' (skipFieldStackX 100)),
    ← sepConj_assoc (vecU8Buf A.repAlloc 0#64 1#64 [])]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono h56
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (emp_entails_two_vecU8Buf_zero A.repAlloc))))))))))))
  apply entails_of_eq; ac_rfl

theorem epilogue_224_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    {x : DecodeGhost} {s0 s : State} (hst : PkEpilogueStatePlaced s0 (s0.sp - 224#64) s)
    (hpc : s.pc = (blkPl_65).base + bv% (548)) (hrun : s.status = .Running) :
    Wire.SepWPp (lsProg_65 H) (s0.readReg64 .x30) s
      (pkEpilogueMem A lim st (2 * x.bytes.length + 3) x.bytes.length
          (s0.sp - 224#64) x.ret x.bytesA x.bytes (PreKeyRecord.deserialize x.bytes) s ∗
        pkCalleeSavedAt (s0.sp - 224#64) s0 ∗
        memRegion (s0.sp - 224#64 - BitVec.ofNat 64 pkSubStack) (pkSubStack - skipFieldStackX 100))
      (fun sf Pf => sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (preKeyDeserializePlacedSpec A lim).post (x, st) s0 sf)) (noPanicQp s0) := by
  rcases hst with ⟨hsp_eq, _hsp, hcrl, htr, hsaved⟩
  unfold pkEpilogueMem pkCalleeSavedAt
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun evs => ?_
  refine Wire.SepWPp.mono_pre
    (P' := ⌜PkSubEnv (2 * x.bytes.length + 3) x.bytes.length evs⌝ ∗
      (memRegion (s0.sp - 224#64) 160 ∗
        ((s0.sp - 224#64 + 184#64) ↦₆₄ (s0.sp - 224#64 + 40#64)) ∗
        preKeyResultAt A.repAlloc x.ret (PreKeyRecord.deserialize x.bytes) ∗
        (x.bytesA ↦ₛ x.bytes) ∗
        A.pool lim (M.stepEvents evs st) s ∗
        stackAt (s0.sp - 224#64) (skipFieldStackX 100) ∗
        ((s0.sp - 224#64 + 160#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 224#64 + 168#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 224#64 + 176#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 224#64 + 192#64) ↦₆₄ s0.readReg64 .x22) ∗
        ((s0.sp - 224#64 + 200#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 224#64 + 208#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 224#64 + 216#64) ↦₆₄ s0.readReg64 .x19) ∗
        memRegion (s0.sp - 224#64 - BitVec.ofNat 64 pkSubStack) (pkSubStack - skipFieldStackX 100)))
    (by apply entails_of_eq; ac_rfl) ?_
  refine Wire.SepWPp.pure_pre fun hevs => ?_
  refine sepWPp_of_sepWP_end_noPanic_lscro hcrl ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro _
  refine ⟨by simp [arm64_norm], fun hv => ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simpa [arm64_norm] using hsaved.x24,
    by simpa [arm64_norm] using hsaved.x25, by simpa [arm64_norm] using hsaved.x26,
    by simpa [arm64_norm] using hsaved.x27, by simpa [arm64_norm] using hsaved.x28,
    by simp [arm64_norm], hv⟩, ?_⟩
  dsimp only [preKeyDeserializePlacedSpec, withLsCodeRoLoaded, preKeyDeserializeRawSpec]
  rw [pure_true_emp (by simp [htr, arm64_norm]), emp_sepConj]
  have hstk := pkStack_smallRoot_unsplit s0.sp s0; unfold pkCalleeSavedAt at hstk
  simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_writeReg64,
    sepExists_sepConj_left, sepConj_assoc]
  refine Entails.sepExists_right evs ?_
  rw [pure_true_emp hevs, emp_sepConj]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk)))
  apply entails_of_eq; ac_rfl

end LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.PostBudget
