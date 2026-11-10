/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import ProofLib.SepLogic.WPp

/-!
# `spqr::decode_state` (Block `325`): Relocatable `ChainEpochPB` Field Merge Helpers

Relocatable `[LibsignalPlacement]` proofs of `ChainEpochPB` tag 1 (`send`), tag 2 (`recv`),
and `skip_field(depth=98)` (`+964..+1164`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.DecodeState.Placed

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Panic-Aware Call Wrapper for `EpochDirection::merge` -/

theorem SepWPpIPlaced.call_epochDirectionMerge [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A)))
    (wt : WireType) (msgPtr : BitVec 64) (msg : EpochDirectionPB)
    (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8))
    {x_outer : DecodeStateGhost} {s0 s : State}
    {P F R : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 wt.toNat)
    (hx1 : s.readReg64 .x1 = msgPtr)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hlen : bs.length < 2 ^ 63)
    (hP : P = (epochDirectionPBCapOkAt A msgPtr bs.length msg ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot ptr bs ∗ A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (m' : EpochDirectionPB) (rest : List (BitVec 8)),
      (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto wt) msg bs 98).toOption = some (m', rest) →
      rest.length ≤ bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          epochDirectionPBCapOkAt A msgPtr rest.length m' ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R))
    (herr : ∀ (sf : State) (n : Nat) (m' : EpochDirectionPB),
      (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto wt) msg bs 98).toOption = none →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 → n ≤ 1 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          decodeErrorAtStackLen A (sf.readReg64 .x0) n ∗
          epochDirectionPBAt A msgPtr m' ∗
          memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F)
        Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R)) :
    SepWPpIPlaced prog ret s P Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R) := by
  intro hinv
  let sp_cur := s0.sp - 1392#64
  let x_ed : EpochDirectionMergeGhost := ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - epochDirectionMergeStack) ∗ F
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  have hwpp : SepWPp prog ret_pc s P
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧
        Pm = (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A)).post x_ed s sm ∗ F_ext)
      (decodeStatePanicPostPlaced H_inner A x_outer s0 R) := by
    refine SepWPp.call (x := x_ed) (F := F_ext) hcall hpc hrun halign hlr ?_ ?_ ?_ ?_ ?_
    · intro R' hm
      dsimp only [withLsCodeRoLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hinv, ?_⟩
      dsimp only [epochDirectionMergeSpec, x_ed]
      rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0, hx1, hx2, hlen⟩, ?_⟩
      rw [hP] at hm
      have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (stackAt_to_callee sp_cur epochDirectionMergeStack (by decide)))))))) hm
      refine Satisfies.mono (Entails.of_eq ?_) hm1
      dsimp only [sp_cur, F_ext]; ac_rfl
    · intro sm _ R' _ hpost
      dsimp only [epochDirectionMergeSpec, withLsCodeRoLoaded] at hpost
      exact allowPanic_not_exited hpost
    · intro sm _ hm'
      dsimp only [decodeStatePanicPostPlaced, spqrDecodeStatePlacedSpec, withLsCodeRoLoaded, epochDirectionMergeSpec] at hm' ⊢
      exact allowPanic_frame (allocFailedIn_trans htr) hm'
    · intro sm hpcm hrunm hspm hcsm
      exact SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩
    · intro sm R' _ hpost
      exact False.elim (not_satisfies_false_sepConj hpost)
  intro R' hm hL
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, _, hpost, hspm, hcsm, rfl⟩ | hpan_or_oom⟩ := hwpp R' hm hL
  · rw [sepConj_assoc] at hpost
    change sm.mem ⊨ (epochDirectionMergeSpec A).post x_ed s sm ∗ (F_ext ∗ R') at hpost
    dsimp only [epochDirectionMergeSpec, x_ed] at hpost
    rw [hsp] at hpost
    rcases hed : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto wt) msg bs 98).toOption with _ | ⟨m', rest⟩
    · simp only [hed, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
      rcases hpost with ⟨m', n, hpost⟩
      have hpost_pure : sm.mem ⊨ ⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 ≠ 0#64⌝ ∗ (⌜n ≤ 1⌝ ∗
          (((bufRef ↦₆₄ slot) ∗ A.pool ∗
            (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
              (v1StateMergeStack - epochDirectionMergeStack) ∗
              stackAt sp_cur epochDirectionMergeStack) ∗
            decodeErrorAtStackLen A (sm.readReg64 .x0) n ∗
            epochDirectionPBAt A msgPtr m' ∗
            memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F) ∗ R')) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨htrm, hx0_ne, hn, hpost1⟩
      rw [hsp] at hspm
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur epochDirectionMergeStack (by decide))))))) hpost1
      obtain ⟨sf, hsteps', hout'⟩ :=
        herr sm n m' hed hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_ne hn (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
    · simp only [hed] at hpost
      have hpost_pure : sm.mem ⊨ ⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 = 0#64⌝ ∗
          (((bufRef ↦₆₄ slot) ∗ A.pool ∗
            (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
              (v1StateMergeStack - epochDirectionMergeStack) ∗
              stackAt sp_cur epochDirectionMergeStack) ∗
            epochDirectionPBCapOkAt A msgPtr rest.length m' ∗
            sliceCursorAfter slot ptr bs rest) ∗ F) ∗ R') := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨htrm, hx0_0, hpost1⟩
      rw [hsp] at hspm
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur epochDirectionMergeStack (by decide))))))) hpost1
      have ⟨hle, hsuf⟩ := proto_mergeMessage_suffix hed
      obtain ⟨sf, hsteps', hout'⟩ :=
        hok sm m' rest hed hle hsuf hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_0 (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr hpan_or_oom⟩

/-! ## `ChainEpochPB` Framing & Initialization Helpers -/

private theorem optEpochDirectionPB_none_split48 (a : BitVec 64) :
    memRegion (a + 8#64) 48 ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 32,
        ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
        ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₃₂ w6) ∗
        memRegion (a + 52#64) 4 := by
  have hs1 := ProofLib.memRegion_split (a + 8#64) 8 40 (by decide)
  have hs2 := ProofLib.memRegion_split ((a + 8#64) + 8#64) 8 32 (by decide)
  have hs3 := ProofLib.memRegion_split (((a + 8#64) + 8#64) + 8#64) 8 24 (by decide)
  have hs4 := ProofLib.memRegion_split ((((a + 8#64) + 8#64) + 8#64) + 8#64) 8 16 (by decide)
  have hs5 := ProofLib.memRegion_split (((((a + 8#64) + 8#64) + 8#64) + 8#64) + 8#64) 8 8 (by decide)
  have hs6 := ProofLib.memRegion_split ((((((a + 8#64) + 8#64) + 8#64) + 8#64) + 8#64) + 8#64) 4 4 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs1 hs2 hs3 hs4 hs5 hs6
  rw [hs1, hs2, hs3, hs4, hs5, hs6,
    ProofLib.memRegion_eight (a + 8#64),
    ProofLib.memRegion_eight (a + 16#64),
    ProofLib.memRegion_eight (a + 24#64),
    ProofLib.memRegion_eight (a + 32#64),
    ProofLib.memRegion_eight (a + 40#64),
    ProofLib.memRegion_four (a + 48#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w6
  apply Entails.sepExists_elim; intro w5
  apply Entails.sepExists_elim; intro w4
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  refine Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right w4
      (Entails.sepExists_right w5 (Entails.sepExists_right w6 ?_)))))
  exact Entails.of_eq (by ac_rfl)

private theorem optEpochDirectionPBCapOkAt_some (A : RustAlloc) (a : BitVec 64) (remLen : Nat) (d : EpochDirectionPB) :
    optEpochDirectionPBCapOkAt A a remLen (some d) = epochDirectionPBCapOkAt A a remLen d := rfl

private theorem optEpochDirectionPBCapOkAt_none (A : RustAlloc) (a : BitVec 64) (remLen : Nat) :
    optEpochDirectionPBCapOkAt A a remLen none = (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 48 := rfl

private theorem optEpochDirectionPBAt_some_eq (A : RustAlloc) (a : BitVec 64) (d : EpochDirectionPB) :
    optEpochDirectionPBAt A a (some d) = epochDirectionPBAt A a d := rfl

private def epochDirectionPBCapOkRestAt (A : RustAlloc) (a : BitVec 64) (remLen : Nat)
    (cap1 : BitVec 64) (d : EpochDirectionPB) : SepProp :=
  (∃∗ ptr1 : BitVec 64,
    ((a + 8#64) ↦₆₄ ptr1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
    vecU8Heap A cap1 ptr1 d.next) ∗
  vecU8CapOkAt A (a + 0x18#64) remLen d.prev ∗
  ((a + 0x30#64) ↦₃₂ d.ctr) ∗
  memRegion (a + 0x34#64) 4

private theorem epochDirectionPBCapOkAt_expose_cap (A : RustAlloc) (a : BitVec 64) (remLen : Nat) (d : EpochDirectionPB) :
    epochDirectionPBCapOkAt A a remLen d ⊢
      ∃∗ cap1 : BitVec 64,
        ⌜BytesMergeCapOk cap1 remLen ∧ cap1.toNat < 2 ^ 63⌝ ∗
        (a ↦₆₄ cap1) ∗
        epochDirectionPBCapOkRestAt A a remLen cap1 d := by
  unfold epochDirectionPBCapOkAt
  rw [show vecU8CapOkAt A a remLen d.next =
    ∃∗ cap1 : BitVec 64, ∃∗ ptr1 : BitVec 64,
      ⌜BytesMergeCapOk cap1 remLen⌝ ∗ vecU8At A a cap1 ptr1 d.next from rfl]
  simp only [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro cap1
  apply Entails.sepExists_elim; intro ptr1
  refine Entails.sepExists_right cap1 ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left; intro hcap
  rw [vecU8At_eq_header_heap]
  unfold vecHeader
  simp only [sepConj_assoc]
  have hlt_ent := vecU8Heap_cap_lt A cap1 ptr1 d.next
  have hreord1 :
      (a ↦₆₄ cap1) ∗ ((a + 8#64) ↦₆₄ ptr1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
        vecU8Heap A cap1 ptr1 d.next ∗
        vecU8CapOkAt A (a + 0x18#64) remLen d.prev ∗
        ((a + 0x30#64) ↦₃₂ d.ctr) ∗ memRegion (a + 0x34#64) 4 =
      vecU8Heap A cap1 ptr1 d.next ∗
        ((a ↦₆₄ cap1) ∗ ((a + 8#64) ↦₆₄ ptr1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
          vecU8CapOkAt A (a + 0x18#64) remLen d.prev ∗
          ((a + 0x30#64) ↦₃₂ d.ctr) ∗ memRegion (a + 0x34#64) 4) := by ac_rfl
  rw [hreord1]
  refine Entails.trans (sepConj_mono_left hlt_ent) ?_
  rw [sepConj_assoc]
  apply Entails.pure_left; intro hcap_lt
  apply Entails.pure_right ⟨hcap, hcap_lt⟩
  unfold epochDirectionPBCapOkRestAt
  have hreord2 :
      vecU8Heap A cap1 ptr1 d.next ∗ ((a ↦₆₄ cap1) ∗ ((a + 8#64) ↦₆₄ ptr1) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
        vecU8CapOkAt A (a + 0x18#64) remLen d.prev ∗
        ((a + 0x30#64) ↦₃₂ d.ctr) ∗ memRegion (a + 0x34#64) 4) =
      (a ↦₆₄ cap1) ∗
        (((a + 8#64) ↦₆₄ ptr1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
          vecU8Heap A cap1 ptr1 d.next) ∗
        vecU8CapOkAt A (a + 0x18#64) remLen d.prev ∗
        ((a + 0x30#64) ↦₃₂ d.ctr) ∗ memRegion (a + 0x34#64) 4 := by ac_rfl
  rw [hreord2]
  exact sepConj_mono_right (sepConj_mono_left (Entails.sepExists_right ptr1 (Entails.refl _)))

attribute [local irreducible] skipField Proto.mergeMessage Proto.spqrDecodeState

private theorem epochDirectionPBCapOkAt_fold_cap (A : RustAlloc) (a cap1 : BitVec 64) (remLen : Nat)
    (d : EpochDirectionPB) (hcap : BytesMergeCapOk cap1 remLen) :
    (a ↦₆₄ cap1) ∗ epochDirectionPBCapOkRestAt A a remLen cap1 d ⊢
      epochDirectionPBCapOkAt A a remLen d := by
  unfold epochDirectionPBCapOkAt epochDirectionPBCapOkRestAt
  rw [show vecU8CapOkAt A a remLen d.next =
    ∃∗ cap1 : BitVec 64, ∃∗ ptr1 : BitVec 64,
      ⌜BytesMergeCapOk cap1 remLen⌝ ∗ vecU8At A a cap1 ptr1 d.next from rfl]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro ptr1
  refine Entails.sepExists_right cap1 (Entails.sepExists_right ptr1 ?_)
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_right hcap
  rw [vecU8At_eq_header_heap]
  unfold vecHeader
  exact Entails.of_eq (by ac_rfl)

theorem chainEpochPBCapOkAt_eq_placed (A : RustAlloc) (sp : BitVec 64) (remLen : Nat) (ep : ChainEpochPB) :
    chainEpochPBCapOkAt A (sp - 688#64) remLen ep =
      optEpochDirectionPBCapOkAt A (sp - 688#64) remLen ep.send ∗
      optEpochDirectionPBCapOkAt A (sp - 632#64) remLen ep.recv := by
  unfold chainEpochPBCapOkAt
  have ha : sp - 688#64 + 0x38#64 = sp - 632#64 := by bv_omega
  rw [ha]

private abbrev chainEpochPBCapOkAt_eq := @chainEpochPBCapOkAt_eq_placed

private theorem chainEpochPBAt_eq (A : RustAlloc) (sp : BitVec 64) (ep : ChainEpochPB) :
    chainEpochPBAt A (sp - 688#64) ep =
      optEpochDirectionPBAt A (sp - 688#64) ep.send ∗
      optEpochDirectionPBAt A (sp - 632#64) ep.recv := by
  unfold chainEpochPBAt
  have ha : sp - 688#64 + 0x38#64 = sp - 632#64 := by bv_omega
  rw [ha]

theorem epochLoop_cursor_to_epochErrFrame_placed [LibsignalPlacement] (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (x : DecodeStateGhost) (cur : List (BitVec 8)) (remSt remEp : Nat)
    (curSt : PqRatchetState) (curEpoch : ChainEpochPB) (s0 : State) :
    sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) remSt curSt ∗
      chainEpochPBCapOkAt A (s0.sp - 688#64) remEp curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A x s0 ⊢
      decodeStateEpochErrFramePlaced H_inner A x curSt curEpoch s0 := by
  dsimp only [decodeStateLoopCommonPlaced, decodeStateEpochErrFramePlaced, decodeStateEpochErrTailFramePlaced]
  have h1 := sliceCursorAfter_to_memRegion s0.sp x.st.ptr x.st.bytes cur
  have h2 := protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) remSt curSt
  have h3 := chainEpochPBCapOkAt_entails_chainEpochPBAt A (s0.sp - 688#64) remEp curEpoch
  have hst := vecArg_join_bytes A x.st
  have hlow := lower_352_fold s0.sp
  have hup := upper_240_fold s0.sp (s0.sp - 1056#64)
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono_left h3))) ?_
  have hreord :
      (memRegion (s0.sp - 1056#64) 16 ∗ (x.st.ptr ↦ₛ x.st.bytes)) ∗
        protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
        chainEpochPBAt A (s0.sp - 688#64) curEpoch ∗
        memRegion (s0.sp - 576#64) 240 ∗
        (v1StateJumpTablesPlacedAt ∗ vecArgRestAt A x.st ∗ memRegion x.outPtr 352 ∗
          A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          memRegion (s0.sp - 1392#64) 336 ∗ ((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗
          memRegion (s0.sp - 328#64) 224 ∗ memRegion (s0.sp - 104#64) 8 ∗
          decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
            (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
            (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
            (s0.readReg64 .x20) (s0.readReg64 .x19)) =
      chainEpochPBAt A (s0.sp - 688#64) curEpoch ∗
        v1StateJumpTablesPlacedAt ∗
        ((x.st.ptr ↦ₛ x.st.bytes) ∗ vecArgRestAt A x.st) ∗
        memRegion x.outPtr 352 ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
        (memRegion (s0.sp - 1392#64) 336 ∗ memRegion (s0.sp - 1056#64) 16) ∗
        protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
        memRegion (s0.sp - 576#64) 240 ∗
        (((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗ memRegion (s0.sp - 328#64) 224 ∗
          memRegion (s0.sp - 104#64) 8) ∗
        decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
          (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
          (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
          (s0.readReg64 .x20) (s0.readReg64 .x19) := by ac_rfl
  rw [hreord]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono hst (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono hlow (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left hup)))))))))

theorem epochLoop_calleeErr_to_epochErrFrame_placed [LibsignalPlacement] (H_inner : V1InnerHeapPred)
    (A : RustAlloc) (x : DecodeStateGhost) {cur : List (BitVec 8)}
    (hcur_le : cur.length ≤ x.st.bytes.length) (hcur_suf : IsDropSuffix x.st.bytes cur)
    (remSt : Nat) (curSt : PqRatchetState) (curEpoch : ChainEpochPB) (s0 : State) :
    memRegion (s0.sp - 1056#64) 16 ∗
      ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
      (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) remSt curSt ∗
      chainEpochPBAt A (s0.sp - 688#64) curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A x s0 ⊢
      decodeStateEpochErrFramePlaced H_inner A x curSt curEpoch s0 := by
  dsimp only [decodeStateLoopCommonPlaced, decodeStateEpochErrFramePlaced, decodeStateEpochErrTailFramePlaced]
  have h1 := pointsToBytes_prefix_join (ptr := x.st.ptr) hcur_le hcur_suf
  have hst := Entails.trans (sepConj_mono_left h1) (vecArg_join_bytes A x.st)
  have h2 := protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) remSt curSt
  have hlow := lower_352_fold s0.sp
  have hup := upper_240_fold s0.sp (s0.sp - 1056#64)
  have hreord :
      memRegion (s0.sp - 1056#64) 16 ∗
        ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
        (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) remSt curSt ∗
        chainEpochPBAt A (s0.sp - 688#64) curEpoch ∗
        memRegion (s0.sp - 576#64) 240 ∗
        (v1StateJumpTablesPlacedAt ∗ vecArgRestAt A x.st ∗ memRegion x.outPtr 352 ∗
          A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          memRegion (s0.sp - 1392#64) 336 ∗ ((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗
          memRegion (s0.sp - 328#64) 224 ∗ memRegion (s0.sp - 104#64) 8 ∗
          decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
            (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
            (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
            (s0.readReg64 .x20) (s0.readReg64 .x19)) =
      chainEpochPBAt A (s0.sp - 688#64) curEpoch ∗
        v1StateJumpTablesPlacedAt ∗
        (((x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
            ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur)) ∗
          vecArgRestAt A x.st) ∗
        memRegion x.outPtr 352 ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
        (memRegion (s0.sp - 1392#64) 336 ∗ memRegion (s0.sp - 1056#64) 16) ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) remSt curSt ∗
        memRegion (s0.sp - 576#64) 240 ∗
        (((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗ memRegion (s0.sp - 328#64) 224 ∗
          memRegion (s0.sp - 104#64) 8) ∗
        decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
          (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
          (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
          (s0.readReg64 .x20) (s0.readReg64 .x19) := by ac_rfl
  rw [hreord]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono hst (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono hlow (sepConj_mono h2
      (sepConj_mono_right (sepConj_mono_left hup)))))))))

theorem SepWPpIPlaced.call_growOneChainEpoch [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (growOneStrideFullSpec A 112 8))
    (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    {x_outer : DecodeStateGhost} {s0 s : State}
    {P F R : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = v)
    (hlen : bs.length = cap.toNat * 112)
    (hptr : ptr ≠ 0#64)
    (hbound : max (2 * cap.toNat) 4 * 112 + 8 ≤ 2 ^ 63)
    (hP : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      (if cap = 0#64 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
      A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (p' : BitVec 64),
      p' ≠ 0#64 → p'.toNat % 8 = 0 →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      SepWPpIPlaced prog ret sf
        (((v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
          A.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length) ((max (2 * cap.toNat) 4 - cap.toNat) * 112) ∗
          A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
        Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R)) :
    SepWPpIPlaced prog ret s P Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R) := by
  intro hinv
  let sp_cur := s0.sp - 1392#64
  let x_go : GrowGhost := (v, cap, ptr, bs)
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - growOneStack) ∗ F
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  have hwpp : SepWPp prog ret_pc s P
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧
        Pm = (growOneStrideFullSpec A 112 8).post x_go s sm ∗ F_ext)
      (decodeStatePanicPostPlaced H_inner A x_outer s0 R) := by
    refine SepWPp.call (x := x_go) (F := F_ext) hcall hpc hrun halign hlr ?_ ?_ ?_ ?_ ?_
    · intro R' hm
      dsimp only [growOneStrideFullSpec, x_go]
      rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0, hlen, hptr, hbound⟩, ?_⟩
      rw [hP] at hm
      have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (stackAt_to_callee sp_cur growOneStack (by decide)))))))) hm
      refine Satisfies.mono (Entails.of_eq ?_) hm1
      dsimp only [sp_cur, F_ext]; ac_rfl
    · intro sm _ R' _ hpost
      dsimp only [growOneStrideFullSpec] at hpost
      exact allowPanic_not_exited hpost
    · intro sm _ hm'
      dsimp only [decodeStatePanicPostPlaced, spqrDecodeStatePlacedSpec, growOneStrideFullSpec] at hm' ⊢
      exact allowPanic_frame (allocFailedIn_trans htr) hm'
    · intro sm hpcm hrunm hspm hcsm
      exact SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩
    · intro sm R' _ hpost
      exact False.elim (not_satisfies_false_sepConj hpost)
  intro R' hm hL
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, _, hpost, hspm, hcsm, rfl⟩ | hpan_or_oom⟩ := hwpp R' hm hL
  · rw [sepConj_assoc] at hpost
    dsimp only [growOneStrideFullSpec, x_go] at hpost
    rw [hsp] at hpost
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
    rcases hpost with ⟨p', hpost⟩
    have hpost_pure : sm.mem ⊨ ⌜sm.trace = s.trace⌝ ∗ (⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0⌝ ∗
        (((v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
          A.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length) ((max (2 * cap.toNat) 4 - cap.toNat) * 112) ∗
          A.pool ∗
          (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
            (v1StateMergeStack - growOneStack) ∗
            stackAt sp_cur growOneStack)) ∗ F) ∗ R') := by
      refine Satisfies.mono (Entails.of_eq ?_) hpost
      dsimp only [sp_cur, F_ext]; ac_rfl
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
    rcases hpost_pure with ⟨htrm, ⟨hp'_ne, hp'_al⟩, hpost1⟩
    rw [hsp] at hspm
    have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (stackAt_of_callee sp_cur growOneStack (by decide)))))))))) hpost1
    obtain ⟨sf, hsteps', hout'⟩ :=
      hok sm p' hp'_ne hp'_al hpcm hrunm hspm (htr.step htrm hcsm) hcsm (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr hpan_or_oom⟩

/-! ## `ChainEpochPB` Tag Body Helpers (`send`, `recv`, `skip_field`) -/

theorem decodeState_epoch_send_call_53914_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {v20 : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (d : EpochDirectionPB)
    (optRecv : Option EpochDirectionPB)
    (rest1 : List (BitVec 8)) (limitEpoch : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt) d rest1 98).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1144#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 limitEpoch)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest1.length curSt ∗
      chainEpochPBCapOkAt A (s0.sp - 688#64) rest1.length ⟨some d, optRecv⟩ ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A x s0)
    (hloop : ∀ (d' : EpochDirectionPB) (rest2 : List (BitVec 8)) (sf : State) (P' : SepProp),
      (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt) d rest1 98).toOption =
        some (d', rest2) →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 984#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 limitEpoch →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length curSt ∗
        chainEpochPBCapOkAt A (s0.sp - 688#64) rest2.length ⟨some d', optRecv⟩ ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A x s0 →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A x s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hed_call := hc.epochDirectionMerge
  subst hP
  rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf, chainEpochPBCapOkAt_eq, optEpochDirectionPBCapOkAt_some]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced] at hpc hed_call ⊢
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 299)
  wp_steps 3
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  have hsp2c0 : s0.sp - 1392#64 + 704#64 = s0.sp - 688#64 := by bv_omega
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  refine SepWPpIPlaced.call_epochDirectionMerge hed_call iwt (s0.sp - 688#64) d
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1
    (ret_pc := (blkPl_325).base + 1156#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hx0])
    (hx1 := by simp only [arm64_norm, hsp, hsp2c0])
    (hx2 := by simp only [arm64_norm, hx29, hx29_f0])
    (hlen := by omega)
    (hP := by sep_focus) ?_ ?_
  · intro s1 d' rest2 hed hle2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 984#64)
    wp_steps 3
    refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
      hrest1_le hrest1_suf hle2) (by sep_focus) ?_
    refine SepWP.fold (protoPqRatchetStateCapOkAt_mono (H_inner := H_inner) (A := A)
      (a := s0.sp - 1040#64) (rem1 := rest1.length) (rem2 := rest2.length) (st := curSt) hle2)
      (by sep_focus) ?_
    refine SepWP.fold (optEpochDirectionPBCapOkAt_mono (A := A) (a := s0.sp - 632#64)
      (rem1 := rest1.length) (rem2 := rest2.length) (opt := optRecv) hle2)
      (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
    exact hloop d' rest2 _ _ hed hle2 hsuf2
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
      (by simp only [arm64_norm, htr1])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by rw [chainEpochPBCapOkAt_eq, optEpochDirectionPBCapOkAt_some]; dsimp only [decodeStateLoopCommonPlaced]; ac_rfl)
  · intro s1 n d' hed hpc1 hrun1 hsp1 htr1 hcs1 hx0_ne hn_le
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2872#64)
    wp_steps 1
    wp_if hcbnz
    · refine SepWP.fold (optEpochDirectionPBCapOkAt_entails_optEpochDirectionPBAt A (s0.sp - 632#64) rest1.length optRecv)
        (by sep_focus) ?_
      have hfold := epochLoop_calleeErr_to_epochErrFrame_placed H_inner A x hrest1_le hrest1_suf rest1.length curSt ⟨some d', optRecv⟩ s0
      rw [chainEpochPBAt_eq, optEpochDirectionPBAt_some_eq] at hfold
      dsimp only [decodeStateLoopCommonPlaced] at hfold
      refine SepWP.fold hfold (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
      exact SepWPpIPlaced.of_sepWPp (decodeState_err_epoch_send_merge_53fd4_placed hc.toDecodeStateCalleeContractsPlaced x curSt ⟨some d', optRecv⟩
        n (by omega) (s1.readReg64 .x0) s0 _ _ R post hpost (herr_of_none hed)
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
        (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
        (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by ac_rfl))
    · exact absurd hcbnz hx0_ne

/-- Tag 1 (`send: Option<EpochDirection>`) in `ChainEpochPB` at `+1108..+1164`. -/
theorem decodeState_epoch_send_538f0_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {v20 : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (rest1 : List (BitVec 8)) (limitEpoch : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.send.getD default) rest1 98).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1108#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 limitEpoch)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest1.length curSt ∗
      chainEpochPBCapOkAt A (s0.sp - 688#64) rest1.length curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A x s0)
    (hloop : ∀ (d' : EpochDirectionPB) (rest2 : List (BitVec 8)) (sf : State) (P' : SepProp),
      (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.send.getD default) rest1 98).toOption = some (d', rest2) →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 984#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 limitEpoch →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length curSt ∗
        chainEpochPBCapOkAt A (s0.sp - 688#64) rest2.length { curEpoch with send := some d' } ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A x s0 →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A x s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  rcases curEpoch with ⟨_ | d, optRecv⟩
  · rw [chainEpochPBCapOkAt_eq, optEpochDirectionPBCapOkAt_none]
    dsimp only [Option.getD, decodeStatePlacedProg, decodeStatePlacedEntry] at hpc herr_of_none hloop ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1144#64)
    refine SepWP.fold (optEpochDirectionPB_none_split48 (s0.sp - 688#64)) (by sep_focus) ?_
    wp_pull_exists
    wp_steps 9
    refine SepWP.fold (epochDirectionPBCapOkAt_default_init A (s0.sp - 688#64) rest1.length)
      (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    exact decodeState_epoch_send_call_53914_placed (v20 := v20) hc x curSt default optRecv rest1 limitEpoch iwt
      hrest1_le hrest1_suf hlen_bound herr_of_none s0 _ _ R post hpost hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
      (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
      (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
      (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
      (by simp only [arm64_norm, hx29])
      (by rw [chainEpochPBCapOkAt_eq, optEpochDirectionPBCapOkAt_some]; ac_rfl)
      hloop
  · rw [chainEpochPBCapOkAt_eq, optEpochDirectionPBCapOkAt_some]
    dsimp only [Option.getD, decodeStatePlacedProg, decodeStatePlacedEntry] at hpc herr_of_none hloop ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1144#64)
    refine SepWP.fold (epochDirectionPBCapOkAt_expose_cap A (s0.sp - 688#64) rest1.length d)
      (by sep_focus) ?_
    wp_pull_exists
    rename_i cap1
    wp_focus_pure; rintro ⟨hcap, hcap_lt⟩
    have hcmn : (cap1 + 1#64 != 0#64) = true := by
      rw [bne_iff_ne, ← beq_eq_false_iff_ne, Bool.eq_false_iff]
      exact cap_add_one_beq_zero_false hcap_lt
    wp_steps 3
    refine SepWP.fold (epochDirectionPBCapOkAt_fold_cap A (s0.sp - 688#64) cap1 rest1.length d hcap)
      (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, hcmn]) (by simp only [arm64_norm, hrun])
    exact decodeState_epoch_send_call_53914_placed (v20 := v20) hc x curSt d optRecv rest1 limitEpoch iwt
      hrest1_le hrest1_suf hlen_bound herr_of_none s0 _ _ R post hpost hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hcmn])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
      (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
      (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
      (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
      (by simp only [arm64_norm, hx29])
      (by rw [chainEpochPBCapOkAt_eq, optEpochDirectionPBCapOkAt_some]; ac_rfl)
      hloop

theorem decodeState_epoch_recv_call_538dc_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {v20 : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (optSend : Option EpochDirectionPB)
    (d : EpochDirectionPB)
    (rest1 : List (BitVec 8)) (limitEpoch : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt) d rest1 98).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1088#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 limitEpoch)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest1.length curSt ∗
      chainEpochPBCapOkAt A (s0.sp - 688#64) rest1.length ⟨optSend, some d⟩ ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A x s0)
    (hloop : ∀ (d' : EpochDirectionPB) (rest2 : List (BitVec 8)) (sf : State) (P' : SepProp),
      (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt) d rest1 98).toOption =
        some (d', rest2) →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 984#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 limitEpoch →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length curSt ∗
        chainEpochPBCapOkAt A (s0.sp - 688#64) rest2.length ⟨optSend, some d'⟩ ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A x s0 →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A x s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hed_call := hc.epochDirectionMerge
  subst hP
  rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf, chainEpochPBCapOkAt_eq, optEpochDirectionPBCapOkAt_some]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced] at hpc hed_call ⊢
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 299)
  wp_steps 3
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  have hx25_38 : s0.sp - 688#64 + 56#64 = s0.sp - 632#64 := by bv_omega
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  refine SepWPpIPlaced.call_epochDirectionMerge hed_call iwt (s0.sp - 632#64) d
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1
    (ret_pc := (blkPl_325).base + 1100#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hx0])
    (hx1 := by simp only [arm64_norm, hx25, hx25_38])
    (hx2 := by simp only [arm64_norm, hx29, hx29_f0])
    (hlen := by omega)
    (hP := by sep_focus) ?_ ?_
  · intro s1 d' rest2 hed hle2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 984#64)
    wp_steps 3
    refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
      hrest1_le hrest1_suf hle2) (by sep_focus) ?_
    refine SepWP.fold (protoPqRatchetStateCapOkAt_mono (H_inner := H_inner) (A := A)
      (a := s0.sp - 1040#64) (rem1 := rest1.length) (rem2 := rest2.length) (st := curSt) hle2)
      (by sep_focus) ?_
    refine SepWP.fold (optEpochDirectionPBCapOkAt_mono (A := A) (a := s0.sp - 688#64)
      (rem1 := rest1.length) (rem2 := rest2.length) (opt := optSend) hle2)
      (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
    exact hloop d' rest2 _ _ hed hle2 hsuf2
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
      (by simp only [arm64_norm, htr1])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by rw [chainEpochPBCapOkAt_eq, optEpochDirectionPBCapOkAt_some]; dsimp only [decodeStateLoopCommonPlaced]; ac_rfl)
  · intro s1 n d' hed hpc1 hrun1 hsp1 htr1 hcs1 hx0_ne hn_le
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 2896#64)
    wp_steps 1
    wp_if hcbz
    · exact absurd hcbz hx0_ne
    · wp_steps 1
      refine SepWP.fold (optEpochDirectionPBCapOkAt_entails_optEpochDirectionPBAt A (s0.sp - 688#64) rest1.length optSend)
        (by sep_focus) ?_
      have hfold := epochLoop_calleeErr_to_epochErrFrame_placed H_inner A x hrest1_le hrest1_suf rest1.length curSt ⟨optSend, some d'⟩ s0
      rw [chainEpochPBAt_eq, optEpochDirectionPBAt_some_eq] at hfold
      dsimp only [decodeStateLoopCommonPlaced] at hfold
      refine SepWP.fold hfold (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
      exact SepWPpIPlaced.of_sepWPp (decodeState_err_epoch_recv_merge_53fec_placed hc.toDecodeStateCalleeContractsPlaced x curSt ⟨optSend, some d'⟩
        n (by omega) (s1.readReg64 .x0) s0 _ _ R post hpost (herr_of_none hed)
        (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
        (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
        (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by ac_rfl))

/-- Tag 2 (`recv: Option<EpochDirection>`) in `ChainEpochPB` at `+1052..+1104`, `+1160..+1164`. -/
theorem decodeState_epoch_recv_538b8_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {v20 : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (rest1 : List (BitVec 8)) (limitEpoch : Nat) (iwt : WireType)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.recv.getD default) rest1 98).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1052#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 limitEpoch)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest1.length curSt ∗
      chainEpochPBCapOkAt A (s0.sp - 688#64) rest1.length curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A x s0)
    (hloop : ∀ (d' : EpochDirectionPB) (rest2 : List (BitVec 8)) (sf : State) (P' : SepProp),
      (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto iwt)
        (curEpoch.recv.getD default) rest1 98).toOption = some (d', rest2) →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 984#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 limitEpoch →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length curSt ∗
        chainEpochPBCapOkAt A (s0.sp - 688#64) rest2.length { curEpoch with recv := some d' } ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A x s0 →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A x s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  rcases curEpoch with ⟨optSend, _ | d⟩
  · rw [chainEpochPBCapOkAt_eq, optEpochDirectionPBCapOkAt_none]
    dsimp only [Option.getD, decodeStatePlacedProg, decodeStatePlacedEntry] at hpc herr_of_none hloop ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1088#64)
    refine SepWP.fold (optEpochDirectionPB_none_split48 (s0.sp - 632#64)) (by sep_focus) ?_
    wp_pull_exists
    wp_steps 9
    refine SepWP.fold (epochDirectionPBCapOkAt_default_init A (s0.sp - 632#64) rest1.length)
      (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    exact decodeState_epoch_recv_call_538dc_placed (v20 := v20) hc x curSt optSend default rest1 limitEpoch iwt
      hrest1_le hrest1_suf hlen_bound herr_of_none s0 _ _ R post hpost hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
      (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
      (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
      (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
      (by simp only [arm64_norm, hx29])
      (by rw [chainEpochPBCapOkAt_eq, optEpochDirectionPBCapOkAt_some]; ac_rfl)
      hloop
  · rw [chainEpochPBCapOkAt_eq, optEpochDirectionPBCapOkAt_some]
    dsimp only [Option.getD, decodeStatePlacedProg, decodeStatePlacedEntry] at hpc herr_of_none hloop ⊢
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1088#64)
    refine SepWP.fold (epochDirectionPBCapOkAt_expose_cap A (s0.sp - 632#64) rest1.length d)
      (by sep_focus) ?_
    wp_pull_exists
    rename_i cap1
    wp_focus_pure; rintro ⟨hcap, hcap_lt⟩
    have hcmn : (cap1 + 1#64 != 0#64) = true := by
      rw [bne_iff_ne, ← beq_eq_false_iff_ne, Bool.eq_false_iff]
      exact cap_add_one_beq_zero_false hcap_lt
    wp_steps 3
    refine SepWP.fold (epochDirectionPBCapOkAt_fold_cap A (s0.sp - 632#64) cap1 rest1.length d hcap)
      (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, hcmn]) (by simp only [arm64_norm, hrun])
    exact decodeState_epoch_recv_call_538dc_placed (v20 := v20) hc x curSt optSend d rest1 limitEpoch iwt
      hrest1_le hrest1_suf hlen_bound herr_of_none s0 _ _ R post hpost hs0A
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hcmn])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx0])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
      (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
      (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
      (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
      (by simp only [arm64_norm, hx29])
      (by rw [chainEpochPBCapOkAt_eq, optEpochDirectionPBCapOkAt_some]; ac_rfl)
      hloop

/-- Unknown tag (`skip_field(depth=98)`) in `ChainEpochPB` at `+964..+980`. -/
theorem decodeState_epoch_skip_53860_placed [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {v20 : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlaced H_inner A ext)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (rest1 : List (BitVec 8)) (limitEpoch tag : Nat) (iwt : WireType)
    (htag : 1 ≤ tag ∧ tag < 2 ^ 32)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none : skipField (2 * rest1.length + 2) 98 tag iwt rest1 = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePostPlaced H_inner A x s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 964#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : BitVec.setWidth 8 (s.readReg64 .x0) = BitVec.ofNat 8 iwt.toNat)
    (hx1 : BitVec.setWidth 32 (s.readReg64 .x1) = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 limitEpoch)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest1.length curSt ∗
      chainEpochPBCapOkAt A (s0.sp - 688#64) rest1.length curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A x s0)
    (hloop : ∀ (rest2 : List (BitVec 8)) (sf : State) (P' : SepProp),
      skipField (2 * rest1.length + 2) 98 tag iwt rest1 = some rest2 →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = decodeStatePlacedEntry + 984#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 limitEpoch →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length curSt ∗
        chainEpochPBCapOkAt A (s0.sp - 688#64) rest2.length curEpoch ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommonPlaced A x s0 →
      SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPostPlaced H_inner A x s0 R)) :
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPostPlaced H_inner A x s0 R) := by
  have hsf_call := hc.skipField3
  subst hP
  rw [sliceCursorAfter_eq_split hrest1_le hrest1_suf]
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, decodeStateLoopCommonPlaced] at hpc hsf_call ⊢
  apply SepWPpIPlaced.of_sepWP (mid := lsmpl.base 263)
  wp_steps 3
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  have hx29_f0 : s0.sp - 96#64 - 240#64 = s0.sp - 336#64 := by bv_omega
  refine SepWPpIPlaced.call_skipField3 hsf_call iwt tag 98
    (s0.sp - 336#64) (s0.sp - 1056#64)
    (x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - rest1.length)) rest1
    (ret_pc := (blkPl_325).base + 976#64)
    (hpc := by simp only [arm64_norm]) (hrun := by simp only [arm64_norm, hrun])
    (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
    (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
    (hx0 := by simp only [arm64_norm, hx0]) (hx1 := by simp only [arm64_norm, hx1])
    (htag := htag.2) (hx2 := by simp only [arm64_norm, hx29, hx29_f0])
    (hx3 := by simp only [arm64_norm]) (hdepth := by decide) (hlen := by omega)
    (hP := by sep_focus) ?_ ?_
  · intro s1 rest2 hsf hle2 hsuf2 hpc1 hrun1 hsp1 htr1 hcs1 hx0_0
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_0 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 984#64)
    wp_steps 2
    refine SepWP.fold (sliceCursorAfter_join (slot := s0.sp - 1056#64) (ptr := x.st.ptr)
      hrest1_le hrest1_suf hle2) (by sep_focus) ?_
    refine SepWP.fold (protoPqRatchetStateCapOkAt_mono (H_inner := H_inner) (A := A)
      (a := s0.sp - 1040#64) (rem1 := rest1.length) (rem2 := rest2.length) (st := curSt) hle2)
      (by sep_focus) ?_
    refine SepWP.fold (chainEpochPBCapOkAt_mono (A := A) (a := s0.sp - 688#64)
      (rem1 := rest1.length) (rem2 := rest2.length) (ep := curEpoch) hle2)
      (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, hx0_0]) (by simp only [arm64_norm, hrun1])
    exact hloop rest2 _ _ hsf hle2 hsuf2
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hx0_0])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
      (by simp only [arm64_norm, htr1])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by dsimp only [decodeStateLoopCommonPlaced]; ac_rfl)
  · intro s1 hsf hpc1 hrun1 hsp1 htr1 hcs1 hx0_ne
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx0_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1
    have hcbz : (s1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have hcbnz : (s1.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    apply SepWPpIPlaced.of_sepWP (mid := (blkPl_325).base + 1916#64)
    wp_steps 2
    refine SepWP.fold (chainEpochPBCapOkAt_entails_chainEpochPBAt A (s0.sp - 688#64) rest1.length curEpoch)
      (by sep_focus) ?_
    have hfold := epochLoop_calleeErr_to_epochErrFrame_placed H_inner A x hrest1_le hrest1_suf rest1.length curSt curEpoch s0
    dsimp only [decodeStateLoopCommonPlaced] at hfold
    refine SepWP.fold hfold (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, hcbz, hcbnz]) (by simp only [arm64_norm, hrun1])
    exact SepWPpIPlaced.of_sepWPp (decodeState_err_drop_epoch_53c18_placed hc x curSt curEpoch 0 (by decide)
      (s1.readReg64 (Reg.gpr 0#5)) s0 _ _ R post hpost (herr_of_none hsf)
      (by dsimp only [decodeStatePlacedEntry]; simp only [arm64_norm, hcbz, hcbnz])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) hs0A
      (by simp only [arm64_norm, htr1]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm]) (by ac_rfl))

end CryptoVerification.SpqrV1.Top.DecodeState
