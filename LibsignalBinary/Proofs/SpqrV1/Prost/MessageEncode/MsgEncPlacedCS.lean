/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase

/-!
# Relocatable `[LibsignalPlacement]` Callee-Saved & Call Helpers for 48-Byte `message::encode`

Defines `MsgEnc48CalleeSavedPlaced`, `withMsgEnc48CSPlaced`, and generic `Program` call and
tailcall steppers for 48-byte `message::encode` frames.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.ProtoRepr

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-- Callee-saved registers `x22..x28` untouched by 48-byte `message::encode` (`x19..x21, fp, lr`
are saved on stack), together with `StepInvPlaced s0 s`. -/
def MsgEnc48CalleeSavedPlaced (s0 s : State) : Prop :=
  s.readReg64 (Reg.gpr 22#5) = s0.readReg64 (Reg.gpr 22#5) ∧
  s.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) ∧
  s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) ∧
  s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) ∧
  s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
  s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
  s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0 ∧
  StepInvPlaced s0 s

theorem MsgEnc48CalleeSavedPlaced.refl (s0 : State) : MsgEnc48CalleeSavedPlaced s0 s0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, StepInvPlaced.refl s0⟩

theorem MsgEnc48CalleeSavedPlaced.trans {s0 s1 s2 : State}
    (h01 : MsgEnc48CalleeSavedPlaced s0 s1) (h12 : MsgEnc48CalleeSavedPlaced s1 s2) :
    MsgEnc48CalleeSavedPlaced s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
    h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
    h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.1,
    h01.2.2.2.2.2.2.2.2.trans h12.2.2.2.2.2.2.2.2⟩

theorem MsgEnc48CalleeSavedPlaced.of_calleeSavedPreserved {s1 s2 : State}
    (hcs : CalleeSavedPreserved s1 s2) (hinv : StepInvPlaced s1 s2) : MsgEnc48CalleeSavedPlaced s1 s2 :=
  ⟨hcs.2.2.2.1, hcs.2.2.2.2.1, hcs.2.2.2.2.2.1, hcs.2.2.2.2.2.2.1,
    hcs.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.2.1,
    hcs.2.2.2.2.2.2.2.2.2.2.2, hinv⟩

theorem MsgEnc48CalleeSavedPlaced.step {s0 s1 s2 : State}
    (h01 : MsgEnc48CalleeSavedPlaced s0 s1)
    (hx22 : s2.readReg64 (Reg.gpr 22#5) = s1.readReg64 (Reg.gpr 22#5))
    (hx23 : s2.readReg64 (Reg.gpr 23#5) = s1.readReg64 (Reg.gpr 23#5))
    (hx24 : s2.readReg64 (Reg.gpr 24#5) = s1.readReg64 (Reg.gpr 24#5))
    (hx25 : s2.readReg64 (Reg.gpr 25#5) = s1.readReg64 (Reg.gpr 25#5))
    (hx26 : s2.readReg64 (Reg.gpr 26#5) = s1.readReg64 (Reg.gpr 26#5))
    (hx27 : s2.readReg64 (Reg.gpr 27#5) = s1.readReg64 (Reg.gpr 27#5))
    (hx28 : s2.readReg64 (Reg.gpr 28#5) = s1.readReg64 (Reg.gpr 28#5))
    (hinv : StepInvPlaced s1 s2)
    (hvregs : calleeSavedVRegs s2 = calleeSavedVRegs s1 := by simp only [arm64_norm, calleeSavedVRegs_setPC]) :
    MsgEnc48CalleeSavedPlaced s0 s2 :=
  h01.trans ⟨hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs, hinv⟩

theorem calleeSavedPreserved_setPC_placed {s0 s : State} (pc : BitVec 64)
    (hcc : CalleeSavedPreserved s0 s) :
    CalleeSavedPreserved s0 (s.setPC pc) := by
  simpa only [CalleeSavedPreserved, State.readReg64_setPC, calleeSavedVRegs_setPC] using hcc

theorem msgEnc48CalleeSavedPlaced_setPC {s0 s : State} (pc : BitVec 64)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s) (hinv : StepInvPlaced s (s.setPC pc)) :
    MsgEnc48CalleeSavedPlaced s0 (s.setPC pc) :=
  hcs.step (State.readReg64_setPC _ _ _) (State.readReg64_setPC _ _ _)
    (State.readReg64_setPC _ _ _) (State.readReg64_setPC _ _ _)
    (State.readReg64_setPC _ _ _) (State.readReg64_setPC _ _ _)
    (State.readReg64_setPC _ _ _) hinv

def withMsgEnc48CSPlaced {α : Type} (s0 : State) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜MsgEnc48CalleeSavedPlaced s0 s⌝ ∗ spec.pre x s }

theorem subroutine_ok_withLsCodeLoaded [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl spec) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s hpc hrun hpre.2 hsp fun _ hout => hout

theorem subroutine_ok_withMsgEnc48CSPlaced_ext {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (s0 : State) (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withMsgEnc48CSPlaced s0 spec) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  rw [withMsgEnc48CSPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s hpc hrun hpre.2 hsp fun _ hout => hout

abbrev subroutine_ok_withMsgEnc48CSPlaced := @subroutine_ok_withMsgEnc48CSPlaced_ext

theorem subroutine_ok_withMsgEnc48CSPlaced_x {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (img : Obj.Image) (s0 : State) (hinv0 : ImgCallInv img s0)
    (h : subroutine_ok prog entry (spec.inImage img)) :
    subroutine_ok prog entry (withMsgEnc48CSPlaced s0 spec) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  rw [withMsgEnc48CSPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  have hpre' : s.mem ⊨ (spec.inImage img).pre x s ∗ R := by
    rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpre.1.2.2.2.2.2.2.2.2.1 img hinv0, hpre.2⟩
  exact h.mono_outcome x R s hpc hrun hpre' hsp fun _ hout => hout

theorem subroutine_ok_withMsgEnc48CSPlaced_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {entry : BitVec 64} {spec : Spec α} (s0 : State) (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (h : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec)) :
    subroutine_ok prog entry (withMsgEnc48CSPlaced s0 spec) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  rw [withMsgEnc48CSPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  refine h.mono_outcome x R s hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hcl0.of_keepsFrozen hpre.1.2.2.2.2.2.2.2.2.2, hpre.2⟩

theorem subroutine_ok_withMsgEnc48CSPlaced_placed_blk [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α} (s0 : State) (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hcallee : subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withMsgEnc48CSPlaced s0 spec) := by
  refine subroutine_ok_mono
    (ls_subroutine_ok_cl_of_block (callerProg := callerProg) hcallee hi hj hj_unmut)
    (fun _ s _ hpre => ?_) (fun _ _ _ _ hpost => ?_)
  · dsimp only [withMsgEnc48CSPlaced, withLsCl] at hpre ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl0.of_keepsFrozen hpre.1.2.2.2.2.2.2.2.2.2, hpre.2⟩
  · dsimp only [withMsgEnc48CSPlaced, withLsCl] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2

theorem subroutine_ok_withMsgEnc48CSPlaced_of_no_panic {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (hok : subroutine_ok prog entry spec)
    (_hnoPanic : ∀ x s1 sf, spec.onPanic x s1 sf = ⌜False⌝) (s0 : State) :
    subroutine_ok prog entry (withMsgEnc48CSPlaced s0 spec) :=
  subroutine_ok_withMsgEnc48CSPlaced_ext s0 hok

theorem sepWPp_mono_placed {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q1 Q2 Qp1 Qp2 : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q1 Qp1)
    (hQ : ∀ sf P_f, Q1 sf P_f → Q2 sf P_f)
    (hQp : ∀ sf P_f, Qp1 sf P_f → Qp2 sf P_f) :
    SepWPp prog ret s P Q2 Qp2 := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨h1, h2, P_f, hm', hq⟩ | ⟨hpan, P_f, hm', hqp⟩ | hoom⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨h1, h2, P_f, hm', hQ sf P_f hq⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f, hm', hQp sf P_f hqp⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

theorem step_msg48_encode_varint_call_placed {resStack : Nat} {prog : Program} (A : RustAlloc)
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok prog call_pc (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (val v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length + (CryptoVerification.LibsignalProtoCodec.encodeVarint val).length ≤ curCap.toNat ∨
      curBs.length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 48#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSavedPlaced s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (CryptoVerification.LibsignalProtoCodec.encodeVarint val).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp prog ret sm
        ((vecU8At A v nextCap nextPtr (curBs ++ CryptoVerification.LibsignalProtoCodec.encodeVarint val) ∗ A.pool ∗
          stackAt (sp - 48#64) (0x30 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_48_aligned halign
  refine SepWPp.call_cs_placed (x := EncodeVarintGhost.mk val v curCap curPtr curBs) (F := F)
    henc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [withMsgEnc48CSPlaced, encodeVarintFitSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hlen_lt⟩, ?_⟩; convert hm using 1; ac_rfl
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withMsgEnc48CSPlaced, encodeVarintFitSpecOf, encodeVarintSpec, encodeVarintSpecOf,
      msgEncOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm; exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call; rw [hsp] at hspm
    dsimp only [withMsgEnc48CSPlaced, encodeVarintFitSpecOf, encodeVarintSpecOf]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_; simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => ?_; refine SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]; refine SepWPp.pure_elim fun ⟨hge, hpres⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm nextCap nextPtr hpcm hrunm hspm htrm' hcsm
        (hcs.trans (MsgEnc48CalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)) hge hpres)


theorem step_msg48_do_reserve2_call_placed {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {prog : Program} (A : RustAlloc) {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok prog call_pc (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (additional : Nat)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 48#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((vecU8At A v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)) newPtr curBs ∗
          A.pool ∗ stackAt (sp - 48#64) (0x30 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_48_aligned halign
  refine SepWPp.call_cs_placed (x := DoReserveCall.mk v curCap curPtr curBs additional)
    (F := memRegion (sp - 48#64 - BitVec.ofNat 64 (0x30 + resStack)) 48 ∗ F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP, stackAt_encodeVarint_eq_doReserve64 hres (sp - 48#64)] at hm
    simp only [withMsgEnc48CSPlaced, doReserve2SpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hx2, hbound⟩, ?_⟩; convert hm using 1; ac_rfl
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withMsgEnc48CSPlaced, doReserve2SpecOf, doReserveSpec, msgEncOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm; exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call; rw [hsp] at hspm
    dsimp only [withMsgEnc48CSPlaced, doReserve2SpecOf]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_; simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun newPtr => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm htrm' hcsm
        (hcs.trans (MsgEnc48CalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_encodeVarint_eq_doReserve64 hres (sp - 48#64)]; exact Entails.of_eq (by ac_rfl)


theorem step_msg48_do_reserve7_call_placed {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {prog : Program} (A : RustAlloc) {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok prog call_pc (withMsgEnc48CSPlaced s0 (doReserveSpecOf resStack A)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (additional : Nat)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional) (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 48#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((vecU8At A v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)) newPtr curBs ∗
          A.pool ∗ stackAt (sp - 48#64) (0x30 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_48_aligned halign
  refine SepWPp.call_cs_placed (x := DoReserveCall.mk v curCap curPtr curBs additional)
    (F := memRegion (sp - 48#64 - BitVec.ofNat 64 (0x30 + resStack)) 48 ∗ F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP, stackAt_encodeVarint_eq_doReserve64 hres (sp - 48#64)] at hm
    simp only [withMsgEnc48CSPlaced, doReserveSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hx2, hx3, hx4, hbound⟩, ?_⟩; convert hm using 1; ac_rfl
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withMsgEnc48CSPlaced, doReserveSpecOf, doReserveSpec, msgEncOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm; exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call; rw [hsp] at hspm
    dsimp only [withMsgEnc48CSPlaced, doReserveSpecOf]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_; simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun newPtr => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm htrm' hcsm
        (hcs.trans (MsgEnc48CalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_encodeVarint_eq_doReserve64 hres (sp - 48#64)]; exact Entails.of_eq (by ac_rfl)


theorem step_msg48_encode_repeated_call_placed {resStack : Nat} {prog : Program} (A : RustAlloc)
    {call_pc : BitVec 64} {s0 s : State}
    (hencRep : subroutine_ok prog call_pc (withMsgEnc48CSPlaced s0 (encodeRepeatedSpecOf resStack A)))
    (tag : Nat) (base v curCap curPtr sp ret_pc : BitVec 64)
    (elems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8))
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 29) (helems : elems.length < 2 ^ 58)
    (hfit : curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat ∨
      curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hw0 : s.readReg32 .x0 = BitVec.ofNat 32 tag) (hx1 : s.readReg64 .x1 = base)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 elems.length) (hx3 : s.readReg64 .x3 = v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (repeatedBytesSliceAt base elems ∗ vecU8At A v curCap curPtr curBs ∗
      A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSavedPlaced s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp prog ret sm
        ((repeatedBytesSliceAt base elems ∗
          vecU8At A v nextCap nextPtr (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)) ∗
          A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_48_aligned halign
  refine SepWPp.call_cs_placed (x := EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs) (F := F)
    hencRep hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [withMsgEnc48CSPlaced, encodeRepeatedSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hw0, hx1, hx2, hx3, htag1, htag2, helems, hfit⟩, ?_⟩; convert hm using 1; ac_rfl
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withMsgEnc48CSPlaced, encodeRepeatedSpecOf, msgEncOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm; exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call; rw [hsp] at hspm
    dsimp only [withMsgEnc48CSPlaced, encodeRepeatedSpecOf]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    rw [sepConj_left_comm (repeatedBytesSliceAt base elems)]; simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => ?_; refine SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]; refine SepWPp.pure_elim fun ⟨hge, hpres⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm nextCap nextPtr hpcm hrunm hspm htrm' hcsm
        (hcs.trans (MsgEnc48CalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)) hge hpres)


theorem step_msg48_encode_varint_tailcall_placed {resStack : Nat} (hres : resStack + 96 < 2 ^ 64)
    {prog : Program} (A : RustAlloc) {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok prog call_pc (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (val v curCap curPtr sp fp lr r21 v3 r20 r19 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length + (CryptoVerification.LibsignalProtoCodec.encodeVarint val).length ≤ curCap.toNat ∨
      curBs.length + 10 < 2 ^ 62)
    {R : SepProp} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = s0.readReg64 .lr)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hcc : CalleeSavedPreserved s0 s) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (0x30 + resStack) ∗ msgEnc48SavedFrame sp fp lr r21 v3 r20 r19) ∗ F)
    (hnext : ∀ (sf : State) (nextCap nextPtr : BitVec 64),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSavedPlaced s0 sf → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (CryptoVerification.LibsignalProtoCodec.encodeVarint val).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      Q sf ((vecU8At A v nextCap nextPtr (curBs ++ CryptoVerification.LibsignalProtoCodec.encodeVarint val) ∗
        A.pool ∗ stackAt sp (msgEnc48VarintStackOf resStack)) ∗ F)) :
    SepWPp prog (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact halign
  refine SepWPp.call_cs_placed (x := EncodeVarintGhost.mk val v curCap curPtr curBs)
    (F := memRegion (sp - BitVec.ofNat 64 (msgEnc48VarintStackOf resStack)) 48 ∗ F)
    henc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    have hm0 : s.mem ⊨ (stackAt (sp - 48#64) (0x30 + resStack) ∗ msgEnc48SavedFrame sp fp lr r21 v3 r20 r19) ∗
        (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ F ∗ R') := by
      rw [hP] at hm; convert hm using 1; ac_rfl
    have hm1 : s.mem ⊨ stackAt sp (msgEnc48VarintStackOf resStack) ∗
        (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ F ∗ R') :=
      Satisfies.mono (sepConj_mono_left (stackAt_msgEnc48_varint_recombine hres sp fp lr r21 v3 r20 r19)) hm0
    rw [stackAt_msgEnc48_varint_eq_bottom hres sp] at hm1
    simp only [withMsgEnc48CSPlaced, encodeVarintFitSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hlen_lt⟩, ?_⟩; convert hm1 using 1; ac_rfl
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withMsgEnc48CSPlaced, encodeVarintFitSpecOf, encodeVarintSpec, encodeVarintSpecOf,
      msgEncOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm; exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call; rw [hsp] at hspm
    dsimp only [withMsgEnc48CSPlaced, encodeVarintFitSpecOf, encodeVarintSpecOf]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_; simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => ?_; refine SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]; refine SepWPp.pure_elim fun ⟨hge, hpres⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    have hccm : CalleeSavedPreserved s0 sm := by
      rcases hcc with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hfp, hv⟩
      rcases hcsm with ⟨h19', h20', h21', h22', h23', h24', h25', h26', h27', h28', hfp', hv'⟩
      exact ⟨h19'.trans h19, h20'.trans h20, h21'.trans h21, h22'.trans h22, h23'.trans h23,
        h24'.trans h24, h25'.trans h25, h26'.trans h26, h27'.trans h27, h28'.trans h28, hfp'.trans hfp, hv'.trans hv⟩
    refine SepWPp.weaken_pre ?_
      (SepWPp.done hpcm hrunm
        (hnext sm nextCap nextPtr hpcm hrunm hspm htrm' hccm
          (hcs.trans (MsgEnc48CalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)) hge hpres))
    rw [stackAt_msgEnc48_varint_eq_bottom hres sp]; exact Entails.of_eq (by ac_rfl)


theorem step_msg48_encode_repeated_tailcall_placed {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {prog : Program} (A : RustAlloc) {call_pc : BitVec 64} {s0 s : State}
    (hencRep : subroutine_ok prog call_pc (withMsgEnc48CSPlaced s0 (encodeRepeatedSpecOf resStack A)))
    (tag : Nat) (base v curCap curPtr sp fp lr r21 v3 r20 r19 : BitVec 64)
    (elems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8))
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 29) (helems : elems.length < 2 ^ 58)
    (hfit : curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat ∨
      curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length + 10 < 2 ^ 62)
    {R : SepProp} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = s0.readReg64 .lr)
    (hw0 : s.readReg32 .x0 = BitVec.ofNat 32 tag) (hx1 : s.readReg64 .x1 = base)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 elems.length) (hx3 : s.readReg64 .x3 = v)
    (hcc : CalleeSavedPreserved s0 s) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (repeatedBytesSliceAt base elems ∗ vecU8At A v curCap curPtr curBs ∗
      A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp fp lr r21 v3 r20 r19) ∗ F)
    (hnext : ∀ (sf : State) (nextCap nextPtr : BitVec 64),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSavedPlaced s0 sf → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      Q sf ((repeatedBytesSliceAt base elems ∗
        vecU8At A v nextCap nextPtr (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)) ∗
        A.pool ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)) :
    SepWPp prog (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact halign
  refine SepWPp.call_cs_placed (x := EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs)
    (F := memRegion (sp - BitVec.ofNat 64 (msgEnc48RepeatedStackOf resStack)) 48 ∗ F)
    hencRep hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    have hm0 : s.mem ⊨ (stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ msgEnc48SavedFrame sp fp lr r21 v3 r20 r19) ∗
        (repeatedBytesSliceAt base elems ∗ vecU8At A v curCap curPtr curBs ∗ A.pool ∗ F ∗ R') := by
      rw [hP] at hm; convert hm using 1; ac_rfl
    have hm1 : s.mem ⊨ stackAt sp (msgEnc48RepeatedStackOf resStack) ∗
        (repeatedBytesSliceAt base elems ∗ vecU8At A v curCap curPtr curBs ∗ A.pool ∗ F ∗ R') :=
      Satisfies.mono (sepConj_mono_left (stackAt_msgEnc48_repeated_recombine hres sp fp lr r21 v3 r20 r19)) hm0
    rw [stackAt_msgEnc48_repeated_eq_bottom hres sp] at hm1
    simp only [withMsgEnc48CSPlaced, encodeRepeatedSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hw0, hx1, hx2, hx3, htag1, htag2, helems, hfit⟩, ?_⟩; convert hm1 using 1; ac_rfl
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withMsgEnc48CSPlaced, encodeRepeatedSpecOf, msgEncOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm; exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call; rw [hsp] at hspm
    dsimp only [withMsgEnc48CSPlaced, encodeRepeatedSpecOf]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    rw [sepConj_left_comm (repeatedBytesSliceAt base elems)]; simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => ?_; refine SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]; refine SepWPp.pure_elim fun ⟨hge, hpres⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    have hccm : CalleeSavedPreserved s0 sm := by
      rcases hcc with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hfp, hv⟩
      rcases hcsm with ⟨h19', h20', h21', h22', h23', h24', h25', h26', h27', h28', hfp', hv'⟩
      exact ⟨h19'.trans h19, h20'.trans h20, h21'.trans h21, h22'.trans h22, h23'.trans h23,
        h24'.trans h24, h25'.trans h25, h26'.trans h26, h27'.trans h27, h28'.trans h28, hfp'.trans hfp, hv'.trans hv⟩
    refine SepWPp.weaken_pre ?_
      (SepWPp.done hpcm hrunm
        (hnext sm nextCap nextPtr hpcm hrunm hspm htrm' hccm
          (hcs.trans (MsgEnc48CalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)) hge hpres))
    rw [stackAt_msgEnc48_repeated_eq_bottom hres sp]; exact Entails.of_eq (by ac_rfl)


end CryptoVerification.SpqrV1.Prost.MessageEncode
