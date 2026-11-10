/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBase
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MessageEncodeCodeSym
import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.SepLogic.WPp

/-!
# Relocatable `[LibsignalPlacement]` Callee-Saved & Call Helpers for `unchunked` `message::encode`

Defines placed contract propositions, `UnchunkedEncodeCalleeSavedPlaced`, and 64-byte-frame
`Program` call wrappers for `EkSentCt1Received::encode` and `Ct1Sent::encode`.
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
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Auth

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

def EkSentCt1ReceivedEncode1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_155 (Rust.withPanics ext)) (blkPl_155).base (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodePinnedSpec A))
def EkSentCt1ReceivedEncode1PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_155 (Rust.withPanics ext)) (blkPl_155).base (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodeSpec A))
def EkSentCt1ReceivedEncode1PinnedPlacedOkX [LibsignalPlacement] (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_155 (Rust.withPanics ext)) (blkPl_155).base ((withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodePinnedSpecX A)).inImage img)
def EkSentCt1ReceivedEncode1PlacedOkX [LibsignalPlacement] (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_155 (Rust.withPanics ext)) (blkPl_155).base ((withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodeSpecX A)).inImage img)
def EkSentCt1ReceivedEncode2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_318 (Rust.withPanics ext)) (blkPl_318).base (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodePinnedSpec A))
def EkSentCt1ReceivedEncode2PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_318 (Rust.withPanics ext)) (blkPl_318).base (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodeSpec A))
def EkSentCt1ReceivedEncode2PinnedPlacedOkX [LibsignalPlacement] (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_318 (Rust.withPanics ext)) (blkPl_318).base ((withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodePinnedSpecX A)).inImage img)
def EkSentCt1ReceivedEncode2PlacedOkX [LibsignalPlacement] (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_318 (Rust.withPanics ext)) (blkPl_318).base ((withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodeSpecX A)).inImage img)

def Ct1SentEncode1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_156 (Rust.withPanics ext)) (blkPl_156).base (withLsCodeLoaded lsmpl (ct1SentEncodePinnedSpec A))
def Ct1SentEncode1PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_156 (Rust.withPanics ext)) (blkPl_156).base (withLsCodeLoaded lsmpl (ct1SentEncodeSpec A))
def Ct1SentEncode1PinnedPlacedOkX [LibsignalPlacement] (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_156 (Rust.withPanics ext)) (blkPl_156).base ((withLsCodeLoaded lsmpl (ct1SentEncodePinnedSpecX A)).inImage img)
def Ct1SentEncode1PlacedOkX [LibsignalPlacement] (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_156 (Rust.withPanics ext)) (blkPl_156).base ((withLsCodeLoaded lsmpl (ct1SentEncodeSpecX A)).inImage img)
def Ct1SentEncode2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_319 (Rust.withPanics ext)) (blkPl_319).base (withLsCodeLoaded lsmpl (ct1SentEncodePinnedSpec A))
def Ct1SentEncode2PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_319 (Rust.withPanics ext)) (blkPl_319).base (withLsCodeLoaded lsmpl (ct1SentEncodeSpec A))
def Ct1SentEncode2PinnedPlacedOkX [LibsignalPlacement] (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_319 (Rust.withPanics ext)) (blkPl_319).base ((withLsCodeLoaded lsmpl (ct1SentEncodePinnedSpecX A)).inImage img)
def Ct1SentEncode2PlacedOkX [LibsignalPlacement] (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_319 (Rust.withPanics ext)) (blkPl_319).base ((withLsCodeLoaded lsmpl (ct1SentEncodeSpecX A)).inImage img)

def UnchunkedEncodeCalleeSavedPlaced (s0 s : State) : Prop :=
  s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) ∧
  s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) ∧
  s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
  s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
  s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0 ∧
  StepInvPlaced s0 s

theorem UnchunkedEncodeCalleeSavedPlaced.refl (s0 : State) : UnchunkedEncodeCalleeSavedPlaced s0 s0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, StepInvPlaced.refl s0⟩

theorem UnchunkedEncodeCalleeSavedPlaced.trans {s0 s1 s2 : State}
    (h01 : UnchunkedEncodeCalleeSavedPlaced s0 s1) (h12 : UnchunkedEncodeCalleeSavedPlaced s1 s2) :
    UnchunkedEncodeCalleeSavedPlaced s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
    h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
    h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1,
    h01.2.2.2.2.2.2.trans h12.2.2.2.2.2.2⟩

theorem UnchunkedEncodeCalleeSavedPlaced.of_calleeSavedPreserved {s1 s2 : State}
    (hcs : CalleeSavedPreserved s1 s2) (hinv : StepInvPlaced s1 s2) : UnchunkedEncodeCalleeSavedPlaced s1 s2 :=
  ⟨hcs.2.2.2.2.2.1, hcs.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.1,
    hcs.2.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.2.1,
    hcs.2.2.2.2.2.2.2.2.2.2.2, hinv⟩

theorem UnchunkedEncodeCalleeSavedPlaced.step {s0 s1 s2 : State}
    (h01 : UnchunkedEncodeCalleeSavedPlaced s0 s1)
    (hx24 : s2.readReg64 (Reg.gpr 24#5) = s1.readReg64 (Reg.gpr 24#5))
    (hx25 : s2.readReg64 (Reg.gpr 25#5) = s1.readReg64 (Reg.gpr 25#5))
    (hx26 : s2.readReg64 (Reg.gpr 26#5) = s1.readReg64 (Reg.gpr 26#5))
    (hx27 : s2.readReg64 (Reg.gpr 27#5) = s1.readReg64 (Reg.gpr 27#5))
    (hx28 : s2.readReg64 (Reg.gpr 28#5) = s1.readReg64 (Reg.gpr 28#5))
    (hinv : StepInvPlaced s1 s2)
    (hvregs : calleeSavedVRegs s2 = calleeSavedVRegs s1 := by simp only [arm64_norm]) :
    UnchunkedEncodeCalleeSavedPlaced s0 s2 :=
  h01.trans ⟨hx24, hx25, hx26, hx27, hx28, hvregs, hinv⟩

def withUnchunkedEncodeCSPlaced {α : Type} (s0 : State) (spec : Spec α) : Spec α where
  pre := fun x s => ⌜UnchunkedEncodeCalleeSavedPlaced s0 s⌝ ∗ spec.pre x s
  post := spec.post
  onPanic := spec.onPanic
  onExit := spec.onExit
  onOom := spec.onOom

theorem subroutine_ok_withLsCodeLoaded_unchunked [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl spec) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s hpc hrun hpre.2 hsp fun _ hout => hout

theorem subroutine_ok_withUnchunkedEncodeCSPlaced {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (s0 : State) (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withUnchunkedEncodeCSPlaced s0 spec) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  rw [withUnchunkedEncodeCSPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s hpc hrun hpre.2 hsp fun _ hout => hout

theorem subroutine_ok_withUnchunkedEncodeCSPlaced_x {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (img : Obj.Image) (s0 : State) (hinv0 : ImgCallInv img s0)
    (h : subroutine_ok prog entry (spec.inImage img)) :
    subroutine_ok prog entry (withUnchunkedEncodeCSPlaced s0 spec) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  rw [withUnchunkedEncodeCSPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  have hpre' : s.mem ⊨ (spec.inImage img).pre x s ∗ R := by
    rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpre.1.2.2.2.2.2.2.1 img hinv0, hpre.2⟩
  exact h.mono_outcome x R s hpc hrun hpre' hsp fun _ hout => hout

theorem subroutine_ok_withUnchunkedEncodeCSPlaced_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {entry : BitVec 64} {spec : Spec α} (s0 : State) (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (h : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec)) :
    subroutine_ok prog entry (withUnchunkedEncodeCSPlaced s0 spec) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  rw [withUnchunkedEncodeCSPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  have hpre' : s.mem ⊨ (withLsCodeLoaded lsmpl spec).pre x s ∗ R := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl0.of_keepsFrozen hpre.1.2.2.2.2.2.2.2, hpre.2⟩
  exact h.mono_outcome x R s hpc hrun hpre' hsp fun _ hout => hout

theorem subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α} (s0 : State) (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hcallee : subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withUnchunkedEncodeCSPlaced s0 spec) := by
  refine subroutine_ok_mono
    (ls_subroutine_ok_cl_of_block (callerProg := callerProg) hcallee hi hj hj_unmut)
    (fun _ s _ hpre => ?_) (fun _ _ _ _ hpost => ?_)
  · dsimp only [withUnchunkedEncodeCSPlaced, withLsCl] at hpre ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl0.of_keepsFrozen hpre.1.2.2.2.2.2.2.2, hpre.2⟩
  · dsimp only [withUnchunkedEncodeCSPlaced, withLsCl] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2


theorem step_unchunked_memcpy_call_placed {prog : Program}
    {call_pc : BitVec 64}
    (hmemcpy : subroutine_ok prog call_pc sessionMemcpyRegionSpec)
    (dst src sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    {s0 s : State} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  refine SepWPp.call_cs_placed (x := (dst, src, bs)) (F := F)
    hmemcpy hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [sessionMemcpyRegionSpec, memcpyRegionSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩; convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [sessionMemcpyRegionSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm; simp only [sessionMemcpyRegionSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (UnchunkedEncodeCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))
    exact Entails.of_eq (by ac_rfl)

theorem step_unchunked_encode_varint_call_placed {prog : Program} {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    (A : RustAlloc)
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok prog call_pc
      (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (val v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length + (CryptoVerification.LibsignalProtoCodec.encodeVarint val).length ≤ curCap.toNat ∨
      curBs.length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (CryptoVerification.LibsignalProtoCodec.encodeVarint val).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp prog ret sm
        ((vecU8At A v nextCap nextPtr (curBs ++ CryptoVerification.LibsignalProtoCodec.encodeVarint val) ∗ A.pool ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  refine SepWPp.call_cs_placed (x := EncodeVarintGhost.mk val v curCap curPtr curBs)
    (F := memRegion (sp - 64#64 - BitVec.ofNat 64 (authEncodeStackOf resStack)) 64 ∗ F)
    henc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP, stackAt_authEncode_eq_encodeVarint64 hres (sp - 64#64)] at hm
    simp only [withUnchunkedEncodeCSPlaced, encodeVarintFitSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hlen_lt⟩, ?_⟩; convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withUnchunkedEncodeCSPlaced, encodeVarintFitSpecOf, encodeVarintSpec, encodeVarintSpecOf,
      msgEncodeOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm; exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withUnchunkedEncodeCSPlaced, encodeVarintFitSpecOf, encodeVarintSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hge, hpres⟩ => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm nextCap nextPtr hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (UnchunkedEncodeCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)) hge hpres)
    rw [stackAt_authEncode_eq_encodeVarint64 hres (sp - 64#64)]
    exact Entails.of_eq (by ac_rfl)

theorem step_unchunked_do_reserve2_call_placed {prog : Program} {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    (A : RustAlloc)
    {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok prog call_pc
      (withUnchunkedEncodeCSPlaced s0 (doReserve2SpecOf resStack A)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (additional : Nat)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((vecU8At A v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)) newPtr curBs ∗
          A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  have hres64 : resStack + 48 + 64 < 2 ^ 64 := by omega
  refine SepWPp.call_cs_placed (x := DoReserveCall.mk v curCap curPtr curBs additional)
    (F := memRegion (sp - 64#64 - BitVec.ofNat 64 (authEncodeStackOf resStack)) 64 ∗
          memRegion (sp - 64#64 - BitVec.ofNat 64 (0x30 + resStack)) 48 ∗ F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_authEncode_eq_encodeVarint64 hres (sp - 64#64),
      stackAt_encodeVarint_eq_doReserve64 hres64 (sp - 64#64)] at hm
    simp only [withUnchunkedEncodeCSPlaced, doReserve2SpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hx2, hbound⟩, ?_⟩; convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withUnchunkedEncodeCSPlaced, doReserve2SpecOf, doReserveSpec, msgEncodeOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm; exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm; dsimp only [withUnchunkedEncodeCSPlaced, doReserve2SpecOf]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]; refine SepWPp.exists_elim fun newPtr => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (UnchunkedEncodeCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_authEncode_eq_encodeVarint64 hres (sp - 64#64),
      stackAt_encodeVarint_eq_doReserve64 hres64 (sp - 64#64)]
    exact Entails.of_eq (by ac_rfl)

theorem step_unchunked_do_reserve7_call_placed {prog : Program} {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    (A : RustAlloc)
    {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok prog call_pc
      (withUnchunkedEncodeCSPlaced s0 (doReserveSpecOf resStack A)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (additional : Nat)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional) (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64) (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((vecU8At A v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)) newPtr curBs ∗
          A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  have hres64 : resStack + 48 + 64 < 2 ^ 64 := by omega
  refine SepWPp.call_cs_placed (x := DoReserveCall.mk v curCap curPtr curBs additional)
    (F := memRegion (sp - 64#64 - BitVec.ofNat 64 (authEncodeStackOf resStack)) 64 ∗
          memRegion (sp - 64#64 - BitVec.ofNat 64 (0x30 + resStack)) 48 ∗ F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_authEncode_eq_encodeVarint64 hres (sp - 64#64),
      stackAt_encodeVarint_eq_doReserve64 hres64 (sp - 64#64)] at hm
    simp only [withUnchunkedEncodeCSPlaced, doReserveSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hx2, hx3, hx4, hbound⟩, ?_⟩; convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withUnchunkedEncodeCSPlaced, doReserveSpecOf, doReserveSpec, msgEncodeOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm; exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm; dsimp only [withUnchunkedEncodeCSPlaced, doReserveSpecOf]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]; refine SepWPp.exists_elim fun newPtr => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (UnchunkedEncodeCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_authEncode_eq_encodeVarint64 hres (sp - 64#64),
      stackAt_encodeVarint_eq_doReserve64 hres64 (sp - 64#64)]
    exact Entails.of_eq (by ac_rfl)

theorem step_unchunked_auth_encode_call_placed {prog : Program} {resStack : Nat}
    (A : RustAlloc)
    {call_pc : BitVec 64} {s0 s : State}
    (hauthEnc : subroutine_ok prog call_pc
      (withUnchunkedEncodeCSPlaced s0 (authEncodePinnedSpecOf resStack A)))
    (authA : BitVec 64) (gAuth : AuthenticatorPBGhost) (auth : AuthenticatorPB)
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hlen_fit : curBs.length + (encodeAuthMsg auth).length ≤ curCap.toNat ∨
      curBs.length + (encodeAuthMsg auth).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = authA) (hx1 : s.readReg64 .x1 = v)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (authenticatorPBPinnedAt A gAuth authA auth ∗
      vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeAuthMsg auth).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp prog ret sm
        ((authenticatorPBPinnedAt A gAuth authA auth ∗
          vecU8At A v nextCap nextPtr (curBs ++ encodeAuthMsg auth) ∗ A.pool ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  refine SepWPp.call_cs_placed (x := AuthEncodePinnedGhost.mk authA gAuth auth v curCap curPtr curBs)
    (F := F) hauthEnc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [withUnchunkedEncodeCSPlaced, authEncodePinnedSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hlen_fit⟩, ?_⟩; convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withUnchunkedEncodeCSPlaced, authEncodePinnedSpecOf, msgEncodeOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm; exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm; dsimp only [withUnchunkedEncodeCSPlaced, authEncodePinnedSpecOf]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun nextCap => SepWPp.exists_elim fun nextPtr => ?_
    rw [sepConj_left_comm (authenticatorPBPinnedAt A gAuth authA auth)]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hpure => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm nextCap nextPtr hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (UnchunkedEncodeCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)) hpure.1 hpure.2)
    exact Entails.of_eq (by ac_rfl)

theorem step_ekSentCt1Received_encoded_len_call_placed {prog : Program} {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    (A : RustAlloc)
    {call_pc : BitVec 64} {s0 s : State}
    (hencLen : subroutine_ok prog call_pc
      (withUnchunkedEncodeCSPlaced s0 (ekSentCt1ReceivedEncodedLenPinnedSpec A)))
    (g : Unchunked4PBGhost) (msgA sp ret_pc : BitVec 64) (m : V1State.Unchunked.EkSentCt1Received)
    (hfit : ekSentCt1ReceivedPBEncodedLen m < 2 ^ 64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = msgA) (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (ekSentCt1ReceivedPBPinnedAt A g msgA m ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen m) →
      CalleeSavedPreserved s sm → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((ekSentCt1ReceivedPBPinnedAt A g msgA m ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  refine SepWPp.call_cs_placed (x := PinnedEncLenGhost.mk msgA g m)
    (F := memRegion (sp - 64#64 - BitVec.ofNat 64 (authEncodeStackOf resStack))
            (authEncodeStackOf resStack - 16) ∗ F)
    hencLen hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_authEncode_eq_encodedLen hres (sp - 64#64)] at hm
    simp only [withUnchunkedEncodeCSPlaced, ekSentCt1ReceivedEncodedLenPinnedSpec,
      unchunked4EncodedLenPinnedSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hfit⟩, ?_⟩; convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withUnchunkedEncodeCSPlaced, ekSentCt1ReceivedEncodedLenPinnedSpec,
      unchunked4EncodedLenPinnedSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withUnchunkedEncodeCSPlaced, ekSentCt1ReceivedEncodedLenPinnedSpec, unchunked4EncodedLenPinnedSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hx0m hcsm
        (hcs.trans (UnchunkedEncodeCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_authEncode_eq_encodedLen hres (sp - 64#64)]
    exact Entails.of_eq (by ac_rfl)

theorem step_ct1Sent_encoded_len_call_placed {prog : Program} {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    (A : RustAlloc)
    {call_pc : BitVec 64} {s0 s : State}
    (hencLen : subroutine_ok prog call_pc
      (withUnchunkedEncodeCSPlaced s0 (ct1SentEncodedLenPinnedSpec A)))
    (g : Unchunked5PBGhost) (msgA sp ret_pc : BitVec 64) (m : V1State.Unchunked.Ct1Sent)
    (hfit : ct1SentPBEncodedLen m < 2 ^ 64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = msgA) (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (ct1SentPBPinnedAt A g msgA m ∗
      stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (ct1SentPBEncodedLen m) →
      CalleeSavedPreserved s sm → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((ct1SentPBPinnedAt A g msgA m ∗
          stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  refine SepWPp.call_cs_placed (x := PinnedEncLenGhost.mk msgA g m)
    (F := memRegion (sp - 64#64 - BitVec.ofNat 64 (authEncodeStackOf resStack))
            (authEncodeStackOf resStack - 16) ∗ F)
    hencLen hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_authEncode_eq_encodedLen hres (sp - 64#64)] at hm
    simp only [withUnchunkedEncodeCSPlaced, ct1SentEncodedLenPinnedSpec,
      unchunked5EncodedLenPinnedSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hfit⟩, ?_⟩; convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withUnchunkedEncodeCSPlaced, ct1SentEncodedLenPinnedSpec,
      unchunked5EncodedLenPinnedSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withUnchunkedEncodeCSPlaced, ct1SentEncodedLenPinnedSpec, unchunked5EncodedLenPinnedSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hx0m hcsm
        (hcs.trans (UnchunkedEncodeCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_authEncode_eq_encodedLen hres (sp - 64#64)]
    exact Entails.of_eq (by ac_rfl)

theorem vecU8At_expose_src_of_ne_nil_placed (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hne : bs ≠ []) (hle : bs.length ≤ cap.toNat) :
    vecU8At A a cap ptr bs = (ptr ↦ₛ bs) ∗ (vecHeader a cap ptr (BitVec.ofNat 64 bs.length) ∗
      ⌜ptr ≠ 0 ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63⌝ ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗ A.live ptr cap.toNat 1) := by
  have hpos := List.length_pos_of_ne_nil hne
  have hcap_ne : cap ≠ 0 := by intro h0; subst h0; change bs.length ≤ 0 at hle; omega
  rw [vecU8At_eq_header_sep_buf, vecU8Buf]; simp only [hcap_ne, ↓reduceIte]; ac_rfl


end CryptoVerification.SpqrV1.Prost.MessageEncode
