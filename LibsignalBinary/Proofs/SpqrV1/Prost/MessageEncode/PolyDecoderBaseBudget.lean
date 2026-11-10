/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyDecoderBase
import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Shared Base for `prost::encoding::message::encode::<PolynomialDecoder, Vec<u8>>`

Provides `VmPreserved`-strengthened `polynomialDecoderEncodedLenElemsOutSpec` and its call wrapper,
allocator event envelopes (`EncodePolyDecoder{Pinned,}Env`), `RustCliAllocBudget` and exact-capacity
specifications, and pinned-to-unpinned bridges for `PolynomialDecoder::encode` (`[local#1, 2]`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyDecoderBaseBudget

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget
  (VecU8EncodeEnv fitsEnv_vecU8EncodeEnv_of_spare)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalSpqrV1 (ProtoPolynomialDecoder)
open CryptoVerification.LibsignalTripleRatchet
  (doReserveStack doReserveStackX tripleRatchetProgAtExt)
open CryptoVerification.LibsignalTripleRatchet.Prost (StepInvPlaced sp_sub_48_aligned)
open CryptoVerification.SpqrV1.Poly
  (ProtoPolynomialDecoderGhost protoPolynomialDecoderAt protoPolynomialDecoderPinnedAt)
open CryptoVerification.SpqrV1.ProtoRepr (PinnedEncLenGhost)
open CryptoVerification.SpqrV1.Varint (encodeRepeatedStackOf)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (EncodePolyDecoderGhost EncodePolyDecoderPinnedGhost MsgEnc48CalleeSavedPlaced
   PolynomialDecoderEncodedLenPinnedGhost
   encodePolyDecoder1Name encodePolyDecoder2Name encodePolyDecoderMsg msgEnc48RepeatedStackOf
   polyDecoderElemsAt polyDecoderRestAt polyEncodedLenStack polynomialDecoderPBEncodedLen
   protoPolynomialDecoderAt_eq_exists_pinned satisfies_protoPolynomialDecoderPinnedAt_iff
   stackAt_encodeRepeated_eq_varint stackAt_varint_eq_stack16 withMsgEnc48CSPlaced)

/-! ## 1. `VmPreserved`-Strengthened `polynomialDecoderEncodedLenElemsOutSpec` & Call Wrapper -/

/-- `VmPreserved`-strengthened `polynomialDecoderEncodedLenElemsOutSpec` (`0` allocations). -/
def polynomialDecoderEncodedLenElemsOutSpec (A : RustAlloc) :
    Spec PolynomialDecoderEncodedLenPinnedGhost :=
  withVmPreserved
    (CryptoVerification.SpqrV1.Prost.MessageEncode.polynomialDecoderEncodedLenElemsOutSpec A)

theorem subroutine_ok_polyDecLenElemsOut_of_pinned {prog : Program} {entry : BitVec 64}
    {A : RustAlloc}
    (h : subroutine_ok prog entry
      (LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBaseBudget.polynomialDecoderEncodedLenPinnedSpec A)) :
    subroutine_ok prog entry (polynomialDecoderEncodedLenElemsOutSpec A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  refine h.mono_outcome x R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [
      LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBaseBudget.polynomialDecoderEncodedLenPinnedSpec,
      withVmPreserved,
      CryptoVerification.SpqrV1.Prost.MessageEncode.polynomialDecoderEncodedLenPinnedSpec] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hvm, hq⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hpure, hq⟩
    have hq' : sf.mem ⊨ protoPolynomialDecoderPinnedAt A x.g x.a x.m ∗
        (stackAt s0.sp polyEncodedLenStack ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hq
    rcases (satisfies_protoPolynomialDecoderPinnedAt_iff A x.g x.a x.m _ sf.mem).mp hq' with
      ⟨ptsElems, hpts_eq, hpts_lt, hm⟩
    dsimp only [polynomialDecoderEncodedLenElemsOutSpec, withVmPreserved,
      CryptoVerification.SpqrV1.Prost.MessageEncode.polynomialDecoderEncodedLenElemsOutSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hvm, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpure, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨ptsElems, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpts_eq, hpts_lt⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

private theorem sepWPp_call_cs_placed_noPanic {α : Type} {prog : Program}
    {entry ret ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R, s.mem ⊨ P ∗ R → s.mem ⊨ spec.pre x s ∗ (F ∗ R))
    (hexit : ∀ sf code R, sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R) → False)
    (hpanic : ∀ sf R, sf.status = .Panicked → (sf.mem ⊨ spec.onPanic x s sf ∗ R) → False)
    (hoom : ∀ sf R, sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R) → False)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running → sm.sp = s.sp →
      CalleeSavedPreserved s sm → StepInvPlaced s sm →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun (hpre R hm) hsp hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpan_mem⟩ | ⟨code, hex, hex_mem⟩ | ⟨hoom_sm, hoom_mem⟩
  · rw [hlr] at hpcm
    rw [← sepConj_assoc] at hpost
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (StepInvPlaced.of_steps hsteps) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact (hpanic sm (F ∗ R) hpan hpan_mem).elim
  · exact (hexit sm code (F ∗ R) hex hex_mem).elim
  · exact (hoom sm (F ∗ R) hoom_sm hoom_mem).elim

/-- Execute `bl PolynomialDecoder::encoded_len` on a generic `prog : Program` (polymorphic in
`Q`, `Qp`, and `oom`), propagating `VmPreserved s sm` across the 0-allocation call. -/
theorem step_msg48rep_polyDecLen_call_prog {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {prog : Program} (A : RustAlloc) {call_pc : BitVec 64} {s0 s : State}
    (hencLen : subroutine_ok prog call_pc
      (withMsgEnc48CSPlaced s0 (polynomialDecoderEncodedLenElemsOutSpec A)))
    (decA sp ret_pc : BitVec 64) (g : ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder)
    (hlen_lt : polynomialDecoderPBEncodedLen pb < 2 ^ 64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (protoPolynomialDecoderPinnedAt A g decA pb ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (ptsElems : List (BitVec 64 × List (BitVec 8))),
      ptsElems.map Prod.snd = pb.pts → pb.pts.length * 24 < 2 ^ 63 →
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb) →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp prog ret sm
        ((polyDecoderElemsAt decA g pb ptsElems ∗
          polyDecoderRestAt A decA g ptsElems ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_48_aligned halign
  have hst : stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) =
      memRegion (sp - 48#64 - BitVec.ofNat 64 (encodeRepeatedStackOf resStack)) 80 ∗
      (memRegion (sp - 48#64 - BitVec.ofNat 64 (0x30 + resStack)) (32 + resStack) ∗
        stackAt (sp - 48#64) polyEncodedLenStack) := by
    rw [stackAt_encodeRepeated_eq_varint hres (sp - 48#64),
      stackAt_varint_eq_stack16 (by omega) (sp - 48#64)]
  refine sepWPp_call_cs_placed_noPanic (x := PinnedEncLenGhost.mk decA g pb)
    (F := memRegion (sp - 48#64 - BitVec.ofNat 64 (encodeRepeatedStackOf resStack)) 80 ∗
      memRegion (sp - 48#64 - BitVec.ofNat 64 (0x30 + resStack)) (32 + resStack) ∗ F)
    hencLen hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, hst] at hm
    simp only [withMsgEnc48CSPlaced, polynomialDecoderEncodedLenElemsOutSpec, withVmPreserved,
      CryptoVerification.SpqrV1.Prost.MessageEncode.polynomialDecoderEncodedLenElemsOutSpec,
      CryptoVerification.SpqrV1.Prost.MessageEncode.polynomialDecoderEncodedLenPinnedSpec,
      hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hlen_lt⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · intro _ _ _ _ hm
    exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ _ hm
    exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ _ hm
    exact (not_satisfies_false_sepConj hm).elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withMsgEnc48CSPlaced, polynomialDecoderEncodedLenElemsOutSpec, withVmPreserved,
      CryptoVerification.SpqrV1.Prost.MessageEncode.polynomialDecoderEncodedLenElemsOutSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun hvm => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun ptsElems => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hpts_eq, hpts_lt⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm ptsElems hpts_eq hpts_lt
        hpcm hrunm hspm htrm' hx0m hcsm
        (hcs.trans (MsgEnc48CalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)) hvm)
    rw [hst]
    exact Entails.of_eq (by sep_ac_rfl)

/-! ## 2. Budget-Threaded Specifications of `encode<PolynomialDecoder>` (`[local#1, 2]`) -/

/-- Concrete allocator event envelope of `encode<PolynomialDecoder>` (pinned ghost). -/
def EncodePolyDecoderPinnedEnv (x : EncodePolyDecoderPinnedGhost)
    (evs : List AllocEvent) : Prop :=
  VecU8EncodeEnv x.cap.toNat (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length) evs

/-- Concrete allocator event envelope of `encode<PolynomialDecoder>` (unpinned ghost). -/
def EncodePolyDecoderEnv (x : EncodePolyDecoderGhost)
    (evs : List AllocEvent) : Prop :=
  VecU8EncodeEnv x.cap.toNat (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length) evs

theorem encodePolyDecoderPinnedEnv_eq_nil_of_spare
    {x : EncodePolyDecoderPinnedGhost} {evs : List AllocEvent}
    (hle : x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat)
    (h : EncodePolyDecoderPinnedEnv x evs) : evs = [] :=
  VecU8EncodeEnv.eq_nil_of_le hle h

/-- Envelope-parameterized pinned budget specification of `encode<PolynomialDecoder>`. -/
def encodePolyDecoderPinnedSpecOfEnv (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv : EncodePolyDecoderPinnedGhost → (List AllocEvent → Prop) → Prop)
    (PostEnv : EncodePolyDecoderPinnedGhost → List AllocEvent → Prop) :
    Spec (EncodePolyDecoderPinnedGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg64 .x1 = x.decA ∧
      s.readReg64 .x2 = x.v ∧
      x.dec.pts.length < 2 ^ 58 ∧
      (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat ∨
        x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length + 10 < 2 ^ 62) ∧
      (∀ Env, PreEnv x Env → FitsEnv M lim st Env)⌝ ∗
      protoPolynomialDecoderPinnedAt A.repAlloc x.g x.decA x.dec ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (msgEnc48RepeatedStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      protoPolynomialDecoderPinnedAt A.repAlloc x.g x.decA x.dec ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodePolyDecoderMsg x.tag x.dec)) ∗
      (∃∗ evs : List AllocEvent,
        ⌜PostEnv x evs ∧
          (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat →
            evs = [] ∧ VmPreserved s0 sf)⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (msgEnc48RepeatedStackOf resStack)

/-- Envelope-parameterized unpinned budget specification of `encode<PolynomialDecoder>`. -/
def encodePolyDecoderSpecOfEnv (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv : EncodePolyDecoderGhost → (List AllocEvent → Prop) → Prop)
    (PostEnv : EncodePolyDecoderGhost → List AllocEvent → Prop) :
    Spec (EncodePolyDecoderGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg64 .x1 = x.decA ∧
      s.readReg64 .x2 = x.v ∧
      x.dec.pts.length < 2 ^ 58 ∧
      (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat ∨
        x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length + 10 < 2 ^ 62) ∧
      (∀ Env, PreEnv x Env → FitsEnv M lim st Env)⌝ ∗
      protoPolynomialDecoderAt A.repAlloc x.decA x.dec ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (msgEnc48RepeatedStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      protoPolynomialDecoderAt A.repAlloc x.decA x.dec ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodePolyDecoderMsg x.tag x.dec)) ∗
      (∃∗ evs : List AllocEvent,
        ⌜PostEnv x evs ∧
          (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat →
            evs = [] ∧ VmPreserved s0 sf)⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (msgEnc48RepeatedStackOf resStack)

/-- Concrete pinned budget specification of `encode<PolynomialDecoder>`. -/
def encodePolyDecoderPinnedSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodePolyDecoderPinnedGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg64 .x1 = x.decA ∧
      s.readReg64 .x2 = x.v ∧
      x.dec.pts.length < 2 ^ 58 ∧
      (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat ∨
        x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length + 10 < 2 ^ 62) ∧
      FitsEnv M lim st (EncodePolyDecoderPinnedEnv x)⌝ ∗
      protoPolynomialDecoderPinnedAt A.repAlloc x.g x.decA x.dec ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (msgEnc48RepeatedStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      protoPolynomialDecoderPinnedAt A.repAlloc x.g x.decA x.dec ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodePolyDecoderMsg x.tag x.dec)) ∗
      (∃∗ evs : List AllocEvent,
        ⌜EncodePolyDecoderPinnedEnv x evs ∧
          (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat →
            evs = [] ∧ VmPreserved s0 sf)⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (msgEnc48RepeatedStackOf resStack)

/-- Concrete unpinned budget specification of `encode<PolynomialDecoder>`. -/
def encodePolyDecoderSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodePolyDecoderGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg64 .x1 = x.decA ∧
      s.readReg64 .x2 = x.v ∧
      x.dec.pts.length < 2 ^ 58 ∧
      (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat ∨
        x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length + 10 < 2 ^ 62) ∧
      FitsEnv M lim st (EncodePolyDecoderEnv x)⌝ ∗
      protoPolynomialDecoderAt A.repAlloc x.decA x.dec ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (msgEnc48RepeatedStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      protoPolynomialDecoderAt A.repAlloc x.decA x.dec ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodePolyDecoderMsg x.tag x.dec)) ∗
      (∃∗ evs : List AllocEvent,
        ⌜EncodePolyDecoderEnv x evs ∧
          (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat →
            evs = [] ∧ VmPreserved s0 sf)⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (msgEnc48RepeatedStackOf resStack)

/-- Exact-capacity 0-allocation (`VmPreserved`) pinned contract of `encode<PolynomialDecoder>`. -/
def encodePolyDecoderPinnedExactVmSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EncodePolyDecoderPinnedGhost where
  pre := fun x s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg64 .x1 = x.decA ∧
      s.readReg64 .x2 = x.v ∧
      x.dec.pts.length < 2 ^ 58 ∧
      x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat⌝ ∗
      protoPolynomialDecoderPinnedAt A x.g x.decA x.dec ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ stackAt s.sp (msgEnc48RepeatedStackOf resStack)
  post := fun x s0 sf =>
    ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace⌝ ∗
      protoPolynomialDecoderPinnedAt A x.g x.decA x.dec ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ encodePolyDecoderMsg x.tag x.dec) ∗
      stackAt s0.sp (msgEnc48RepeatedStackOf resStack)

abbrev encodePolyDecoderPinnedSpec {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodePolyDecoderPinnedGhost × M.σ) :=
  encodePolyDecoderPinnedSpecOf doReserveStack A lim

abbrev encodePolyDecoderSpec {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodePolyDecoderGhost × M.σ) :=
  encodePolyDecoderSpecOf doReserveStack A lim

abbrev encodePolyDecoderPinnedSpecX {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodePolyDecoderPinnedGhost × M.σ) :=
  encodePolyDecoderPinnedSpecOf doReserveStackX A lim

abbrev encodePolyDecoderSpecX {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodePolyDecoderGhost × M.σ) :=
  encodePolyDecoderSpecOf doReserveStackX A lim

/-! ## 3. Pinned-to-Unpinned & Envelope Bridges -/

theorem subroutine_ok_encodePolyDecoderPinned_of_env {resStack : Nat} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry
      (encodePolyDecoderPinnedSpecOfEnv resStack A lim
        (fun x Env => Env = EncodePolyDecoderPinnedEnv x) EncodePolyDecoderPinnedEnv)) :
    subroutine_ok prog entry (encodePolyDecoderPinnedSpecOf resStack A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [encodePolyDecoderPinnedSpecOf] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hw0, hx1, hx2, hpts, hfit, hEnv⟩, hrest⟩
  have hpreE : s0.mem ⊨
      (encodePolyDecoderPinnedSpecOfEnv resStack A lim
        (fun x Env => Env = EncodePolyDecoderPinnedEnv x) EncodePolyDecoderPinnedEnv).pre
        (x, st) s0 ∗ R := by
    dsimp only [encodePolyDecoderPinnedSpecOfEnv]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hw0, hx1, hx2, hpts, hfit, fun _ h => h ▸ hEnv⟩, hrest⟩
  exact h.mono_outcome (x, st) R s0 hpc hrun hpreE hsp fun _ hout => hout

theorem polyDecoder_post_unpinned_of_pinned_env {resStack : Nat} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PostP : EncodePolyDecoderPinnedGhost → List AllocEvent → Prop}
    {PostU : EncodePolyDecoderGhost → List AllocEvent → Prop}
    {x : EncodePolyDecoderGhost} {g : ProtoPolynomialDecoderGhost} {st : M.σ}
    {s0 sf : State} {R : SepProp}
    (hpost : ∀ evs,
      PostP ⟨x.tag, x.decA, g, x.dec, x.v, x.cap, x.ptr, x.bs⟩ evs → PostU x evs)
    {PreP PreU}
    (hq : sf.mem ⊨ (encodePolyDecoderPinnedSpecOfEnv resStack A lim PreP PostP).post
      (⟨x.tag, x.decA, g, x.dec, x.v, x.cap, x.ptr, x.bs⟩, st) s0 sf ∗ R) :
    sf.mem ⊨ (encodePolyDecoderSpecOfEnv resStack A lim PreU PostU).post (x, st) s0 sf ∗ R := by
  refine Satisfies.mono (sepConj_mono_left ?_) hq
  dsimp only [encodePolyDecoderPinnedSpecOfEnv, encodePolyDecoderSpecOfEnv]
  refine sepConj_mono (Entails.refl _)
    (sepConj_mono ?_
      (sepConj_mono (Entails.refl _)
        (sepConj_mono ?_ (Entails.refl _))))
  · rw [protoPolynomialDecoderAt_eq_exists_pinned]
    exact Entails.sepExists_right g (Entails.refl _)
  · exact Entails.sepExists_elim fun evs => Entails.sepExists_right evs
      (Entails.pure_left fun ⟨hp1, hp2⟩ => Entails.pure_right ⟨hpost evs hp1, hp2⟩ (Entails.refl _))

theorem polyDecoder_unpinned_of_pinned {resStack : Nat} {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hpinned : subroutine_ok prog entry (encodePolyDecoderPinnedSpecOf resStack A lim)) :
    subroutine_ok prog entry (encodePolyDecoderSpecOf resStack A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [encodePolyDecoderSpecOf] at hpre
  rw [protoPolynomialDecoderAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome (⟨x.tag, x.decA, g, x.dec, x.v, x.cap, x.ptr, x.bs⟩, st)
      R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    exact polyDecoder_post_unpinned_of_pinned_env
      (PreP := fun y Env => Env = EncodePolyDecoderPinnedEnv y)
      (PreU := fun y Env => Env = EncodePolyDecoderEnv y)
      (fun _ h => h)
      (by
        dsimp only [encodePolyDecoderPinnedSpecOf] at hq
        dsimp only [encodePolyDecoderPinnedSpecOfEnv]
        exact hq)
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem polyDecoder_unpinned_of_pinned_x {resStack : Nat} {M : AllocCostModel}
    {img : Obj.Image} {prog : Program} {entry : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hpinned : subroutine_ok prog entry ((encodePolyDecoderPinnedSpecOf resStack A lim).inImage img)) :
    subroutine_ok prog entry ((encodePolyDecoderSpecOf resStack A lim).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hinv0, hpre⟩ := hpre
  dsimp only [encodePolyDecoderSpecOf] at hpre
  rw [protoPolynomialDecoderAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  have hpre' : s0.mem ⊨ ((encodePolyDecoderPinnedSpecOf resStack A lim).inImage img).pre
      (⟨x.tag, x.decA, g, x.dec, x.v, x.cap, x.ptr, x.bs⟩, st) s0 ∗ R := by
    rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv0, hpre⟩
  refine hpinned.mono_outcome (⟨x.tag, x.decA, g, x.dec, x.v, x.cap, x.ptr, x.bs⟩, st)
      R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    exact polyDecoder_post_unpinned_of_pinned_env
      (PreP := fun y Env => Env = EncodePolyDecoderPinnedEnv y)
      (PreU := fun y Env => Env = EncodePolyDecoderEnv y)
      (fun _ h => h)
      (by
        dsimp only [Spec.inImage, encodePolyDecoderPinnedSpecOf] at hq
        dsimp only [encodePolyDecoderPinnedSpecOfEnv]
        exact hq)
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

def EncodePolyDecoder1PinnedOkExt {M : AllocCostModel} (b : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder1Name)
    (encodePolyDecoderPinnedSpec A lim)

def EncodePolyDecoder1OkExt {M : AllocCostModel} (b : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder1Name)
    (encodePolyDecoderSpec A lim)

def EncodePolyDecoder1PinnedOkX {M : AllocCostModel} (img : Obj.Image)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr encodePolyDecoder1Name)
    ((encodePolyDecoderPinnedSpecX A lim).inImage img)

def EncodePolyDecoder1OkX {M : AllocCostModel} (img : Obj.Image)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr encodePolyDecoder1Name)
    ((encodePolyDecoderSpecX A lim).inImage img)

def EncodePolyDecoder2PinnedOkExt {M : AllocCostModel} (b : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder2Name)
    (encodePolyDecoderPinnedSpec A lim)

def EncodePolyDecoder2OkExt {M : AllocCostModel} (b : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder2Name)
    (encodePolyDecoderSpec A lim)

def EncodePolyDecoder2PinnedOkX {M : AllocCostModel} (img : Obj.Image)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr encodePolyDecoder2Name)
    ((encodePolyDecoderPinnedSpecX A lim).inImage img)

def EncodePolyDecoder2OkX {M : AllocCostModel} (img : Obj.Image)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr encodePolyDecoder2Name)
    ((encodePolyDecoderSpecX A lim).inImage img)

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyDecoderBaseBudget
