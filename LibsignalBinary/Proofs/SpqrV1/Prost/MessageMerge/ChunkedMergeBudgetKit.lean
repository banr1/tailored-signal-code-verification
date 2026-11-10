/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommon
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Shared Budget Combinators and `SpqrMergeLoopEnv` Kit

Reusable `SepWPpLscro` + `VmPreserved` stepping and call combinators together with
`SpqrMergeIterEnv`, `SpqrMergeLoopEnv`, and `spqrPoolAt` framing lemmas for `V1State.Chunked.*`
budget proofs.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit

open Arm64 ProofLib SepProp
open CryptoVerification.LibsignalProtoCodec (decodeVarint skipField)
open CryptoVerification.LibsignalSpqrV1 (ProtoAuthenticator)
open CryptoVerification.LibsignalTripleRatchet (withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost (BytesMergeCapOk SkipFieldGhost)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.SpqrV1.Auth (authenticatorPBCapAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge (SepWPpLscro vecU8Buf)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget
  (AuthMergeLoopEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (DecodeErrorPushMergeEnv FitsEnv.spqrMergeLoop_head FitsEnv.spqrMergeLoop_split
   SpqrMergeIterEnv SpqrMergeLoopEnv)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv SkipFieldEnv decodeVarintSliceEvents skipFieldEventsCore)

/-! ## 1. `SepWPpLscro` + `VmPreserved` & Panic-Free Call Combinators -/

/-- Panic postcondition predicate for budget-threaded `SepWPp` specs (`onPanic = ⌜False⌝`).
    Kept as a `def` (not `abbrev`) so `SepWPpLscro ... (WppPanicFalse R)` unifies `R` rigidly. -/
def WppPanicFalse (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R)

theorem wppPanicFalse_frame {R F : SepProp} {sf : State} :
    WppPanicFalse R sf ((⌜False⌝ : SepProp) ∗ F) :=
  fun hm => (not_satisfies_false_sepConj (by simpa only [sepConj_assoc] using hm)).elim

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_setPC_left (s₁ s₂ : State) (pc : BitVec 64) :
    LibsignalBinary.Heap.FdsHiFrame (s₁.setPC pc) s₂ ↔ LibsignalBinary.Heap.FdsHiFrame s₁ s₂ := by
  cases s₁; rfl

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_advancePC_left (s₁ s₂ : State) :
    LibsignalBinary.Heap.FdsHiFrame s₁.advancePC s₂ ↔ LibsignalBinary.Heap.FdsHiFrame s₁ s₂ := by
  cases s₁; rfl

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_setPState_left (s₁ s₂ : State) (ps : PState) :
    LibsignalBinary.Heap.FdsHiFrame (s₁.setPState ps) s₂ ↔
      LibsignalBinary.Heap.FdsHiFrame s₁ s₂ := by
  cases s₁; rfl

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_writeReg64_left (s₁ s₂ : State) (r : Reg) (v : BitVec 64) :
    LibsignalBinary.Heap.FdsHiFrame (s₁.writeReg64 r v) s₂ ↔
      LibsignalBinary.Heap.FdsHiFrame s₁ s₂ := by
  cases s₁; cases r <;> rfl

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_writeReg32_left (s₁ s₂ : State) (r : Reg) (v : BitVec 32) :
    LibsignalBinary.Heap.FdsHiFrame (s₁.writeReg32 r v) s₂ ↔
      LibsignalBinary.Heap.FdsHiFrame s₁ s₂ :=
  fdsHiFrame_writeReg64_left s₁ s₂ r _

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_writeReg_left (s₁ s₂ : State) (w : Width) (r : Reg) (v : BitVec 64) :
    LibsignalBinary.Heap.FdsHiFrame (s₁.writeReg w r v) s₂ ↔
      LibsignalBinary.Heap.FdsHiFrame s₁ s₂ :=
  fdsHiFrame_writeReg64_left s₁ s₂ r _

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_writeVReg128_left (s₁ s₂ : State) (i : BitVec 5) (v : BitVec 128) :
    LibsignalBinary.Heap.FdsHiFrame (s₁.writeVReg128 i v) s₂ ↔
      LibsignalBinary.Heap.FdsHiFrame s₁ s₂ := by
  cases s₁; rfl

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_writeVReg64_left (s₁ s₂ : State) (i : BitVec 5) (v : BitVec 64) :
    LibsignalBinary.Heap.FdsHiFrame (s₁.writeVReg64 i v) s₂ ↔
      LibsignalBinary.Heap.FdsHiFrame s₁ s₂ := by
  cases s₁; rfl

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_writeVReg32_left (s₁ s₂ : State) (i : BitVec 5) (v : BitVec 32) :
    LibsignalBinary.Heap.FdsHiFrame (s₁.writeVReg32 i v) s₂ ↔
      LibsignalBinary.Heap.FdsHiFrame s₁ s₂ := by
  cases s₁; rfl

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_applyWriteback_left (s₁ s₂ : State) (wb : Option (Reg × BitVec 64)) :
    LibsignalBinary.Heap.FdsHiFrame (applyWriteback s₁ wb) s₂ ↔
      LibsignalBinary.Heap.FdsHiFrame s₁ s₂ := by
  cases wb with
  | none => rfl
  | some p => exact fdsHiFrame_writeReg64_left s₁ s₂ p.1 p.2

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_setMem_left (s₁ s₂ : State) (m : Memory) :
    LibsignalBinary.Heap.FdsHiFrame (s₁.setMem m) s₂ ↔ LibsignalBinary.Heap.FdsHiFrame s₁ s₂ := by
  cases s₁; rfl

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_setFpsr_left (s₁ s₂ : State) (f : BitVec 32) :
    LibsignalBinary.Heap.FdsHiFrame (s₁.setFpsr f) s₂ ↔ LibsignalBinary.Heap.FdsHiFrame s₁ s₂ := by
  cases s₁; rfl

@[simp, arm64_norm, wp_norm]
theorem fdsHiFrame_orFpsr_left (s₁ s₂ : State) (f : BitVec 32) :
    LibsignalBinary.Heap.FdsHiFrame (s₁.orFpsr f) s₂ ↔ LibsignalBinary.Heap.FdsHiFrame s₁ s₂ := by
  cases s₁; rfl

theorem vmPreserved_setMem_same (s₁ s₂ : State) (m : Memory) :
    VmPreserved (s₁.setMem m) (s₂.setMem m) ↔
      s₂.brkStart = s₁.brkStart ∧ s₂.brk = s₁.brk ∧
      s₂.tpidrEl0 = s₁.tpidrEl0 ∧ s₂.physMemAvail = s₁.physMemAvail ∧
      LibsignalBinary.Heap.FdsHiFrame s₁ s₂ := by
  cases s₁; cases s₂
  exact ⟨fun ⟨⟨hb0, hb, htp⟩, hp, _, hfds⟩ => ⟨hb0, hb, htp, hp, hfds⟩,
         fun ⟨hb0, hb, htp, hp, hfds⟩ => ⟨⟨hb0, hb, htp⟩, hp, fun _ => rfl, hfds⟩⟩

private theorem vecU8Buf_entails_cap_lt_kit (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8Buf
  exact Entails.pure_left fun h => Entails.pure_right h.2.1 (Entails.pure_right h (Entails.refl _))

private theorem vecU8At_eq_header_sep_buf_kit (A : RustAlloc) (a cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs =
      vecHeader a cap ptr (BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8At vecU8Buf; sep_ac_rfl

private theorem vecU8At_entails_header_cap_lt_kit (A : RustAlloc) (a cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs ⊢
      ⌜cap.toNat < 2 ^ 63⌝ ∗ (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs := by
  rw [vecU8At_eq_header_sep_buf_kit, vecHeader]
  exact Entails.trans (sepConj_mono_right (vecU8Buf_entails_cap_lt_kit A cap ptr bs)) (by sep_entail)

private theorem header_buf_entails_vecU8At_kit (A : RustAlloc) (a cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A cap ptr bs ⊢ vecU8At A a cap ptr bs := by
  rw [vecU8At_eq_header_sep_buf_kit, vecHeader]; sep_entail

def authMacKeyCapAtKit (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (auth : ProtoAuthenticator) : SepProp :=
  ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
    ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A (a + 0x18#64) cap ptr auth.macKey

theorem authenticatorPBCapAt_entails_cmn_kit (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (auth : ProtoAuthenticator) :
    authenticatorPBCapAt A a bsLen auth ⊢
      ∃∗ cap_ik : BitVec 64, ∃∗ ptr_ik : BitVec 64,
        ⌜cap_ik.toNat < 2 ^ 63⌝ ∗ ⌜BytesMergeCapOk cap_ik bsLen⌝ ∗
        (a ↦₆₄ cap_ik) ∗ ((a + 8#64) ↦₆₄ ptr_ik) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
        vecU8Buf A cap_ik ptr_ik auth.rootKey ∗ authMacKeyCapAtKit A a bsLen auth := by
  unfold authenticatorPBCapAt authMacKeyCapAtKit
  rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun cap_ik => ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun ptr_ik => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro cap_ik)
  refine Entails.trans ?_ (Entails.sepExists_intro ptr_ik)
  rw [sepConj_assoc]; refine Entails.pure_left fun hcap => ?_
  refine Entails.trans (sepConj_mono_left (vecU8At_entails_header_cap_lt_kit A a cap_ik ptr_ik auth.rootKey)) ?_
  simp only [sepConj_assoc]
  exact Entails.pure_left fun hlt => Entails.pure_right hlt (Entails.pure_right hcap (Entails.refl _))

theorem cmn_entails_authenticatorPBCapAt_kit (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (auth : ProtoAuthenticator) (cap_ik ptr_ik : BitVec 64) (hcap : BytesMergeCapOk cap_ik bsLen) :
    (a ↦₆₄ cap_ik) ∗ ((a + 8#64) ↦₆₄ ptr_ik) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      vecU8Buf A cap_ik ptr_ik auth.rootKey ∗ authMacKeyCapAtKit A a bsLen auth ⊢
      authenticatorPBCapAt A a bsLen auth := by
  unfold authenticatorPBCapAt
  refine Entails.trans (Entails.of_eq (show _ =
    ((a ↦₆₄ cap_ik) ∗ ((a + 8#64) ↦₆₄ ptr_ik) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      vecU8Buf A cap_ik ptr_ik auth.rootKey) ∗ authMacKeyCapAtKit A a bsLen auth by sep_ac_rfl)) ?_
  unfold authMacKeyCapAtKit; refine sepConj_mono_left ?_
  refine Entails.trans (header_buf_entails_vecU8At_kit A a cap_ik ptr_ik auth.rootKey) ?_
  refine Entails.trans ?_ (Entails.sepExists_intro cap_ik)
  refine Entails.trans ?_ (Entails.sepExists_intro ptr_ik)
  exact Entails.pure_right hcap (Entails.refl _)

theorem sepWPpLscro_of_vm {pl : Obj.MultiPlacement} {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)} {mid ret : BitVec 64} {s : State}
    {Pre : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP (P.rebase b Hk) mid s Pre
      (fun sm Pm => VmPreserved s sm ∧
        (VmPreserved s sm → SepWPpLscro pl (P.rebase b Hk) ret sm Pm Q Qp))) :
    SepWPpLscro pl (P.rebase b Hk) ret s Pre Q Qp :=
  SepWPpLscro.of_sepWP (SepWP.mono h fun _ _ _ _ ⟨hvm, hk⟩ => hk hvm)

theorem sepWPpLscro_of_ret_vm {pl : Obj.MultiPlacement} {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)} {ret : BitVec 64} {s : State}
    {Pre : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP (P.rebase b Hk) ret s Pre
      (fun sm Pm => VmPreserved s sm ∧ (VmPreserved s sm → Q sm Pm))) :
    SepWPpLscro pl (P.rebase b Hk) ret s Pre Q Qp :=
  SepWPpLscro.of_sepWP_ret (SepWP.mono h fun _ _ _ _ ⟨hvm, hq⟩ => hq hvm)

theorem sepWPpLscro_pure_elim {pl : Obj.MultiPlacement} {prog : Program} {ret : BitVec 64}
    {s : State} {φ : Prop} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPpLscro pl prog ret s P Q Qp) :
    SepWPpLscro pl prog ret s (⌜φ⌝ ∗ P) Q Qp :=
  fun hli => SepWPp.pure_left fun hφ => h hφ hli

theorem sepWPpLscro_exists_elim {pl : Obj.MultiPlacement} {prog : Program} {ret : BitVec 64}
    {s : State} {α : Sort _} {P : α → SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ a, SepWPpLscro pl prog ret s (P a) Q Qp) :
    SepWPpLscro pl prog ret s (∃∗ a, P a) Q Qp := by
  intro hli R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨a, hma⟩
  exact h a hli R hma hL

theorem call_budget {pl : Obj.MultiPlacement} {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q : State → SepProp → Prop} {R : SepProp}
    {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {φ : Prop} {T F : SepProp}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPpLscro pl prog ret sf (spec.post x s sf ∗ F) Q (WppPanicFalse R))
    (hexit_eq : ∀ sf code, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpanic_eq : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPpLscro pl prog ret s P Q (WppPanicFalse R) :=
  SepWPpLscro.call_frame hcall hpc hrun hsp hlr hspec hφ hP
    (fun sf code _ _ hex => by rw [hexit_eq sf code] at hex; exact not_satisfies_false_sepConj hex)
    (fun sf _ => by rw [hpanic_eq sf]; exact wppPanicFalse_frame)
    hnext
    (fun sf _ _ hoom => by rw [hoom_eq sf] at hoom; exact (not_satisfies_false_sepConj hoom).elim)

theorem call_budget_lscro {pl : Obj.MultiPlacement} {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q : State → SepProp → Prop} {R : SepProp}
    {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {φ : Prop} {T F : SepProp}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPpLscro pl prog ret sf (spec.post x s sf ∗ F) Q (WppPanicFalse R))
    (hexit_eq : ∀ sf code, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpanic_eq : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPpLscro pl prog ret s P Q (WppPanicFalse R) :=
  SepWPpLscro.call_frame_lscro hcall hpc hrun hsp hlr hspec hφ hP
    (fun sf code _ _ hex => by rw [hexit_eq sf code] at hex; exact not_satisfies_false_sepConj hex)
    (fun sf _ => by rw [hpanic_eq sf]; exact wppPanicFalse_frame)
    hnext
    (fun sf _ _ hoom => by rw [hoom_eq sf] at hoom; exact (not_satisfies_false_sepConj hoom).elim)

/-! ## 2. Envelope Embedding, `FitsEnv`, & `spqrPoolAt` Helpers -/

theorem decodeErrorFromEnv_to_spqr {maxLen polyCapBound : Nat} {evs : List AllocEvent}
    (h : DecodeErrorFromEnv evs) :
    SpqrMergeIterEnv maxLen polyCapBound evs :=
  h ▸ .fromErr

theorem decodeErrorPushEnv_to_spqr {n maxLen polyCapBound : Nat} {evs : List AllocEvent}
    (hn : n ≤ 4) (h : DecodeErrorPushMergeEnv n evs) :
    SpqrMergeIterEnv maxLen polyCapBound evs :=
  .pushErr hn h

theorem decodeVarint2Env_to_spqr {bs : List (BitVec 8)} {maxLen polyCapBound : Nat}
    {evs : List AllocEvent} (h : DecodeVarint2Env bs evs) :
    SpqrMergeIterEnv maxLen polyCapBound evs := by
  unfold DecodeVarint2Env DecodeVarintSliceEnv decodeVarintSliceEvents at h
  cases hd : decodeVarint bs with
  | some _ => rw [hd] at h; subst h; exact .nil
  | none => rw [hd] at h; subst h; exact .fromErr

theorem decodeVarint2Env_eq_nil_of_some {bs : List (BitVec 8)}
    {p : BitVec 64 × List (BitVec 8)} {evs : List AllocEvent}
    (hd : decodeVarint bs = some p) (h : DecodeVarint2Env bs evs) :
    evs = [] := by
  simpa [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents, hd] using h

theorem skipFieldEnv_to_spqr {x : SkipFieldGhost} {maxLen polyCapBound : Nat}
    {evs : List AllocEvent} (h : SkipFieldEnv x evs) :
    SpqrMergeIterEnv maxLen polyCapBound evs := by
  unfold SkipFieldEnv skipFieldEventsCore at h
  cases hsk : skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs with
  | some _ => rw [hsk] at h; subst h; exact .nil
  | none => rw [hsk] at h; subst h; exact .fromErr

theorem skipFieldEnv_eq_nil_of_some {x : SkipFieldGhost} {rest : List (BitVec 8)}
    {evs : List AllocEvent}
    (hsk : skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs = some rest)
    (h : SkipFieldEnv x evs) :
    evs = [] := by
  simpa [SkipFieldEnv, skipFieldEventsCore, hsk] using h

theorem authMergeLoopEnv_to_spqr {errRem byteRem maxLen polyCapBound : Nat} {evs : List AllocEvent}
    (hlen : byteRem ≤ maxLen) (h : AuthMergeLoopEnv errRem byteRem evs) :
    SpqrMergeLoopEnv (errRem + 2 * byteRem) maxLen polyCapBound evs := by
  induction h with
  | nil => exact .nil
  | @errFrom e b _ _ ih =>
    rw [show (e + 1) + 2 * b = (e + 2 * b) + 1 by omega]
    exact .step .fromErr (ih hlen)
  | @errPush e b n _ _ hn hp _ ih =>
    rw [show (e + 1) + 2 * b = (e + 2 * b) + 1 by omega]
    exact .step (.pushErr (by omega) hp) (ih hlen)
  | @bytesStep e b b' wt valCap bs v rest _ _ hm hbs hshr hcore _ ih =>
    exact (SpqrMergeLoopEnv.bytesStep wt valCap bs v rest hm
      (Nat.le_trans hbs hlen) hcore (ih (by omega))).mono_fuel (by omega)

theorem spqrMergeLoopEnv_snoc {fuel maxLen polyCapBound : Nat} {evs₁ evs₂ : List AllocEvent}
    (h₁ : SpqrMergeLoopEnv fuel maxLen polyCapBound evs₁)
    (h₂ : SpqrMergeIterEnv maxLen polyCapBound evs₂) :
    SpqrMergeLoopEnv (fuel + 1) maxLen polyCapBound (evs₁ ++ evs₂) :=
  h₁.append (SpqrMergeLoopEnv.single (fuel := 0) (maxLen := maxLen) h₂)

theorem fitsEnv_decodeErrorFrom_of_spqr {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {f₀ f_tot maxLen polyCapBound : Nat} {evs₀ : List AllocEvent}
    (hf : f₀ + 1 ≤ f_tot)
    (hevs₀ : SpqrMergeLoopEnv f₀ maxLen polyCapBound evs₀)
    (hFit : FitsEnv M lim st (SpqrMergeLoopEnv f_tot maxLen polyCapBound)) :
    FitsEnv M lim (M.stepEvents evs₀ st) DecodeErrorFromEnv := by
  have hrem : FitsEnv M lim (M.stepEvents evs₀ st) (SpqrMergeLoopEnv 1 maxLen polyCapBound) :=
    FitsEnv.spqrMergeLoop_split hevs₀ (hFit.mono fun _ h => h.mono_fuel hf)
  exact FitsEnv.spqrMergeLoop_head (fun _ h => decodeErrorFromEnv_to_spqr h) hrem

theorem fitsEnv_decodeErrorPush_of_spqr {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {n f₀ f_tot maxLen polyCapBound : Nat} {evs₀ : List AllocEvent}
    (hn : n ≤ 4) (hf : f₀ + 1 ≤ f_tot)
    (hevs₀ : SpqrMergeLoopEnv f₀ maxLen polyCapBound evs₀)
    (hFit : FitsEnv M lim st (SpqrMergeLoopEnv f_tot maxLen polyCapBound)) :
    FitsEnv M lim (M.stepEvents evs₀ st)
      (DecodeErrorPushMergeEnv n) := by
  have hrem : FitsEnv M lim (M.stepEvents evs₀ st) (SpqrMergeLoopEnv 1 maxLen polyCapBound) :=
    FitsEnv.spqrMergeLoop_split hevs₀ (hFit.mono fun _ h => h.mono_fuel hf)
  exact FitsEnv.spqrMergeLoop_head (fun _ h => decodeErrorPushEnv_to_spqr hn h) hrem

theorem fitsEnv_decodeVarint2_of_spqr {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {bs : List (BitVec 8)} {f₀ f_tot maxLen polyCapBound : Nat} {evs₀ : List AllocEvent}
    (hf : f₀ + 1 ≤ f_tot)
    (hevs₀ : SpqrMergeLoopEnv f₀ maxLen polyCapBound evs₀)
    (hFit : FitsEnv M lim st (SpqrMergeLoopEnv f_tot maxLen polyCapBound)) :
    FitsEnv M lim (M.stepEvents evs₀ st) (DecodeVarint2Env bs) := by
  have hrem : FitsEnv M lim (M.stepEvents evs₀ st) (SpqrMergeLoopEnv 1 maxLen polyCapBound) :=
    FitsEnv.spqrMergeLoop_split hevs₀ (hFit.mono fun _ h => h.mono_fuel hf)
  exact FitsEnv.spqrMergeLoop_head (fun _ h => decodeVarint2Env_to_spqr h) hrem

theorem fitsEnv_skipField_of_spqr {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {x : SkipFieldGhost} {f₀ f_tot maxLen polyCapBound : Nat} {evs₀ : List AllocEvent}
    (hf : f₀ + 1 ≤ f_tot)
    (hevs₀ : SpqrMergeLoopEnv f₀ maxLen polyCapBound evs₀)
    (hFit : FitsEnv M lim st (SpqrMergeLoopEnv f_tot maxLen polyCapBound)) :
    FitsEnv M lim (M.stepEvents evs₀ st) (SkipFieldEnv x) := by
  have hrem : FitsEnv M lim (M.stepEvents evs₀ st) (SpqrMergeLoopEnv 1 maxLen polyCapBound) :=
    FitsEnv.spqrMergeLoop_split hevs₀ (hFit.mono fun _ h => h.mono_fuel hf)
  exact FitsEnv.spqrMergeLoop_head (fun _ h => skipFieldEnv_to_spqr h) hrem

theorem fitsEnv_authMerge_of_spqr {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {f₀ errRem byteRem f_tot maxLen polyCapBound : Nat} {evs₀ : List AllocEvent}
    (hf : f₀ + (errRem + 2 * byteRem) ≤ f_tot) (hlen : byteRem ≤ maxLen)
    (hevs₀ : SpqrMergeLoopEnv f₀ maxLen polyCapBound evs₀)
    (hFit : FitsEnv M lim st (SpqrMergeLoopEnv f_tot maxLen polyCapBound)) :
    FitsEnv M lim (M.stepEvents evs₀ st) (AuthMergeLoopEnv errRem byteRem) := by
  have hrem : FitsEnv M lim (M.stepEvents evs₀ st)
      (SpqrMergeLoopEnv (errRem + 2 * byteRem) maxLen polyCapBound) :=
    FitsEnv.spqrMergeLoop_split hevs₀ (hFit.mono fun _ h => h.mono_fuel hf)
  exact hrem.mono fun _ ha => authMergeLoopEnv_to_spqr hlen ha

theorem pool_spqr_mono {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {f₁ f₂ maxLen polyBound : Nat}
    {evs : List AllocEvent} {s sf : State}
    (hvm : VmPreserved s sf) (hf : f₁ ≤ f₂)
    (hevs : SpqrMergeLoopEnv f₁ maxLen polyBound evs) :
    A.pool lim (M.stepEvents evs st) s ⊢
      ∃∗ evs' : List AllocEvent,
        ⌜SpqrMergeLoopEnv f₂ maxLen polyBound evs'⌝ ∗
        A.pool lim (M.stepEvents evs' st) sf := by
  refine Entails.trans ?_ (Entails.sepExists_intro (P := fun evs' =>
    ⌜SpqrMergeLoopEnv f₂ maxLen polyBound evs'⌝ ∗ A.pool lim (M.stepEvents evs' st) sf) evs)
  rw [A.pool_of_vmPreserved hvm]
  exact Entails.pure_right (hevs.mono_fuel hf) (Entails.refl _)

theorem pool_spqr_snoc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {f₁ f₂ maxLen polyBound : Nat}
    {evs₁ evs₂ : List AllocEvent} {s sf : State}
    (hvm : VmPreserved s sf) (hf : f₁ + 1 ≤ f₂)
    (h₁ : SpqrMergeLoopEnv f₁ maxLen polyBound evs₁)
    (h₂ : SpqrMergeIterEnv maxLen polyBound evs₂) :
    A.pool lim (M.stepEvents evs₂ (M.stepEvents evs₁ st)) s ⊢
      ∃∗ evs' : List AllocEvent,
        ⌜SpqrMergeLoopEnv f₂ maxLen polyBound evs'⌝ ∗
        A.pool lim (M.stepEvents evs' st) sf := by
  rw [← M.stepEvents_append]
  exact pool_spqr_mono A lim st hvm hf (spqrMergeLoopEnv_snoc h₁ h₂)

theorem pool_spqr_append {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {f₁ f₂ f₃ maxLen polyBound : Nat}
    {evs₁ evs₂ : List AllocEvent} {s sf : State}
    (hvm : VmPreserved s sf) (hf : f₁ + f₂ ≤ f₃)
    (h₁ : SpqrMergeLoopEnv f₁ maxLen polyBound evs₁)
    (h₂ : SpqrMergeLoopEnv f₂ maxLen polyBound evs₂) :
    A.pool lim (M.stepEvents evs₂ (M.stepEvents evs₁ st)) s ⊢
      ∃∗ evs' : List AllocEvent,
        ⌜SpqrMergeLoopEnv f₃ maxLen polyBound evs'⌝ ∗
        A.pool lim (M.stepEvents evs' st) sf := by
  rw [← M.stepEvents_append]
  exact pool_spqr_mono A lim st hvm hf (h₁.append h₂)

/-- Opaque-friendly budget pool bundle at fuel `f` and state `s`. -/
def spqrPoolAt {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (f maxLen polyBound : Nat) (s : State) : SepProp :=
  ∃∗ evs : List AllocEvent,
    ⌜SpqrMergeLoopEnv f maxLen polyBound evs⌝ ∗
    A.pool lim (M.stepEvents evs st) s

theorem spqrPoolAt_of_vmPreserved {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {f maxLen polyBound : Nat} {s s' : State}
    (hvm : VmPreserved s s') :
    spqrPoolAt A lim st f maxLen polyBound s' = spqrPoolAt A lim st f maxLen polyBound s := by
  simp only [spqrPoolAt, A.pool_of_vmPreserved hvm]

theorem spqrPoolAt_mono {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {f₁ f₂ maxLen polyBound : Nat} {s sf : State}
    (hvm : VmPreserved s sf) (hf : f₁ ≤ f₂) :
    spqrPoolAt A lim st f₁ maxLen polyBound s ⊢ spqrPoolAt A lim st f₂ maxLen polyBound sf := by
  unfold spqrPoolAt
  exact Entails.sepExists_elim fun evs => Entails.pure_left fun hevs =>
    pool_spqr_mono A lim st hvm hf hevs

theorem pool_entails_spqrPoolAt_snoc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {f₁ f₂ maxLen polyBound : Nat}
    {evs₁ evs₂ : List AllocEvent} {s sf : State}
    (hvm : VmPreserved s sf) (hf : f₁ + 1 ≤ f₂)
    (h₁ : SpqrMergeLoopEnv f₁ maxLen polyBound evs₁)
    (h₂ : SpqrMergeIterEnv maxLen polyBound evs₂) :
    A.pool lim (M.stepEvents evs₂ (M.stepEvents evs₁ st)) s ⊢
      spqrPoolAt A lim st f₂ maxLen polyBound sf :=
  pool_spqr_snoc A lim st hvm hf h₁ h₂

theorem pool_entails_spqrPoolAt_nil {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {f₁ f₂ maxLen polyBound : Nat}
    {evs₁ evs₂ : List AllocEvent} {s sf : State}
    (hvm : VmPreserved s sf) (hf : f₁ ≤ f₂)
    (h₁ : SpqrMergeLoopEnv f₁ maxLen polyBound evs₁) (hnil : evs₂ = []) :
    A.pool lim (M.stepEvents evs₂ (M.stepEvents evs₁ st)) s ⊢
      spqrPoolAt A lim st f₂ maxLen polyBound sf := by
  subst hnil
  exact pool_spqr_mono A lim st hvm hf h₁

theorem pool_entails_spqrPoolAt_append {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {f₁ f₂ f₃ maxLen polyBound : Nat}
    {evs₁ evs₂ : List AllocEvent} {s sf : State}
    (hvm : VmPreserved s sf) (hf : f₁ + f₂ ≤ f₃)
    (h₁ : SpqrMergeLoopEnv f₁ maxLen polyBound evs₁)
    (h₂ : SpqrMergeLoopEnv f₂ maxLen polyBound evs₂) :
    A.pool lim (M.stepEvents evs₂ (M.stepEvents evs₁ st)) s ⊢
      spqrPoolAt A lim st f₃ maxLen polyBound sf :=
  pool_spqr_append A lim st hvm hf h₁ h₂

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
