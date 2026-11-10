/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.Defs
public import LibsignalBinary.Proofs.RecordCodecs.SignedDeps
public import LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymD
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.RecordCodecs.Deps

/-!
# Budget-Threaded `SignedPreKeyRecordStructure::decode` Callee Wrappers and State

`RustCliAllocBudget`-threaded relocatable `[LibsignalPlacement]` callee bundle and convergence
state definitions for `SignedPreKeyRecordStructure::decode` (Block `562`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.DefsBudget

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecs
open CryptoVerification
open CryptoVerification.RecordCodecs.Placed
open LibsignalBinary.Heap
open CryptoVerification.RecordCodecsBinary (ls_subroutine_ok_lscro_of_block ls_subroutine_ok_lscro_of_cl)
open CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers
  (SpkBytesField SpkGhost SpkGhostCapOk SpkSavedRegs spkConvergeMem spkOff_converge
   spkStructAt spkStructAt_entails_loopOf spkStructAt_entails_of spkStructLoopOf spkStructOf)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
  (SignedHooksPlaced SignedPortDepsPlaced SpkCaps SpkField SpkLoopBoundedEnv SpkLoopEnv
   bmNextCap bytesMerge3RawBudgetSpec decodeErrorFromBudgetSpec decodeErrorPushBoundedSpec
   decodeVarint2BudgetSpec skipField3BudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (bytesMergeEventsCore)

theorem spk_decodeVarint6_placed_ok [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : SignedPortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_562 H) (lsmpl.base 559)
      (withLsCodeRoLoaded lsmpl (decodeVarint2BudgetSpec M A lim)) :=
  ls_subroutine_ok_lscro_of_cl (callerProg := lsProg_562 H) d.decodeVarint6

theorem spk_skipField7_placed_ok [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : SignedPortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_562 H) (lsmpl.base 546)
      (withLsCodeRoLoaded lsmpl (skipField3BudgetSpec M A lim)) :=
  ls_subroutine_ok_lscro_of_cl (callerProg := lsProg_562 H) d.skipField7

theorem spk_bytesMerge7_placed_ok [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : SignedPortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_562 H) (lsmpl.base 558)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec M A lim)) :=
  ls_subroutine_ok_lscro_of_block (callerProg := lsProg_562 H) d.bytesMerge7

theorem spk_decodeErrorFrom_placed_ok [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hH : SignedHooksPlaced M A lim H) :
    subroutine_ok (lsProg_562 H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)) :=
  ls_subroutine_ok_lscro_of_cl (callerProg := lsProg_562 H) hH.decodeErrorFrom

theorem spk_decodeErrorPush_placed_ok [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hH : SignedHooksPlaced M A lim H) :
    subroutine_ok (lsProg_562 H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushBoundedSpec M A lim)) :=
  ls_subroutine_ok_lscro_of_cl (callerProg := lsProg_562 H) hH.decodeErrorPush

theorem spk_dealloc_placed_ok [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hH : SignedHooksPlaced M A lim H) :
    subroutine_ok (lsProg_562 H) (lsρ lsRustDeallocSym)
      (withLsCodeRoLoaded lsmpl (rustCliDeallocBudgetSpec M A lim)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain
    (ls_hook_ok_of_mem hH.dealloc (by decide) (by decide) (by decide))

def noPanicQp (_s0 : State) : State → SepProp → Prop :=
  fun _ _ => False

theorem sepWPp_frame_noPanic {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P F : SepProp} {Q Q' : State → SepProp → Prop}
    (h : Wire.SepWPp prog ret s P Q' (noPanicQp s0))
    (hq : ∀ sf Pm, Q' sf Pm → Q sf (Pm ∗ F)) :
    Wire.SepWPp prog ret s (P ∗ F) Q (noPanicQp s0) := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pm, hmm, hqm, hv⟩ | ⟨_, _, _, hqp⟩ | ⟨_, hoom⟩⟩ := h (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmm
    exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pm ∗ F, hmm, hq sf Pm hqm, hv⟩⟩
  · exact hqp.elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem sepWPp_end_noPanic_lscro {prog : Program} {pl : Obj.MultiPlacement} {ret : BitVec 64}
    {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded pl s.mem)
    (h : ProofLib.SepWP prog ret s P (fun sf Pf =>
      Wire.VRegsAt s sf ∧
      (LibsignalCodeRoLoaded pl sf.mem → Q sf Pf))) :
    Wire.SepWPp prog ret s P Q (noPanicQp s0) := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hv, hq⟩ | ⟨_, hoom⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf,
      hq (hcrl.of_keepsFrozen hsteps.keepsFrozen), hv.eq⟩⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem spk_call_noPanic_lscro {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {ret entry ret_pc : BitVec 64} {s0 s : State} {P T F : SepProp} {φ : Prop}
    {Q : State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded pl s.mem)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F := by sep_focus)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → LibsignalCodeRoLoaded pl sf.mem →
      CalleeSavedPreserved s sf →
      Wire.SepWPp prog ret sf (spec.post x s sf ∗ F) Q (noPanicQp s0))
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    Wire.SepWPp prog ret s P Q (noPanicQp s0) := by
  intro R' hm hL
  have hpre : s.mem ⊨ (withLsCodeRoLoaded pl spec).pre x s ∗ (F ∗ R') := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hoom⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hspm_align : sm.spAligned = true := by
      rw [State.spAligned, hspm, ← State.spAligned]; exact hsp
    have hcrl_m := hcrl.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', ⟨hpcf, hrunf, Pf, hmf, hqf, hvf⟩ | hpanf⟩ :=
      hnext sm hpcm hrunm hspm hspm_align hcrl_m hcsm R' hpost (hsteps.codeLoaded hL)
    · exact ⟨sf, hsteps.trans hsteps',
        Or.inl ⟨hpcf, hrunf, Pf, hmf, hqf, hvf.trans hcsm.2.2.2.2.2.2.2.2.2.2.2⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr hpanf⟩
  · dsimp only [withLsCodeRoLoaded] at hpost; rw [hpan sm] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCodeRoLoaded] at hpost; rw [hexit sm code] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCodeRoLoaded] at hoom; rw [hoom_eq sm] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

theorem sepWPp_call_budget_lscro {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {ret entry ret_pc : BitVec 64} {s0 s : State} {P T F : SepProp} {φ : Prop}
    {Q : State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded pl s.mem)
    (hlr : s.readReg64 Reg.lr = ret_pc) (_htr : s.trace = s0.trace)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F := by sep_focus)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → LibsignalCodeRoLoaded pl sf.mem →
      CalleeSavedPreserved s sf →
      Wire.SepWPp prog ret sf (spec.post x s sf ∗ F) Q (noPanicQp s0))
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    Wire.SepWPp prog ret s P Q (noPanicQp s0) :=
  spk_call_noPanic_lscro x hcall hpc hrun hsp hcrl hlr hspec hφ hP hnext hexit hpan hoom_eq

structure SpkConvergeStatePlaced [CryptoVerification.LibsignalPlacement] (s0 : State) (sp' x19 : BitVec 64)
    (s : State) : Prop where
  sp : s.sp = sp'
  spAlign : s.spAligned = true
  crl : LibsignalCodeRoLoaded lsmpl s.mem
  tr : s.trace = s0.trace
  x24 : s.readReg64 .x24 = sp' + 16#64
  x19_eq : s.readReg64 .x19 = x19
  saved : SpkSavedRegs s0 s

def spkBytesFieldToField : SpkBytesField → SpkField
  | .pub => .pub
  | .priv => .priv
  | .sig => .sig

structure SpkGhostCapsMatch (g : SpkGhost) (caps : SpkCaps) : Prop where
  pub_eq : g.pub.cap.toNat = caps.pub
  priv_eq : g.priv.cap.toNat = caps.priv
  sig_eq : g.sig.cap.toNat = caps.sig
  pub_lt : caps.pub < 2 ^ 63
  priv_lt : caps.priv < 2 ^ 63
  sig_lt : caps.sig < 2 ^ 63

theorem spkBytesField_cap_pin_eq {g : SpkGhost} {caps : SpkCaps}
    (hc : SpkGhostCapsMatch g caps) (f : SpkBytesField) :
    (f.pin g).cap = BitVec.ofNat 64 (caps.get (spkBytesFieldToField f)) ∧
      (f.pin g).cap.toNat = caps.get (spkBytesFieldToField f) ∧
      caps.get (spkBytesFieldToField f) < 2 ^ 63 := by
  cases f
  · dsimp only [SpkBytesField.pin, SpkCaps.get, spkBytesFieldToField]
    refine ⟨?_, hc.pub_eq, hc.pub_lt⟩
    apply BitVec.eq_of_toNat_eq
    rw [hc.pub_eq, BitVec.toNat_ofNat]
    have hlt := hc.pub_lt
    omega
  · dsimp only [SpkBytesField.pin, SpkCaps.get, spkBytesFieldToField]
    refine ⟨?_, hc.priv_eq, hc.priv_lt⟩
    apply BitVec.eq_of_toNat_eq
    rw [hc.priv_eq, BitVec.toNat_ofNat]
    have hlt := hc.priv_lt
    omega
  · dsimp only [SpkBytesField.pin, SpkCaps.get, spkBytesFieldToField]
    refine ⟨?_, hc.sig_eq, hc.sig_lt⟩
    apply BitVec.eq_of_toNat_eq
    rw [hc.sig_eq, BitVec.toNat_ofNat]
    have hlt := hc.sig_lt
    omega

theorem spkBytesField_capsMatch_update {g : SpkGhost} {caps : SpkCaps}
    (hc : SpkGhostCapsMatch g caps) {cap' ptr' : BitVec 64} {v : Nat}
    (hcap' : cap'.toNat = v) (hv : v < 2 ^ 63) (f : SpkBytesField) :
    SpkGhostCapsMatch (f.setPin g ⟨cap', ptr'⟩) (caps.set (spkBytesFieldToField f) v) := by
  cases f
  · exact ⟨hcap', hc.priv_eq, hc.sig_eq, hv, hc.priv_lt, hc.sig_lt⟩
  · exact ⟨hc.pub_eq, hcap', hc.sig_eq, hc.pub_lt, hv, hc.sig_lt⟩
  · exact ⟨hc.pub_eq, hc.priv_eq, hcap', hc.pub_lt, hc.priv_lt, hv⟩

def spkStructLoopCapsOf (A : RustAlloc) (sp' : BitVec 64) (n : Nat)
    (caps : SpkCaps) (m : SignedPreKeyRecordStructure) : SepProp :=
  ∃∗ g : SpkGhost, ⌜SpkGhostCapOk g n ∧ SpkGhostCapsMatch g caps⌝ ∗ spkStructAt A g sp' m

theorem spkStructAt_entails_loopCapsOf (A : RustAlloc) (g : SpkGhost) (sp' : BitVec 64)
    (n : Nat) (caps : SpkCaps) (m : SignedPreKeyRecordStructure)
    (hg : SpkGhostCapOk g n) (hc : SpkGhostCapsMatch g caps) :
    spkStructAt A g sp' m ⊢ spkStructLoopCapsOf A sp' n caps m := by
  unfold spkStructLoopCapsOf
  refine Entails.trans ?_
    (Entails.sepExists_intro
      (P := fun g' => ⌜SpkGhostCapOk g' n ∧ SpkGhostCapsMatch g' caps⌝ ∗ spkStructAt A g' sp' m) g)
  rw [pure_true_emp ⟨hg, hc⟩, emp_sepConj]
  exact Entails.refl _

theorem spkStructLoopCapsOf_entails_loopOf (A : RustAlloc) (sp' : BitVec 64) (n : Nat)
    (caps : SpkCaps) (m : SignedPreKeyRecordStructure) :
    spkStructLoopCapsOf A sp' n caps m ⊢ spkStructLoopOf A sp' n m :=
  Entails.sepExists_elim fun g =>
    Entails.pure_left fun ⟨hg, _⟩ => spkStructAt_entails_loopOf A g sp' n m hg

theorem spkStructLoopCapsOf_entails_of (A : RustAlloc) (sp' : BitVec 64) (n : Nat)
    (caps : SpkCaps) (m : SignedPreKeyRecordStructure) :
    spkStructLoopCapsOf A sp' n caps m ⊢ spkStructOf A sp' m :=
  Entails.sepExists_elim fun g =>
    Entails.pure_left fun _ => spkStructAt_entails_of A g sp' m

theorem spkStructLoopCapsOf_mono (A : RustAlloc) (sp' : BitVec 64) {m n : Nat}
    {caps : SpkCaps} (st : SignedPreKeyRecordStructure) (hle : m ≤ n) :
    spkStructLoopCapsOf A sp' n caps st ⊢ spkStructLoopCapsOf A sp' m caps st :=
  Entails.sepExists_elim fun g =>
    Entails.pure_left fun ⟨hg, hc⟩ =>
      spkStructAt_entails_loopCapsOf A g sp' m caps st (hg.mono hle) hc

def spkLoopCapsMemAt (subStack : Nat) (A : RustAlloc) (sp' x19 ptr : BitVec 64)
    (caps : SpkCaps) (bs : List (BitVec 8)) (m : SignedPreKeyRecordStructure) : SepProp :=
  sliceCursorAt sp' ptr bs ∗
    ((sp' + 104#64) ↦₆₄ sp') ∗
    memRegion (sp' + 112#64) 48 ∗
    spkStructLoopCapsOf A sp' bs.length caps m ∗
    memRegion x19 88 ∗
    A.pool ∗
    stackAt sp' subStack

abbrev spkLoopCapsMem (A : RustAlloc) (sp' x19 ptr : BitVec 64)
    (caps : SpkCaps) (bs : List (BitVec 8)) (m : SignedPreKeyRecordStructure) : SepProp :=
  spkLoopCapsMemAt (SpqrV1.Varint.skipField3Stack 100) A sp' x19 ptr caps bs m

def spkAfterVarintCapsMemAt (subStack : Nat) (A : RustAlloc) (sp' x19 ptr : BitVec 64)
    (caps : SpkCaps) (bs rest : List (BitVec 8)) (n : Nat)
    (m : SignedPreKeyRecordStructure) : SepProp :=
  sliceCursorAfter sp' ptr bs rest ∗
    ((sp' + 104#64) ↦₆₄ sp') ∗
    memRegion (sp' + 112#64) 48 ∗
    spkStructLoopCapsOf A sp' n caps m ∗
    memRegion x19 88 ∗
    A.pool ∗
    stackAt sp' subStack

abbrev spkAfterVarintCapsMem (A : RustAlloc) (sp' x19 ptr : BitVec 64)
    (caps : SpkCaps) (bs rest : List (BitVec 8)) (n : Nat)
    (m : SignedPreKeyRecordStructure) : SepProp :=
  spkAfterVarintCapsMemAt (SpqrV1.Varint.skipField3Stack 100) A sp' x19 ptr caps bs rest n m

def spkConvergePostPlaced [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (rem : Nat) (caps : SpkCaps)
    (s0 : State) (sp' x19 ptr : BitVec 64) (bs : List (BitVec 8))
    (out : Option SignedPreKeyRecordStructure) : State → SepProp → Prop :=
  fun sf Pf =>
    SpkConvergeStatePlaced s0 sp' x19 sf ∧
      ∃ evs : List AllocEvent, SpkLoopBoundedEnv rem caps evs ∧
        (Pf ⊢ spkConvergeMem (A.atState lim (M.stepEvents evs st) sf)
          sp' x19 ptr bs out (sf.readReg64 .x1))

theorem spkConvergePostPlaced_mono_rem [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) {rem₁ rem₂ : Nat} {caps : SpkCaps}
    (hle : rem₁ ≤ rem₂) (s0 : State) (sp' x19 ptr : BitVec 64) (bs : List (BitVec 8))
    (out : Option SignedPreKeyRecordStructure) (sf : State) (Pf : SepProp)
    (hq : spkConvergePostPlaced A lim st rem₁ caps s0 sp' x19 ptr bs out sf Pf) :
    spkConvergePostPlaced A lim st rem₂ caps s0 sp' x19 ptr bs out sf Pf := by
  rcases hq with ⟨hst, evs, hevs, hent⟩
  exact ⟨hst, evs, hevs.mono_rem hle, hent⟩

theorem spkConvergePostPlaced_skipStep [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) {rem rem' : Nat} {caps : SpkCaps}
    (hlt : rem' < rem) (s0 : State) (sp' x19 ptr : BitVec 64) (bs : List (BitVec 8))
    (out : Option SignedPreKeyRecordStructure) (sf : State) (Pf : SepProp)
    (hq : spkConvergePostPlaced A lim st rem' caps s0 sp' x19 ptr bs out sf Pf) :
    spkConvergePostPlaced A lim st rem caps s0 sp' x19 ptr bs out sf Pf := by
  rcases hq with ⟨hst, evs, hevs, hent⟩
  exact ⟨hst, evs, .skipStep hlt hevs, hent⟩

theorem spkConvergePostPlaced_bytesStep [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (f : SpkField) {rem rem' : Nat} {caps : SpkCaps}
    {wt : WireType} {bs_m v rest_m : List (BitVec 8)} {evs₁ : List AllocEvent}
    (hm : mergeBytes wt bs_m = some (v, rest_m))
    (hbs_le : bs_m.length ≤ rem)
    (hprog : rem' + v.length + 1 ≤ rem)
    (hcap_lt : caps.get f < 2 ^ 63)
    (hevs₁ : evs₁ = bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get f)) bs_m)
    (s0 : State) (sp' x19 ptr : BitVec 64) (bs : List (BitVec 8))
    (out : Option SignedPreKeyRecordStructure) (sf : State) (Pf : SepProp)
    (hq : spkConvergePostPlaced A lim (M.stepEvents evs₁ st) rem'
      (caps.set f (bmNextCap (caps.get f) v.length)) s0 sp' x19 ptr bs out sf Pf) :
    spkConvergePostPlaced A lim st rem caps s0 sp' x19 ptr bs out sf Pf := by
  subst hevs₁
  rcases hq with ⟨hst, evs₂, hevs₂, hent⟩
  refine ⟨hst, _ ++ evs₂, .bytesStep f wt bs_m v rest_m hm hbs_le hprog hcap_lt hevs₂, ?_⟩
  rwa [M.stepEvents_append]

theorem spkConvergePostPlaced_append_prefix [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (rem : Nat) (caps : SpkCaps)
    (s0 : State) (sp' x19 ptr : BitVec 64) (bs : List (BitVec 8)) (k : ℕ) (hkl : k ≤ bs.length)
    (out : Option SignedPreKeyRecordStructure) (sf : State) (Pf : SepProp)
    (hq : spkConvergePostPlaced A lim st rem caps s0 sp' x19
      (ptr + BitVec.ofNat 64 k) (bs.drop k) out sf Pf) :
    spkConvergePostPlaced A lim st rem caps s0 sp' x19 ptr bs out sf
      (Pf ∗ (ptr ↦ₛ bs.take k)) := by
  rcases hq with ⟨hst, evs, hevs, hent⟩
  refine ⟨hst, evs, hevs, ?_⟩
  have hcat : (ptr ↦ₛ bs.take k) ∗ ((ptr + BitVec.ofNat 64 k) ↦ₛ bs.drop k) = (ptr ↦ₛ bs) := by
    have ht : (bs.take k).length = k := by simp [Nat.min_eq_left hkl]
    have hp := (pointsToBytes_append ptr (bs.take k) (bs.drop k)).symm
    rw [ht, List.take_append_drop] at hp
    exact hp
  cases out <;> (
    dsimp only [spkConvergeMem] at hent ⊢
    refine Entails.trans (sepConj_mono_left hent) ?_
    apply entails_of_eq; rw [← hcat]; ac_rfl)

theorem spkAdvanceCursor_placed [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem : Nat} {caps : SpkCaps}
    {H : LibsignalHooks} {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {out : Option SignedPreKeyRecordStructure} {R : SepProp}
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k)
    (h : Wire.SepWPp (lsProg_562 H)
      ((blkPl_562).base + spkOff_converge) s
      (sliceCursorAt sp' (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest ∗ R)
      (spkConvergePostPlaced A lim st rem caps s0 sp' x19
        (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest out)
      (noPanicQp s0)) :
    Wire.SepWPp (lsProg_562 H)
      ((blkPl_562).base + spkOff_converge) s
      (sliceCursorAfter sp' ptr bs rest ∗ R)
      (spkConvergePostPlaced A lim st rem caps s0 sp' x19 ptr bs out)
      (noPanicQp s0) := by
  rw [sliceCursorAfter_eq_take_cursorAt sp' ptr bs rest hsuf]
  rcases hsuf with ⟨k, hkl, rfl⟩
  have hk : bs.length - (bs.drop k).length = k := by simp; omega
  rw [hk] at h ⊢
  refine Wire.SepWPp.mono_pre
    (P' := (sliceCursorAt sp' (ptr + BitVec.ofNat 64 k) (bs.drop k) ∗ R) ∗
      (ptr ↦ₛ bs.take k))
    (by apply entails_of_eq; ac_rfl) ?_
  exact sepWPp_frame_noPanic h
    (fun sf Pf hqm => spkConvergePostPlaced_append_prefix A lim st rem caps
      s0 sp' x19 ptr bs k hkl out sf Pf hqm)

end LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.DefsBudget
