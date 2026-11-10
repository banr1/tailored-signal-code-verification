/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Steps
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
public import LibsignalBinary.Proofs.PublicApi.StoreKit.RecordMove

/-!
# Stage P1 `SepWPp` Combinators and Kit Algebra

Shared OOM-prefix transport, `Steps`-carrying `SepWPp` sequencing combinators, stack-splitting and
kit precondition introducers, and `SessionRecord` / `trustPollOutAt` packing lemmas for Stage P1.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust
open CryptoVerification.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

/-! ## 1. OOM Prefix Transport & `Steps`-Carrying `SepWPp` Combinators -/

theorem allocFailedIn_trans {s0 s sf : State}
    (h0s : s0.trace <+: s.trace) (hsf : allocFailedIn s sf) :
    allocFailedIn s0 sf := by
  unfold allocFailedIn at hsf ⊢
  obtain ⟨pre, hpre⟩ := h0s
  have hlen : (s0.trace ++ pre).length = s0.trace.length + pre.length := List.length_append
  have hle : s0.trace.length ≤ s.trace.length := by rw [← hpre]; omega
  have hdrop : sf.trace.drop s.trace.length =
      (sf.trace.drop s0.trace.length).drop (s.trace.length - s0.trace.length) := by
    rw [List.drop_drop, Nat.add_sub_of_le hle]
  rw [hdrop] at hsf
  exact List.mem_of_mem_drop hsf

theorem allowPanic_oom_of_prefix {s0 s sf : State} {F : SepProp}
    (htr : s0.trace <+: s.trace) :
    PanicOomProp s0 sf ((⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) := by
  intro R hm
  exact allowPanic_frame (fun ⟨ha, hp⟩ => ⟨allocFailedIn_trans htr ha, htr.trans hp⟩) hm

theorem _root_.CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.bind_sepWP_steps_frame
    {prog : Program} {img : Obj.Image} {mid ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (hstep : SepWP prog mid s P_step
      (fun sm P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      ImgCallInv img sm → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rcases hinv with ⟨hF, hsym⟩
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent) hmm
  have hinv' : ImgCallInv img sm :=
    ⟨hF.of_keepsFrozen hsteps.keepsFrozen, hsteps.symtab_eq.trans hsym⟩
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hsteps hpc hrun hinv' hregs R hmm' (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

theorem _root_.CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.ret_sepWP_steps_frame
    {prog : Program} {img : Obj.Image} {ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (hstep : SepWP prog ret s P_step
      (fun sf P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sf))
    (hP : P = P_step ∗ F)
    (hret : ∀ sf : State, Steps prog s sf → sf.pc = ret → sf.status = .Running →
      ImgCallInv img sf → Q_regs sf →
      Q sf (P_step_post ∗ F)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.bind_sepWP_steps_frame hinv hstep hP fun sf hsteps hpc hrun hinv' hregs =>
    SepWPp.done hpc hrun (hret sf hsteps hpc hrun hinv' hregs)

theorem _root_.CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.bind_sepWPp_steps_frame
    {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P_stage P_stage_post F : SepProp} {Q_regs : State → Prop}
    {Q : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => (P_m ⊢ P_stage_post) ∧ Q_regs sm)
      (PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      Q_regs sm →
      SepWPp prog ret sm (P_stage_post ∗ F) Q (PanicOomProp s0)) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨hpan, P_m, hmm, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ F, hmm, fun R' hmR' => by
      rw [sepConj_assoc] at hmR'
      have h1 := hpanm (F ∗ R') hmR'
      rw [← sepConj_assoc] at h1
      exact allowPanic_frame id h1⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem _root_.CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.call_nopanic_steps_frame
    {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      ImgCallInv img sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro _; repeat (simp only [Spec.inImage]); rfl) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rcases hinv with ⟨hF, hsym⟩
  have hm' : s.mem ⊨ spec.pre x s ∗ (F ∗ R) := by
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ |
    ⟨_, _hoom_post⟩
  rotate_right; · rw [hoom_false] at _hoom_post; exact (not_satisfies_false_sepConj _hoom_post).elim
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    have hinv' : ImgCallInv img sm :=
      ⟨hF.of_keepsFrozen hsteps.keepsFrozen, hsteps.symtab_eq.trans hsym⟩
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hspm hsp_alm hcsm hinv' R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [hpan_false] at hpost
    exact (allowPanic_not_exited hpost).elim
  · rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

theorem _root_.CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp.call_oom_steps_frame
    {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State}
    {P P_spec F : SepProp} {Q : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (htr : s0.trace <+: s.trace)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : P_spec ⊢ spec.pre x s)
    (hP : P = P_spec ∗ F)
    (hpan : ∀ sf, spec.onPanic x s sf ⊢ ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      ImgCallInv img sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (PanicOomProp s0))
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by
      intro _ _; repeat (first | simp only [Spec.inImage] | simp only [withLogOff] | simp only [withEnvPre]); rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro _; repeat (first | simp only [Spec.inImage] | simp only [withLogOff] | simp only [withEnvPre]); rfl) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  rcases hinv with ⟨hF, hsym⟩
  rw [hP, sepConj_assoc] at hm
  have hm' : s.mem ⊨ spec.pre x s ∗ (F ∗ R) :=
    Satisfies.mono (sepConj_mono_left hpre) hm
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpanm, hpost⟩ |
    ⟨code, _, hpost⟩ | ⟨_, _hoom_post⟩
  rotate_right; · rw [hoom_false] at _hoom_post; exact (not_satisfies_false_sepConj _hoom_post).elim
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    have hinv' : ImgCallInv img sm :=
      ⟨hF.of_keepsFrozen hsteps.keepsFrozen, hsteps.symtab_eq.trans hsym⟩
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hspm hsp_alm hcsm hinv' R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · have hpost' : sm.mem ⊨ ((⌜allocFailedIn s sm ∧ s.trace <+: sm.trace⌝ ∗ anyHeap) ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left (hpan sm)) hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpanm,
      (⌜allocFailedIn s sm ∧ s.trace <+: sm.trace⌝ ∗ anyHeap) ∗ F, hpost',
      allowPanic_oom_of_prefix htr⟩)⟩
  · rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

/-! ## 2. Stack Split Lemmas & Kit Precondition Introducers -/

theorem stack_loadCall_to_loadShim {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (sp : BitVec 64) (hn : loadCallStack kit ≤ 2 ^ 64) :
    stackAt sp (loadCallStack kit) =
      memRegion (sp - BitVec.ofNat 64 (loadCallStack kit))
        (loadCallStack kit - kit.loadShimStack) ∗
        stackAt sp kit.loadShimStack :=
  stackAt_split_of_le sp (loadCallStack kit) kit.loadShimStack (Nat.le_max_left _ _) hn

theorem stack_loadCall_to_loadPoll {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (sp : BitVec 64) (hn : loadCallStack kit ≤ 2 ^ 64) :
    stackAt sp (loadCallStack kit) =
      memRegion (sp - BitVec.ofNat 64 (loadCallStack kit))
        (loadCallStack kit - kit.loadPollStack) ∗
        stackAt sp kit.loadPollStack :=
  stackAt_split_of_le sp (loadCallStack kit) kit.loadPollStack
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn

theorem stack_loadCall_to_alloc {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (sp : BitVec 64) (hn : loadCallStack kit ≤ 2 ^ 64) :
    stackAt sp (loadCallStack kit) =
      memRegion (sp - BitVec.ofNat 64 (loadCallStack kit))
        (loadCallStack kit - allocHookStack) ∗
        stackAt sp allocHookStack :=
  stackAt_split_of_le sp (loadCallStack kit) allocHookStack
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn

theorem stack_trustCall_to_trustPoll {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (sp : BitVec 64) (hn : trustCallStack ikit ≤ 2 ^ 64) :
    stackAt sp (trustCallStack ikit) =
      memRegion (sp - BitVec.ofNat 64 (trustCallStack ikit))
        (trustCallStack ikit - ikit.trustPollStack) ∗
        stackAt sp ikit.trustPollStack :=
  stackAt_split_of_le sp (trustCallStack ikit) ikit.trustPollStack
    (trustPollStack_le_trustCall ikit) hn

theorem stack_trustCall_to_alloc {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (sp : BitVec 64) (hn : trustCallStack ikit ≤ 2 ^ 64) :
    stackAt sp (trustCallStack ikit) =
      memRegion (sp - BitVec.ofNat 64 (trustCallStack ikit))
        (trustCallStack ikit - allocHookStack) ∗
        stackAt sp allocHookStack :=
  stackAt_split_of_le sp (trustCallStack ikit) allocHookStack
    (allocHookStack_le_trustCall ikit) hn

theorem stack_stageP1_to_load {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) (sp : BitVec 64)
    (hn : stageP1CallStack kit ikit ≤ 2 ^ 64) :
    stackAt sp (stageP1CallStack kit ikit) =
      memRegion (sp - BitVec.ofNat 64 (stageP1CallStack kit ikit))
        (stageP1CallStack kit ikit - loadCallStack kit) ∗
        stackAt sp (loadCallStack kit) :=
  stackAt_split_of_le sp (stageP1CallStack kit ikit) (loadCallStack kit)
    (Nat.le_max_left _ _) hn

theorem stack_stageP1_to_trust {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) (sp : BitVec 64)
    (hn : stageP1CallStack kit ikit ≤ 2 ^ 64) :
    stackAt sp (stageP1CallStack kit ikit) =
      memRegion (sp - BitVec.ofNat 64 (stageP1CallStack kit ikit))
        (stageP1CallStack kit ikit - trustCallStack ikit) ∗
        stackAt sp (trustCallStack ikit) :=
  stackAt_split_of_le sp (stageP1CallStack kit ikit) (trustCallStack ikit)
    (Nat.le_max_right _ _) hn

theorem loadShim_pre_intro {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {s : State} {self addrA : BitVec 64}
    (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = self)
    (hx1 : s.readReg64 .x1 = addrA) :
    A.pool ∗ stackAt s.sp kit.loadShimStack ⊢
      ((kitLoadShimSpec kit).inImage img).pre
        ({ self := self, addrA := addrA } : LoadShimCall) s := by
  dsimp only [Spec.inImage, kitLoadShimSpec]
  exact Entails.pure_right ⟨hinv.1, hinv.2⟩ (Entails.pure_right ⟨hx0, hx1⟩ (Entails.refl _))

theorem loadPoll_pre_intro {A : RustAlloc} {img : Obj.Image}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {s : State} {sp fut self addrA : BitVec 64} {peer : AddrGhost}
    (henv : kit.envOk s.fs.files)
    (hinv : ImgCallInv img s)
    (hsp : s.sp = sp)
    (hx0 : s.readReg64 .x0 = fut)
    (hx8 : s.readReg64 .x8 = sp + 0x3e0#64)
    (haddr : kit.addrOk peer.val) :
    kit.loadBoxAt fut self addrA 0#8 ∗
      kit.storeAt self st0 ∗
      memRegion (sp + 0x3e0#64) 368 ∗
      protocolAddressAt A peer addrA ∗
      A.pool ∗
      stackAt sp kit.loadPollStack ⊢
      (kitLoadPollSpecSE img kit Scope encRecord).pre
        (({ fut := fut, out := sp + 0x3e0#64, addrA := addrA, addr := peer } : LoadPollCall),
          self, st0) s := by
  dsimp only [kitLoadPollSpecSE, withEnvPre, kitLoadPollSpecS]
  rw [hsp]
  exact Entails.pure_right henv
    (Entails.pure_right ⟨hinv.1, hinv.2, hx0, hx8, haddr⟩ (Entails.refl _))

theorem trustShim_pre_intro {A : RustAlloc} {img : Obj.Image}
    {ikit : IdentityStoreSpec A img.base} {s : State}
    {self addrA keyA : BitVec 64} {d : BitVec 8}
    (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = self)
    (hx1 : s.readReg64 .x1 = addrA)
    (hx2 : s.readReg64 .x2 = keyA)
    (hx3 : (s.readReg64 .x3).setWidth 8 = d) :
    A.pool ∗ stackAt s.sp ikit.trustShimStack ⊢
      ((kitTrustShimSpec ikit).inImage img).pre
        (({ self := self, addrA := addrA, keyA := keyA } : IdentityShimCall), d) s := by
  dsimp only [Spec.inImage, kitTrustShimSpec]
  exact Entails.pure_right ⟨hinv.1, hinv.2⟩
    (Entails.pure_right ⟨hx0, hx1, hx2, hx3⟩ (Entails.refl _))

theorem trustPoll_pre_intro {A : RustAlloc} {img : Obj.Image}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {s : State} {sp fut self addrA keyA : BitVec 64}
    {peer : AddrGhost} {remoteIdKey : IdentityKey}
    (henv : ikit.envOk s.fs.files)
    (hinv : ImgCallInv img s)
    (hsp : s.sp = sp)
    (hx0 : s.readReg64 .x0 = fut)
    (hx8 : s.readReg64 .x8 = sp + 0x3e0#64)
    (haddr : ikit.addrOk peer.val) :
    ikit.trustBoxAt fut self addrA keyA 0#8 (directionByte Direction.receiving) ∗
      ikit.identityAt self ist0 ∗
      memRegion (sp + 0x3e0#64) 48 ∗
      protocolAddressAt A peer addrA ∗
      (keyA ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
      A.pool ∗
      stackAt sp ikit.trustPollStack ∗
      logOff img ⊢
      (kitTrustPollSpecI img ikit).pre
        (({ fut := fut, out := sp + 0x3e0#64,
            call := { addrA := addrA, addr := peer, keyA := keyA, key := remoteIdKey } }
            : IdentityPollCall),
          Direction.receiving, self, ist0) s := by
  dsimp only [kitTrustPollSpecI, Spec.inImage, withLogOff, kitTrustPollSpecE, withEnvPre,
    kitTrustPollSpec]
  rw [hsp]
  refine Entails.pure_right ⟨hinv.1, hinv.2⟩ ?_
  have h1 :
      ikit.trustBoxAt fut self addrA keyA 0#8 (directionByte Direction.receiving) ∗
        ikit.identityAt self ist0 ∗
        memRegion (sp + 0x3e0#64) 48 ∗
        protocolAddressAt A peer addrA ∗
        (keyA ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
        A.pool ∗
        stackAt sp ikit.trustPollStack ⊢
      ⌜ikit.envOk s.fs.files⌝ ∗
        (⌜s.readReg64 .x0 = fut ∧ s.readReg64 .x8 = sp + 0x3e0#64 ∧ ikit.addrOk peer.val⌝ ∗
          ikit.trustBoxAt fut self addrA keyA 0#8 (directionByte Direction.receiving) ∗
          ikit.identityAt self ist0 ∗
          memRegion (sp + 0x3e0#64) 48 ∗
          protocolAddressAt A peer addrA ∗
          (keyA ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
          A.pool ∗
          stackAt sp ikit.trustPollStack) :=
    Entails.pure_right henv (Entails.pure_right ⟨hx0, hx8, haddr⟩ (Entails.refl _))
  simpa only [sepConj_assoc] using sepConj_mono_left (Q := logOff img) h1

/-! ## 3. `SessionRecord` Move & `trustPollOutAt` Unpack/Pack Lemmas -/

theorem recordHeap_prevCap_lt {A : RustAlloc} {g : RecordGhost}
    {r : SessionRecord (List (BitVec 8))} :
    recordHeap A g r ⊢ ⌜g.prevCap.toNat < 2 ^ 63⌝ ∗ recordHeap A g r := by
  unfold recordHeap vecBuf
  sep_norm
  apply Entails.pure_left; rintro ⟨h1, h2, h3⟩
  exact Entails.pure_right (by omega) (Entails.pure_right ⟨h1, h2, h3⟩ (Entails.refl _))

theorem loadPollOut_some_unpack (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (A : RustAlloc) (b sp : BitVec 64) (r : SessionRecord (List (BitVec 8))) :
    loadPollOutAtS Scope A b (sp + 0x3e0#64) (.ok (some r)) ⊢
      ∃∗ g : RecordGhost, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
      ∃∗ tail : List (BitVec 8),
        ⌜Scope r ∧ g.prevCap.toNat < 2 ^ 63 ∧ RecordTailInline g r w4 w5 w6 tail ∧
          tail.length = 312⌝ ∗
        ((sp + 0x3e0#64) ↦₆₄ g.prevCap) ∗
        ((sp + 0x3e8#64) ↦₆₄ g.prevPtr) ∗
        ((sp + 0x3f0#64) ↦₃₂ (0#64 : BitVec 64).extractLsb' 0 32) ∗
        ((sp + 0x3f4#64) ↦₆₄
          ((recordCurCap g).extractLsb' 0 32 ++ (0#64 : BitVec 64).extractLsb' 32 32)) ∗
        ((sp + 0x3fc#64) ↦₆₄ (w4.extractLsb' 0 32 ++ (recordCurCap g).extractLsb' 32 32)) ∗
        ((sp + 0x404#64) ↦₆₄ (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)) ∗
        ((sp + 0x40c#64) ↦₆₄ (w6.extractLsb' 0 32 ++ w5.extractLsb' 32 32)) ∗
        ((sp + 0x414#64) ↦₃₂ w6.extractLsb' 32 32) ∗
        ((sp + 0x418#64) ↦ₛ tail) ∗
        recordHeap A g r := by
  dsimp only [loadPollOutAtS, loadPollOutAt]
  apply Entails.pure_left; intro hscope
  apply Entails.sepExists_elim; intro g
  rw [sessionRecordAt_eq_words56_sep_tail A (sp + 0x3e0#64) g r]
  apply Entails.sepExists_elim; intro w4
  apply Entails.sepExists_elim; intro w5
  apply Entails.sepExists_elim; intro w6
  apply Entails.sepExists_elim; intro tail
  apply Entails.pure_left; intro htail
  have hlen : tail.length = 312 := htail.1
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right recordHeap_prevCap_lt)) ?_
  dsimp only [recordWords56At]
  sep_norm
  repeat (simp only [sepConj_pure_left_comm])
  apply Entails.pure_left; intro hprev
  refine Entails.sepExists_right g
    (Entails.sepExists_right w4
      (Entails.sepExists_right w5
        (Entails.sepExists_right w6
          (Entails.sepExists_right tail
            (Entails.pure_right ⟨hscope, hprev, htail, hlen⟩ ?_)))))
  have hrep := words5_repack_sp3e0 sp 0#64 (recordCurCap g) w4 w5 w6
  refine Entails.of_eq ?_
  calc
    _ = ((sp + 992#64) ↦₆₄ g.prevCap) ∗ ((sp + 1000#64) ↦₆₄ g.prevPtr) ∗
        (((sp + 1008#64) ↦₆₄ 0#64) ∗ ((sp + 1016#64) ↦₆₄ recordCurCap g) ∗
          ((sp + 1024#64) ↦₆₄ w4) ∗ ((sp + 1032#64) ↦₆₄ w5) ∗ ((sp + 1040#64) ↦₆₄ w6)) ∗
        ((sp + 1048#64) ↦ₛ tail) ∗ recordHeap A g r := by ac_rfl
    _ = _ := by rw [hrep]; ac_rfl

theorem sp3e0_368_fold (sp w0 w1 w2 w3 w4 w5 : BitVec 64) (d0 d6 : BitVec 32)
    (tail : List (BitVec 8)) (htail : tail.length = 312) :
    ((sp + 0x3e0#64) ↦₆₄ w0) ∗
      ((sp + 0x3e8#64) ↦₆₄ w1) ∗
      ((sp + 0x3f0#64) ↦₃₂ d0) ∗
      ((sp + 0x3f4#64) ↦₆₄ w2) ∗
      ((sp + 0x3fc#64) ↦₆₄ w3) ∗
      ((sp + 0x404#64) ↦₆₄ w4) ∗
      ((sp + 0x40c#64) ↦₆₄ w5) ∗
      ((sp + 0x414#64) ↦₃₂ d6) ∗
      ((sp + 0x418#64) ↦ₛ tail) ⊢
      memRegion (sp + 0x3e0#64) 368 := by
  rw [ProofLib.memRegion_split (sp + 0x3e0#64) 8 360 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64) 8 352 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64 + 8#64) 4 348 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64 + 8#64 + 4#64) 8 340 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64 + 8#64 + 4#64 + 8#64) 8 332 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64 + 8#64 + 4#64 + 8#64 + 8#64) 8 324
        (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64 + 8#64 + 4#64 + 8#64 + 8#64 + 8#64) 8 316
        (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64 + 8#64 + 4#64 + 8#64 + 8#64 + 8#64 + 8#64)
        4 312 (by decide)]
  sep_norm
  have hb := pointsToBytes_entails_memRegion (sp + 1048#64) tail
  rw [htail] at hb
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (sepConj_mono (pointsTo32_entails_memRegion _ _) hb)))))))

theorem sp_d8_bytes_rejoin (sp v0 v1 v2 v3 : BitVec 64) (dv4 : BitVec 32)
    (tail : List (BitVec 8)) (htail : tail.length = 312) :
    ((sp + 0xd8#64) ↦ₛ tail) ∗
      ((sp + 0x210#64) ↦₆₄ v0) ∗ ((sp + 0x218#64) ↦₆₄ v1) ∗
      ((sp + 0x220#64) ↦₆₄ v2) ∗ ((sp + 0x228#64) ↦₆₄ v3) ∗
      ((sp + 0x230#64) ↦₃₂ dv4) ⊢
      memRegion (sp + 0xd8#64) 348 := by
  have hb := pointsToBytes_entails_memRegion (sp + 0xd8#64) tail
  rw [htail] at hb
  exact Entails.trans (sepConj_mono_left hb) (sp_d8_348_rejoin sp v0 v1 v2 v3 dv4)

theorem coro_e0_some_pack (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (A : RustAlloc) (coroPtr : BitVec 64) (g : RecordGhost)
    (r : SessionRecord (List (BitVec 8)))
    (w4 w5 w6 : BitVec 64) (tail : List (BitVec 8))
    (hscope : Scope r) (htail : RecordTailInline g r w4 w5 w6 tail) :
    ((coroPtr + 0xe0#64) ↦₆₄ g.prevCap) ∗
      ((coroPtr + 0xe8#64) ↦₆₄ g.prevPtr) ∗
      ((coroPtr + 0xf0#64) ↦₃₂ (0#64 : BitVec 64).extractLsb' 0 32) ∗
      ((coroPtr + 0xf4#64) ↦₆₄
        ((recordCurCap g).extractLsb' 0 32 ++ (0#64 : BitVec 64).extractLsb' 32 32)) ∗
      ((coroPtr + 0xfc#64) ↦₆₄ (w4.extractLsb' 0 32 ++ (recordCurCap g).extractLsb' 32 32)) ∗
      ((coroPtr + 0x104#64) ↦₆₄ (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)) ∗
      ((coroPtr + 0x10c#64) ↦₆₄ (w6.extractLsb' 0 32 ++ w5.extractLsb' 32 32)) ∗
      ((coroPtr + 0x114#64) ↦₃₂ w6.extractLsb' 32 32) ∗
      ((coroPtr + 0x118#64) ↦ₛ tail) ∗
      recordHeap A g r ⊢
      p1LoadedRecordAt Scope A coroPtr (some r) := by
  dsimp only [p1LoadedRecordAt]
  refine Entails.pure_right hscope (Entails.sepExists_right g ?_)
  have hunp := words5_unpack_coro_e0 coroPtr 0#64 (recordCurCap g) w4 w5 w6
  have hrec := sessionRecordAt_of_words56_sep_tail A (coroPtr + 0xe0#64) g r htail
  dsimp only [recordWords56At] at hrec
  (try simp only [BitVec.add_assoc] at hunp hrec ⊢); (try simp only [BitVec.reduceAdd] at hunp hrec ⊢); (try simp only [sepConj_assoc] at hunp hrec ⊢)
  refine Entails.trans (Entails.of_eq ?_) hrec
  calc
    _ = ((coroPtr + 224#64) ↦₆₄ g.prevCap) ∗ ((coroPtr + 232#64) ↦₆₄ g.prevPtr) ∗
        (((coroPtr + 240#64) ↦₃₂ (0#64 : BitVec 64).extractLsb' 0 32) ∗
          ((coroPtr + 244#64) ↦₆₄
            ((recordCurCap g).extractLsb' 0 32 ++ (0#64 : BitVec 64).extractLsb' 32 32)) ∗
          ((coroPtr + 252#64) ↦₆₄ (w4.extractLsb' 0 32 ++ (recordCurCap g).extractLsb' 32 32)) ∗
          ((coroPtr + 260#64) ↦₆₄ (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)) ∗
          ((coroPtr + 268#64) ↦₆₄ (w6.extractLsb' 0 32 ++ w5.extractLsb' 32 32)) ∗
          ((coroPtr + 276#64) ↦₃₂ w6.extractLsb' 32 32)) ∗
        ((coroPtr + 280#64) ↦ₛ tail) ∗ recordHeap A g r := by ac_rfl
    _ = _ := by rw [hunp]; ac_rfl

theorem cells2_fold_398 (coroPtr w0 w1 : BitVec 64) :
    ((coroPtr + 0x398#64) ↦₆₄ w0) ∗ ((coroPtr + 0x3a0#64) ↦₆₄ w1) ⊢
      cells (coroPtr + 0x398#64) 2 := by
  dsimp only [cells]
  sep_norm
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.refl _))

theorem trustPollOut_any_unpack (b sp : BitVec 64) (ans : Except Unit Bool) :
    trustPollOutAt b (sp + 0x3e0#64) ans ⊢
      ∃∗ b_3e8 : BitVec 8, ∃∗ d_3e9 : BitVec 32, ∃∗ h_3ed : BitVec 16, ∃∗ b_3ef : BitVec 8,
      ∃∗ w_3f0 : BitVec 64, ∃∗ d_3f8 : BitVec 32, ∃∗ d_3fc : BitVec 32,
      ∃∗ w_400 : BitVec 64, ∃∗ w_408 : BitVec 64,
        ⌜trustPollTag ans ≠ 0xfffffffffffffffd#64 ∧
          (ans = .ok true → b_3e8 = 1#8) ∧
          (ans = .ok false → b_3e8 = 0#8)⌝ ∗
        ((sp + 0x3e0#64) ↦₆₄ trustPollTag ans) ∗
        ((sp + 0x3e8#64) ↦₈ b_3e8) ∗
        ((sp + 0x3e9#64) ↦₃₂ d_3e9) ∗
        ((sp + 0x3ed#64) ↦₁₆ h_3ed) ∗
        ((sp + 0x3ef#64) ↦₈ b_3ef) ∗
        ((sp + 0x3f0#64) ↦₆₄ w_3f0) ∗
        ((sp + 0x3f8#64) ↦₃₂ d_3f8) ∗
        ((sp + 0x3fc#64) ↦₃₂ d_3fc) ∗
        ((sp + 0x400#64) ↦₆₄ w_400) ∗
        ((sp + 0x408#64) ↦₆₄ w_408) ∗
        (if ans.isOk then emp
         else ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr)) := by
  rcases ans with ⟨⟨⟩⟩ | t
  · refine Entails.trans (trustOutErr_split_p1 b sp) ?_
    apply Entails.sepExists_elim; intro b_3e8
    apply Entails.sepExists_elim; intro d_3e9
    apply Entails.sepExists_elim; intro h_3ed
    apply Entails.sepExists_elim; intro b_3ef
    apply Entails.sepExists_elim; intro w_3f0
    apply Entails.sepExists_elim; intro d_3f8
    apply Entails.sepExists_elim; intro d_3fc
    apply Entails.sepExists_elim; intro w_400
    apply Entails.sepExists_elim; intro w_408
    refine Entails.sepExists_right b_3e8
      (Entails.sepExists_right d_3e9
        (Entails.sepExists_right h_3ed
          (Entails.sepExists_right b_3ef
            (Entails.sepExists_right w_3f0
              (Entails.sepExists_right d_3f8
                (Entails.sepExists_right d_3fc
                  (Entails.sepExists_right w_400
                    (Entails.sepExists_right w_408 ?_))))))))
    refine Entails.pure_right ?_ ?_
    · refine ⟨by decide, ?_, ?_⟩
      · intro h; cases h
      · intro h; cases h
    · exact Entails.refl _
  · dsimp only [trustPollOutAt, Except.isOk, Except.toBool, trustPollTag]
    sep_norm
    have hsplit39 := trustOut39_split_p1 sp
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right hsplit39)) ?_
    sep_norm
    apply Entails.sepExists_elim; intro d_3e9
    apply Entails.sepExists_elim; intro h_3ed
    apply Entails.sepExists_elim; intro b_3ef
    apply Entails.sepExists_elim; intro w_3f0
    apply Entails.sepExists_elim; intro d_3f8
    apply Entails.sepExists_elim; intro d_3fc
    apply Entails.sepExists_elim; intro w_400
    apply Entails.sepExists_elim; intro w_408
    refine Entails.sepExists_right (if t then 1#8 else 0#8)
      (Entails.sepExists_right d_3e9
        (Entails.sepExists_right h_3ed
          (Entails.sepExists_right b_3ef
            (Entails.sepExists_right w_3f0
              (Entails.sepExists_right d_3f8
                (Entails.sepExists_right d_3fc
                  (Entails.sepExists_right w_400
                    (Entails.sepExists_right w_408 ?_))))))))
    cases t
    · refine Entails.pure_right ?_ ?_
      · refine ⟨by decide, ?_, ?_⟩
        · intro h; cases h
        · intro _; rfl
      · exact Entails.refl _
    · refine Entails.pure_right ?_ ?_
      · refine ⟨by decide, ?_, ?_⟩
        · intro _; rfl
        · intro h; cases h
      · exact Entails.refl _

/-! ## 4. Post-Specialization Wrappers for `stageP1_trust_call_wp_kit` -/

theorem SepWPp.mono_run {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q₁ Q₂ Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q₁ Qp)
    (himp : ∀ sf P_f, Q₁ sf P_f → Q₂ sf P_f) :
    SepWPp prog ret s P Q₂ Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hq⟩ | hrest⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f, hmf, himp sf P_f hq⟩⟩
  · exact ⟨sf, hsteps, Or.inr hrest⟩

theorem trust_call_wp_specialize_true {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    {ikit : IdentityStoreSpec A img.base} {ist : ikit.IdState}
    {peer : AddrGhost} {remoteIdKey : IdentityKey}
    {s0 s : State} {P : SepProp}
    {outPtr coroPtr ctxPtr msgPtr remoteAddrPtr idStorePtr : BitVec 64}
    (htrust_true : ∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok true)
    (hcall : SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x6e4#64) s P
      (fun sm P_m =>
        (∃ ans : Except Unit Bool,
          ikit.trustRel ist peer.val remoteIdKey .receiving ans ∧
          sm.trace = s.trace ++ ikit.trustEvs peer.val remoteIdKey .receiving ans ∧
          sm.readReg64 .x20 = trustPollTag ans ∧
          (ans = .ok true → sm.readReg64 .x23 = 1#64) ∧
          (ans = .ok false → sm.readReg64 .x23 = 0#64) ∧
          (P_m ⊢
            ∃∗ v_a8 : BitVec 64, ∃∗ v_b8 : BitVec 64, ∃∗ v_d0 : BitVec 64,
              cells (coroPtr + 0x398#64) 2 ∗
              ((s.sp + 0xa8#64) ↦₆₄ v_a8) ∗
              ((s.sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
              ((s.sp + 0xb8#64) ↦₆₄ v_b8) ∗
              ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
              ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
              ((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗
              memRegion (s.sp + 0x3e0#64) 368 ∗
              ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
              ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
              ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
              ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
              (if ans.isOk then emp
               else ((img.base + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr)) ∗
              logOff img ∗
              ikit.identityAt idStorePtr
                (ikit.trustUpdate ist peer.val remoteIdKey .receiving ans) ∗
              protocolAddressAt A peer remoteAddrPtr ∗
              ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
              A.pool ∗
              stackAt s.sp (trustCallStack ikit))) ∧
        sm.sp = s.sp ∧
        sm.readReg64 .x19 = coroPtr ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        ImgCallInv img sm)
      (PanicOomProp s0)) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x6e4#64) s P
      (fun sm P_m =>
        (P_m ⊢
          ∃∗ v_a8 : BitVec 64, ∃∗ v_b8 : BitVec 64, ∃∗ v_d0 : BitVec 64,
            cells (coroPtr + 0x398#64) 2 ∗
            ((s.sp + 0xa8#64) ↦₆₄ v_a8) ∗
            ((s.sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
            ((s.sp + 0xb8#64) ↦₆₄ v_b8) ∗
            ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
            ((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗
            memRegion (s.sp + 0x3e0#64) 368 ∗
            ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
            ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
            ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
            logOff img ∗
            ikit.identityAt idStorePtr
              (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok true)) ∗
            protocolAddressAt A peer remoteAddrPtr ∗
            ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
            A.pool ∗
            stackAt s.sp (trustCallStack ikit)) ∧
        ikit.trustRel ist peer.val remoteIdKey .receiving (.ok true) ∧
        sm.trace = s.trace ++ ikit.trustEvs peer.val remoteIdKey .receiving (.ok true) ∧
        sm.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
        sm.readReg64 .x23 = 1#64 ∧
        sm.sp = s.sp ∧
        sm.readReg64 .x19 = coroPtr ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        ImgCallInv img sm)
      (PanicOomProp s0) := by
  refine SepWPp.mono_run hcall fun sm P_m h => ?_
  rcases h with ⟨⟨ans, hrel, htrm, hx20, htrue, _, hent⟩, hsp, hx19, hx29, hinvm⟩
  have hans : ans = .ok true := htrust_true ans hrel
  subst hans
  dsimp only [Except.isOk, Except.toBool, trustPollTag] at hent hx20
  (try simp only [↓reduceIte] at hent); (try simp only [emp_sepConj] at hent)
  exact ⟨hent, hrel, htrm, hx20, htrue rfl, hsp, hx19, hx29, hinvm⟩

theorem trust_call_wp_specialize_false {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    {ikit : IdentityStoreSpec A img.base} {ist : ikit.IdState}
    {peer : AddrGhost} {remoteIdKey : IdentityKey}
    {s0 s : State} {P : SepProp}
    {outPtr coroPtr ctxPtr msgPtr remoteAddrPtr idStorePtr : BitVec 64}
    (htrust_false : ∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok false)
    (hcall : SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x6e4#64) s P
      (fun sm P_m =>
        (∃ ans : Except Unit Bool,
          ikit.trustRel ist peer.val remoteIdKey .receiving ans ∧
          sm.trace = s.trace ++ ikit.trustEvs peer.val remoteIdKey .receiving ans ∧
          sm.readReg64 .x20 = trustPollTag ans ∧
          (ans = .ok true → sm.readReg64 .x23 = 1#64) ∧
          (ans = .ok false → sm.readReg64 .x23 = 0#64) ∧
          (P_m ⊢
            ∃∗ v_a8 : BitVec 64, ∃∗ v_b8 : BitVec 64, ∃∗ v_d0 : BitVec 64,
              cells (coroPtr + 0x398#64) 2 ∗
              ((s.sp + 0xa8#64) ↦₆₄ v_a8) ∗
              ((s.sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
              ((s.sp + 0xb8#64) ↦₆₄ v_b8) ∗
              ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
              ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
              ((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗
              memRegion (s.sp + 0x3e0#64) 368 ∗
              ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
              ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
              ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
              ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
              (if ans.isOk then emp
               else ((img.base + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr)) ∗
              logOff img ∗
              ikit.identityAt idStorePtr
                (ikit.trustUpdate ist peer.val remoteIdKey .receiving ans) ∗
              protocolAddressAt A peer remoteAddrPtr ∗
              ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
              A.pool ∗
              stackAt s.sp (trustCallStack ikit))) ∧
        sm.sp = s.sp ∧
        sm.readReg64 .x19 = coroPtr ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        ImgCallInv img sm)
      (PanicOomProp s0)) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x6e4#64) s P
      (fun sm P_m =>
        (P_m ⊢
          ∃∗ v_a8 : BitVec 64, ∃∗ v_b8 : BitVec 64, ∃∗ v_d0 : BitVec 64,
            cells (coroPtr + 0x398#64) 2 ∗
            ((s.sp + 0xa8#64) ↦₆₄ v_a8) ∗
            ((s.sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
            ((s.sp + 0xb8#64) ↦₆₄ v_b8) ∗
            ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
            ((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗
            memRegion (s.sp + 0x3e0#64) 368 ∗
            ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
            ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
            ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
            logOff img ∗
            ikit.identityAt idStorePtr
              (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
            protocolAddressAt A peer remoteAddrPtr ∗
            ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
            A.pool ∗
            stackAt s.sp (trustCallStack ikit)) ∧
        ikit.trustRel ist peer.val remoteIdKey .receiving (.ok false) ∧
        sm.trace = s.trace ++ ikit.trustEvs peer.val remoteIdKey .receiving (.ok false) ∧
        sm.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
        sm.readReg64 .x23 = 0#64 ∧
        sm.sp = s.sp ∧
        sm.readReg64 .x19 = coroPtr ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        ImgCallInv img sm)
      (PanicOomProp s0) := by
  refine SepWPp.mono_run hcall fun sm P_m h => ?_
  rcases h with ⟨⟨ans, hrel, htrm, hx20, _, hfalse, hent⟩, hsp, hx19, hx29, hinvm⟩
  have hans : ans = .ok false := htrust_false ans hrel
  subst hans
  dsimp only [Except.isOk, Except.toBool, trustPollTag] at hent hx20
  (try simp only [↓reduceIte] at hent); (try simp only [emp_sepConj] at hent)
  exact ⟨hent, hrel, htrm, hx20, hfalse rfl, hsp, hx19, hx29, hinvm⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
