/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadTrustTailsXExt
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.PublicApi.StoreKit.RecordMove

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadTrustTailsXExtPlaced

open Arm64 ProofLib
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
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlaced

theorem bind_sepWP_steps_frame_placed [LibsignalPlacement]
    {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P_step
      (fun sm P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent) hmm
  have hcrl' : StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem :=
    hcrl.of_keepsFrozen hsteps.keepsFrozen
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hsteps hpc hrun hcrl' hregs R hmm' (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

theorem ret_sepWP_steps_frame_placed [LibsignalPlacement]
    {prog : Program} {ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog ret s P_step
      (fun sf P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sf))
    (hP : P = P_step ∗ F)
    (hret : ∀ sf : State, Steps prog s sf → sf.pc = ret → sf.status = .Running →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem → Q_regs sf →
      Q sf (P_step_post ∗ F)) :
    SepWPp prog ret s P Q Qp :=
  bind_sepWP_steps_frame_placed hcrl hstep hP fun sf hsteps hpc hrun hcrl' hregs =>
    SepWPp.done hpc hrun (hret sf hsteps hpc hrun hcrl' hregs)

theorem call_nopanic_rocl_steps_frame_placed [LibsignalPlacement]
    {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State}
    {P F T : SepProp} {R_pure : Prop} {Q Qp : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (StoreKit.withLsRoCl lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : spec.pre x s = ⌜R_pure⌝ ∗ T)
    (hpure : R_pure)
    (hP : P = T ∗ F)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  have hm' : s.mem ⊨ (StoreKit.withLsRoCl lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [StoreKit.withLsRoCl]
    rw [hpre, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpure, ?_⟩
    rw [sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcrl, hm⟩
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ |
    ⟨code, _, hpost⟩ | ⟨_, _hoom_post⟩
  rotate_right; · dsimp only [StoreKit.withLsRoCl] at _hoom_post; rw [hoom_false] at _hoom_post; exact (not_satisfies_false_sepConj _hoom_post).elim
  · dsimp only [StoreKit.withLsRoCl] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hcrl', hpost⟩ := hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hspm hsp_alm hcsm hcrl' R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [StoreKit.withLsRoCl] at hpost; rw [hpan_false] at hpost
    exact (allowPanic_not_exited hpost).elim
  · dsimp only [StoreKit.withLsRoCl] at hpost; rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim
theorem call_oom_rocl_steps_frame_placed [LibsignalPlacement]
    {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State}
    {P P_spec F : SepProp} {Q : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s0.trace <+: s.trace)
    (hcall : subroutine_ok prog entry (StoreKit.withLsRoCl lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : P_spec ⊢ spec.pre x s)
    (hP : P = P_spec ∗ F)
    (hpan : ∀ sf, spec.onPanic x s sf ⊢ ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (PanicOomProp s0))
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by
      intro _ _; repeat (first | simp only [StoreKit.withLsLogOff] | simp only [withEnvPre]); rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro _; repeat (first | simp only [StoreKit.withLsLogOff] | simp only [withEnvPre]); rfl) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  have hm' : s.mem ⊨ (StoreKit.withLsRoCl lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [StoreKit.withLsRoCl]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcrl, Satisfies.mono (sepConj_mono_left hpre) hm⟩
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpanm, hpost⟩ |
    ⟨code, _, hpost⟩ | ⟨_, _hoom_post⟩
  rotate_right; · dsimp only [StoreKit.withLsRoCl] at _hoom_post; rw [hoom_false] at _hoom_post; exact (not_satisfies_false_sepConj _hoom_post).elim
  · dsimp only [StoreKit.withLsRoCl] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hcrl', hpost⟩ := hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hspm hsp_alm hcsm hcrl' R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [StoreKit.withLsRoCl] at hpost
    have hpost' : sm.mem ⊨ ((⌜allocFailedIn s sm ∧ s.trace <+: sm.trace⌝ ∗ anyHeap) ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left (hpan sm)) hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpanm,
      (⌜allocFailedIn s sm ∧ s.trace <+: sm.trace⌝ ∗ anyHeap) ∗ F, hpost',
      allowPanic_oom_of_prefix htr⟩)⟩
  · dsimp only [StoreKit.withLsRoCl] at hpost; rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

theorem loadShim_pre_intro_placed {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {s : State} {self addrA : BitVec 64}
    (hx0 : s.readReg64 .x0 = self)
    (hx1 : s.readReg64 .x1 = addrA) :
    A.pool ∗ stackAt s.sp kit.loadShimStack ⊢
      (kitLoadShimSpec kit).pre
        ({ self := self, addrA := addrA } : LoadShimCall) s := by
  dsimp only [kitLoadShimSpec]
  exact Entails.pure_right ⟨hx0, hx1⟩ (Entails.refl _)

theorem loadPoll_pre_intro_placed {A : RustAlloc}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {s : State} {sp fut self addrA : BitVec 64} {peer : AddrGhost}
    (henv : kit.envOk s.fs.files)
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
      (StoreKit.kitLoadPollPlacedSpecSE kit Scope encRecord).pre
        (({ fut := fut, out := sp + 0x3e0#64, addrA := addrA, addr := peer } : LoadPollCall),
          self, st0) s := by
  dsimp only [StoreKit.kitLoadPollPlacedSpecSE, withEnvPre, StoreKit.kitLoadPollPlacedSpecS]
  rw [hsp]
  exact Entails.pure_right henv
    (Entails.pure_right ⟨hx0, hx8, haddr⟩ (Entails.refl _))
theorem trustShim_pre_intro_placed {A : RustAlloc}
    {ikit : IdentityStoreSpec A 0#64} {s : State}
    {self addrA keyA : BitVec 64} {d : BitVec 8}
    (hx0 : s.readReg64 .x0 = self)
    (hx1 : s.readReg64 .x1 = addrA)
    (hx2 : s.readReg64 .x2 = keyA)
    (hx3 : (s.readReg64 .x3).setWidth 8 = d) :
    A.pool ∗ stackAt s.sp ikit.trustShimStack ⊢
      (kitTrustShimSpec ikit).pre
        (({ self := self, addrA := addrA, keyA := keyA } : IdentityShimCall), d) s := by
  dsimp only [kitTrustShimSpec]
  exact Entails.pure_right ⟨hx0, hx1, hx2, hx3⟩ (Entails.refl _)

theorem trustPoll_pre_intro_placed [LibsignalPlacement] {A : RustAlloc}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {s : State} {sp fut self addrA keyA : BitVec 64}
    {peer : AddrGhost} {remoteIdKey : IdentityKey}
    (henv : ikit.envOk s.fs.files)
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
      FromRecordCallees.lsLogOff ⊢
      (StoreKit.kitTrustPollPlacedSpecI ikit).pre
        (({ fut := fut, out := sp + 0x3e0#64,
            call := { addrA := addrA, addr := peer, keyA := keyA, key := remoteIdKey } }
            : IdentityPollCall),
          Direction.receiving, self, ist0) s := by
  dsimp only [StoreKit.kitTrustPollPlacedSpecI, StoreKit.withLsLogOff,
    StoreKit.kitTrustPollPlacedSpecE, withEnvPre, StoreKit.kitTrustPollPlacedSpec]
  rw [hsp]
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
  simpa only [sepConj_assoc] using sepConj_mono_left (Q := FromRecordCallees.lsLogOff) h1

theorem trustOutErr_split_p1_placed (sp : BitVec 64) :
    StoreKit.trustPollPlacedOutAt (sp + 0x3e0#64) (.error ()) ⊢
      ∃∗ b_3e8 : BitVec 8, ∃∗ d_3e9 : BitVec 32, ∃∗ h_3ed : BitVec 16, ∃∗ b_3ef : BitVec 8,
      ∃∗ w_3f0 : BitVec 64, ∃∗ d_3f8 : BitVec 32, ∃∗ d_3fc : BitVec 32,
      ∃∗ w_400 : BitVec 64, ∃∗ w_408 : BitVec 64,
        ((sp + 0x3e0#64) ↦₆₄ 0x800000000000001a#64) ∗
        ((sp + 0x3e8#64) ↦₈ b_3e8) ∗
        ((sp + 0x3e9#64) ↦₃₂ d_3e9) ∗
        ((sp + 0x3ed#64) ↦₁₆ h_3ed) ∗
        ((sp + 0x3ef#64) ↦₈ b_3ef) ∗
        ((sp + 0x3f0#64) ↦₆₄ w_3f0) ∗
        ((sp + 0x3f8#64) ↦₃₂ d_3f8) ∗
        ((sp + 0x3fc#64) ↦₃₂ d_3fc) ∗
        ((sp + 0x400#64) ↦₆₄ w_400) ∗
        ((sp + 0x408#64) ↦₆₄ w_408) ∗
        (∃∗ strPtr : BitVec 64, strPtr ↦ᵣ storeHookStr) := by
  dsimp only [StoreKit.trustPollPlacedOutAt, StoreKit.errTailPlacedAt]
  apply Entails.sepExists_elim; intro pStr
  apply Entails.sepExists_elim; intro pVt
  have h40 :
      ((sp + 0x3e0#64 + 8#64) ↦₆₄ pStr) ∗
        (((sp + 0x3e0#64 + 0x10#64) ↦₆₄ 10#64) ∗
          ((sp + 0x3e0#64 + 0x18#64) ↦₆₄ 1#64) ∗
          ((sp + 0x3e0#64 + 0x20#64) ↦₆₄ pVt) ∗
          (pStr ↦ᵣ storeHookStr)) ∗
        memRegion (sp + 0x3e0#64 + 0x28#64) 8 ⊢
      memRegion (sp + 0x3e8#64) 40 ∗ (pStr ↦ᵣ storeHookStr) := by
    rw [ProofLib.memRegion_split (sp + 0x3e8#64) 8 32 (by decide),
        ProofLib.memRegion_split (sp + 0x3e8#64 + 8#64) 8 24 (by decide),
        ProofLib.memRegion_split (sp + 0x3e8#64 + 8#64 + 8#64) 8 16 (by decide),
        ProofLib.memRegion_split (sp + 0x3e8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    have hcomm :
        ((sp + 1000#64) ↦₆₄ pStr) ∗ ((sp + 1008#64) ↦₆₄ 10#64) ∗
          ((sp + 1016#64) ↦₆₄ 1#64) ∗ ((sp + 1024#64) ↦₆₄ pVt) ∗
          (pStr ↦ᵣ storeHookStr) ∗ memRegion (sp + 1032#64) 8 =
        ((sp + 1000#64) ↦₆₄ pStr) ∗ ((sp + 1008#64) ↦₆₄ 10#64) ∗
          ((sp + 1016#64) ↦₆₄ 1#64) ∗ ((sp + 1024#64) ↦₆₄ pVt) ∗
          memRegion (sp + 1032#64) 8 ∗ (pStr ↦ᵣ storeHookStr) := by ac_rfl
    rw [hcomm]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _))))
  refine Entails.trans (sepConj_mono_right h40) ?_
  rw [ProofLib.memRegion_split (sp + 0x3e8#64) 1 39 (by decide), ProofLib.memRegion_one]
  conv =>
    lhs
    simp only [BitVec.add_assoc, BitVec.reduceAdd,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro b_3e8
  refine Entails.sepExists_right b_3e8 ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
    (trustOut39_split_p1 sp)))) ?_
  conv =>
    lhs
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro d_3e9
  apply Entails.sepExists_elim; intro h_3ed
  apply Entails.sepExists_elim; intro b_3ef
  apply Entails.sepExists_elim; intro w_3f0
  apply Entails.sepExists_elim; intro d_3f8
  apply Entails.sepExists_elim; intro d_3fc
  apply Entails.sepExists_elim; intro w_400
  apply Entails.sepExists_elim; intro w_408
  refine Entails.sepExists_right d_3e9 (Entails.sepExists_right h_3ed
    (Entails.sepExists_right b_3ef (Entails.sepExists_right w_3f0
      (Entails.sepExists_right d_3f8 (Entails.sepExists_right d_3fc
        (Entails.sepExists_right w_400 (Entails.sepExists_right w_408 ?_)))))))
  have hex : (pStr ↦ᵣ storeHookStr) ⊢ ∃∗ strPtr : BitVec 64, strPtr ↦ᵣ storeHookStr :=
    Entails.sepExists_right pStr (Entails.refl _)
  refine Entails.trans (Entails.of_eq ?_)
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right hex))))))))))
  ac_rfl
theorem trustPollPlacedOut_any_unpack (sp : BitVec 64) (ans : Except Unit Bool) :
    StoreKit.trustPollPlacedOutAt (sp + 0x3e0#64) ans ⊢
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
         else (∃∗ strPtr : BitVec 64, strPtr ↦ᵣ storeHookStr)) := by
  rcases ans with ⟨⟨⟩⟩ | t
  · refine Entails.trans (trustOutErr_split_p1_placed sp) ?_
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
    refine Entails.pure_right ?_ (Entails.refl _)
    refine ⟨by decide, ?_, ?_⟩
    · intro h; cases h
    · intro h; cases h
  · dsimp only [StoreKit.trustPollPlacedOutAt, Except.isOk, Except.toBool, trustPollTag]
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
    · refine Entails.pure_right ?_ (Entails.refl _)
      refine ⟨by decide, ?_, ?_⟩
      · intro h; cases h
      · intro _; rfl
    · refine Entails.pure_right ?_ (Entails.refl _)
      refine ⟨by decide, ?_, ?_⟩
      · intro _; rfl
      · intro h; cases h
set_option maxHeartbeats 1200000 in
theorem stageP1_load_none_tail_x_ext_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A 0#64}
    {ikit : IdentityStoreSpec A 0#64}
    {st : kit.StoreState}
    (peer : AddrGhost)
    (hdealloc : subroutine_ok (stageP1ProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hmemcpy : subroutine_ok (stageP1ProgPlaced ext) (lsρ "memcpy")
      (StoreKit.withLsCodeRoLoaded lsmpl session2MemcpySpecX))
    (hkit_drop : subroutine_ok (stageP1ProgPlaced ext) (0#64 + kit.loadFutDropOff)
      (StoreKit.withLsRoCl lsmpl futDropSpec))
    (hext_stack : extHookStack ≤ loadCallStack kit)
    (hstack_lt : loadCallStack kit ≤ 2 ^ 64)
    (s0 s s3 : State)
    (loadFutPtr outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     sessStorePtr idStorePtr
     preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
     kyberStorePtr kyberStoreVt rngPtr : BitVec 64)
    (b_390 : BitVec 8)
    (hdrop_nz : 0#64 + kit.loadFutDropOff ≠ 0#64)
    (hbs_nz : BitVec.ofNat 64 kit.loadBoxSize ≠ 0#64)
    (hbs_lt : kit.loadBoxSize < 2 ^ 64)
    (hrel : kit.loadRel st peer.val (.ok none))
    (htr3_s : s3.trace = s.trace ++ kit.loadEvs encRecord peer.val (.ok none))
    (hcrl3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem)
    (hpc3 : s3.pc = stageP1EntryPlaced + 0x14c#64)
    (hrun3 : s3.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hsp3_s : s3.sp = s.sp)
    (hx19_3 : s3.readReg64 .x19 = coroPtr)
    (hx21_3 : s3.readReg64 .x21 = s3.sp + 0x3e0#64)
    (hx24_3 : s3.readReg64 .x24 = s3.sp + 0x370#64)
    (hx25_3 : s3.readReg64 .x25 = s3.sp + 0x210#64)
    (hx26_3 : s3.readReg64 .x26 = outPtr)
    (hx27_3 : s3.readReg64 .x27 = ctxPtr)
    (hx29_3 : s3.readReg64 .x29 = s.readReg64 .x29)
    (hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s) :
    SepWPp (stageP1ProgPlaced ext)
      (0#64 + ikit.trustShimOff) s3
      (((coroPtr + 0x2c8#64) ↦₆₄ loadFutPtr) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ (0#64 + kit.loadFutVtOff)) ∗
       cells (coroPtr + 0x2d8#64) 23 ∗
       decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
         preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
         kyberStorePtr kyberStoreVt rngPtr ∗
       cells (coroPtr + 0xe0#64) 4 ∗
       memRegion (coroPtr + 0x100#64) 336 ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       memRegion (s.sp + 0xd8#64) 348 ∗
       StoreKit.loadPollPlacedOutAtS Scope A (s.sp + 0x3e0#64) (.ok none) ∗
       A.live loadFutPtr kit.loadBoxSize 8 ∗
       kit.loadBoxAt loadFutPtr sessStorePtr remoteAddrPtr 1#8 ∗
       ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (0#64 + ikit.trustShimOff)) ∗
       ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
       ((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
       ((0#64 + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((0#64 + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff)) ∗
       kit.storeAt sessStorePtr st ∗
       protocolAddressAt A peer remoteAddrPtr ∗
       A.pool ∗
       stackAt s.sp (loadCallStack kit))
      (fun s6 P_f =>
        (∃ opt : Option (SessionRecord (List (BitVec 8))),
          kit.loadRel st peer.val (.ok opt) ∧
          s6.trace = s.trace ++ kit.loadEvs encRecord peer.val (.ok opt) ∧
          (P_f ⊢
            decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
              sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
              preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
              kyberStorePtr kyberStoreVt rngPtr ∗
            p1LoadedRecordAt Scope A coroPtr opt ∗
            processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
              idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
              spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
            ((coroPtr + 0x390#64) ↦₈ 0#8) ∗
            memRegion (s.sp + 0xd8#64) 348 ∗
            memRegion (s.sp + 0x3e0#64) 368 ∗
            ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (0#64 + ikit.trustShimOff)) ∗
            ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
            ((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
            ((0#64 + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            ((0#64 + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff)) ∗
            kit.storeAt sessStorePtr st ∗
            protocolAddressAt A peer remoteAddrPtr ∗
            A.pool ∗
            stackAt s.sp (loadCallStack kit))) ∧
        s6.sp = s.sp ∧
        s6.readReg64 .x0 = idStorePtr ∧
        s6.readReg64 .x1 = remoteAddrPtr ∧
        s6.readReg64 .x2 = msgPtr + 0xc8#64 ∧
        s6.readReg64 .x3 = 1#64 ∧
        s6.readReg64 .x19 = coroPtr ∧
        s6.readReg64 .x21 = coroPtr + 0x390#64 ∧
        s6.readReg64 .x26 = outPtr ∧
        s6.readReg64 .x27 = ctxPtr ∧
        s6.readReg64 .x29 = s.readReg64 .x29 ∧
        s6.readReg64 .x30 = stageP1EntryPlaced + 0x650#64 ∧
        calleeSavedVRegs s6 = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl s6.mem)
      (PanicOomProp s0) := by
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3_s]; exact hsp_align
  have hmr_d8 : memRegion (s.sp + 0xd8#64) 348 =
      memRegion (s.sp + 0xd8#64) 312 ∗ memRegion (s.sp + 0x210#64) 36 :=
    ProofLib.memRegion_split' (b := s.sp + 0xd8#64) (n := 312) (k := 36)
      (b' := s.sp + 0x210#64) rfl (by bv_omega) (by decide)
  rw [show StoreKit.loadPollPlacedOutAtS Scope A (s.sp + 0x3e0#64) (.ok none) =
    E2E.InMem.HashbrownBin.pollOptSessionRecordResultAt A (s.sp + 0x3e0#64) none from rfl]
  refine SepWPp.weaken_frame (Entails.of_eq (pollOptSessionRecordNone_split_eq A s.sp))
    (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun bs_418 => SepWPp.exists_elim fun d_414 =>
    SepWPp.exists_elim fun w_40c => SepWPp.exists_elim fun w_404 =>
    SepWPp.exists_elim fun w_3fc => SepWPp.exists_elim fun w_3f4 =>
    SepWPp.exists_elim fun d_3f0 => SepWPp.exists_elim fun w_3e8 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hmr_d8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (sp210_36_split_eq s.sp)) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u_230 => SepWPp.exists_elim fun u_228 =>
    SepWPp.exists_elim fun u_220 => SepWPp.exists_elim fun u_218 =>
    SepWPp.exists_elim fun u_210 => ?_
  refine SepWPp.weaken_frame (P₁ := ⌜bs_418.length = 312⌝) (P₂ := ⌜bs_418.length = 312⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun hbs312 => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_loadCall_to_ext kit s.sp hext_stack hstack_lt))
    (by sep_focus) ?_
  sep_norm
  have hstep4 := p1_seg3_vregs_wp_ext_placed
    ext hmemcpy s3 hcrl3 coroPtr
    loadFutPtr (0#64 + kit.loadFutVtOff) (0#64 + kit.loadFutDropOff)
    w_3e8 w_3f4 w_3fc w_404 w_40c u_210 u_218 u_220 u_228
    d_3f0 d_414 u_230 bs_418
    hpc3 hrun3 hsp3_align hbs312 hdrop_nz hx19_3 hx21_3 hx24_3 hx25_3
  rw [hsp3_s] at hstep4
  refine bind_sepWP_steps_frame_placed hcrl3 hstep4 (by sep_focus)
    fun s4 _ hpc4 hrun4 hcrl4 hregs4 => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_loadCall_to_ext kit s.sp hext_stack hstack_lt).symm)
    (by sep_focus) ?_
  rcases hregs4 with ⟨hsp4_s, htr4_3, _, hx19_4, hx21_4, _, hx23_4, hx24_4, _, hx26_4, hx27_4,
    _, hx29_4, hx30_4, hvregs4_3⟩
  have hsp4_al : s4.spAligned = true := by simpa only [State.spAligned, hsp4_s] using hsp_align
  refine call_nopanic_rocl_steps_frame_placed (x := ()) (T := emp)
    hcrl4 hkit_drop hpc4 hrun4 hsp4_al hx30_4
    (by dsimp only [LibsignalPublicApi.StoreSession.futDropSpec]; exact (pure_true_sepConj emp).symm)
    True.intro (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s5 _ hpc5 hrun5 hsp5_4 _ hcs5 hcrl5 => ?_)
  dsimp only [LibsignalPublicApi.StoreSession.futDropSpec]
  refine SepWPp.pure_elim fun htr5_4 => ?_
  have hsp5_s : s5.sp = s.sp := hsp5_4.trans hsp4_s
  have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5_s]; exact hsp_align
  rcases hcs5 with ⟨hx19_cs5, _, hx21_cs5, _, hx23_cs5, hx24_cs5, _, hx26_cs5, hx27_cs5, _,
    hx29_cs5, hvregs_cs5⟩
  have hx19_5 : s5.readReg64 .x19 = coroPtr := hx19_cs5.trans hx19_4
  have hx21_5 : s5.readReg64 .x21 = loadFutPtr := hx21_cs5.trans hx21_4
  have hx23_5 : s5.readReg64 .x23 = 0xffffffffffffffff#64 := hx23_cs5.trans hx23_4
  have hx24_5 : s5.readReg64 .x24 = 0#64 + kit.loadFutVtOff := hx24_cs5.trans hx24_4
  have hx26_5 : s5.readReg64 .x26 = outPtr := by rw [hx26_cs5, hx26_4, hx26_3]
  have hx27_5 : s5.readReg64 .x27 = ctxPtr := by rw [hx27_cs5, hx27_4, hx27_3]
  have hx29_5 : s5.readReg64 .x29 = s.readReg64 .x29 := by rw [hx29_cs5, hx29_4, hx29_3]
  refine SepWPp.weaken_frame
    (kit.loadBoxAt_memRegion loadFutPtr sessStorePtr remoteAddrPtr 1#8)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (cells25_fold2 coroPtr loadFutPtr (0#64 + kit.loadFutVtOff))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_loadCall_to_alloc kit s.sp hstack_lt))
    (by sep_focus) ?_
  sep_norm
  have hstep6 := p1_seg4_vregs_wp_ext_placed
    (A := A) ext hdealloc s5
    coroPtr loadFutPtr (0#64 + kit.loadFutVtOff) (0#64 + ikit.trustShimOff)
    msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr
    kit.loadBoxSize b_390
    hpc5 hrun5 hsp5_align hbs_nz hbs_lt hx19_5 hx21_5 hx23_5 hx24_5
  rw [hsp5_s] at hstep6
  simp only [BitVec.add_assoc] at hstep6
  refine bind_sepWP_steps_frame_placed hcrl5 hstep6 (by sep_focus)
    fun s6 _ hpc6 hrun6 hcrl6 hregs6 => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_loadCall_to_alloc kit s.sp hstack_lt).symm)
    (by sep_focus) ?_
  refine SepWPp.done hpc6 hrun6 ?_
  rcases hregs6 with ⟨hsp6_s, htr6_5, hx0_6, hx1_6, hx2_6, hx3_6, hx19_6, hx21_6, _, hx26_6,
    hx27_6, _, hx29_6, hx30_6, hvregs6_5⟩
  have htr6_s : s6.trace = s.trace ++ kit.loadEvs encRecord peer.val (.ok none) := by
    rw [htr6_5, htr5_4, htr4_3, htr3_s]
  have hvregs6_s : calleeSavedVRegs s6 = calleeSavedVRegs s := by
    rw [hvregs6_5, hvregs_cs5, hvregs4_3, hvregs3]
  refine ⟨⟨none, hrel, htr6_s, ?_⟩, hsp6_s, hx0_6, hx1_6, hx2_6, hx3_6, hx19_6, hx21_6,
    hx26_6.trans hx26_5, hx27_6.trans hx27_5, hx29_6.trans hx29_5, hx30_6, hvregs6_s, hcrl6⟩
  dsimp only [p1LoadedRecordAt]
  sep_norm
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))
set_option maxHeartbeats 1200000 in
theorem stageP1_load_some_tail_x_ext_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A 0#64}
    {ikit : IdentityStoreSpec A 0#64}
    {st : kit.StoreState}
    (peer : AddrGhost) (r : SessionRecord (List (BitVec 8)))
    (hdealloc : subroutine_ok (stageP1ProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hmemcpy : subroutine_ok (stageP1ProgPlaced ext) (lsρ "memcpy")
      (StoreKit.withLsCodeRoLoaded lsmpl session2MemcpySpecX))
    (hkit_drop : subroutine_ok (stageP1ProgPlaced ext) (0#64 + kit.loadFutDropOff)
      (StoreKit.withLsRoCl lsmpl futDropSpec))
    (hext_stack : extHookStack ≤ loadCallStack kit)
    (hstack_lt : loadCallStack kit ≤ 2 ^ 64)
    (s0 s s3 : State)
    (loadFutPtr outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     sessStorePtr idStorePtr
     preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
     kyberStorePtr kyberStoreVt rngPtr : BitVec 64)
    (b_390 : BitVec 8)
    (hdrop_nz : 0#64 + kit.loadFutDropOff ≠ 0#64)
    (hbs_nz : BitVec.ofNat 64 kit.loadBoxSize ≠ 0#64)
    (hbs_lt : kit.loadBoxSize < 2 ^ 64)
    (hrel : kit.loadRel st peer.val (.ok (some r)))
    (htr3_s : s3.trace = s.trace ++ kit.loadEvs encRecord peer.val (.ok (some r)))
    (hcrl3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem)
    (hpc3 : s3.pc = stageP1EntryPlaced + 0x14c#64)
    (hrun3 : s3.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hsp3_s : s3.sp = s.sp)
    (hx19_3 : s3.readReg64 .x19 = coroPtr)
    (hx21_3 : s3.readReg64 .x21 = s3.sp + 0x3e0#64)
    (hx24_3 : s3.readReg64 .x24 = s3.sp + 0x370#64)
    (hx25_3 : s3.readReg64 .x25 = s3.sp + 0x210#64)
    (hx26_3 : s3.readReg64 .x26 = outPtr)
    (hx27_3 : s3.readReg64 .x27 = ctxPtr)
    (hx29_3 : s3.readReg64 .x29 = s.readReg64 .x29)
    (hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s) :
    SepWPp (stageP1ProgPlaced ext)
      (0#64 + ikit.trustShimOff) s3
      (((coroPtr + 0x2c8#64) ↦₆₄ loadFutPtr) ∗
       ((coroPtr + 0x2d0#64) ↦₆₄ (0#64 + kit.loadFutVtOff)) ∗
       cells (coroPtr + 0x2d8#64) 23 ∗
       decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
         preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
         kyberStorePtr kyberStoreVt rngPtr ∗
       cells (coroPtr + 0xe0#64) 4 ∗
       memRegion (coroPtr + 0x100#64) 336 ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       memRegion (s.sp + 0xd8#64) 348 ∗
       StoreKit.loadPollPlacedOutAtS Scope A (s.sp + 0x3e0#64) (.ok (some r)) ∗
       A.live loadFutPtr kit.loadBoxSize 8 ∗
       kit.loadBoxAt loadFutPtr sessStorePtr remoteAddrPtr 1#8 ∗
       ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (0#64 + ikit.trustShimOff)) ∗
       ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
       ((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
       ((0#64 + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((0#64 + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff)) ∗
       kit.storeAt sessStorePtr st ∗
       protocolAddressAt A peer remoteAddrPtr ∗
       A.pool ∗
       stackAt s.sp (loadCallStack kit))
      (fun s6 P_f =>
        (∃ opt : Option (SessionRecord (List (BitVec 8))),
          kit.loadRel st peer.val (.ok opt) ∧
          s6.trace = s.trace ++ kit.loadEvs encRecord peer.val (.ok opt) ∧
          (P_f ⊢
            decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
              sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
              preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
              kyberStorePtr kyberStoreVt rngPtr ∗
            p1LoadedRecordAt Scope A coroPtr opt ∗
            processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
              idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
              spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
            ((coroPtr + 0x390#64) ↦₈ 0#8) ∗
            memRegion (s.sp + 0xd8#64) 348 ∗
            memRegion (s.sp + 0x3e0#64) 368 ∗
            ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (0#64 + ikit.trustShimOff)) ∗
            ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
            ((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
            ((0#64 + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            ((0#64 + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff)) ∗
            kit.storeAt sessStorePtr st ∗
            protocolAddressAt A peer remoteAddrPtr ∗
            A.pool ∗
            stackAt s.sp (loadCallStack kit))) ∧
        s6.sp = s.sp ∧
        s6.readReg64 .x0 = idStorePtr ∧
        s6.readReg64 .x1 = remoteAddrPtr ∧
        s6.readReg64 .x2 = msgPtr + 0xc8#64 ∧
        s6.readReg64 .x3 = 1#64 ∧
        s6.readReg64 .x19 = coroPtr ∧
        s6.readReg64 .x21 = coroPtr + 0x390#64 ∧
        s6.readReg64 .x26 = outPtr ∧
        s6.readReg64 .x27 = ctxPtr ∧
        s6.readReg64 .x29 = s.readReg64 .x29 ∧
        s6.readReg64 .x30 = stageP1EntryPlaced + 0x650#64 ∧
        calleeSavedVRegs s6 = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl s6.mem)
      (PanicOomProp s0) := by
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3_s]; exact hsp_align
  have hmr_d8 : memRegion (s.sp + 0xd8#64) 348 =
      memRegion (s.sp + 0xd8#64) 312 ∗ memRegion (s.sp + 0x210#64) 36 :=
    ProofLib.memRegion_split' (b := s.sp + 0xd8#64) (n := 312) (k := 36)
      (b' := s.sp + 0x210#64) rfl (by bv_omega) (by decide)
  rw [show StoreKit.loadPollPlacedOutAtS Scope A (s.sp + 0x3e0#64) (.ok (some r)) =
    loadPollOutAtS Scope A 0#64 (s.sp + 0x3e0#64) (.ok (some r)) from rfl]
  refine SepWPp.weaken_frame
    (loadPollOut_some_unpack Scope A 0#64 s.sp r)
    (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun g =>
    SepWPp.exists_elim fun w4 =>
    SepWPp.exists_elim fun w5 =>
    SepWPp.exists_elim fun w6 =>
    SepWPp.exists_elim fun tail => ?_
  refine SepWPp.pure_elim fun ⟨hscope, hprev_lt, htail_inl, htail_len⟩ => ?_
  have hw_ne_neg3 : g.prevCap ≠ 0xfffffffffffffffd#64 := by bv_omega
  have hw_ne_neg2 : g.prevCap ≠ 0xfffffffffffffffe#64 := by bv_omega
  have hw_ne_neg1 : g.prevCap ≠ 0xffffffffffffffff#64 := by bv_omega
  refine SepWPp.weaken_frame (Entails.of_eq hmr_d8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (sp210_36_split_eq s.sp)) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u_230 => SepWPp.exists_elim fun u_228 =>
    SepWPp.exists_elim fun u_220 => SepWPp.exists_elim fun u_218 =>
    SepWPp.exists_elim fun u_210 => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_loadCall_to_ext kit s.sp hext_stack hstack_lt))
    (by sep_focus) ?_
  sep_norm
  have hstep4 := p1_load_some_seg3_vregs_wp_ext_placed
    ext hmemcpy s3 hcrl3 coroPtr
    loadFutPtr (0#64 + kit.loadFutVtOff) (0#64 + kit.loadFutDropOff)
    g.prevCap g.prevPtr
    ((recordCurCap g).extractLsb' 0 32 ++ (0#64 : BitVec 64).extractLsb' 32 32)
    (w4.extractLsb' 0 32 ++ (recordCurCap g).extractLsb' 32 32)
    (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
    (w6.extractLsb' 0 32 ++ w5.extractLsb' 32 32)
    u_210 u_218 u_220 u_228
    ((0#64 : BitVec 64).extractLsb' 0 32) (w6.extractLsb' 32 32) u_230 tail
    hw_ne_neg3 hpc3 hrun3 hsp3_align htail_len hdrop_nz hx19_3 hx21_3 hx24_3 hx25_3
  rw [hsp3_s] at hstep4
  refine bind_sepWP_steps_frame_placed hcrl3 hstep4 (by sep_focus)
    fun s4 _ hpc4 hrun4 hcrl4 hregs4 => ?_
  rcases hregs4 with ⟨hsp4_s, htr4_3, _, hx19_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4,
    hx26_4, hx27_4, hx28_4, hx29_4, hx30_4, hvregs4_3⟩
  have hsp4_al : s4.spAligned = true := by simpa only [State.spAligned, hsp4_s] using hsp_align
  refine SepWPp.weaken_frame
    (sp3e0_368_fold s.sp g.prevCap g.prevPtr
      ((recordCurCap g).extractLsb' 0 32 ++ (0#64 : BitVec 64).extractLsb' 32 32)
      (w4.extractLsb' 0 32 ++ (recordCurCap g).extractLsb' 32 32)
      (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
      (w6.extractLsb' 0 32 ++ w5.extractLsb' 32 32)
      ((0#64 : BitVec 64).extractLsb' 0 32) (w6.extractLsb' 32 32) tail htail_len)
    (by sep_focus) ?_
  refine call_nopanic_rocl_steps_frame_placed (x := ()) (T := emp)
    hcrl4 hkit_drop hpc4 hrun4 hsp4_al hx30_4
    (by dsimp only [LibsignalPublicApi.StoreSession.futDropSpec]; exact (pure_true_sepConj emp).symm)
    True.intro (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s5 _ hpc5 hrun5 hsp5_4 _ hcs5 hcrl5 => ?_)
  dsimp only [LibsignalPublicApi.StoreSession.futDropSpec]
  refine SepWPp.pure_elim fun htr5_4 => ?_
  have hsp5_s : s5.sp = s.sp := hsp5_4.trans hsp4_s
  have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5_s]; exact hsp_align
  rcases hcs5 with ⟨hx19_cs5, _, hx21_cs5, hx22_cs5, hx23_cs5, hx24_cs5, hx25_cs5,
    hx26_cs5, hx27_cs5, hx28_cs5, hx29_cs5, hvregs_cs5⟩
  have hx19_5 : s5.readReg64 .x19 = coroPtr := hx19_cs5.trans hx19_4
  have hx21_5 : s5.readReg64 .x21 = loadFutPtr := hx21_cs5.trans hx21_4
  have hx22_5 : s5.readReg64 .x22 = ((0#64 : BitVec 64).extractLsb' 0 32).zeroExtend 64 :=
    hx22_cs5.trans hx22_4
  have hx23_5 : s5.readReg64 .x23 = g.prevCap := hx23_cs5.trans hx23_4
  have hx24_5 : s5.readReg64 .x24 = 0#64 + kit.loadFutVtOff := hx24_cs5.trans hx24_4
  have hx25_5 : s5.readReg64 .x25 = s5.sp + 0x210#64 := by rw [hx25_cs5, hx25_4, hsp5_s]
  have hx26_5 : s5.readReg64 .x26 = outPtr := by rw [hx26_cs5, hx26_4, hx26_3]
  have hx27_5 : s5.readReg64 .x27 = ctxPtr := by rw [hx27_cs5, hx27_4, hx27_3]
  have hx28_5 : s5.readReg64 .x28 = g.prevPtr := hx28_cs5.trans hx28_4
  have hx29_5 : s5.readReg64 .x29 = s.readReg64 .x29 := by rw [hx29_cs5, hx29_4, hx29_3]
  refine SepWPp.weaken_frame
    (kit.loadBoxAt_memRegion loadFutPtr sessStorePtr remoteAddrPtr 1#8)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (cells25_fold2 coroPtr loadFutPtr (0#64 + kit.loadFutVtOff))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (coro_body336_split coroPtr) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun c0 => SepWPp.exists_elim fun c1 =>
    SepWPp.exists_elim fun c2 => SepWPp.exists_elim fun c3 =>
    SepWPp.exists_elim fun c4 => SepWPp.exists_elim fun c5 =>
    SepWPp.exists_elim fun c6 => ?_
  have hstep6 := p1_load_some_seg4_vregs_wp_ext_placed
    (A := A) ext hdealloc hmemcpy s5 hcrl5
    coroPtr loadFutPtr (0#64 + kit.loadFutVtOff) (0#64 + ikit.trustShimOff)
    msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr
    g.prevCap g.prevPtr
    ((recordCurCap g).extractLsb' 0 32 ++ (0#64 : BitVec 64).extractLsb' 32 32)
    (w4.extractLsb' 0 32 ++ (recordCurCap g).extractLsb' 32 32)
    (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
    (w6.extractLsb' 0 32 ++ w5.extractLsb' 32 32)
    c0 c1
    (c3.extractLsb' 0 32 ++ c2.extractLsb' 32 32)
    (c4.extractLsb' 0 32 ++ c3.extractLsb' 32 32)
    (c5.extractLsb' 0 32 ++ c4.extractLsb' 32 32)
    (c6.extractLsb' 0 32 ++ c5.extractLsb' 32 32)
    ((0#64 : BitVec 64).extractLsb' 0 32) (w6.extractLsb' 32 32)
    (c2.extractLsb' 0 32) (c6.extractLsb' 32 32)
    tail kit.loadBoxSize b_390
    hw_ne_neg2 hw_ne_neg1 htail_len
    hpc5 hrun5 hsp5_align hbs_nz hbs_lt
    hx19_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 hx28_5
  rw [hsp5_s] at hstep6
  simp only [BitVec.add_assoc] at hstep6
  refine bind_sepWP_steps_frame_placed hcrl5 hstep6 (by sep_focus)
    fun s6 _ hpc6 hrun6 hcrl6 hregs6 => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_loadCall_to_ext kit s.sp hext_stack hstack_lt).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (sp_d8_bytes_rejoin s.sp
      ((recordCurCap g).extractLsb' 0 32 ++ (0#64 : BitVec 64).extractLsb' 32 32)
      (w4.extractLsb' 0 32 ++ (recordCurCap g).extractLsb' 32 32)
      (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
      (w6.extractLsb' 0 32 ++ w5.extractLsb' 32 32)
      (w6.extractLsb' 32 32) tail htail_len)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (coro_e0_some_pack Scope A coroPtr g r w4 w5 w6 tail hscope htail_inl)
    (by sep_focus) ?_
  refine SepWPp.done hpc6 hrun6 ?_
  rcases hregs6 with ⟨hsp6_s, htr6_5, hx0_6, hx1_6, hx2_6, hx3_6, hx19_6, hx21_6, _, hx26_6,
    hx27_6, _, hx29_6, hx30_6, hvregs6_5⟩
  have htr6_s : s6.trace = s.trace ++ kit.loadEvs encRecord peer.val (.ok (some r)) := by
    rw [htr6_5, htr5_4, htr4_3, htr3_s]
  have hvregs6_s : calleeSavedVRegs s6 = calleeSavedVRegs s := by
    rw [hvregs6_5, hvregs_cs5, hvregs4_3, hvregs3]
  refine ⟨⟨some r, hrel, htr6_s, ?_⟩, hsp6_s, hx0_6, hx1_6, hx2_6, hx3_6, hx19_6, hx21_6,
    hx26_6.trans hx26_5, hx27_6.trans hx27_5, hx29_6.trans hx29_5, hx30_6, hvregs6_s, hcrl6⟩
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))
set_option maxHeartbeats 1200000 in
theorem stageP1_trust_call_tail_x_ext_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {ikit : IdentityStoreSpec A 0#64}
    {ist : ikit.IdState}
    (peer : AddrGhost) (remoteIdKey : IdentityKey) (ans : Except Unit Bool)
    (hdealloc : subroutine_ok (stageP1ProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hikit_drop : subroutine_ok (stageP1ProgPlaced ext) (0#64 + ikit.trustFutDropOff)
      (StoreKit.withLsRoCl lsmpl futDropSpec))
    (hstack_lt : trustCallStack ikit ≤ 2 ^ 64)
    (s0 s s9 : State)
    (trustFutPtr outPtr coroPtr ctxPtr msgPtr remoteAddrPtr idStorePtr
     u_a8 u_b0 u_b8 u_c8 u_d0 : BitVec 64)
    (hdrop_nz : 0#64 + ikit.trustFutDropOff ≠ 0#64)
    (hbs_nz : BitVec.ofNat 64 ikit.trustBoxSize ≠ 0#64)
    (hbs_lt : ikit.trustBoxSize < 2 ^ 64)
    (hrel : ikit.trustRel ist peer.val remoteIdKey .receiving ans)
    (htr9_s : s9.trace = s.trace ++ ikit.trustEvs peer.val remoteIdKey .receiving ans)
    (hcrl9 : StoreKit.LibsignalCodeRoLoaded lsmpl s9.mem)
    (hpc9 : s9.pc = stageP1EntryPlaced + 0x66c#64)
    (hrun9 : s9.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hsp9_s : s9.sp = s.sp)
    (hx19_9 : s9.readReg64 .x19 = coroPtr)
    (hx21_9 : s9.readReg64 .x21 = coroPtr + 0x390#64)
    (hx26_9 : s9.readReg64 .x26 = outPtr)
    (hx29_9 : s9.readReg64 .x29 = s.readReg64 .x29)
    (hvregs9 : calleeSavedVRegs s9 = calleeSavedVRegs s) :
    SepWPp (stageP1ProgPlaced ext)
      (stageP1EntryPlaced + 0x6e4#64) s9
      (((coroPtr + 0x398#64) ↦₆₄ trustFutPtr) ∗
       ((coroPtr + 0x3a0#64) ↦₆₄ (0#64 + ikit.trustFutVtOff)) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       StoreKit.trustPollPlacedOutAt (s.sp + 0x3e0#64) ans ∗
       memRegion (s.sp + 0x410#64) 320 ∗
       ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff)) ∗
       ((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
       ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff)) ∗
       FromRecordCallees.lsLogOff ∗
       A.live trustFutPtr ikit.trustBoxSize 8 ∗
       ikit.trustBoxAt trustFutPtr idStorePtr remoteAddrPtr
         (msgPtr + 0xc8#64) 1#8 (directionByte .receiving) ∗
       ikit.identityAt idStorePtr
         (ikit.trustUpdate ist peer.val remoteIdKey .receiving ans) ∗
       protocolAddressAt A peer remoteAddrPtr ∗
       ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
       A.pool ∗
       stackAt s.sp (trustCallStack ikit))
      (fun sm P_m =>
        (∃ ans' : Except Unit Bool,
          ikit.trustRel ist peer.val remoteIdKey .receiving ans' ∧
          sm.trace = s.trace ++ ikit.trustEvs peer.val remoteIdKey .receiving ans' ∧
          sm.readReg64 .x20 = trustPollTag ans' ∧
          (ans' = .ok true → sm.readReg64 .x23 = 1#64) ∧
          (ans' = .ok false → sm.readReg64 .x23 = 0#64) ∧
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
              ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff)) ∗
              ((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
              ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
              ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff)) ∗
              (if ans'.isOk then emp
               else (∃∗ strPtr : BitVec 64, strPtr ↦ᵣ storeHookStr)) ∗
              FromRecordCallees.lsLogOff ∗
              ikit.identityAt idStorePtr
                (ikit.trustUpdate ist peer.val remoteIdKey .receiving ans') ∗
              protocolAddressAt A peer remoteAddrPtr ∗
              ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
              A.pool ∗
              stackAt s.sp (trustCallStack ikit))) ∧
        sm.sp = s.sp ∧
        sm.readReg64 .x19 = coroPtr ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem)
      (PanicOomProp s0) := by
  have hsp9_align : (s9.sp &&& 15#64 == 0#64) = true := by rw [hsp9_s]; exact hsp_align
  have hmr_3e0 : memRegion (s.sp + 0x3e0#64) 368 =
      memRegion (s.sp + 0x3e0#64) 48 ∗ memRegion (s.sp + 0x410#64) 320 :=
    ProofLib.memRegion_split' (b := s.sp + 0x3e0#64) (n := 48) (k := 320)
      (b' := s.sp + 0x410#64) rfl (by bv_omega) (by decide)
  refine SepWPp.weaken_frame
    (trustPollPlacedOut_any_unpack s.sp ans)
    (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun b_3e8 =>
    SepWPp.exists_elim fun d_3e9 =>
    SepWPp.exists_elim fun h_3ed =>
    SepWPp.exists_elim fun b_3ef =>
    SepWPp.exists_elim fun w_3f0 =>
    SepWPp.exists_elim fun d_3f8 =>
    SepWPp.exists_elim fun d_3fc =>
    SepWPp.exists_elim fun w_400 =>
    SepWPp.exists_elim fun w_408 => ?_
  refine SepWPp.pure_elim fun ⟨hw_ne_neg3, hb_true, hb_false⟩ => ?_
  have hstep10 := p1_seg6a_any_vregs_wp_ext_placed
    ext s9 coroPtr outPtr
    trustFutPtr (0#64 + ikit.trustFutVtOff) (0#64 + ikit.trustFutDropOff)
    (trustPollTag ans) w_3f0 w_400 w_408 u_a8 u_b0 u_b8 u_c8 u_d0
    d_3e9 d_3f8 d_3fc h_3ed b_3e8 b_3ef
    hw_ne_neg3 hpc9 hrun9 hsp9_align hdrop_nz hx19_9 hx21_9 hx26_9
  rw [hsp9_s] at hstep10
  refine bind_sepWP_steps_frame_placed hcrl9 hstep10 (by sep_focus)
    fun s10 _ hpc10 hrun10 hcrl10 hregs10 => ?_
  rcases hregs10 with ⟨hsp10_s, htr10_9, _, hx19_10, hx20_10, hx21_10, hx23_10, hx25_10,
    _, hx29_10, hx30_10, hvregs10_9⟩
  have hsp10_al : s10.spAligned = true := by simpa only [State.spAligned, hsp10_s] using hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq hmr_3e0.symm) (by sep_focus) ?_
  refine call_nopanic_rocl_steps_frame_placed (x := ()) (T := emp)
    hcrl10 hikit_drop hpc10 hrun10 hsp10_al hx30_10
    (by dsimp only [LibsignalPublicApi.StoreSession.futDropSpec]; exact (pure_true_sepConj emp).symm)
    True.intro (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s11 _ hpc11 hrun11 hsp11_10 _ hcs11 hcrl11 => ?_)
  dsimp only [LibsignalPublicApi.StoreSession.futDropSpec]
  refine SepWPp.pure_elim fun htr11_10 => ?_
  have hsp11_s : s11.sp = s.sp := hsp11_10.trans hsp10_s
  have hsp11_align : (s11.sp &&& 15#64 == 0#64) = true := by rw [hsp11_s]; exact hsp_align
  rcases hcs11 with ⟨hx19_cs11, hx20_cs11, hx21_cs11, _, hx23_cs11, _, hx25_cs11, _, _, _,
    hx29_cs11, hvregs_cs11⟩
  have hx19_11 : s11.readReg64 .x19 = coroPtr := hx19_cs11.trans hx19_10
  have hx20_11 : s11.readReg64 .x20 = trustPollTag ans := hx20_cs11.trans hx20_10
  have hx21_11 : s11.readReg64 .x21 = trustFutPtr := hx21_cs11.trans hx21_10
  have hx23_11 : s11.readReg64 .x23 = b_3e8.zeroExtend 64 := hx23_cs11.trans hx23_10
  have hx25_11 : s11.readReg64 .x25 = 0#64 + ikit.trustFutVtOff := hx25_cs11.trans hx25_10
  have hx29_11 : s11.readReg64 .x29 = s.readReg64 .x29 :=
    by rw [hx29_cs11, hx29_10, hx29_9]
  refine SepWPp.weaken_frame
    (ikit.trustBoxAt_memRegion trustFutPtr idStorePtr remoteAddrPtr
      (msgPtr + 0xc8#64) 1#8 (directionByte .receiving))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (cells2_fold_398 coroPtr trustFutPtr (0#64 + ikit.trustFutVtOff))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_trustCall_to_alloc ikit s.sp hstack_lt))
    (by sep_focus) ?_
  sep_norm
  have hstep12 := p1_seg6_dealloc_vregs_wp_ext_placed
    (A := A) ext hdealloc s11
    coroPtr trustFutPtr (0#64 + ikit.trustFutVtOff)
    (trustPollTag ans) (b_3e8.zeroExtend 64) ikit.trustBoxSize
    hpc11 hrun11 hsp11_align hbs_nz hbs_lt
    hx19_11 hx20_11 hx21_11 hx23_11 hx25_11
  rw [hsp11_s] at hstep12
  simp only [BitVec.add_assoc] at hstep12
  refine bind_sepWP_steps_frame_placed hcrl11 hstep12 (by sep_focus)
    fun sm _ hpcm hrunm hcrlm hregsm => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_trustCall_to_alloc ikit s.sp hstack_lt).symm)
    (by sep_focus) ?_
  refine SepWPp.done hpcm hrunm ?_
  rcases hregsm with ⟨hspm_s, htrm_11, hx19_m, hx20_m, hx23_m, _, hx29_m, hvregsm_11⟩
  have htrm_s : sm.trace = s.trace ++ ikit.trustEvs peer.val remoteIdKey .receiving ans := by
    rw [htrm_11, htr11_10, htr10_9, htr9_s]
  have hvregsm_s : calleeSavedVRegs sm = calleeSavedVRegs s := by
    rw [hvregsm_11, hvregs_cs11, hvregs10_9, hvregs9]
  have htrue_m : ans = .ok true → sm.readReg64 .x23 = 1#64 := fun ha => by
    rw [hx23_m, hb_true ha]; rfl
  have hfalse_m : ans = .ok false → sm.readReg64 .x23 = 0#64 := fun ha => by
    rw [hx23_m, hb_false ha]; rfl
  refine ⟨⟨ans, hrel, htrm_s, hx20_m, htrue_m, hfalse_m, ?_⟩,
    hspm_s, hx19_m, hx29_m.trans hx29_11, hvregsm_s, hcrlm⟩
  refine Entails.sepExists_right (d_3fc.zeroExtend 64)
    (Entails.sepExists_right w_3f0
      (Entails.sepExists_right (d_3f8.zeroExtend 64) ?_))
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadTrustTailsXExtPlaced
