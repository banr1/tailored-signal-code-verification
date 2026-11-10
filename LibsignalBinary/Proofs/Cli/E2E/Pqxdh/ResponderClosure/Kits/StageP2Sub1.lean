/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitE
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA1
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs

/-!
# Stage P2 Substages P2.1 and P2.2

Composes basic-block lemmas with `StageP2PureCallees` and `SignedPreKeyStoreKitOkImgE` on
`tripleRatchetProgAtExt img.base ext` to prove `stageP2_sub1_kits` (`+0x0868 → +0x0f14`) and CPS
`stageP2_sub2_kits` (`+0x0f14 → +0x1460` or `+0x0f38` Arm 1).
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
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  protocolAddressAt decryptPrekeySavedRegsAt

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

theorem p2_fnAddr_pkSerialize_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName +
      bv% ((2^64 + ls_off% "<libsignal_core::curve::PublicKey>::serialize" -
        ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64) =
    (tripleRatchetProgAtExt b ext).fnAddr "<libsignal_core::curve::PublicKey>::serialize" := by
  simp [tripleRatchetProgAtExt, Program.fnAddr, decryptPrekeyClosureName,
    ls_lemma% fnOff "<libsignal_core::curve::PublicKey>::serialize",
    ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"]

theorem p2_fnAddr_promoteMatching_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName +
      bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session" -
        ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64) =
    (tripleRatchetProgAtExt b ext).fnAddr
      "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session" := by
  simp [tripleRatchetProgAtExt, Program.fnAddr, decryptPrekeyClosureName,
    ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session",
    ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"]

theorem p2_fnAddr_curveKeyPairSerde_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName +
      bv% ((2^64 + ls_off% "<libsignal_core::curve::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private" -
        ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64) =
    (tripleRatchetProgAtExt b ext).fnAddr
      "<libsignal_core::curve::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private" := by
  simp [tripleRatchetProgAtExt, Program.fnAddr, decryptPrekeyClosureName,
    ls_lemma% fnOff "<libsignal_core::curve::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private",
    ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"]

/-! ## 1. Substage P2.1 (`+0x0868 -> +0x0f14`) -/

theorem p2_pkSerStack_le_pure : publicKeySerializeStack ≤ stageP2PureAndErrStack :=
  Nat.le_trans (by decide : publicKeySerializeStack ≤ stageP2aStack) p2_stageP2a_le_pure

theorem p2_prom1248_le_pure : 1248 ≤ stageP2PureAndErrStack :=
  Nat.le_trans (by decide : 1248 ≤ stageP2aStack) p2_stageP2a_le_pure

theorem p2_kp176_le_pure : 176 ≤ stageP2PureAndErrStack :=
  Nat.le_trans (by decide : 176 ≤ stageP2aStack) p2_stageP2a_le_pure

theorem p2_spkShim_le_spkGetCallStack {A : RustAlloc} {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A b) :
    spkKit.getShimStack ≤ spkGetCallStack spkKit :=
  Nat.le_max_left _ _

theorem p2_spkPoll_le_spkGetCallStack {A : RustAlloc} {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A b) :
    spkKit.getPollStack ≤ spkGetCallStack spkKit :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem p2_pure_le_spkGetCallStack {A : RustAlloc} {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A b) :
    stageP2PureAndErrStack ≤ spkGetCallStack spkKit :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

theorem p2_call_nopanic_steps_frame {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by
      intro _; first | rfl | simp only [Spec.inImage])
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by
      intro _ _; first | rfl | simp only [Spec.inImage])
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro _; first | rfl | simp only [Spec.inImage]) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ spec.pre x s ∗ (F ∗ R) := by
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, _⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ |
    ⟨_, _hoom_post⟩
  rotate_right; · rw [hoom_false] at _hoom_post; exact (not_satisfies_false_sepConj _hoom_post).elim
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hspm hsp_alm hcsm
        (hF.of_keepsFrozen hsteps.keepsFrozen) (hsteps.symtab_eq.trans hsym)
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [hpan_false] at hpost
    exact (allowPanic_not_exited hpost).elim
  · rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

theorem p2_call_oom_steps_frame {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State}
    {P P_spec F : SepProp} {Q : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s0.trace <+: s.trace)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : P_spec ⊢ spec.pre x s)
    (hP : P = P_spec ∗ F)
    (hpan : ∀ sf, spec.onPanic x s sf ⊢ ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (PanicOomProp s0))
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by
      intro _ _; repeat (first | simp only [Spec.inImage] | simp only [withLogOff] | simp only [withEnvPre]); rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro _; repeat (first | simp only [Spec.inImage] | simp only [withLogOff] | simp only [withEnvPre]); rfl) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  have hm' : s.mem ⊨ spec.pre x s ∗ (F ∗ R) :=
    Arm64.Satisfies.mono (sepConj_mono_left hpre) hm
  obtain ⟨sm, hsteps, hout, _⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpanm, hpost⟩ |
    ⟨code, _, hpost⟩ | ⟨_, _hoom_post⟩
  rotate_right; · rw [hoom_false] at _hoom_post; exact (not_satisfies_false_sepConj _hoom_post).elim
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hspm hsp_alm hcsm
        (hF.of_keepsFrozen hsteps.keepsFrozen) (hsteps.symtab_eq.trans hsym)
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · have hpost' : sm.mem ⊨ ((⌜allocFailedIn s sm ∧ s.trace <+: sm.trace⌝ ∗ anyHeap) ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left (hpan sm)) hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpanm,
      (⌜allocFailedIn s sm ∧ s.trace <+: sm.trace⌝ ∗ anyHeap) ∗ F, hpost',
      p2_allowPanic_oom_of_trace_prefix htr⟩)⟩
  · rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

theorem p2_spkGetShim_pre_intro {A : RustAlloc} {img : Obj.Image}
    {spkKit : SignedPreKeyStoreSpec A img.base} {x : PreKeyShimCall} {s : State}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hx0 : s.readReg64 .x0 = x.self) (hx1 : s.readReg32 .x1 = x.id) :
    A.pool ∗ stackAt s.sp spkKit.getShimStack ⊢
      ((kitSpkGetShimSpec spkKit).inImage img).pre x s := by
  dsimp only [Spec.inImage, kitSpkGetShimSpec]
  refine Entails.pure_right ⟨hF, hsym⟩ ?_
  refine Entails.pure_right ⟨hb, hx0, hx1⟩ ?_
  exact Entails.refl _

set_option maxHeartbeats 1200000 in
/-- Kit-generic Substage P2.1 (`+0x0868 -> +0x0f14`):
Serializes `baseKey` (`PublicKey::serialize`), calls `SessionRecord::promote_matching_session`
on an empty `SessionRecord`, deallocates the serialized key buffer, and calls `spkKit.getShim`. -/
theorem stageP2_sub1_kits_ext {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (img : Obj.Image) (ext : String → Option (State → State))
    (hH : StageP2ClosureHooks A img.base ext)
    (hPure : StageP2PureCallees4K P A F img ext)
    (spkKit : SignedPreKeyStoreSpec A img.base)
    (hspkOk : SignedPreKeyStoreKitOkImgE img spkKit ext)
    (stk : Nat)
    (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_shim : spkKit.getShimStack ≤ stk)
    (hstk_lt : stk ≤ 2 ^ 64)
    (s0 s : State)
    (coroPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
     spkStorePtr kyberStorePtr kyberStoreVt : BitVec 64)
    (baseKey : PublicKey) (spkId : BitVec 32) (b_4f1 : BitVec 8)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x868#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx8 : s.readReg64 .x8 = kyberStorePtr)
    (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kyberStoreVt)
    (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr)
    (hx13 : s.readReg64 .x13 = preKeyStoreVt)
    (hx14 : s.readReg64 .x14 = localAddrPtr)
    (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = idStoreVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkKit.spk_vt) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0xf14#64) s
      (cells (coroPtr + 0x3f8#64) 6 ∗
       cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
       ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
       ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
       ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
       memRegion (s.sp + 0x3e0#64) 9 ∗
       ((spkKit.spk_vt + 0x18#64) ↦₆₄ᵣ (img.base + spkKit.getShimOff)) ∗
       A.pool ∗
       stackAt s.sp stk)
      (fun sf P_f =>
        (P_f ⊢
          ∃∗ spkFutPtr : BitVec 64,
            ⌜sf.readReg64 .x0 = spkFutPtr ∧
              sf.readReg64 .x1 = img.base + spkKit.getFutVtOff ∧
              spkFutPtr ≠ 0#64 ∧
              spkFutPtr.toNat % 8 = 0⌝ ∗
            processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
              idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
              kyberStorePtr kyberStoreVt ∗
            ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
            sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
            ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
            ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
            ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
            memRegion (s.sp + 0x3e0#64) 9 ∗
            ((spkKit.spk_vt + 0x18#64) ↦₆₄ᵣ (img.base + spkKit.getShimOff)) ∗
            A.live spkFutPtr spkKit.getBoxSize 8 ∗
            spkKit.getBoxAt spkFutPtr spkStorePtr spkId 0#8 ∗
            A.pool ∗
            stackAt s.sp stk) ∧
        sf.sp = s.sp ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x19 = coroPtr ∧
        sf.readReg64 .x22 = spkStorePtr ∧
        sf.readReg64 .x23 = 0#64 ∧
        sf.readReg64 .x24 = spkKit.spk_vt ∧
        sf.readReg64 .x25 = s.sp + 0x210#64 ∧
        sf.readReg64 .x26 = 33#64 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab)
      (PanicOomProp s0) := by
  have hstep1 := p2_seg1a_ext_wp img.base ext s coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkKit.spk_vt kyberStorePtr kyberStoreVt b_4f1
    hpc hrun hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24
  refine p2_bind_sepWP_steps_frame hF hsym hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx19_1, _, hx22_1, hx23_1, hx24_1, hx25_1, _, hx27_1,
    hx28_1, hx29_1, hx30_1, hvregs1⟩
  rw [p2_fnAddr_pkSerialize_eq] at hpc1
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  have hstk_ser := p2_stackAt_split_of_le s.sp stk publicKeySerializeStack
    (Nat.le_trans p2_pkSerStack_le_pure hstk_pure) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_ser) (by sep_focus) ?_
  sep_norm
  refine p2_call_frame_frozen_oom_prefix hF1 hsym1 (htr1 ▸ htr) hPure.publicKeySerialize
    hpc1 hrun1 hsp1_al hx30_1
    (x := ⟨msgPtr + 0xa8#64, baseKey⟩)
    (T := ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗ A.pool ∗
      stackAt s.sp publicKeySerializeStack)
    (by dsimp only [publicKeySerializeSpec]; rw [hsp1])
    hx0_1 (by sep_focus)
    (by intro _; rfl) (by intro _ _; rfl)
    fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hF2 hsym2 _ => ?_
  dsimp only [publicKeySerializeSpec]
  rcases hcs2 with ⟨hcs2_19, _, _, hcs2_22, hcs2_23, hcs2_24, hcs2_25, _, hcs2_27, hcs2_28,
    hcs2_29, hvregs2_1⟩
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hcs2_19.trans hx19_1
  have hx22_2 : s2.readReg64 .x22 = spkStorePtr := hcs2_22.trans hx22_1
  have hx23_2 : s2.readReg64 .x23 = coroPtr + 0xe0#64 := hcs2_23.trans hx23_1
  have hx24_2 : s2.readReg64 .x24 = spkKit.spk_vt := hcs2_24.trans hx24_1
  have hx25_2 : s2.readReg64 .x25 = 4#64 := hcs2_25.trans hx25_1
  have hx27_2 : s2.readReg64 .x27 = s.readReg64 .x27 := hcs2_27.trans hx27_1
  have hx28_2 : s2.readReg64 .x28 = s.readReg64 .x28 := hcs2_28.trans hx28_1
  have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 := hcs2_29.trans hx29_1
  rw [hsp1]
  sep_norm
  refine SepWPp.pure_elim fun ⟨hx1_2, htr2⟩ => ?_
  refine SepWPp.weaken_frame (boxU8Buf_pk_serialize_entails A (s2.readReg64 .x0) baseKey)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_ser.symm) (by sep_focus) ?_
  have hstep3 := p2_seg1b_ext_wp img.base ext s2 coroPtr (s2.readReg64 .x0) spkStorePtr
    spkKit.spk_vt hpc2 hrun2 rfl hx1_2 hx19_2 hx22_2 hx23_2 hx24_2 hx25_2
  rw [hsp2] at hstep3
  refine p2_bind_sepWP_steps_frame hF2 hsym2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hF3 hsym3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3, htr3, hx0_3, _, _, _, hx8_3, hx19_3, hx21_3, hx22_3, _, hx24_3, _,
    hx26_3, hx27_3, hx28_3, hx29_3, hx30_3, hvregs3_2⟩
  rw [p2_fnAddr_promoteMatching_eq] at hpc3
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3] using hsp_align
  have hstk_prom1 := p2_stackAt_split_of_le s.sp stk 1248
    (Nat.le_trans p2_prom1248_le_pure hstk_pure) hstk_lt
  have hstk_prom2 := stackAt_1248_promote_eq s.sp
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom1) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom2) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (memRegion_9_sp3e0_eq s.sp)) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine p2_call_nopanic_steps_frame hF3 hsym3 hPure.promoteMatchingSessionEmpty
    hpc3 hrun3 hsp3_al hx30_3
    (x := (coroPtr + 0xe0#64, s.sp + 0x3e0#64))
    (φ := s3.readReg64 .x0 = coroPtr + 0xe0#64 ∧ s3.readReg64 .x8 = s.sp + 0x3e0#64)
    (T := sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
      (∃∗ w0 : BitVec 64, (s.sp + 0x3e0#64) ↦₆₄ w0) ∗
      (∃∗ b8 : BitVec 8, (s.sp + 0x3e8#64) ↦₈ b8) ∗
      cells (s.sp - 1248#64) 8 ∗
      cells (s.sp - 1184#64) 10 ∗
      (∃∗ w2e0 : BitVec 64, (s.sp - 448#64) ↦₆₄ w2e0) ∗
      cells (s.sp - 96#64) 12)
    (by
      dsimp only [ResponderStore.promoteMatchingSessionEmptySpec]
      rw [hsp3, show (s.sp + 0x3e0#64) + 8#64 = s.sp + 0x3e8#64 by bv_omega]
      rfl)
    ⟨hx0_3, hx8_3⟩ (by sep_focus)
    (hnext := fun s4 _ hpc4 hrun4 hsp4_3 _ hcs4 hF4 hsym4 => ?_)
  dsimp only [ResponderStore.promoteMatchingSessionEmptySpec]
  rcases hcs4 with ⟨hcs4_19, _, hcs4_21, hcs4_22, _, hcs4_24, _, hcs4_26, hcs4_27, hcs4_28,
    hcs4_29, hvregs4_3⟩
  have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4]; exact hsp_align
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hcs4_19.trans hx19_3
  have hx21_4 : s4.readReg64 .x21 = s2.readReg64 .x0 := hcs4_21.trans hx21_3
  have hx22_4 : s4.readReg64 .x22 = spkStorePtr := hcs4_22.trans hx22_3
  have hx24_4 : s4.readReg64 .x24 = spkKit.spk_vt := hcs4_24.trans hx24_3
  have hx26_4 : s4.readReg64 .x26 = 33#64 := hcs4_26.trans hx26_3
  have hx27_4 : s4.readReg64 .x27 = s.readReg64 .x27 := hcs4_27.trans (hx27_3.trans hx27_2)
  have hx28_4 : s4.readReg64 .x28 = s.readReg64 .x28 := hcs4_28.trans (hx28_3.trans hx28_2)
  have hx29_4 : s4.readReg64 .x29 = s.readReg64 .x29 := hcs4_29.trans (hx29_3.trans hx29_2)
  rw [hsp3, show (s.sp + 0x3e0#64) + 8#64 = s.sp + 0x3e8#64 by bv_omega,
    show ResponderStore.sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) =
      sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) from rfl]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr4 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom2.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom1.symm) (by sep_focus) ?_
  have hstk_alloc := p2_stackAt_split_of_le s.sp stk allocHookStack
    (Nat.le_trans p2_alloc_le_pure hstk_pure) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
  have hAct_split :
      processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
        idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt kyberStorePtr kyberStoreVt =
      ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
      (((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗
       ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
       ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗
       ((coroPtr + 0x410#64) ↦₆₄ preKeyStoreVt) ∗
       ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
       ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
       ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
       ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64))) := by
    unfold processPrekeyActive10At; ac_rfl
  refine SepWPp.weaken_frame (Entails.of_eq hAct_split) (by sep_focus) ?_
  have hstep5 := p2_seg1c_hooks_wp img.base ext hH s4 coroPtr msgPtr (s2.readReg64 .x0)
    spkStorePtr spkKit.spk_vt (img.base + spkKit.getShimOff) spkId
    hpc4 hrun4 hsp4_align hx19_4 hx21_4 hx22_4 hx24_4 hx26_4
  rw [hsp4] at hstep5
  refine p2_bind_sepWP_steps_frame hF4 hsym4 hstep5 (by sep_focus)
    fun s5 _ hpc5 hrun5 hF5 hsym5 hregs5 => ?_
  rcases hregs5 with ⟨hsp5, htr5, hx0_5, hx1_5, hx19_5, _, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5,
    hx27_5, hx28_5, hx29_5, hx30_5, hvregs5_4⟩
  have hsp5_al : s5.spAligned = true := by simpa only [State.spAligned, hsp5] using hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq hAct_split.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (sp3e0_9_entails_memRegion s.sp 0#64 0#8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
  have hstk_shim' := p2_stackAt_split_of_le s.sp stk spkKit.getShimStack hstk_shim hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_shim') (by sep_focus) ?_
  sep_norm
  have htr5_eq : s5.trace = s.trace := by rw [htr5, htr4, htr3, htr2, htr1]
  have hx1_5_32 : s5.readReg32 .x1 = spkId := by
    change (s5.readReg64 .x1).setWidth 32 = spkId
    rw [hx1_5, p2_zext64_trunc32_id]
  refine p2_call_oom_steps_frame
    (x := ({ self := spkStorePtr, id := spkId } : PreKeyShimCall))
    hF5 hsym5 (htr5_eq ▸ htr) hspkOk.getShim hpc5 hrun5 hsp5_al hx30_5
    (hsp5 ▸ p2_spkGetShim_pre_intro hF5 hsym5 hb hx0_5 hx1_5_32)
    (by sep_focus)
    (fun _ => Entails.refl _)
    (hnext := fun sf _ hpcf hrunf hspf_5 _ hcsf hFf hsymf => ?_)
  dsimp only [Spec.inImage, kitSpkGetShimSpec]
  rcases hcsf with ⟨hcsf_19, _, _, hcsf_22, hcsf_23, hcsf_24, hcsf_25, hcsf_26, hcsf_27, hcsf_28,
    hcsf_29, hvregsf_5⟩
  rw [hsp5]
  sep_norm
  refine SepWPp.pure_elim fun ⟨hx1_f, hfut_nz, hfut_al, htrf_5⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_shim'.symm) (by sep_focus) ?_
  have hvregs_full : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    rw [hvregsf_5, hvregs5_4, hvregs4_3, hvregs3_2, hvregs2_1, hvregs1, hvregs]
  refine SepWPp.done hpcf hrunf ⟨?_, hspf_5.trans hsp5, htrf_5.trans htr5_eq,
    hcsf_19.trans hx19_5, hcsf_22.trans hx22_5, hcsf_23.trans hx23_5,
    hcsf_24.trans hx24_5, hcsf_25.trans hx25_5, hcsf_26.trans hx26_5,
    hcsf_27.trans (hx27_5.trans hx27_4), hcsf_28.trans (hx28_5.trans hx28_4),
    hcsf_29.trans (hx29_5.trans hx29_4), hvregs_full, hFf, hsymf⟩
  refine Entails.sepExists_right (sf.readReg64 .x0) ?_
  rw [← sepConj_assoc]
  refine Entails.pure_right ⟨rfl, hx1_f, hfut_nz, hfut_al⟩ ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

abbrev stageP2_sub1_kits_4k := @stageP2_sub1_kits_ext
abbrev stageP2_sub1_kits_hooks := @stageP2_sub1_kits_ext

theorem stageP2_sub1_kits {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (img : Obj.Image) (ext : String → Option (State → State))
    (hA : AllocContracts img.base A ext)
    (hPure : StageP2PureCallees P A F img ext)
    (spkKit : SignedPreKeyStoreSpec A img.base)
    (hspkOk : SignedPreKeyStoreKitOkImgE img spkKit ext)
    (stk : Nat)
    (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_shim : spkKit.getShimStack ≤ stk)
    (hstk_lt : stk ≤ 2 ^ 64)
    (s0 s : State)
    (coroPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
     spkStorePtr kyberStorePtr kyberStoreVt : BitVec 64)
    (baseKey : PublicKey) (spkId : BitVec 32) (b_4f1 : BitVec 8)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x868#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx8 : s.readReg64 .x8 = kyberStorePtr) (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kyberStoreVt) (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr) (hx13 : s.readReg64 .x13 = preKeyStoreVt)
    (hx14 : s.readReg64 .x14 = localAddrPtr) (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = idStoreVt) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr) (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkKit.spk_vt) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0xf14#64) s
      (cells (coroPtr + 0x3f8#64) 6 ∗ cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗ sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
       ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗ ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
       ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗ memRegion (s.sp + 0x3e0#64) 9 ∗
       ((spkKit.spk_vt + 0x18#64) ↦₆₄ᵣ (img.base + spkKit.getShimOff)) ∗
       A.pool ∗ stackAt s.sp stk)
      (fun sf P_f =>
        (P_f ⊢
          ∃∗ spkFutPtr : BitVec 64,
            ⌜sf.readReg64 .x0 = spkFutPtr ∧
              sf.readReg64 .x1 = img.base + spkKit.getFutVtOff ∧
              spkFutPtr ≠ 0#64 ∧ spkFutPtr.toNat % 8 = 0⌝ ∗
            processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
              idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt kyberStorePtr kyberStoreVt ∗
            ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
            ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗ ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
            ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗ memRegion (s.sp + 0x3e0#64) 9 ∗
            ((spkKit.spk_vt + 0x18#64) ↦₆₄ᵣ (img.base + spkKit.getShimOff)) ∗
            A.live spkFutPtr spkKit.getBoxSize 8 ∗
            spkKit.getBoxAt spkFutPtr spkStorePtr spkId 0#8 ∗ A.pool ∗ stackAt s.sp stk) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧ sf.readReg64 .x19 = coroPtr ∧
        sf.readReg64 .x22 = spkStorePtr ∧ sf.readReg64 .x23 = 0#64 ∧
        sf.readReg64 .x24 = spkKit.spk_vt ∧ sf.readReg64 .x25 = s.sp + 0x210#64 ∧
        sf.readReg64 .x26 = 33#64 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ img.FrozenLoaded sf ∧ sf.symtab = img.symtab)
      (PanicOomProp s0) :=
  stageP2_sub1_kits_ext img ext (.of_allocContracts hA) hPure.to_4K spkKit hspkOk
    stk hstk_pure hstk_shim hstk_lt s0 s coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt spkStorePtr kyberStorePtr kyberStoreVt
    baseKey spkId b_4f1 hb hF hsym hpc hrun hsp_align htr hvregs
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24

/-! ## 2. Substage P2.2 (`+0x0f14 -> +0x1460` or Arm 1 Unwind to `s0.readReg64 .x30`) -/

theorem p2_spkGetPoll_pre_intro {A : RustAlloc} {img : Obj.Image}
    {spkKit : SignedPreKeyStoreSpec A img.base}
    {x : PreKeyPollCall} {st0 : spkKit.SpkState} {s : State}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (henv : spkKit.envOk s.fs.files)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hx0 : s.readReg64 .x0 = x.fut) (hx8 : s.readReg64 .x8 = x.out)
    (hid : spkKit.idOk x.id) :
    spkKit.getBoxAt x.fut x.self x.id 0#8 ∗ spkKit.storeAt x.self st0 ∗
      memRegion x.out 88 ∗ A.pool ∗ stackAt s.sp spkKit.getPollStack ⊢
        ((kitSpkGetPollSpecE spkKit).inImage img).pre (x, st0) s := by
  dsimp only [Spec.inImage, kitSpkGetPollSpecE, withEnvPre, kitSpkGetPollSpec]
  refine Entails.pure_right ⟨hF, hsym⟩ ?_
  refine Entails.pure_right henv ?_
  refine Entails.pure_right ⟨hb, hx0, hx8, hid⟩ ?_
  exact Entails.refl _

theorem p2_kpkGetShim_pre_intro {A : RustAlloc} {img : Obj.Image}
    {kpkKit : KyberPreKeyStoreSpec A img.base} {x : PreKeyShimCall} {s : State}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hx0 : s.readReg64 .x0 = x.self) (hx1 : s.readReg32 .x1 = x.id) :
    A.pool ∗ stackAt s.sp kpkKit.getShimStack ⊢
      ((kitKpkGetShimSpec kpkKit).inImage img).pre x s := by
  dsimp only [Spec.inImage, kitKpkGetShimSpec]
  refine Entails.pure_right ⟨hF, hsym⟩ ?_
  refine Entails.pure_right ⟨hb, hx0, hx1⟩ ?_
  exact Entails.refl _

theorem p2_signedPreKeyStructAt_unpack (A : RustAlloc) (out : BitVec 64)
    (m : SignedPreKeyRecordStructure) :
    signedPreKeyStructAt A out m ⊢
      ∃∗ pubCap : BitVec 64, ∃∗ pubPtr : BitVec 64,
      ∃∗ privCap : BitVec 64, ∃∗ privPtr : BitVec 64,
      ∃∗ sigCap : BitVec 64, ∃∗ sigPtr : BitVec 64,
      ∃∗ pad32 : BitVec 32,
        preKeyRecordOut64At out
          pubCap pubPtr (BitVec.ofNat 64 m.publicKey.length)
          privCap privPtr (BitVec.ofNat 64 m.privateKey.length)
          sigCap sigPtr ∗
        ((out + 0x40#64) ↦₆₄ BitVec.ofNat 64 m.signature.length) ∗
        ((out + 0x48#64) ↦₆₄ m.timestamp) ∗
        ((out + 0x50#64) ↦₆₄ (pad32 ++ m.id)) ∗
        vecU8Buf A pubCap pubPtr m.publicKey ∗
        vecU8Buf A privCap privPtr m.privateKey ∗
        vecU8Buf A sigCap sigPtr m.signature := by
  unfold signedPreKeyStructAt RustHeap.vecU8
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun sigCap => Entails.sepExists_elim fun sigPtr =>
    Entails.sepExists_elim fun privCap => Entails.sepExists_elim fun privPtr =>
    Entails.sepExists_elim fun pubCap => Entails.sepExists_elim fun pubPtr => ?_
  rw [ProofLib.memRegion_four (out + 0x54#64)]
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun pad32 => ?_
  refine Entails.sepExists_right pubCap (Entails.sepExists_right pubPtr
    (Entails.sepExists_right privCap (Entails.sepExists_right privPtr
    (Entails.sepExists_right sigCap (Entails.sepExists_right sigPtr
    (Entails.sepExists_right pad32 ?_))))))
  rw [LibsignalTripleRatchet.Wire.vecU8At_eq_header_buf,
      LibsignalTripleRatchet.Wire.vecU8At_eq_header_buf,
      LibsignalTripleRatchet.Wire.vecU8At_eq_header_buf]
  dsimp only [vecHeader, preKeyRecordOut64At]
  have hp80 : ((out + 0x50#64) ↦₃₂ m.id) ∗ ((out + 0x54#64) ↦₃₂ pad32) =
      ((out + 0x50#64) ↦₆₄ (pad32 ++ m.id)) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair (out + 0x50#64) m.id pad32
  rw [hp80]
  sep_norm
  exact Entails.of_eq (by ac_rfl)

theorem p2_preKeyRecordOut64_tail_to_memRegion88
    (out w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : BitVec 64) :
    preKeyRecordOut64At out w0 w1 w2 w3 w4 w5 w6 w7 ∗
      ((out + 0x40#64) ↦₆₄ w8) ∗ ((out + 0x48#64) ↦₆₄ w9) ∗ ((out + 0x50#64) ↦₆₄ w10) ⊢
      memRegion out 88 := by
  dsimp only [preKeyRecordOut64At]
  rw [ProofLib.memRegion_split out 8 80 (by decide),
      ProofLib.memRegion_split (out + 8#64) 8 72 (by decide),
      ProofLib.memRegion_split (out + 8#64 + 8#64) 8 64 (by decide),
      ProofLib.memRegion_split (out + 8#64 + 8#64 + 8#64) 8 56 (by decide),
      ProofLib.memRegion_split (out + 8#64 + 8#64 + 8#64 + 8#64) 8 48 (by decide),
      ProofLib.memRegion_split (out + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 40 (by decide),
      ProofLib.memRegion_split (out + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
      ProofLib.memRegion_split (out + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
      ProofLib.memRegion_split (out + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
      ProofLib.memRegion_split (out + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  sep_norm
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (sepConj_mono (pointsTo64_entails_memRegion _ _)
                  (sepConj_mono (pointsTo64_entails_memRegion _ _)
                    (sepConj_mono (pointsTo64_entails_memRegion _ _)
                      (pointsTo64_entails_memRegion _ _))))))))))

theorem p2_vecU8Buf_nonempty (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hlen : 0 < bs.length) :
    vecU8Buf A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ cap ≠ 0#64 ∧
        cap ≠ 0xfffffffffffffffe#64 ∧ cap ≠ 0xffffffffffffffff#64⌝ ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) := by
  unfold vecU8Buf
  refine Entails.pure_left fun ⟨hle, hlt, _⟩ => ?_
  have hcap_pos : 0 < cap.toNat := Nat.lt_of_lt_of_le hlen hle
  have hnz : cap ≠ 0#64 := fun hc => by subst hc; simp at hcap_pos
  have hcap0 : (cap = 0) = False := eq_false hnz
  have hne2 : cap ≠ 0xfffffffffffffffe#64 := fun hc => by subst hc; norm_num at hlt
  have hne1 : cap ≠ 0xffffffffffffffff#64 := fun hc => by subst hc; norm_num at hlt
  simp only [hcap0, ↓reduceIte]
  exact Entails.pure_right ⟨hle, hlt, hnz, hne2, hne1⟩ (Entails.refl _)

theorem p2_vecU8Buf_rejoin (ptr cap : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) :
    (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ⊢
      memRegion ptr cap.toNat := by
  have hlt : cap.toNat < 2 ^ 64 := cap.isLt
  have hsplit : cap.toNat = bs.length + (cap.toNat - bs.length) := (Nat.add_sub_of_le hle).symm
  conv => rhs; rw [hsplit, ProofLib.memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)]
  exact sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)

theorem p2_vecU8Buf_zero (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A 0#64 ptr bs ⊢ emp := by
  unfold vecU8Buf
  have h0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [h0, ↓reduceIte]
  exact Entails.pure_left fun _ => Entails.refl emp

theorem p2_vecU8Buf_dealloc_nonzero (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) (hcap_ne : cap ≠ 0#64) :
    vecU8Buf A cap ptr bs ⊢ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  unfold vecU8Buf
  exact Entails.pure_left fun ⟨hle, _, _⟩ => p2_vecBuf_dealloc_nonzero A cap ptr bs hcap_ne hle

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
