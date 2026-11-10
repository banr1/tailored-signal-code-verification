/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Hops
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SpeOwnedBridges
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Specifications.AsmConstants

/-!
# `signal_session::run` Receive PreKey and Bad-Wire Arms

Proves `run_hop_recvBad_ok` and `run_hop_recvP_ok` on `signal_session::run`:
- `run_hop_recvBad_ok`: from `AtDispatch` (`g.c = .recv peerV`, empty `stdin` or leading byte
  `∉ {2, 3}`), rejects to `AtReject .postDispatch` (`R + 0x2c7c`).
- `run_hop_recvP_ok`: from `AtDispatch` (`g.c = .recv peerV`, `g.i.stdin = 3#8 :: rest`), parses
  `PreKeySignalMessage::try_from`, shuffles the 248-byte message and store vtables, invokes
  `hc.decryptPrekey`, drops the `PreKeySignalMessage`, and routes `Ok` to `AtJoin` (`R + 0xf8c`) or
  `Err` to `AtReject .postDispatch` (`R + 0x2c7c`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Arm64.Process
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunProofs

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] ProofLib.bv_sub_add_lit

attribute [local arm64_norm ↓, local wp_norm ↓]
  conditionHolds_eq_addsPState64 conditionHolds_ne_addsPState64

private abbrev r3b_stOf {img : Obj.Image} {st : State} (_ : ImgCallInv img st) : State := st

private theorem r3b_perm {P P' Q : SepProp} (h : P' ⊢ Q) (heq : P = P') : P ⊢ Q :=
  heq ▸ h

private theorem r3b_perm_post {P Q' Q : SepProp} (h : P ⊢ Q') (heq : Q' = Q) : P ⊢ Q :=
  heq ▸ h

private theorem r3b_stackAt_split_ge (sp : BitVec 64) {k n : Nat}
    (hle : k ≤ n) (hn : n ≤ 2 ^ 64) :
    stackAt sp n = memRegion (sp - BitVec.ofNat 64 n) (n - k) ∗ stackAt sp k := by
  have h := ProofLib.stackAt_split_bottom sp k (n - k) (by omega)
  rwa [Nat.add_sub_of_le hle] at h

/-! ## 1. Layout-Independent Decode Tables, Symbol `fnOff`s & Vtable `ADRP` Identities -/

gen_decodes CryptoVerification.libsignalSessionCode_tree r3b_dec_disp1
  [(ls_off% "libsignal_cli::run" + 532) → (ls_off% "libsignal_cli::run" + 540)]

gen_decodes CryptoVerification.libsignalSessionCode_tree r3b_dec_disp2
  [(ls_off% "libsignal_cli::run" + 1200) → (ls_off% "libsignal_cli::run" + 1208)]

gen_decodes CryptoVerification.libsignalSessionCode_tree r3b_dec_head
  [(ls_off% "libsignal_cli::run" + 1956) → (ls_off% "libsignal_cli::run" + 2016)]

gen_decodes CryptoVerification.libsignalSessionCode_tree r3b_dec_menone
  [(ls_off% "libsignal_cli::run" + 2156) → (ls_off% "libsignal_cli::run" + 2168)]

gen_decodes CryptoVerification.libsignalSessionCode_tree r3b_dec_pkpre
  [(ls_off% "libsignal_cli::run" + 2436) → (ls_off% "libsignal_cli::run" + 2452)]

gen_decodes CryptoVerification.libsignalSessionCode_tree r3b_dec_pkchk
  [(ls_off% "libsignal_cli::run" + 2452) → (ls_off% "libsignal_cli::run" + 2488)]

gen_decodes CryptoVerification.libsignalSessionCode_tree r3b_dec_shuf1
  [(ls_off% "libsignal_cli::run" + 2488) → (ls_off% "libsignal_cli::run" + 2720)]

gen_decodes CryptoVerification.libsignalSessionCode_tree r3b_dec_shuf2
  [(ls_off% "libsignal_cli::run" + 2720) → (ls_off% "libsignal_cli::run" + 2936)]

gen_decodes CryptoVerification.libsignalSessionCode_tree r3b_dec_pkdrop
  [(ls_off% "libsignal_cli::run" + 2936) → (ls_off% "libsignal_cli::run" + 2948)]

gen_decodes CryptoVerification.libsignalSessionCode_tree r3b_dec_dpchk
  [(ls_off% "libsignal_cli::run" + 3476) → (ls_off% "libsignal_cli::run" + 3568)]

gen_decodes CryptoVerification.libsignalSessionCode_tree r3b_dec_pkerr
  [(ls_off% "libsignal_cli::run" + 3768) → (ls_off% "libsignal_cli::run" + 3792)]

gen_decodes CryptoVerification.libsignalSessionCode_tree r3b_dec_pjoin
  [(ls_off% "libsignal_cli::run" + 3972) → (ls_off% "libsignal_cli::run" + 3980)]

gen_decodes CryptoVerification.libsignalSessionCode_tree r3b_dec_dperr
  [(ls_off% "libsignal_cli::run" + 4036) → (ls_off% "libsignal_cli::run" + 4076)]

gen_decodes CryptoVerification.libsignalSessionCode_tree r3b_dec_rej
  [(ls_off% "libsignal_cli::run" + 4076) → (ls_off% "libsignal_cli::run" + 4120)]

gen_decodes CryptoVerification.libsignalSessionCode_tree r3b_dec_prej
  [(ls_off% "libsignal_cli::run" + 11380) → (ls_off% "libsignal_cli::run" + 11388)]

private theorem r3b_dropPkm_fnOff :
    libsignalSessionCode.fnOff cliDropPreKeyMsgName =
      num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::PreKeySignalMessage>") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::protocol::PreKeySignalMessage>")

private theorem r3b_pksm_fnOff :
    libsignalSessionCode.fnOff CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromName =
      num% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")

private theorem r3b_decpk_fnOff :
    libsignalSessionCode.fnOff wrapDecryptPrekeyName =
      num% (ls_off% "libsignal_cli_handshake::decrypt_prekey") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "libsignal_cli_handshake::decrypt_prekey")

private theorem r3b_sessVt_eq {img : Obj.Image} (hb : (img.base &&& 0xfff#64) = 0#64)
    {pRun : BitVec 64} (hp : pRun = img.base + bv% (ls_off% "libsignal_cli::run")) :
    ((pRun + 2776#64 &&& bv% (2 ^ 64 - 4096)) + 93240#64) = sessVt img := by
  subst hp
  have hadd : img.base + bv% (ls_off% "libsignal_cli::run") + 2776#64 =
      img.base + bv% (ls_off% "libsignal_cli::run" + 2776) := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [hadd, adrp_page_of_aligned hb]; unfold sessVt
  rw [BitVec.add_assoc]; congr 1

private theorem r3b_idVt_eq {img : Obj.Image} (hb : (img.base &&& 0xfff#64) = 0#64)
    {pRun : BitVec 64} (hp : pRun = img.base + bv% (ls_off% "libsignal_cli::run")) :
    ((pRun + 2804#64 &&& bv% (2 ^ 64 - 4096)) + 93280#64) = idVt img := by
  subst hp
  have hadd : img.base + bv% (ls_off% "libsignal_cli::run") + 2804#64 =
      img.base + bv% (ls_off% "libsignal_cli::run" + 2804) := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [hadd, adrp_page_of_aligned hb]; unfold idVt
  rw [BitVec.add_assoc]; congr 1

private theorem r3b_oneTimeVt_eq {img : Obj.Image} (hb : (img.base &&& 0xfff#64) = 0#64)
    {pRun : BitVec 64} (hp : pRun = img.base + bv% (ls_off% "libsignal_cli::run")) :
    ((pRun + 2752#64 &&& bv% (2 ^ 64 - 4096)) + 93344#64) = oneTimeVt img := by
  subst hp
  have hadd : img.base + bv% (ls_off% "libsignal_cli::run") + 2752#64 =
      img.base + bv% (ls_off% "libsignal_cli::run" + 2752) := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [hadd, adrp_page_of_aligned hb]; unfold oneTimeVt
  rw [BitVec.add_assoc]; congr 1

private theorem r3b_signedVt_eq {img : Obj.Image} (hb : (img.base &&& 0xfff#64) = 0#64)
    {pRun : BitVec 64} (hp : pRun = img.base + bv% (ls_off% "libsignal_cli::run")) :
    ((pRun + 2888#64 &&& bv% (2 ^ 64 - 4096)) + 89296#64) = signedVt img := by
  subst hp
  have hadd : img.base + bv% (ls_off% "libsignal_cli::run") + 2888#64 =
      img.base + bv% (ls_off% "libsignal_cli::run" + 2888) := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [hadd, adrp_page_of_aligned hb]; unfold signedVt
  rw [BitVec.add_assoc]; congr 1

private theorem r3b_kyberVt_eq {img : Obj.Image} (hb : (img.base &&& 0xfff#64) = 0#64)
    {pRun : BitVec 64} (hp : pRun = img.base + bv% (ls_off% "libsignal_cli::run")) :
    ((pRun + 2728#64 &&& bv% (2 ^ 64 - 4096)) + 93432#64) = kyberVt img := by
  subst hp
  have hadd : img.base + bv% (ls_off% "libsignal_cli::run") + 2728#64 =
      img.base + bv% (ls_off% "libsignal_cli::run" + 2728) := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [hadd, adrp_page_of_aligned hb]; unfold kyberVt
  rw [BitVec.add_assoc]; congr 1

/-! ## 2. `SepWPp` Call / Weakening Combinators for `runOom s0` -/

private theorem r3b_sepWPp_weaken_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hP : P ⊢ P') (h : SepWPp prog ret s P' Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  exact h R (Satisfies.mono (sepConj_mono_left hP) hm) hL

private theorem r3b_sepWPp_exists_left {α : Sort _} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x : α, SepWPp prog ret s (P x) Q Qp oom) :
    SepWPp prog ret s (∃∗ x, P x) Q Qp oom := by
  intro R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨x, hx⟩ := hm
  exact h x R hx hL

private theorem r3b_sepWPp_pure_left {P0 : Prop} {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : P0 → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s (⌜P0⌝ ∗ P) Q Qp oom := by
  intro R hm hL
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL

private theorem r3b_pure1 {P0 : Prop} {X Y Q : SepProp}
    (h : P0 → X ∗ Y ⊢ Q) : X ∗ (⌜P0⌝ ∗ Y) ⊢ Q := by
  rw [show X ∗ (⌜P0⌝ ∗ Y) = ⌜P0⌝ ∗ (X ∗ Y) by ac_rfl]
  exact Entails.pure_left h

private theorem r3b_pure2 {P0 : Prop} {X1 X2 Y Q : SepProp}
    (h : P0 → X1 ∗ X2 ∗ Y ⊢ Q) : X1 ∗ X2 ∗ (⌜P0⌝ ∗ Y) ⊢ Q := by
  rw [show X1 ∗ X2 ∗ (⌜P0⌝ ∗ Y) = ⌜P0⌝ ∗ (X1 ∗ X2 ∗ Y) by ac_rfl]
  exact Entails.pure_left h

private theorem r3b_pure5 {P0 : Prop} {X1 X2 X3 X4 X5 Y Q : SepProp}
    (h : P0 → X1 ∗ X2 ∗ X3 ∗ X4 ∗ X5 ∗ Y ⊢ Q) :
    X1 ∗ X2 ∗ X3 ∗ X4 ∗ X5 ∗ (⌜P0⌝ ∗ Y) ⊢ Q := by
  rw [show X1 ∗ X2 ∗ X3 ∗ X4 ∗ X5 ∗ (⌜P0⌝ ∗ Y) = ⌜P0⌝ ∗ (X1 ∗ X2 ∗ X3 ∗ X4 ∗ X5 ∗ Y) by ac_rfl]
  exact Entails.pure_left h

private theorem r3b_call_inImage {α : Type} {prog : Program} {img : Obj.Image}
    {callee retAddr ret : BitVec 64} {spec : Spec α} {s0 s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (x : α)
    (hcall : subroutine_ok prog callee (spec.inImage img))
    (hinv : ImgCallInv img s)
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = retAddr)
    (hP : P ⊢ spec.pre x s ∗ F)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F) := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ runOom s0 sf ∗ R') := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sm : State,
      Steps prog s sm →
      ImgCallInv img sm →
      sm.pc = retAddr →
      sm.status = .Running →
      sm.sp = s.sp →
      CalleeSavedPreserved s sm →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp (runOom s0)) :
    SepWPp prog ret s P Q Qp (runOom s0) := by
  intro R hm hL
  have hm_pre : s.mem ⊨ (spec.pre x s ∗ F) ∗ R :=
    Satisfies.mono (sepConj_mono_left hP) hm
  have hpre : s.mem ⊨ (spec.inImage img).pre x s ∗ (F ∗ R) := by
    dsimp only [Spec.inImage]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, by simpa only [sepConj_assoc] using hm_pre⟩
  obtain ⟨sm, hsteps, hout⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hpre hsp hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ |
      ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · dsimp only [Spec.inImage] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps (hinv.of_steps hsteps) hpcm hrunm hspm hcsm R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [Spec.inImage] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, spec.onPanic x s sm ∗ F,
      by simpa only [sepConj_assoc] using hpost,
      hpanic sm (F ∗ R) hpan hpost⟩)⟩
  · exact (hexit sm code (F ∗ R) hex hpost).elim
  · dsimp only [Spec.inImage] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_s, hoom sm R hoom_s hpost⟩)⟩

private theorem r3b_call_raw {α : Type} {prog : Program} {img : Obj.Image}
    {callee retAddr ret : BitVec 64} {spec : Spec α} {s0 s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (x : α)
    (hcall : subroutine_ok prog callee spec)
    (hinv : ImgCallInv img s)
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = retAddr)
    (hP : P ⊢ spec.pre x s ∗ F)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F) := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ runOom s0 sf ∗ R') := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sm : State,
      Steps prog s sm →
      ImgCallInv img sm →
      sm.pc = retAddr →
      sm.status = .Running →
      sm.sp = s.sp →
      CalleeSavedPreserved s sm →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp (runOom s0)) :
    SepWPp prog ret s P Q Qp (runOom s0) := by
  intro R hm hL
  have hm_pre : s.mem ⊨ spec.pre x s ∗ (F ∗ R) :=
    by simpa only [sepConj_assoc] using Satisfies.mono (sepConj_mono_left hP) hm
  obtain ⟨sm, hsteps, hout⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hm_pre hsp hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ |
      ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps (hinv.of_steps hsteps) hpcm hrunm hspm hcsm R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, spec.onPanic x s sm ∗ F,
      by simpa only [sepConj_assoc] using hpost,
      hpanic sm (F ∗ R) hpan hpost⟩)⟩
  · exact (hexit sm code (F ∗ R) hex hpost).elim
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_s, hoom sm R hoom_s hpost⟩)⟩

private theorem r3b_inRun_step {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s s' : State} {k k' : Nat} (h : InRun img ext s0 s k)
    (hpc : s'.pc = runPc img ext k') (hrun : s'.status = .Running)
    (hsp : s'.sp = s.sp) (hfp : s'.readReg64 .fp = s.readReg64 .fp)
    (hinv : ImgCallInv img s') (hv : calleeSavedVRegs s' = calleeSavedVRegs s) :
    InRun img ext s0 s' k' :=
  ⟨hpc, hrun, hsp.trans h.sp, hfp.trans h.fp, hinv, hv.trans h.vregs, h.spAligned⟩

private theorem r3b_hist_of_eq {i : Inputs} {s0 s s' : State}
    (htr : s'.trace = s.trace) (hfs : s'.fs.files = s.fs.files)
    (h : RunHistOk i s0 s) : RunHistOk i s0 s' :=
  ⟨hfs.trans h.1, by rw [htr]; exact h.2⟩

private theorem r3b_files_of_trace_eq {P : Program} (hP : TraceFsSound P) {s sm : State}
    (hsteps : Steps P s sm) (htr : sm.trace = s.trace) : sm.fs.files = s.fs.files :=
  hP.files_eq hsteps (by rw [htr]; simp) NoFsEv.nil

/-! ## 3. Pure-`SepProp` Magic-Wand Shift & Word Packing Infrastructure -/

private def r3b_pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 64 :=
  b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0

private theorem r3b_wand_refl (P : SepProp) : emp ⊢ (P -∗ P) :=
  Entails.wand_intro (Entails.of_eq (emp_sepConj P))

private theorem r3b_wand_post {P Q Q' : SepProp} (h : Q ⊢ Q') :
    (P -∗ Q) ⊢ (P -∗ Q') :=
  Entails.wand_intro (Entails.trans (Entails.of_eq (sepConj_comm _ _))
    (Entails.trans (Entails.wand_elim P Q) h))

private theorem r3b_pointsTo64_pack (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (a ↦₆₄ r3b_pack64 b0 b1 b2 b3 b4 b5 b6 b7) =
      (a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3) ∗
        ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗
        ((a + 7#64) ↦₈ b7) := by
  have a2 : a + 1#64 + 1#64 = a + 2#64 := by bv_omega
  have a3 : a + 2#64 + 1#64 = a + 3#64 := by bv_omega
  have a4 : a + 3#64 + 1#64 = a + 4#64 := by bv_omega
  have a5 : a + 4#64 + 1#64 = a + 5#64 := by bv_omega
  have a6 : a + 5#64 + 1#64 = a + 6#64 := by bv_omega
  have a7 : a + 6#64 + 1#64 = a + 7#64 := by bv_omega
  dsimp only [r3b_pack64]
  rw [← pointsToBytes8_eq_pointsTo64 a b0 b1 b2 b3 b4 b5 b6 b7]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, a2, a3, a4, a5, a6, a7]

private theorem r3b_pointsTo64_pack32x2 (a : BitVec 64) (c1 c2 : BitVec 32) :
    (a ↦₆₄ (c2 ++ c1)) = (a ↦₃₂ c1) ∗ ((a + 4#64) ↦₃₂ c2) := by
  have hlo : (c2 ++ c1).extractLsb' 0 32 = c1 := BitVec.extractLsb'_append_eq_right
  have hhi : (c2 ++ c1).extractLsb' 32 32 = c2 := BitVec.extractLsb'_append_eq_left
  rw [pointsTo64_split32 a (c2 ++ c1), hlo, hhi]

private theorem r3b_u64_to_u8pad7 (a : BitVec 64) (b0 : BitVec 8) (hi : BitVec 64)
    (hhi : hi.setWidth 8 = b0) :
    (a ↦₆₄ hi) ⊢ (a ↦₈ b0) ∗ memRegion (a + 1#64) 7 := by
  rw [pointsTo64_eq_pointsToBytes a hi]
  dsimp only [unpack64]
  rw [pointsToBytes_cons]
  have hlow : hi.extractLsb' 0 8 = b0 := by
    rw [← BitVec.setWidth_eq_extractLsb' (by decide), hhi]
  rw [hlow]
  exact sepConj_mono_right (ProofLib.pointsToBytes_entails_memRegion (a + 1#64) _)

private theorem r3b_u8pad7_to_u64 (a : BitVec 64) (b0 : BitVec 8) :
    ((a ↦₈ b0) ∗ memRegion (a + 1#64) 7) ⊢
      ∃∗ hi : BitVec 64, ⌜hi.setWidth 8 = b0⌝ ∗ (a ↦₆₄ hi) := by
  rw [ProofLib.memRegion_split' (b := a + 1#64) (n := 1) (k := 6) (b' := a + 2#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 2#64) (n := 1) (k := 5) (b' := a + 3#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 3#64) (n := 1) (k := 4) (b' := a + 4#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 4#64) (n := 1) (k := 3) (b' := a + 5#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 5#64) (n := 1) (k := 2) (b' := a + 6#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 6#64) (n := 1) (k := 1) (b' := a + 7#64) rfl (by bv_omega) (by decide)]
  simp only [Path.Helpers.memRegion_1_eq_pointsTo8, sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro b7
  apply Entails.sepExists_elim; intro b6
  apply Entails.sepExists_elim; intro b5
  apply Entails.sepExists_elim; intro b4
  apply Entails.sepExists_elim; intro b3
  apply Entails.sepExists_elim; intro b2
  apply Entails.sepExists_elim; intro b1
  let hi := r3b_pack64 b0 b1 b2 b3 b4 b5 b6 b7
  have hlow : hi.setWidth 8 = b0 := BitVec.setWidth_append_eq_right
  refine Entails.sepExists_right hi (Entails.pure_right hlow ?_)
  rw [r3b_pointsTo64_pack a b0 b1 b2 b3 b4 b5 b6 b7]
  exact Entails.of_eq (by ac_rfl)

private theorem r3b_ws_u64 (s d w : BitVec 64) :
    (s ↦₆₄ w) ⊢ (s ↦₆₄ w) ∗ ((d ↦₆₄ w) -∗ (d ↦₆₄ w)) :=
  Entails.trans (Entails.of_eq (sepConj_emp (s ↦₆₄ w)).symm)
    (sepConj_mono_right (r3b_wand_refl (d ↦₆₄ w)))

private theorem r3b_ws_mem8 (s d : BitVec 64) :
    memRegion s 8 ⊢ ∃∗ w : BitVec 64, (s ↦₆₄ w) ∗ ((d ↦₆₄ w) -∗ memRegion d 8) := by
  rw [ProofLib.memRegion_eight s]
  apply Entails.sepExists_elim; intro w
  exact Entails.sepExists_right w
    (Entails.trans (r3b_ws_u64 s d w)
      (sepConj_mono_right (r3b_wand_post (pointsTo64_entails_memRegion d w))))

private theorem r3b_ws_u8pad7 (s d : BitVec 64) (b0 : BitVec 8) :
    ((s ↦₈ b0) ∗ memRegion (s + 1#64) 7) ⊢
      ∃∗ w : BitVec 64,
        (s ↦₆₄ w) ∗ ((d ↦₆₄ w) -∗ ((d ↦₈ b0) ∗ memRegion (d + 1#64) 7)) := by
  refine Entails.trans (r3b_u8pad7_to_u64 s b0) ?_
  apply Entails.sepExists_elim; intro w
  apply Entails.pure_left; intro hlow
  exact Entails.sepExists_right w
    (Entails.trans (r3b_ws_u64 s d w)
      (sepConj_mono_right (r3b_wand_post (r3b_u64_to_u8pad7 d b0 w hlow))))

private theorem r3b_ws_u32x2 (s d : BitVec 64) (c1 c2 : BitVec 32) :
    ((s ↦₃₂ c1) ∗ ((s + 4#64) ↦₃₂ c2)) ⊢
      (s ↦₆₄ (c2 ++ c1)) ∗ ((d ↦₆₄ (c2 ++ c1)) -∗ ((d ↦₃₂ c1) ∗ ((d + 4#64) ↦₃₂ c2))) := by
  rw [← r3b_pointsTo64_pack32x2 s c1 c2, ← r3b_pointsTo64_pack32x2 d c1 c2]
  exact r3b_ws_u64 s d (c2 ++ c1)

private theorem r3b_ex_left {α : Sort _} {P : α → SepProp} {Q R : SepProp}
    (h : ∀ x : α, P x ∗ Q ⊢ R) : (∃∗ x, P x) ∗ Q ⊢ R := by
  rw [sepExists_sepConj_left]; exact Entails.sepExists_elim h

private theorem r3b_keep {A X Rest G : SepProp} (h : (A ∗ X) ∗ Rest ⊢ G) :
    A ∗ (X ∗ Rest) ⊢ G := by
  rw [← sepConj_assoc]; exact h

private theorem r3b_peel {α : Sort _} {A : SepProp} {P : α → SepProp} {Rest G : SepProp}
    (h : ∀ x : α, A ∗ (P x ∗ Rest) ⊢ G) : A ∗ ((∃∗ x, P x) ∗ Rest) ⊢ G := by
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; exact Entails.sepExists_elim h

private theorem r3b_peel_end {α : Sort _} {A : SepProp} {P : α → SepProp} {G : SepProp}
    (h : ∀ x : α, A ∗ P x ⊢ G) : A ∗ (∃∗ x, P x) ⊢ G := by
  rw [sepExists_sepConj_right]; exact Entails.sepExists_elim h

private def r3b_vecHeap (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    if cap = 0 then emp
    else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)

private theorem r3b_vecU8At_eq (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs =
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        r3b_vecHeap A cap ptr bs := by
  dsimp only [vecU8At, vecHeader, r3b_vecHeap]
  ac_rfl

private theorem r3b_vecHeap_cap_lt (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    r3b_vecHeap A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ r3b_vecHeap A cap ptr bs := by
  unfold r3b_vecHeap
  apply Entails.pure_left; rintro ⟨hle, hlt, hne⟩
  exact Entails.pure_right hlt (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))

private structure r3b_W6 where
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  w4 : BitVec 64
  w5 : BitVec 64

private def r3b_slot6 (a : BitVec 64) (e : r3b_W6) : SepProp :=
  (a ↦₆₄ e.w0) ∗ ((a + 8#64) ↦₆₄ e.w1) ∗ ((a + 16#64) ↦₆₄ e.w2) ∗
    ((a + 24#64) ↦₆₄ e.w3) ∗ ((a + 32#64) ↦₆₄ e.w4) ∗ ((a + 40#64) ↦₆₄ e.w5)

private theorem r3b_ws_combine6 {src dst : BitVec 64} (e : r3b_W6)
    (D0 D1 D2 D3 D4 D5 H : SepProp)
    (htag : e.w0 ≠ pendingTag ∧ e.w0 ≠ okTagVec) :
    (((src ↦₆₄ e.w0) ∗ ((dst ↦₆₄ e.w0) -∗ D0)) ∗
      (((src + 8#64) ↦₆₄ e.w1) ∗ (((dst + 8#64) ↦₆₄ e.w1) -∗ D1)) ∗
      (((src + 16#64) ↦₆₄ e.w2) ∗ (((dst + 16#64) ↦₆₄ e.w2) -∗ D2)) ∗
      (((src + 24#64) ↦₆₄ e.w3) ∗ (((dst + 24#64) ↦₆₄ e.w3) -∗ D3)) ∗
      (((src + 32#64) ↦₆₄ e.w4) ∗ (((dst + 32#64) ↦₆₄ e.w4) -∗ D4)) ∗
      (((src + 40#64) ↦₆₄ e.w5) ∗ (((dst + 40#64) ↦₆₄ e.w5) -∗ D5)) ∗
      H) ⊢
      ∃∗ e' : r3b_W6,
        ⌜e'.w0 ≠ pendingTag ∧ e'.w0 ≠ okTagVec⌝ ∗
        r3b_slot6 src e' ∗
        (r3b_slot6 dst e' -∗ (D0 ∗ D1 ∗ D2 ∗ D3 ∗ D4 ∗ D5 ∗ H)) := by
  let W : SepProp :=
    ((dst ↦₆₄ e.w0) -∗ D0) ∗ (((dst + 8#64) ↦₆₄ e.w1) -∗ D1) ∗
      (((dst + 16#64) ↦₆₄ e.w2) -∗ D2) ∗ (((dst + 24#64) ↦₆₄ e.w3) -∗ D3) ∗
      (((dst + 32#64) ↦₆₄ e.w4) -∗ D4) ∗ (((dst + 40#64) ↦₆₄ e.w5) -∗ D5) ∗ H
  have h1 :
      (((src ↦₆₄ e.w0) ∗ ((dst ↦₆₄ e.w0) -∗ D0)) ∗
        (((src + 8#64) ↦₆₄ e.w1) ∗ (((dst + 8#64) ↦₆₄ e.w1) -∗ D1)) ∗
        (((src + 16#64) ↦₆₄ e.w2) ∗ (((dst + 16#64) ↦₆₄ e.w2) -∗ D2)) ∗
        (((src + 24#64) ↦₆₄ e.w3) ∗ (((dst + 24#64) ↦₆₄ e.w3) -∗ D3)) ∗
        (((src + 32#64) ↦₆₄ e.w4) ∗ (((dst + 32#64) ↦₆₄ e.w4) -∗ D4)) ∗
        (((src + 40#64) ↦₆₄ e.w5) ∗ (((dst + 40#64) ↦₆₄ e.w5) -∗ D5)) ∗ H) =
      r3b_slot6 src e ∗ W := by
    dsimp only [r3b_slot6, W]; ac_rfl
  have h2 :
      W ∗ r3b_slot6 dst e =
        ((dst ↦₆₄ e.w0) ∗ ((dst ↦₆₄ e.w0) -∗ D0)) ∗
          (((dst + 8#64) ↦₆₄ e.w1) ∗ (((dst + 8#64) ↦₆₄ e.w1) -∗ D1)) ∗
          (((dst + 16#64) ↦₆₄ e.w2) ∗ (((dst + 16#64) ↦₆₄ e.w2) -∗ D2)) ∗
          (((dst + 24#64) ↦₆₄ e.w3) ∗ (((dst + 24#64) ↦₆₄ e.w3) -∗ D3)) ∗
          (((dst + 32#64) ↦₆₄ e.w4) ∗ (((dst + 32#64) ↦₆₄ e.w4) -∗ D4)) ∗
          (((dst + 40#64) ↦₆₄ e.w5) ∗ (((dst + 40#64) ↦₆₄ e.w5) -∗ D5)) ∗ H := by
    dsimp only [r3b_slot6, W]; ac_rfl
  refine Entails.sepExists_right e (Entails.pure_right htag ?_)
  rw [h1]
  exact sepConj_mono_right
    (Entails.wand_intro
      (Entails.trans (Entails.of_eq h2)
        (sepConj_mono (Entails.wand_elim _ _)
          (sepConj_mono (Entails.wand_elim _ _)
            (sepConj_mono (Entails.wand_elim _ _)
              (sepConj_mono (Entails.wand_elim _ _)
                (sepConj_mono (Entails.wand_elim _ _)
                  (sepConj_mono (Entails.wand_elim _ _) (Entails.refl H)))))))))

private theorem r3b_speWord_tags {i : Nat} (hi : i ≤ 40) :
    speWord i ≠ pendingTag ∧ speWord i ≠ okTagVec := by
  unfold speWord pendingTag okTagVec
  constructor <;> bv_omega

private theorem r3b_cap_tags {cap : BitVec 64} (hcap : cap.toNat < 2 ^ 63) :
    cap ≠ pendingTag ∧ cap ≠ okTagVec := by
  unfold pendingTag okTagVec
  constructor <;> bv_omega

private theorem r3b_plainSpeTag_le {i : Nat} (h : RunDrop.PlainSpeTag i) : i ≤ 40 := by
  unfold RunDrop.PlainSpeTag RunDrop.plainSpeTags at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> omega

private theorem r3b_strSpeTag_le {i : Nat} (h : RunDrop.StrSpeTag i) : i ≤ 40 := by
  unfold RunDrop.StrSpeTag RunDrop.strSpeTags at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

private theorem r3b_speOwnedAt_post {src dst : BitVec 64} {P Q : SepProp}
    (hPQ : P ⊢ Q) :
    (∃∗ e : r3b_W6,
      ⌜e.w0 ≠ pendingTag ∧ e.w0 ≠ okTagVec⌝ ∗ r3b_slot6 src e ∗ (r3b_slot6 dst e -∗ P)) ⊢
    (∃∗ e : r3b_W6,
      ⌜e.w0 ≠ pendingTag ∧ e.w0 ≠ okTagVec⌝ ∗ r3b_slot6 src e ∗ (r3b_slot6 dst e -∗ Q)) :=
  Entails.sepExists_mono fun _ =>
    sepConj_mono_right (sepConj_mono_right (r3b_wand_post hPQ))

/-- Unpack any 48-byte `RunDrop.speOwnedAt A src k` into 6 words `e` with `e.w0 ∉ {-3, -2}` and
a pure-`SepProp` magic wand restoring `RunDrop.speOwnedAt A dst k` from `r3b_slot6 dst e`. -/
private theorem r3b_speOwnedAt_words6 (A : RustAlloc) (src dst : BitVec 64)
    (k : RunDrop.SpeOwned) :
    RunDrop.speOwnedAt A src k ⊢
      ∃∗ e : r3b_W6,
        ⌜e.w0 ≠ pendingTag ∧ e.w0 ≠ okTagVec⌝ ∗
        r3b_slot6 src e ∗
        (r3b_slot6 dst e -∗ RunDrop.speOwnedAt A dst k) := by
  have hmem40 : ∀ (w0 : BitVec 64) (H : SepProp),
      (w0 ≠ pendingTag ∧ w0 ≠ okTagVec) →
      ((src ↦₆₄ w0) ∗ memRegion (src + 8#64) 40 ∗ H) ⊢
        ∃∗ e : r3b_W6,
          ⌜e.w0 ≠ pendingTag ∧ e.w0 ≠ okTagVec⌝ ∗ r3b_slot6 src e ∗
          (r3b_slot6 dst e -∗ ((dst ↦₆₄ w0) ∗ memRegion (dst + 8#64) 40 ∗ H)) := by
    intro w0 H htag
    rw [ProofLib.memRegion_split' (b := src + 8#64) (n := 8) (k := 32) (b' := src + 16#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := src + 16#64) (n := 8) (k := 24) (b' := src + 24#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := src + 24#64) (n := 8) (k := 16) (b' := src + 32#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := src + 32#64) (n := 8) (k := 8) (b' := src + 40#64) rfl (by bv_omega) (by decide)]
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (Entails.trans
        (sepConj_mono (r3b_ws_u64 src dst w0)
          (sepConj_mono (r3b_ws_mem8 (src + 8#64) (dst + 8#64))
            (sepConj_mono (r3b_ws_mem8 (src + 16#64) (dst + 16#64))
              (sepConj_mono (r3b_ws_mem8 (src + 24#64) (dst + 24#64))
                (sepConj_mono (r3b_ws_mem8 (src + 32#64) (dst + 32#64))
                  (sepConj_mono (r3b_ws_mem8 (src + 40#64) (dst + 40#64))
                    (Entails.refl H))))))) ?_)
    apply r3b_peel; intro w1; apply r3b_keep
    apply r3b_peel; intro w2; apply r3b_keep
    apply r3b_peel; intro w3; apply r3b_keep
    apply r3b_peel; intro w4; apply r3b_keep
    apply r3b_peel; intro w5
    refine Entails.trans
      (Entails.trans (Entails.of_eq (by ac_rfl))
        (r3b_ws_combine6 ⟨w0, w1, w2, w3, w4, w5⟩
          (dst ↦₆₄ w0) (memRegion (dst + 8#64) 8) (memRegion (dst + 16#64) 8)
          (memRegion (dst + 24#64) 8) (memRegion (dst + 32#64) 8) (memRegion (dst + 40#64) 8)
          H htag))
      (r3b_speOwnedAt_post ?_)
    rw [ProofLib.memRegion_split' (b := dst + 8#64) (n := 8) (k := 32) (b' := dst + 16#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := dst + 16#64) (n := 8) (k := 24) (b' := dst + 24#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := dst + 24#64) (n := 8) (k := 16) (b' := dst + 32#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := dst + 32#64) (n := 8) (k := 8) (b' := dst + 40#64) rfl (by bv_omega) (by decide)]
    exact Entails.of_eq (by ac_rfl)
  have hplain40 : ∀ (i : Nat), i ≤ 40 →
      ((src ↦₆₄ speWord i) ∗ memRegion (src + 8#64) 40) ⊢
        ∃∗ e : r3b_W6,
          ⌜e.w0 ≠ pendingTag ∧ e.w0 ≠ okTagVec⌝ ∗ r3b_slot6 src e ∗
          (r3b_slot6 dst e -∗ ((dst ↦₆₄ speWord i) ∗ memRegion (dst + 8#64) 40)) := by
    intro i hi
    exact Entails.trans (Entails.of_eq (by simp))
      (Entails.trans (hmem40 (speWord i) emp (r3b_speWord_tags hi))
        (r3b_speOwnedAt_post (Entails.of_eq (by simp))))
  have hw4_mem16 : ∀ (w0 w1 w2 w3 : BitVec 64) (H : SepProp),
      (w0 ≠ pendingTag ∧ w0 ≠ okTagVec) →
      ((src ↦₆₄ w0) ∗ ((src + 8#64) ↦₆₄ w1) ∗ ((src + 16#64) ↦₆₄ w2) ∗
        ((src + 24#64) ↦₆₄ w3) ∗ memRegion (src + 32#64) 16 ∗ H) ⊢
        ∃∗ e : r3b_W6,
          ⌜e.w0 ≠ pendingTag ∧ e.w0 ≠ okTagVec⌝ ∗ r3b_slot6 src e ∗
          (r3b_slot6 dst e -∗
            ((dst ↦₆₄ w0) ∗ ((dst + 8#64) ↦₆₄ w1) ∗ ((dst + 16#64) ↦₆₄ w2) ∗
              ((dst + 24#64) ↦₆₄ w3) ∗ memRegion (dst + 32#64) 16 ∗ H)) := by
    intro w0 w1 w2 w3 H htag
    rw [ProofLib.memRegion_split' (b := src + 32#64) (n := 8) (k := 8) (b' := src + 40#64) rfl (by bv_omega) (by decide)]
    refine Entails.trans
      (sepConj_mono (r3b_ws_u64 src dst w0)
        (sepConj_mono (r3b_ws_u64 (src + 8#64) (dst + 8#64) w1)
          (sepConj_mono (r3b_ws_u64 (src + 16#64) (dst + 16#64) w2)
            (sepConj_mono (r3b_ws_u64 (src + 24#64) (dst + 24#64) w3)
              (sepConj_mono
                (sepConj_mono (r3b_ws_mem8 (src + 32#64) (dst + 32#64))
                  (r3b_ws_mem8 (src + 40#64) (dst + 40#64)))
                (Entails.refl H)))))) ?_
    have hassoc :
        ((src ↦₆₄ w0) ∗ ((dst ↦₆₄ w0) -∗ (dst ↦₆₄ w0))) ∗
          (((src + 8#64) ↦₆₄ w1) ∗ (((dst + 8#64) ↦₆₄ w1) -∗ ((dst + 8#64) ↦₆₄ w1))) ∗
          (((src + 16#64) ↦₆₄ w2) ∗ (((dst + 16#64) ↦₆₄ w2) -∗ ((dst + 16#64) ↦₆₄ w2))) ∗
          (((src + 24#64) ↦₆₄ w3) ∗ (((dst + 24#64) ↦₆₄ w3) -∗ ((dst + 24#64) ↦₆₄ w3))) ∗
          ((∃∗ w, ((src + 32#64) ↦₆₄ w) ∗ (((dst + 32#64) ↦₆₄ w) -∗ memRegion (dst + 32#64) 8)) ∗
           (∃∗ w, ((src + 40#64) ↦₆₄ w) ∗ (((dst + 40#64) ↦₆₄ w) -∗ memRegion (dst + 40#64) 8))) ∗ H =
        ((((src ↦₆₄ w0) ∗ ((dst ↦₆₄ w0) -∗ (dst ↦₆₄ w0))) ∗
          (((src + 8#64) ↦₆₄ w1) ∗ (((dst + 8#64) ↦₆₄ w1) -∗ ((dst + 8#64) ↦₆₄ w1))) ∗
          (((src + 16#64) ↦₆₄ w2) ∗ (((dst + 16#64) ↦₆₄ w2) -∗ ((dst + 16#64) ↦₆₄ w2))) ∗
          (((src + 24#64) ↦₆₄ w3) ∗ (((dst + 24#64) ↦₆₄ w3) -∗ ((dst + 24#64) ↦₆₄ w3)))) ∗
          ((∃∗ w, ((src + 32#64) ↦₆₄ w) ∗ (((dst + 32#64) ↦₆₄ w) -∗ memRegion (dst + 32#64) 8)) ∗
           (∃∗ w, ((src + 40#64) ↦₆₄ w) ∗ (((dst + 40#64) ↦₆₄ w) -∗ memRegion (dst + 40#64) 8)) ∗ H)) := by
      ac_rfl
    rw [hassoc]
    apply r3b_peel; intro w4; apply r3b_keep
    apply r3b_peel; intro w5
    refine Entails.trans
      (Entails.trans (Entails.of_eq (by ac_rfl))
        (r3b_ws_combine6 ⟨w0, w1, w2, w3, w4, w5⟩
          (dst ↦₆₄ w0) ((dst + 8#64) ↦₆₄ w1) ((dst + 16#64) ↦₆₄ w2)
          ((dst + 24#64) ↦₆₄ w3) (memRegion (dst + 32#64) 8) (memRegion (dst + 40#64) 8)
          H htag))
      (r3b_speOwnedAt_post ?_)
    rw [ProofLib.memRegion_split' (b := dst + 32#64) (n := 8) (k := 8) (b' := dst + 40#64) rfl (by bv_omega) (by decide)]
    exact Entails.of_eq (by ac_rfl)
  have hw1_u8_mem32 : ∀ (i : Nat) (v : BitVec 8), i ≤ 40 →
      ((src ↦₆₄ speWord i) ∗ ((src + 8#64) ↦₈ v) ∗ memRegion (src + 9#64) 39) ⊢
        ∃∗ e : r3b_W6,
          ⌜e.w0 ≠ pendingTag ∧ e.w0 ≠ okTagVec⌝ ∗ r3b_slot6 src e ∗
          (r3b_slot6 dst e -∗
            ((dst ↦₆₄ speWord i) ∗ ((dst + 8#64) ↦₈ v) ∗ memRegion (dst + 9#64) 39)) := by
    intro i v hi
    rw [ProofLib.memRegion_split' (b := src + 9#64) (n := 7) (k := 32) (b' := src + 16#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := src + 16#64) (n := 8) (k := 24) (b' := src + 24#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := src + 24#64) (n := 8) (k := 16) (b' := src + 32#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := src + 32#64) (n := 8) (k := 8) (b' := src + 40#64) rfl (by bv_omega) (by decide)]
    have hs9 : src + 8#64 + 1#64 = src + 9#64 := by bv_omega
    have hd9 : dst + 8#64 + 1#64 = dst + 9#64 := by bv_omega
    have hu8 := r3b_ws_u8pad7 (src + 8#64) (dst + 8#64) v
    rw [hs9, hd9] at hu8
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (Entails.trans
        (sepConj_mono (r3b_ws_u64 src dst (speWord i))
          (sepConj_mono hu8
            (sepConj_mono (r3b_ws_mem8 (src + 16#64) (dst + 16#64))
              (sepConj_mono (r3b_ws_mem8 (src + 24#64) (dst + 24#64))
                (sepConj_mono (r3b_ws_mem8 (src + 32#64) (dst + 32#64))
                  (r3b_ws_mem8 (src + 40#64) (dst + 40#64))))))) ?_)
    apply r3b_peel; intro w1; apply r3b_keep
    apply r3b_peel; intro w2; apply r3b_keep
    apply r3b_peel; intro w3; apply r3b_keep
    apply r3b_peel; intro w4; apply r3b_keep
    apply r3b_peel_end; intro w5
    refine Entails.trans
      (Entails.trans (Entails.of_eq (by simp))
        (r3b_ws_combine6 ⟨speWord i, w1, w2, w3, w4, w5⟩
          (dst ↦₆₄ speWord i) (((dst + 8#64) ↦₈ v) ∗ memRegion (dst + 9#64) 7)
          (memRegion (dst + 16#64) 8) (memRegion (dst + 24#64) 8)
          (memRegion (dst + 32#64) 8) (memRegion (dst + 40#64) 8)
          emp (r3b_speWord_tags hi)))
      (r3b_speOwnedAt_post ?_)
    rw [ProofLib.memRegion_split' (b := dst + 9#64) (n := 7) (k := 32) (b' := dst + 16#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := dst + 16#64) (n := 8) (k := 24) (b' := dst + 24#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := dst + 24#64) (n := 8) (k := 16) (b' := dst + 32#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := dst + 32#64) (n := 8) (k := 8) (b' := dst + 40#64) rfl (by bv_omega) (by decide)]
    exact Entails.of_eq (by simp)
  cases k with
  | badKemKeyType => exact hplain40 31 (by omega)
  | badKemKeyLength => exact hplain40 33 (by omega)
  | plain i hi => exact hplain40 i (r3b_plainSpeTag_le hi)
  | withString i hi =>
    dsimp only [RunDrop.speOwnedAt, vecU8]
    apply r3b_peel; intro bs
    apply r3b_peel; intro cap
    apply r3b_peel; intro ptr
    rw [r3b_vecU8At_eq]
    have hs16 : src + 8#64 + 8#64 = src + 16#64 := by bv_omega
    have hs24 : src + 8#64 + 16#64 = src + 24#64 := by bv_omega
    have hd16 : dst + 8#64 + 8#64 = dst + 16#64 := by bv_omega
    have hd24 : dst + 8#64 + 16#64 = dst + 24#64 := by bv_omega
    rw [hs16, hs24]
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (Entails.trans (hw4_mem16 (speWord i) cap ptr (BitVec.ofNat 64 bs.length)
        (r3b_vecHeap A cap ptr bs)
        (r3b_speWord_tags (r3b_strSpeTag_le hi)))
        (r3b_speOwnedAt_post ?_))
    rw [← hd16, ← hd24]
    have hvec :
        ((dst + 8#64) ↦₆₄ cap) ∗ ((dst + 8#64 + 8#64) ↦₆₄ ptr) ∗
          ((dst + 8#64 + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          r3b_vecHeap A cap ptr bs ⊢
        ∃∗ bs', ∃∗ cap', ∃∗ ptr', vecU8At A (dst + 8#64) cap' ptr' bs' :=
      Entails.sepExists_right bs (Entails.sepExists_right cap
        (Entails.sepExists_right ptr (Entails.of_eq (r3b_vecU8At_eq A (dst + 8#64) cap ptr bs).symm)))
    exact r3b_perm
      (sepConj_mono (Entails.refl (dst ↦₆₄ speWord i))
        (sepConj_mono hvec (Entails.refl (memRegion (dst + 0x20#64) 16))))
      (by ac_rfl)
  | sessionNotFound addr op =>
    dsimp only [RunDrop.speOwnedAt, apiErrAt, addrCloneAt, strRefAt, vecU8]
    rw [sepConj_assoc, sepConj_assoc]
    apply r3b_ex_left; intro cap
    apply r3b_ex_left; intro ptr
    rw [← sepConj_assoc, ← sepConj_assoc]
    apply r3b_peel_end; intro p
    rw [r3b_vecU8At_eq]
    have hs28 : src + 0x20#64 + asm64% boxSliceLenOff = src + 40#64 := by bv_omega
    have hd28 : dst + 0x20#64 + asm64% boxSliceLenOff = dst + 40#64 := by bv_omega
    have hs25 : src + 0x18#64 + 1#64 = src + 0x19#64 := by bv_omega
    have hd25 : dst + 0x18#64 + 1#64 = dst + 0x19#64 := by bv_omega
    have hu8 := r3b_ws_u8pad7 (src + 24#64) (dst + 24#64) addr.device
    rw [show (24#64 : BitVec 64) = 0x18#64 from rfl] at *
    rw [hs25, hd25] at hu8
    rw [hs28]
    let Hsnf : SepProp := r3b_vecHeap A cap ptr addr.name ∗ (p ↦ᵣ utf8 op)
    refine r3b_perm
      (sepConj_mono (r3b_vecHeap_cap_lt A cap ptr addr.name)
        (Entails.refl ((src ↦₆₄ cap) ∗ ((src + 8#64) ↦₆₄ ptr) ∗
          ((src + 16#64) ↦₆₄ BitVec.ofNat 64 addr.name.length) ∗
          (((src + 0x18#64) ↦₈ addr.device) ∗ memRegion (src + 0x19#64) 7) ∗
          ((src + 0x20#64) ↦₆₄ p) ∗ ((src + 40#64) ↦₆₄ BitVec.ofNat 64 (utf8 op).length) ∗
          (p ↦ᵣ utf8 op))))
      (by ac_rfl)
      |> Entails.trans <| ?_
    rw [sepConj_assoc]
    apply Entails.pure_left; intro hcap_lt
    refine r3b_perm
      (sepConj_mono (r3b_ws_u64 src dst cap)
        (sepConj_mono hu8
          (sepConj_mono (r3b_ws_u64 (src + 8#64) (dst + 8#64) ptr)
            (sepConj_mono (r3b_ws_u64 (src + 16#64) (dst + 16#64) (BitVec.ofNat 64 addr.name.length))
              (sepConj_mono (r3b_ws_u64 (src + 32#64) (dst + 32#64) p)
                (sepConj_mono (r3b_ws_u64 (src + 40#64) (dst + 40#64) (BitVec.ofNat 64 (utf8 op).length))
                  (Entails.refl Hsnf)))))))
      (by dsimp only [Hsnf]; ac_rfl)
      |> Entails.trans <| ?_
    apply r3b_peel; intro w3
    refine Entails.trans
      (Entails.trans (Entails.of_eq (by dsimp only [Hsnf]; ac_rfl))
        (r3b_ws_combine6 ⟨cap, ptr, BitVec.ofNat 64 addr.name.length, w3, p, BitVec.ofNat 64 (utf8 op).length⟩
          (dst ↦₆₄ cap) ((dst + 8#64) ↦₆₄ ptr) ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 addr.name.length)
          (((dst + 0x18#64) ↦₈ addr.device) ∗ memRegion (dst + 0x19#64) 7)
          ((dst + 32#64) ↦₆₄ p) ((dst + 40#64) ↦₆₄ BitVec.ofNat 64 (utf8 op).length)
          Hsnf (r3b_cap_tags hcap_lt)))
      (r3b_speOwnedAt_post ?_)
    rw [← hd28]
    have hvec :
        (dst ↦₆₄ cap) ∗ ((dst + 8#64) ↦₆₄ ptr) ∗
          ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 addr.name.length) ∗
          r3b_vecHeap A cap ptr addr.name ⊢
        ∃∗ cap', ∃∗ ptr', vecU8At A dst cap' ptr' addr.name :=
      Entails.sepExists_right cap (Entails.sepExists_right ptr
        (Entails.of_eq (r3b_vecU8At_eq A dst cap ptr addr.name).symm))
    have hstr :
        ((dst + 32#64) ↦₆₄ p) ∗ ((dst + 0x20#64 + asm64% boxSliceLenOff) ↦₆₄ BitVec.ofNat 64 (utf8 op).length) ∗
          (p ↦ᵣ utf8 op) ⊢
        (∃∗ p',
          ((dst + 0x20#64) ↦₆₄ p') ∗ ((dst + 0x20#64 + asm64% boxSliceLenOff) ↦₆₄ BitVec.ofNat 64 (utf8 op).length) ∗
            (p' ↦ᵣ utf8 op)) :=
      Entails.sepExists_right p (Entails.of_eq (by ac_rfl))
    exact r3b_perm
      (r3b_perm_post
        (sepConj_mono
          (sepConj_mono hvec
            (Entails.refl (((dst + 0x18#64) ↦₈ addr.device) ∗ memRegion (dst + 0x19#64) 7)))
          hstr)
        (by ac_rfl))
      (by dsimp only [Hsnf]; ac_rfl)
  | untrustedIdentity addr =>
    dsimp only [RunDrop.speOwnedAt, apiErrAt, addrCloneAt, vecU8]
    rw [sepConj_assoc ((∃∗ cap, _))]
    apply r3b_peel; intro cap
    apply r3b_peel; intro ptr
    rw [r3b_vecU8At_eq]
    have hs16 : src + 8#64 + 8#64 = src + 16#64 := by bv_omega
    have hs24 : src + 8#64 + 16#64 = src + 24#64 := by bv_omega
    have hs32 : src + 8#64 + 0x18#64 = src + 32#64 := by bv_omega
    have hs33 : src + 8#64 + 0x19#64 = src + 33#64 := by bv_omega
    have hd16 : dst + 8#64 + 8#64 = dst + 16#64 := by bv_omega
    have hd24 : dst + 8#64 + 16#64 = dst + 24#64 := by bv_omega
    have hd32 : dst + 8#64 + 0x18#64 = dst + 32#64 := by bv_omega
    have hd33 : dst + 8#64 + 0x19#64 = dst + 33#64 := by bv_omega
    have hu8 := r3b_ws_u8pad7 (src + 32#64) (dst + 32#64) addr.device
    have ha33s : src + 32#64 + 1#64 = src + 33#64 := by bv_omega
    have ha33d : dst + 32#64 + 1#64 = dst + 33#64 := by bv_omega
    rw [ha33s, ha33d] at hu8
    rw [hs16, hs24, hs32, hs33]
    let Huid : SepProp := r3b_vecHeap A cap ptr addr.name
    refine Entails.trans (Entails.of_eq (by dsimp only [Huid]; ac_rfl))
      (Entails.trans
        (sepConj_mono (r3b_ws_u64 src dst (speWord speUntrustedIdentity))
          (sepConj_mono hu8
            (sepConj_mono (r3b_ws_mem8 (src + 40#64) (dst + 40#64))
              (sepConj_mono (r3b_ws_u64 (src + 8#64) (dst + 8#64) cap)
                (sepConj_mono (r3b_ws_u64 (src + 16#64) (dst + 16#64) ptr)
                  (sepConj_mono (r3b_ws_u64 (src + 24#64) (dst + 24#64) (BitVec.ofNat 64 addr.name.length))
                    (Entails.refl Huid))))))) ?_)
    apply r3b_peel; intro w4; apply r3b_keep
    apply r3b_peel; intro w5
    refine Entails.trans
      (Entails.trans (Entails.of_eq (by dsimp only [Huid]; ac_rfl))
        (r3b_ws_combine6 ⟨speWord speUntrustedIdentity, cap, ptr, BitVec.ofNat 64 addr.name.length, w4, w5⟩
          (dst ↦₆₄ speWord speUntrustedIdentity) ((dst + 8#64) ↦₆₄ cap) ((dst + 16#64) ↦₆₄ ptr)
          ((dst + 24#64) ↦₆₄ BitVec.ofNat 64 addr.name.length)
          (((dst + 32#64) ↦₈ addr.device) ∗ memRegion (dst + 33#64) 7)
          (memRegion (dst + 40#64) 8) Huid
          (r3b_speWord_tags (by dsimp only [speUntrustedIdentity]; omega))))
      (r3b_speOwnedAt_post ?_)
    rw [← hd16, ← hd24, ← hd32, ← hd33]
    have hvec :
        ((dst + 8#64) ↦₆₄ cap) ∗ ((dst + 8#64 + 8#64) ↦₆₄ ptr) ∗
          ((dst + 8#64 + 16#64) ↦₆₄ BitVec.ofNat 64 addr.name.length) ∗ Huid ⊢
        ∃∗ cap', ∃∗ ptr', vecU8At A (dst + 8#64) cap' ptr' addr.name :=
      Entails.sepExists_right cap (Entails.sepExists_right ptr
        (Entails.of_eq (r3b_vecU8At_eq A (dst + 8#64) cap ptr addr.name).symm))
    exact r3b_perm
      (r3b_perm_post
        (sepConj_mono (Entails.refl (dst ↦₆₄ speWord speUntrustedIdentity))
          (sepConj_mono hvec
            (Entails.refl (((dst + 8#64 + 0x18#64) ↦₈ addr.device) ∗
              memRegion (dst + 8#64 + 0x19#64) 7 ∗ memRegion (dst + 40#64) 8))))
        (by ac_rfl))
      (by ac_rfl)
  | proto fnName err =>
    cases err with
    | panic =>
      dsimp only [RunDrop.speOwnedAt, speAt]
      rw [← sepConj_emp ⌜False⌝]
      exact Entails.pure_left False.elim
    | invalidProtobufEncoding => exact hplain40 2 (by omega)
    | noKeyTypeIdentifier => exact hplain40 7 (by omega)
    | invalidKeyAgreement => exact hplain40 10 (by omega)
    | ciphertextMessageTooShort n =>
      dsimp only [RunDrop.speOwnedAt, speAt]
      rw [ProofLib.memRegion_split' (b := src + 16#64) (n := 8) (k := 24) (b' := src + 24#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := src + 24#64) (n := 8) (k := 16) (b' := src + 32#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_eight (src + 16#64), ProofLib.memRegion_eight (src + 24#64)]
      rw [← sepConj_assoc (src ↦₆₄ _)]
      apply r3b_peel; intro w2; apply r3b_keep
      apply r3b_peel; intro w3
      refine Entails.trans (Entails.of_eq (by simp))
        (Entails.trans (hw4_mem16 (speWord 3) (BitVec.ofNat 64 n) w2 w3 emp (r3b_speWord_tags (by omega)))
          (r3b_speOwnedAt_post ?_))
      rw [ProofLib.memRegion_split' (b := dst + 16#64) (n := 8) (k := 24) (b' := dst + 24#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := dst + 24#64) (n := 8) (k := 16) (b' := dst + 32#64) rfl (by bv_omega) (by decide)]
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono (pointsTo64_entails_memRegion _ w2)
            (sepConj_mono_left (pointsTo64_entails_memRegion _ w3)))))
        (Entails.of_eq (by simp))
    | badKeyLength n =>
      dsimp only [RunDrop.speOwnedAt, speAt]
      rw [ProofLib.memRegion_split' (b := src + 16#64) (n := 8) (k := 24) (b' := src + 24#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := src + 24#64) (n := 8) (k := 16) (b' := src + 32#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_eight (src + 16#64), ProofLib.memRegion_eight (src + 24#64)]
      rw [← sepConj_assoc (src ↦₆₄ _)]
      apply r3b_peel; intro w2; apply r3b_keep
      apply r3b_peel; intro w3
      refine Entails.trans (Entails.of_eq (by simp))
        (Entails.trans (hw4_mem16 (speWord 9) (BitVec.ofNat 64 n) w2 w3 emp (r3b_speWord_tags (by omega)))
          (r3b_speOwnedAt_post ?_))
      rw [ProofLib.memRegion_split' (b := dst + 16#64) (n := 8) (k := 24) (b' := dst + 24#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := dst + 24#64) (n := 8) (k := 16) (b' := dst + 32#64) rfl (by bv_omega) (by decide)]
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono (pointsTo64_entails_memRegion _ w2)
            (sepConj_mono_left (pointsTo64_entails_memRegion _ w3)))))
        (Entails.of_eq (by simp))
    | legacyCiphertextVersion v => exact hw1_u8_mem32 4 v (by omega)
    | unrecognizedCiphertextVersion v => exact hw1_u8_mem32 5 v (by omega)
    | badKeyType v => exact hw1_u8_mem32 8 v (by omega)
    | duplicatedMessage c1 c2 =>
      dsimp only [RunDrop.speOwnedAt, speAt]
      have hs12 : src + 8#64 + 4#64 = src + 12#64 := by bv_omega
      have hd12 : dst + 8#64 + 4#64 = dst + 12#64 := by bv_omega
      have hsrc32 : ((src + 8#64) ↦₃₂ c1) ∗ ((src + 12#64) ↦₃₂ c2) =
          ((src + 8#64) ↦₆₄ (c2 ++ c1)) := by
        rw [r3b_pointsTo64_pack32x2 (src + 8#64) c1 c2, hs12]
      have hdst32 : ((dst + 8#64) ↦₆₄ (c2 ++ c1)) =
          ((dst + 8#64) ↦₃₂ c1) ∗ ((dst + 12#64) ↦₃₂ c2) := by
        rw [r3b_pointsTo64_pack32x2 (dst + 8#64) c1 c2, hd12]
      rw [ProofLib.memRegion_split' (b := src + 16#64) (n := 8) (k := 24) (b' := src + 24#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := src + 24#64) (n := 8) (k := 16) (b' := src + 32#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_eight (src + 16#64), ProofLib.memRegion_eight (src + 24#64),
          ← sepConj_assoc ((src + 8#64) ↦₃₂ c1), hsrc32, ← sepConj_assoc (src ↦₆₄ _)]
      apply r3b_peel; intro w2; apply r3b_keep
      apply r3b_peel; intro w3
      refine Entails.trans (Entails.of_eq (by simp))
        (Entails.trans (hw4_mem16 (speWord 23) (c2 ++ c1) w2 w3 emp (r3b_speWord_tags (by omega)))
          (r3b_speOwnedAt_post ?_))
      rw [hdst32,
          ProofLib.memRegion_split' (b := dst + 16#64) (n := 8) (k := 24) (b' := dst + 24#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := dst + 24#64) (n := 8) (k := 16) (b' := dst + 32#64) rfl (by bv_omega) (by decide)]
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono (pointsTo64_entails_memRegion _ w2)
            (sepConj_mono_left (pointsTo64_entails_memRegion _ w3)))))
        (Entails.of_eq (by simp))
    | invalidSessionStructure rsn =>
      dsimp only [RunDrop.speOwnedAt, speAt, strRefAt]
      apply r3b_peel; intro p; apply r3b_keep
      rw [ProofLib.memRegion_split' (b := src + 24#64) (n := 8) (k := 16) (b' := src + 32#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_eight (src + 24#64)]
      apply r3b_peel; intro w3
      have hs16 : src + 8#64 + 8#64 = src + 16#64 := by bv_omega
      have hd16 : dst + 8#64 + 8#64 = dst + 16#64 := by bv_omega
      rw [hs16]
      refine Entails.trans (Entails.of_eq (by ac_rfl))
        (Entails.trans (hw4_mem16 (speWord 20) p (BitVec.ofNat 64 (invalidSessionStructureStr rsn).length) w3 (p ↦ᵣ invalidSessionStructureStr rsn)
          (r3b_speWord_tags (by omega)))
          (r3b_speOwnedAt_post ?_))
      rw [← hd16,
          ProofLib.memRegion_split' (b := dst + 24#64) (n := 8) (k := 16) (b' := dst + 32#64) rfl (by bv_omega) (by decide)]
      have hstr :
          ((dst + 8#64) ↦₆₄ p) ∗ ((dst + 8#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (invalidSessionStructureStr rsn).length) ∗ (p ↦ᵣ invalidSessionStructureStr rsn) ⊢
          (∃∗ p', ((dst + 8#64) ↦₆₄ p') ∗ ((dst + 8#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (invalidSessionStructureStr rsn).length) ∗ (p' ↦ᵣ invalidSessionStructureStr rsn)) :=
        Entails.sepExists_right p (Entails.of_eq (by ac_rfl))
      exact r3b_perm
        (r3b_perm_post
          (sepConj_mono (Entails.refl (dst ↦₆₄ speWord 20))
            (sepConj_mono hstr
              (sepConj_mono (pointsTo64_entails_memRegion (dst + 24#64) w3)
                (Entails.refl (memRegion (dst + 32#64) 16)))))
          (by ac_rfl))
        (by ac_rfl)
    | invalidState =>
      dsimp only [RunDrop.speOwnedAt, speAt, strRefAt, vecU8]
      apply r3b_peel; intro bs
      apply r3b_peel; intro cap
      apply r3b_peel; intro ptr
      apply r3b_keep
      apply r3b_peel_end; intro p
      rw [r3b_vecU8At_eq]
      have hs16 : src + 8#64 + 8#64 = src + 16#64 := by bv_omega
      have hs24 : src + 8#64 + 16#64 = src + 24#64 := by bv_omega
      have hs40 : src + 0x20#64 + 8#64 = src + 40#64 := by bv_omega
      have hd16 : dst + 8#64 + 8#64 = dst + 16#64 := by bv_omega
      have hd24 : dst + 8#64 + 16#64 = dst + 24#64 := by bv_omega
      have hd40 : dst + 0x20#64 + 8#64 = dst + 40#64 := by bv_omega
      rw [hs16, hs24, hs40]
      let Hst : SepProp := r3b_vecHeap A cap ptr bs ∗ (p ↦ᵣ fnName)
      refine Entails.trans (Entails.of_eq (by dsimp only [Hst]; ac_rfl))
        (Entails.trans
          (sepConj_mono (r3b_ws_u64 src dst (speWord 1))
            (sepConj_mono (r3b_ws_u64 (src + 8#64) (dst + 8#64) cap)
              (sepConj_mono (r3b_ws_u64 (src + 16#64) (dst + 16#64) ptr)
                (sepConj_mono (r3b_ws_u64 (src + 24#64) (dst + 24#64) (BitVec.ofNat 64 bs.length))
                  (sepConj_mono (r3b_ws_u64 (src + 32#64) (dst + 32#64) p)
                    (sepConj_mono (r3b_ws_u64 (src + 40#64) (dst + 40#64) (BitVec.ofNat 64 fnName.length))
                      (Entails.refl Hst))))))) ?_)
      refine Entails.trans
        (Entails.trans (Entails.of_eq (by dsimp only [Hst]))
          (r3b_ws_combine6 ⟨speWord 1, cap, ptr, BitVec.ofNat 64 bs.length, p, BitVec.ofNat 64 fnName.length⟩
            (dst ↦₆₄ speWord 1) ((dst + 8#64) ↦₆₄ cap) ((dst + 16#64) ↦₆₄ ptr)
            ((dst + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length)
            ((dst + 32#64) ↦₆₄ p) ((dst + 40#64) ↦₆₄ BitVec.ofNat 64 fnName.length)
            Hst (r3b_speWord_tags (by omega))))
        (r3b_speOwnedAt_post ?_)
      rw [← hd16, ← hd24, ← hd40]
      have hvec :
          ((dst + 8#64) ↦₆₄ cap) ∗ ((dst + 8#64 + 8#64) ↦₆₄ ptr) ∗
            ((dst + 8#64 + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            r3b_vecHeap A cap ptr bs ⊢
          ∃∗ bs', ∃∗ cap', ∃∗ ptr', vecU8At A (dst + 8#64) cap' ptr' bs' :=
        Entails.sepExists_right bs (Entails.sepExists_right cap
          (Entails.sepExists_right ptr (Entails.of_eq (r3b_vecU8At_eq A (dst + 8#64) cap ptr bs).symm)))
      have hstr :
          ((dst + 32#64) ↦₆₄ p) ∗ ((dst + 0x20#64 + 8#64) ↦₆₄ BitVec.ofNat 64 fnName.length) ∗
            (p ↦ᵣ fnName) ⊢
          (∃∗ p', ((dst + 0x20#64) ↦₆₄ p') ∗ ((dst + 0x20#64 + 8#64) ↦₆₄ BitVec.ofNat 64 fnName.length) ∗
            (p' ↦ᵣ fnName)) :=
        Entails.sepExists_right p (Entails.of_eq (by ac_rfl))
      exact r3b_perm
        (sepConj_mono (Entails.refl (dst ↦₆₄ speWord 1)) (sepConj_mono hvec hstr))
        (by dsimp only [Hst]; ac_rfl)
    | invalidMessage mt rsn =>
      have hinval : ∀ bs : List (BitVec 8),
          ((src ↦₆₄ speWord 24) ∗ vecU8 A (src + 8#64) bs ∗
            ((src + 0x20#64) ↦₈ msgTypeByte mt) ∗ memRegion (src + 0x21#64) 15) ⊢
            ∃∗ e : r3b_W6,
              ⌜e.w0 ≠ pendingTag ∧ e.w0 ≠ okTagVec⌝ ∗ r3b_slot6 src e ∗
              (r3b_slot6 dst e -∗
                ((dst ↦₆₄ speWord 24) ∗ vecU8 A (dst + 8#64) bs ∗
                  ((dst + 0x20#64) ↦₈ msgTypeByte mt) ∗ memRegion (dst + 0x21#64) 15)) := by
        intro bs
        dsimp only [vecU8]
        apply r3b_peel; intro cap
        apply r3b_peel; intro ptr
        rw [r3b_vecU8At_eq]
        rw [ProofLib.memRegion_split' (b := src + 0x21#64) (n := 7) (k := 8) (b' := src + 40#64) rfl (by bv_omega) (by decide)]
        have hs16 : src + 8#64 + 8#64 = src + 16#64 := by bv_omega
        have hs24 : src + 8#64 + 16#64 = src + 24#64 := by bv_omega
        have hd16 : dst + 8#64 + 8#64 = dst + 16#64 := by bv_omega
        have hd24 : dst + 8#64 + 16#64 = dst + 24#64 := by bv_omega
        have hu8 := r3b_ws_u8pad7 (src + 32#64) (dst + 32#64) (msgTypeByte mt)
        have ha33s : src + 32#64 + 1#64 = src + 0x21#64 := by bv_omega
        have ha33d : dst + 32#64 + 1#64 = dst + 0x21#64 := by bv_omega
        rw [ha33s, ha33d] at hu8
        rw [hs16, hs24]
        let Him : SepProp := r3b_vecHeap A cap ptr bs
        refine Entails.trans (Entails.of_eq (by dsimp only [Him]; ac_rfl))
          (Entails.trans
            (sepConj_mono (r3b_ws_u64 src dst (speWord 24))
              (sepConj_mono hu8
                (sepConj_mono (r3b_ws_mem8 (src + 40#64) (dst + 40#64))
                  (sepConj_mono (r3b_ws_u64 (src + 8#64) (dst + 8#64) cap)
                    (sepConj_mono (r3b_ws_u64 (src + 16#64) (dst + 16#64) ptr)
                      (sepConj_mono (r3b_ws_u64 (src + 24#64) (dst + 24#64) (BitVec.ofNat 64 bs.length))
                        (Entails.refl Him))))))) ?_)
        apply r3b_peel; intro w4; apply r3b_keep
        apply r3b_peel; intro w5
        refine Entails.trans
          (Entails.trans (Entails.of_eq (by dsimp only [Him]; ac_rfl))
            (r3b_ws_combine6 ⟨speWord 24, cap, ptr, BitVec.ofNat 64 bs.length, w4, w5⟩
              (dst ↦₆₄ speWord 24) ((dst + 8#64) ↦₆₄ cap) ((dst + 16#64) ↦₆₄ ptr)
              ((dst + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length)
              (((dst + 32#64) ↦₈ msgTypeByte mt) ∗ memRegion (dst + 0x21#64) 7)
              (memRegion (dst + 40#64) 8) Him
              (r3b_speWord_tags (by omega))))
          (r3b_speOwnedAt_post ?_)
        rw [← hd16, ← hd24,
            ProofLib.memRegion_split' (b := dst + 0x21#64) (n := 7) (k := 8) (b' := dst + 40#64) rfl (by bv_omega) (by decide)]
        have hvec :
            ((dst + 8#64) ↦₆₄ cap) ∗ ((dst + 8#64 + 8#64) ↦₆₄ ptr) ∗
              ((dst + 8#64 + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ Him ⊢
            ∃∗ cap', ∃∗ ptr', vecU8At A (dst + 8#64) cap' ptr' bs :=
          Entails.sepExists_right cap (Entails.sepExists_right ptr
            (Entails.of_eq (r3b_vecU8At_eq A (dst + 8#64) cap ptr bs).symm))
        exact r3b_perm
          (sepConj_mono (Entails.refl (dst ↦₆₄ speWord 24))
            (sepConj_mono hvec
              (Entails.of_eq (show (((dst + 32#64) ↦₈ msgTypeByte mt) ∗ memRegion (dst + 0x21#64) 7) ∗
                  memRegion (dst + 40#64) 8 =
                ((dst + 0x20#64) ↦₈ msgTypeByte mt) ∗ (memRegion (dst + 0x21#64) 7 ∗ memRegion (dst + 40#64) 8) by ac_rfl))))
          (by ac_rfl)
      cases rsn with
      | decryptionFailed =>
        dsimp only [RunDrop.speOwnedAt, speAt, invalidMessageStrAt]
        rw [sepConj_pure_left_comm]
        exact Entails.pure_left False.elim
      | tooFarInFuture => exact hinval tooFarInFutureStr
      | macFailed => exact hinval macFailedStr
      | pqRatchet =>
        dsimp only [RunDrop.speOwnedAt, speAt, invalidMessageStrAt]
        apply r3b_peel; intro bs
        exact Entails.trans (hinval bs)
          (r3b_speOwnedAt_post
            (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro bs))))
      | badCiphertext =>
        dsimp only [RunDrop.speOwnedAt, speAt, invalidMessageStrAt]
        apply r3b_peel; intro bs
        exact Entails.trans (hinval bs)
          (r3b_speOwnedAt_post
            (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro bs))))

/-! ## 4. Local Stack Splitting, Address Unpacking & Shared Deallocation / Reject Tail -/

private theorem r3b_memRegion_to_cells :
    ∀ (k : Nat), 8 * k ≤ 2 ^ 64 → ∀ (a : BitVec 64), memRegion a (8 * k) ⊢ cells a k
  | 0, _, _ => by simp only [Nat.mul_zero, ProofLib.memRegion_zero, cells]; exact Entails.refl _
  | k + 1, hk, a => by
    have hsplit : 8 * (k + 1) = 8 + 8 * k := by omega
    rw [hsplit, ProofLib.memRegion_split a 8 (8 * k) (by omega), ProofLib.memRegion_eight a]
    refine Entails.trans (sepConj_mono_right (r3b_memRegion_to_cells k (by omega) (a + 8#64))) ?_
    simp only [cells, sepExists_sepConj_left]
    exact Entails.sepExists_mono fun _ => Entails.refl _

private theorem r3b_memRegion_to_runLocalsFrom (fsp : BitVec 64) :
    ∀ (off : Nat) (cs : List (Nat × Nat × SepProp)),
      RunLocalsFromWf off cs →
      (∀ c ∈ cs, c.2.2 = memRegion (fsp + BitVec.ofNat 64 c.1) c.2.1) →
      memRegion (fsp + BitVec.ofNat 64 off) (runLocalBytes - off) =
        runLocalsFrom fsp off cs
  | _, [], _, _ => rfl
  | off, (o, n, P) :: cs, ⟨hle, hwf'⟩, hcells => by
    have hlb : runLocalBytes = 0x29f0 := rfl
    have hon : o + n ≤ runLocalBytes := runLocalsFrom_le hwf'
    have hP : P = memRegion (fsp + BitVec.ofNat 64 o) n := hcells (o, n, P) (.head _)
    have htail := r3b_memRegion_to_runLocalsFrom fsp (o + n) cs hwf'
      (fun c hc => hcells c (.tail _ hc))
    have h1 : memRegion (fsp + BitVec.ofNat 64 off) (runLocalBytes - off) =
        memRegion (fsp + BitVec.ofNat 64 off) (o - off) ∗
          memRegion (fsp + BitVec.ofNat 64 o) (runLocalBytes - o) := by
      have hs := ProofLib.memRegion_split (fsp + BitVec.ofNat 64 off) (o - off)
        (runLocalBytes - o) (by omega)
      have hl : (o - off) + (runLocalBytes - o) = runLocalBytes - off := by omega
      have ha : fsp + BitVec.ofNat 64 off + BitVec.ofNat 64 (o - off) =
          fsp + BitVec.ofNat 64 o := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, show off + (o - off) = o by omega]
      simpa only [hl, ha] using hs
    have h2 : memRegion (fsp + BitVec.ofNat 64 o) (runLocalBytes - o) =
        memRegion (fsp + BitVec.ofNat 64 o) n ∗
          memRegion (fsp + BitVec.ofNat 64 (o + n)) (runLocalBytes - (o + n)) := by
      have hs := ProofLib.memRegion_split (fsp + BitVec.ofNat 64 o) n
        (runLocalBytes - (o + n)) (by omega)
      have hl : n + (runLocalBytes - (o + n)) = runLocalBytes - o := by omega
      have ha : fsp + BitVec.ofNat 64 o + BitVec.ofNat 64 n =
          fsp + BitVec.ofNat 64 (o + n) := by
        rw [BitVec.add_assoc, BitVec.ofNat_add]
      simpa only [hl, ha] using hs
    rw [h1, h2, htail, ← hP]
    rfl

private theorem r3b_ownedBytes_entails_nameHeap (A : RustAlloc) (cap ptr len : BitVec 64)
    (bs : List (BitVec 8)) :
    ownedBytes A cap ptr len bs ⊢
      ⌜len = BitVec.ofNat 64 bs.length⌝ ∗
        addrNameHeap A ⟨⟨cap, ptr, bs⟩, 0#8⟩ := by
  unfold ownedBytes addrNameHeap
  apply Entails.pure_left; rintro ⟨hlen, hle, hlt, hne⟩
  exact Entails.pure_right hlen (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))

private theorem r3b_addrNameHeap_dev_congr (A : RustAlloc) (v : VecGhost) (d₁ d₂ : BitVec 8) :
    addrNameHeap A ⟨v, d₁⟩ = addrNameHeap A ⟨v, d₂⟩ := rfl

private theorem r3b_addrUpperAt_words (a : BitVec 64) (g : AddrGhost) :
    addrUpperAt a g ⊢
      ∃∗ hi : BitVec 64,
        ⌜hi.setWidth 8 = g.device⌝ ∗ (a ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
          ((a + 8#64) ↦₆₄ hi) := by
  unfold addrUpperAt
  have hu := r3b_u8pad7_to_u64 (a + 8#64) g.device
  have ha9 : a + 8#64 + 1#64 = a + 9#64 := by bv_omega
  rw [ha9] at hu
  refine Entails.trans (sepConj_mono_right hu) ?_
  simp only [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro hi
  exact Entails.sepExists_right hi (Entails.of_eq (by ac_rfl))

private theorem r3b_words_to_addrUpperAt (a : BitVec 64) (g : AddrGhost) (hi : BitVec 64)
    (hhi : hi.setWidth 8 = g.device) :
    ((a ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗ ((a + 8#64) ↦₆₄ hi)) ⊢ addrUpperAt a g := by
  unfold addrUpperAt
  have hu := r3b_u64_to_u8pad7 (a + 8#64) g.device hi hhi
  have ha9 : a + 8#64 + 1#64 = a + 9#64 := by bv_omega
  rw [ha9] at hu
  exact sepConj_mono_right hu

private theorem r3b_nameHeap_dealloc (A : RustAlloc) (g : AddrGhost) (hcap : g.name.cap ≠ 0) :
    addrNameHeap A g ⊢
      ⌜LayoutOk g.name.cap.toNat 1⌝ ∗ A.live g.name.ptr g.name.cap.toNat 1 ∗
        memRegion g.name.ptr g.name.cap.toNat := by
  unfold addrNameHeap
  simp only [hcap, ↓reduceIte]
  apply Entails.pure_left; rintro ⟨hle, hlt, _⟩
  have hpos : 0 < g.name.cap.toNat :=
    Nat.pos_of_ne_zero fun h0 => hcap (BitVec.eq_of_toNat_eq h0)
  refine Entails.pure_right ⟨hpos, ⟨0, rfl⟩, by omega⟩ (sepConj_mono_right ?_)
  have hmerge :
      memRegion g.name.ptr g.name.bytes.length ∗
        memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
          (g.name.cap.toNat - g.name.bytes.length) =
      memRegion g.name.ptr g.name.cap.toNat := by
    have hsum : g.name.bytes.length + (g.name.cap.toNat - g.name.bytes.length) =
        g.name.cap.toNat := Nat.add_sub_of_le hle
    simpa only [hsum] using
      (ProofLib.memRegion_split g.name.ptr g.name.bytes.length
        (g.name.cap.toNat - g.name.bytes.length) (by omega)).symm
  rw [← hmerge]
  exact sepConj_mono_left (ProofLib.pointsToBytes_entails_memRegion g.name.ptr g.name.bytes)

private theorem r3b_nameHeap_zero (A : RustAlloc) (g : AddrGhost) (hcap : g.name.cap = 0) :
    addrNameHeap A g ⊢ emp := by
  unfold addrNameHeap
  simp only [hcap, ↓reduceIte]
  exact Entails.pure_left fun _ => Entails.refl emp

/-- Shared `peer` deallocation block `R+0x1008 → R+0x2c7c` (`AtReject .postDispatch`). -/
private theorem r3b_reject_from_1008 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {g : RunCall}
    (g' : StoresGhost) (peerG : AddrGhost) (u230 u238 : BitVec 64)
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRun img ext s0 s 0x1008)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (hrej : RejectK img ext A g s0 resStack Q Qp) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A peerG ∗
        runSaved s0 ∗
        memRegion (runFsp s0) 0x220 ∗
        (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((runFsp s0 + 0x230#64) ↦₆₄ u230) ∗
          ((runFsp s0 + 0x238#64) ↦₆₄ u238)) ∗
        memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      Q Qp (runOom s0) := by
  let fsp := runFsp s0
  have hloc_rejoin :
      memRegion fsp 0x220 ∗
        (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((fsp + 0x230#64) ↦₆₄ u230) ∗ ((fsp + 0x238#64) ↦₆₄ u238)) ∗
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ⊢
      runLocals fsp [] := by
    have h4 :
        ((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((fsp + 0x230#64) ↦₆₄ u230) ∗ ((fsp + 0x238#64) ↦₆₄ u238) ⊢
        memRegion (fsp + 0x220#64) 32 := by
      rw [ProofLib.memRegion_split' (b := fsp + 0x220#64) (n := 8) (k := 24)
            (b' := fsp + 0x228#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x228#64) (n := 8) (k := 16)
            (b' := fsp + 0x230#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x230#64) (n := 8) (k := 8)
            (b' := fsp + 0x238#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)))
    have hz : fsp + BitVec.ofNat 64 0 = fsp := by bv_omega
    have hwf : RunLocalsFromWf 0 [(0x220, 32, memRegion (fsp + 0x220#64) 32)] := by
      dsimp only [RunLocalsFromWf, runLocalBytes]; omega
    have hrej0 := runLocals_rejoin_empty fsp [(0x220, 32, memRegion (fsp + 0x220#64) 32)]
      hwf (by intro c hc; simp at hc; subst hc; exact Entails.refl _)
    dsimp only [runLocals, runLocalsFrom, Nat.sub_zero] at hrej0 ⊢
    rw [hz] at hrej0 ⊢
    rw [show BitVec.ofNat 64 (0x220 + 32) = 0x240#64 from rfl] at hrej0
    exact Entails.trans (sepConj_mono_right (sepConj_mono_left h4)) hrej0
  by_cases hcap : peerG.name.cap = 0#64
  · have hpc : s.pc = runPc img ext 0x1008 := hs.pc
    have hrun : s.status = .Running := hs.run
    have hsp : s.sp = fsp := hs.sp
    have hsp_al : s.spAligned = true := hs.spAligned_cur
    apply sepWPp_seq_inImage (mid := runPc img ext 0x2c7c) hs.inv
    have hfn0 := run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_rej img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 4104 16
    clear hfn0
    dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc ⊢
    generalize hfn :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
    examples_hide_fetches
    rw [hcap, show runFsp s0 = s.sp from hsp.symm]
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv'
    have hs' : InRun img ext s0 _ 0x2c7c :=
      r3b_inRun_step hs (by simp only [arm64_norm]; rw [← hfn])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv' (by simp only [calleeSavedVRegs, arm64_norm])
    have hat : AtReject img ext g g' .postDispatch s0 _ :=
      { base := hs'
        x19 := by simp only [arm64_norm, hx19]
        preRegs := fun hk => nomatch hk
        trace := by simpa only [arm64_norm] using htr
        hist := r3b_hist_of_eq (by simp only [arm64_norm]) (by simp only [arm64_norm]) hhist
        ans := hans }
    refine r3b_sepWPp_weaken_pre ?_ (hrej _ g' .postDispatch hat)
    rw [hsp, ← hcap]
    exact r3b_perm
      (r3b_perm_post
        (sepConj_mono (r3b_nameHeap_zero A peerG hcap)
          (sepConj_mono hloc_rejoin
            (Entails.refl (runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
              storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              runSaved s0 ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap))))
        (by rw [emp_sepConj]; dsimp only [rejectMem]; ac_rfl))
      (by ac_rfl)
  · have hbeq : (peerG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hpc : s.pc = runPc img ext 0x1008 := hs.pc
    have hrun : s.status = .Running := hs.run
    have hsp : s.sp = fsp := hs.sp
    have hsp_al : s.spAligned = true := hs.spAligned_cur
    apply r3b_sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (r3b_nameHeap_dealloc A peerG hcap))))))
    rw [show (runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        (⌜LayoutOk peerG.name.cap.toNat 1⌝ ∗
          A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
          memRegion peerG.name.ptr peerG.name.cap.toNat) ∗
        runSaved s0 ∗ memRegion fsp 0x220 ∗
        (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((fsp + 0x230#64) ↦₆₄ u230) ∗ ((fsp + 0x238#64) ↦₆₄ u238)) ∗
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap) =
      ⌜LayoutOk peerG.name.cap.toNat 1⌝ ∗
        (runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
          memRegion peerG.name.ptr peerG.name.cap.toNat ∗
          runSaved s0 ∗ memRegion fsp 0x220 ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            ((fsp + 0x230#64) ↦₆₄ u230) ∗ ((fsp + 0x238#64) ↦₆₄ u238)) ∗
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap) by ac_rfl]
    apply r3b_sepWPp_pure_left; intro hlay
    apply sepWPp_seq_inImage (mid := (mProg img ext).fnAddr deallocName) hs.inv
    have hfn0 := run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_rej img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 4104 16
    code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_prej img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 11380 8
    clear hfn0
    dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc ⊢
    generalize hfn :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
    examples_hide_fetches
    rw [← hsp]
    wp_steps
    apply SepWP.done
      (by simp only [arm64_norm, ← hfn, Program.fnAddr_rebase, run_fnOff, rustDealloc_fnOff])
      (by simp only [arm64_norm, hrun])
    intro hinv_c
    have hstk_split := r3b_stackAt_split_ge s.sp hext_le hsub64
    refine r3b_call_inImage
      (F := runResAt A cliWrOk g.res (some none) ∗
        memRegion g.call 56 ∗
        storesAt A g.stores g' ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗
        runSaved s0 ∗
        memRegion s.sp 0x220 ∗
        (((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((s.sp + 0x230#64) ↦₆₄ u230) ∗
          ((s.sp + 0x238#64) ↦₆₄ u238)) ∗
        memRegion (s.sp + 0x240#64) (runLocalBytes - 0x240) ∗
        memRegion (s.sp - BitVec.ofNat 64 (resStack - runFrame))
          (resStack - runFrame - extHookStack) ∗
        anyHeap)
      (s0 := s0) (peerG.name.ptr, peerG.name.cap.toNat, 1)
      hh.allocFs.dealloc hinv_c
      (by simp only [arm64_norm, ← hfn, Program.fnAddr_rebase, run_fnOff, rustDealloc_fnOff])
      (by simp only [arm64_norm, hrun])
      (by simpa only [State.spAligned, arm64_norm] using hsp_al)
      (retAddr := runPc img ext 0x2c7c)
      (by simp only [arm64_norm, runPc, mProg, tripleRatchetProgAtExt, ← hfn])
      ?_
      (hnext := fun sm _ hinv_m hpcm hrunm hspm hcsm => ?_)
    · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
      simp only [sepConj_assoc]
      apply Entails.pure_right
      · exact ⟨by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], hlay⟩
      rw [hstk_split]
      simp only [arm64_norm]
      exact Entails.of_eq (by ac_rfl)
    · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
      simp only [sepConj_assoc]
      apply r3b_sepWPp_pure_left; intro hfs_m
      apply r3b_sepWPp_pure_left; intro htr_m
      have hs_m : InRun img ext s0 sm 0x2c7c :=
        r3b_inRun_step hs hpcm hrunm (hspm.trans (by simp only [arm64_norm]))
          (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm])) hinv_m
          (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [calleeSavedVRegs, arm64_norm]))
      have htr_tot : sm.trace = s.trace := htr_m.trans (by simp only [arm64_norm])
      have hfs_tot : sm.fs = s.fs := hfs_m.trans (by simp only [arm64_norm])
      have hat : AtReject img ext g g' .postDispatch s0 sm :=
        { base := hs_m
          x19 := hcsm.1.trans (by simp only [arm64_norm, hx19])
          preRegs := fun hk => nomatch hk
          trace := htr_tot ▸ htr
          hist := r3b_hist_of_eq htr_tot (congrArg FsState.files hfs_tot) hhist
          ans := hans }
      refine r3b_sepWPp_weaken_pre ?_ (hrej sm g' .postDispatch hat)
      rw [hsp] at hstk_split
      dsimp only [rejectMem, fsp] at hloc_rejoin hstk_split ⊢
      simp only [arm64_norm, hsp]
      rw [hstk_split]
      exact r3b_perm
        (r3b_perm_post
          (sepConj_mono hloc_rejoin
            (Entails.refl (runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
              storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              runSaved s0 ∗
              memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
                (resStack - runFrame - extHookStack) ∗
              stackAt (runFsp s0) extHookStack ∗ A.pool ∗ anyHeap)))
          (by simp only [arm64_norm]; ac_rfl))
        (by dsimp only [fsp]; simp only [arm64_norm]; ac_rfl)

/-- Shared reject tail from `R+0xfec → R+0x2c7c` when `me = .some meV meG`:
writes `-1` to `[g.res]`, frees `meG.name`, and finishes via `r3b_reject_from_1008`. -/
private theorem r3b_reject_from_fec {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {g : RunCall}
    (g' : StoresGhost) (meG peerG : AddrGhost) (u230 u238 : BitVec 64)
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRun img ext s0 s 0xfec)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (hrej : RejectK img ext A g s0 resStack Q Qp) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A meG ∗ addrNameHeap A peerG ∗
        runSaved s0 ∗
        memRegion (runFsp s0) 0x220 ∗
        (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((runFsp s0 + 0x230#64) ↦₆₄ u230) ∗
          ((runFsp s0 + 0x238#64) ↦₆₄ u238)) ∗
        memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      Q Qp (runOom s0) := by
  have hres_split : memRegion g.res runResSize =
      (∃∗ vr, g.res ↦₆₄ vr) ∗ memRegion (g.res + 8#64) (runResSize - 8) := by
    rw [← ProofLib.memRegion_eight g.res]
    exact ProofLib.memRegion_split g.res 8 (runResSize - 8) (by decide)
  rw [hres_split]
  simp only [sepExists_sepConj_left]
  apply r3b_sepWPp_exists_left; intro vr
  by_cases hcap : meG.name.cap = 0#64
  · have hpc : s.pc = runPc img ext 0xfec := hs.pc
    have hrun : s.status = .Running := hs.run
    apply sepWPp_seq_inImage (mid := runPc img ext 0x1008) hs.inv
    have hfn0 := run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_rej img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 4076 28
    clear hfn0
    dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc ⊢
    generalize hfn :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
    examples_hide_fetches
    rw [hcap] at hx21
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv'
    have hs1 : InRun img ext s0 _ 0x1008 :=
      r3b_inRun_step hs (by simp only [arm64_norm]; rw [← hfn])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv' (by simp only [calleeSavedVRegs, arm64_norm])
    refine r3b_sepWPp_weaken_pre ?_
      (r3b_reject_from_1008 g' peerG u230 u238 hh hext_le hsub64 hs1
        (by simp only [arm64_norm, hx19])
        (by simpa only [arm64_norm] using htr)
        (r3b_hist_of_eq (by simp only [arm64_norm]) (by simp only [arm64_norm]) hhist)
        hans
        hrej)
    exact r3b_perm
      (r3b_perm_post
        (sepConj_mono (r3b_nameHeap_zero A meG hcap)
          (Entails.refl (runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
            storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            addrNameHeap A peerG ∗ runSaved s0 ∗
            memRegion (runFsp s0) 0x220 ∗
            (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
              ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
              ((runFsp s0 + 0x230#64) ↦₆₄ u230) ∗
              ((runFsp s0 + 0x238#64) ↦₆₄ u238)) ∗
            memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
            stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap)))
        (by rw [emp_sepConj]))
      (by dsimp only [runResAt]; ac_rfl)
  · have hbeq : (meG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hbeq21 : (s.readReg64 (.gpr 21#5) == 0#64) = false := by rw [hx21]; exact hbeq
    have hpc : s.pc = runPc img ext 0xfec := hs.pc
    have hrun : s.status = .Running := hs.run
    have hsp : s.sp = runFsp s0 := hs.sp
    have hsp_al : s.spAligned = true := hs.spAligned_cur
    apply r3b_sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (r3b_nameHeap_dealloc A meG hcap))))))
    rw [show (((g.res ↦₆₄ vr) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        (⌜LayoutOk meG.name.cap.toNat 1⌝ ∗
          A.live meG.name.ptr meG.name.cap.toNat 1 ∗
          memRegion meG.name.ptr meG.name.cap.toNat) ∗
        addrNameHeap A peerG ∗ runSaved s0 ∗
        memRegion (runFsp s0) 0x220 ∗
        (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((runFsp s0 + 0x230#64) ↦₆₄ u230) ∗
          ((runFsp s0 + 0x238#64) ↦₆₄ u238)) ∗
        memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap) =
      ⌜LayoutOk meG.name.cap.toNat 1⌝ ∗
        (((g.res ↦₆₄ vr) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          A.live meG.name.ptr meG.name.cap.toNat 1 ∗
          memRegion meG.name.ptr meG.name.cap.toNat ∗
          addrNameHeap A peerG ∗ runSaved s0 ∗
          memRegion (runFsp s0) 0x220 ∗
          (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            ((runFsp s0 + 0x230#64) ↦₆₄ u230) ∗
            ((runFsp s0 + 0x238#64) ↦₆₄ u238)) ∗
          memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap) by ac_rfl]
    apply r3b_sepWPp_pure_left; intro hlay
    apply sepWPp_seq_inImage (mid := (mProg img ext).fnAddr deallocName) hs.inv
    have hfn0 := run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_rej img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 4076 28
    clear hfn0
    dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc ⊢
    generalize hfn :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
    examples_hide_fetches
    wp_steps
    apply SepWP.done
      (by simp only [arm64_norm, ← hfn, Program.fnAddr_rebase, run_fnOff, rustDealloc_fnOff])
      (by simp only [arm64_norm, hrun])
    intro hinv_c
    have hstk_split := r3b_stackAt_split_ge s.sp hext_le hsub64
    refine r3b_call_inImage
      (F := ((g.res ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
        memRegion g.call 56 ∗
        storesAt A g.stores g' ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A peerG ∗ runSaved s0 ∗
        memRegion (runFsp s0) 0x220 ∗
        (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((runFsp s0 + 0x230#64) ↦₆₄ u230) ∗
          ((runFsp s0 + 0x238#64) ↦₆₄ u238)) ∗
        memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
        memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
          (resStack - runFrame - extHookStack) ∗
        anyHeap)
      (s0 := s0) (meG.name.ptr, meG.name.cap.toNat, 1)
      hh.allocFs.dealloc hinv_c
      (by simp only [arm64_norm, ← hfn, Program.fnAddr_rebase, run_fnOff, rustDealloc_fnOff])
      (by simp only [arm64_norm, hrun])
      (by simpa only [State.spAligned, arm64_norm] using hsp_al)
      (retAddr := runPc img ext 0x1008)
      (by simp only [arm64_norm, runPc, mProg, tripleRatchetProgAtExt, ← hfn])
      ?_
      (hnext := fun sm _ hinv_m hpcm hrunm hspm hcsm => ?_)
    · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
      simp only [sepConj_assoc]
      apply Entails.pure_right
      · exact ⟨by simp only [arm64_norm]; try rw [hx28],
          by simp only [arm64_norm]; try rw [hx21], by simp only [arm64_norm], hlay⟩
      rw [hsp] at hstk_split
      rw [hstk_split]
      simp only [arm64_norm, hsp]
      exact Entails.of_eq (by ac_rfl)
    · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
      simp only [sepConj_assoc]
      apply r3b_sepWPp_pure_left; intro hfs_m
      apply r3b_sepWPp_pure_left; intro htr_m
      have hs_m : InRun img ext s0 sm 0x1008 :=
        r3b_inRun_step hs hpcm hrunm (hspm.trans (by simp only [arm64_norm]))
          (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm])) hinv_m
          (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [calleeSavedVRegs, arm64_norm]))
      have htr_tot : sm.trace = s.trace := htr_m.trans (by simp only [arm64_norm])
      have hfs_tot : sm.fs = s.fs := hfs_m.trans (by simp only [arm64_norm])
      refine r3b_sepWPp_weaken_pre ?_
        (r3b_reject_from_1008 g' peerG u230 u238 hh hext_le hsub64 hs_m
          (hcsm.1.trans (by simp only [arm64_norm, hx19]))
          (htr_tot ▸ htr)
          (r3b_hist_of_eq htr_tot (congrArg FsState.files hfs_tot) hhist)
          hans
          hrej)
      rw [hsp] at hstk_split
      rw [hstk_split]
      simp only [arm64_norm, hsp]
      exact Entails.of_eq (by dsimp only [runResAt]; ac_rfl)

private theorem r3b_call7_to_memRegion56 (a : BitVec 64) (cw : CallW) :
    (a ↦₆₄ cw.w0) ∗ ((a + 8#64) ↦₆₄ cw.w1) ∗ ((a + 16#64) ↦₆₄ cw.w2) ∗
      ((a + 24#64) ↦₆₄ cw.w3) ∗ ((a + 32#64) ↦₆₄ cw.w4) ∗ ((a + 40#64) ↦₆₄ cw.w5) ∗
      ((a + 48#64) ↦₆₄ cw.w6) ⊢ memRegion a 56 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 48) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 40) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 32) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 24) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 16) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 40#64) (n := 8) (k := 8) (b' := a + 48#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo64_entails_memRegion _ _))))))

private theorem r3b_words4_entails_mem32 (a w0 w1 w2 w3 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ⊢
      memRegion a 32 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 24) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 8) (b' := a + 24#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)))

private theorem r3b_mem32_to_words4 (a : BitVec 64) :
    memRegion a 32 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 24) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 8) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64), ProofLib.memRegion_eight (a + 24#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w0
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.of_eq (by ac_rfl)))))

private theorem r3b_nameHeap_cap_ne_neg1 (A : RustAlloc) (g : AddrGhost) :
    addrNameHeap A g ⊢ ⌜g.name.cap ≠ 0xffffffffffffffff#64⌝ ∗ addrNameHeap A g := by
  unfold addrNameHeap
  apply Entails.pure_left; rintro ⟨hle, hlt, hne⟩
  have hne1 : g.name.cap ≠ 0xffffffffffffffff#64 := by
    intro heq
    have hbig : (0xffffffffffffffff#64).toNat = 2 ^ 64 - 1 := by decide
    rw [heq, hbig] at hlt
    omega
  exact Entails.pure_right hne1 (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))

/-- Shared `me = .none` path (`R+0x214 → R+0x4b0 → R+0x7a4 → R+0x86c → R+0x1008 → R+0x2c7c`). -/
private theorem r3b_me_none {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {g : RunCall} {peerV : AddrV} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hres : runNeed B (slotsOf A img S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63)
    (he : AtRunEntry S img ext g s0)
    (hd : AtDispatch img ext g .none s0 s)
    (hcall : g.c = .recv peerV)
    (hrej : RejectK img ext A g s0 resStack Q Qp) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (dispatchMem A img g .none s0 resStack) Q Qp (runOom s0) := by
  have hbnds := runNeed_bounds hres hres64
  have hext_le : extHookStack ≤ resStack - runFrame := by
    have := hbnds.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
  have hsub64 : resStack - runFrame ≤ 2 ^ 64 := hbnds.2.2.1
  have hans : g.a = some none := hd.reject_of_me_none he
  let fsp := runFsp s0
  dsimp only [dispatchMem, dispatchMeHeap, dispatchCells]
  rw [hcall]
  dsimp only [callAt, callHeap, addrWords]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply r3b_sepWPp_exists_left; intro cw
  have hres_split : memRegion g.res runResSize =
      (∃∗ vr, g.res ↦₆₄ vr) ∗ memRegion (g.res + 8#64) (runResSize - 8) := by
    rw [← ProofLib.memRegion_eight g.res]
    exact ProofLib.memRegion_split g.res 8 (runResSize - 8) (by decide)
  have hloc_split : runLocals fsp [] =
      memRegion fsp 0x220 ∗ memRegion (fsp + 0x220#64) 32 ∗
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) := by
    have hwf : RunLocalsFromWf 0 [(0x220, 32, memRegion (fsp + 0x220#64) 32)] := by
      dsimp only [RunLocalsFromWf, runLocalBytes]; omega
    have h0 := r3b_memRegion_to_runLocalsFrom fsp 0 [(0x220, 32, memRegion (fsp + 0x220#64) 32)]
      hwf (by intro c hc; simp at hc; subst hc; rfl)
    have hz : fsp + BitVec.ofNat 64 0 = fsp := by bv_omega
    dsimp only [runLocals, runLocalsFrom, Nat.sub_zero] at h0 ⊢
    rw [hz] at h0 ⊢
    rw [show BitVec.ofNat 64 (0x220 + 32) = 0x240#64 from rfl,
        show 0x220 + 32 = 0x240 from rfl] at h0
    exact h0
  rw [hres_split, hloc_split]
  let peerG : AddrGhost := ⟨⟨cw.w1, cw.w2, peerV.name⟩, peerV.device⟩
  have hpre_prep :
      (((∃∗ vr, g.res ↦₆₄ vr) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
        ((g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
          ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
          ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6) ∗
          ⌜cw.w0 = 0x8000000000000003#64⌝ ∗
          (ownedBytes A cw.w1 cw.w2 cw.w3 peerV.name ∗ ⌜cw.w4.setWidth 8 = peerV.device⌝)) ∗
        storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i (.recv peerV)) ∗
        coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ logOff img ∗ emp ∗
        runSaved s0 ∗
        (memRegion fsp 0x220 ∗ memRegion (fsp + 0x220#64) 32 ∗
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240)) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool) ⊢
      ∃∗ vr, ∃∗ u0, ∃∗ u1, ∃∗ u2, ∃∗ u3,
        (g.res ↦₆₄ vr) ∗ memRegion (g.res + 8#64) (runResSize - 8) ∗
        (g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
        ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
        ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6) ∗
        storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A peerG ∗ runSaved s0 ∗
        memRegion fsp 0x220 ∗
        ((fsp + 0x220#64) ↦₆₄ u0) ∗ ((fsp + 0x228#64) ↦₆₄ u1) ∗
        ((fsp + 0x230#64) ↦₆₄ u2) ∗ ((fsp + 0x238#64) ↦₆₄ u3) ∗
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap := by
    rw [← hcall, emp_sepConj]
    refine Entails.trans
      (r3b_perm
        (sepConj_mono (r3b_ownedBytes_entails_nameHeap A cw.w1 cw.w2 cw.w3 peerV.name)
          (sepConj_mono (r3b_mem32_to_words4 (fsp + 0x220#64))
            (sepConj_mono
              (entails_anyHeap (⌜cw.w0 = 0x8000000000000003#64⌝ ∗ ⌜cw.w4.setWidth 8 = peerV.device⌝ ∗
                coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
                CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ logOff img))
              (Entails.refl ((∃∗ vr, g.res ↦₆₄ vr) ∗ memRegion (g.res + 8#64) (runResSize - 8) ∗
                (g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
                ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
                ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6) ∗
                storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
                runSaved s0 ∗ memRegion fsp 0x220 ∗
                memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
                stackAt fsp (resStack - runFrame) ∗ A.pool)))))
        (by ac_rfl))
      ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro vr
    apply Entails.sepExists_elim; intro u0
    apply Entails.sepExists_elim; intro u1
    apply Entails.sepExists_elim; intro u2
    apply Entails.sepExists_elim; intro u3
    simp only [sepConj_assoc]
    apply Entails.pure_left; intro _
    rw [r3b_addrNameHeap_dev_congr A ⟨cw.w1, cw.w2, peerV.name⟩ 0#8 peerV.device]
    have ha8 : fsp + 0x220#64 + 8#64 = fsp + 0x228#64 := by bv_omega
    have ha16 : fsp + 0x220#64 + 16#64 = fsp + 0x230#64 := by bv_omega
    have ha24 : fsp + 0x220#64 + 24#64 = fsp + 0x238#64 := by bv_omega
    rw [ha8, ha16, ha24]
    exact Entails.sepExists_right vr (Entails.sepExists_right u0
      (Entails.sepExists_right u1 (Entails.sepExists_right u2
        (Entails.sepExists_right u3 (Entails.of_eq (by ac_rfl))))))
  apply r3b_sepWPp_weaken_pre hpre_prep
  apply r3b_sepWPp_exists_left; intro vr
  apply r3b_sepWPp_exists_left; intro u0
  apply r3b_sepWPp_exists_left; intro u1
  apply r3b_sepWPp_exists_left; intro u2
  apply r3b_sepWPp_exists_left; intro u3
  have hpc : s.pc = runPc img ext 0x214 := hd.base.pc
  have hrun : s.status = .Running := hd.base.run
  have hsp : s.sp = fsp := hd.base.sp
  have hsp_al : s.spAligned = true := hd.base.spAligned_cur
  have hx8 : s.readReg64 (.gpr 8#5) = 3#64 := by simpa [hcall, CallV.tag] using hd.x8
  have hx20 : s.readReg64 (.gpr 20#5) = g.res := hd.x20
  have hx21 : s.readReg64 (.gpr 21#5) = noneCap := hd.meRegs
  have hx25 : s.readReg64 (.gpr 25#5) = g.call := hd.x25
  apply sepWPp_seq_inImage (mid := runPc img ext 0x1008) hd.base.inv
  have hfn0 := run_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_disp1 img.base
    (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 532 8
  code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_disp2 img.base
    (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 1200 8
  code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_head img.base
    (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 1956 20
  code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_menone img.base
    (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 2156 12
  clear hfn0
  dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc ⊢
  generalize hfn :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
  examples_hide_fetches
  dsimp only [noneCap] at hx21
  rw [← hsp]
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
  intro hinv1
  have hs1 : InRun img ext s0 _ 0x1008 :=
    r3b_inRun_step hd.base (by simp only [arm64_norm]; rw [← hfn])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1 (by simp only [calleeSavedVRegs, arm64_norm])
  have hhist : RunHistOk g.i s0 _ :=
    ⟨by simpa only [arm64_norm] using hd.fs, by simpa only [arm64_norm] using hd.stdout⟩
  refine r3b_sepWPp_weaken_pre ?_
    (r3b_reject_from_1008 StoresGhost.opened peerG cw.w3 cw.w4 hh hext_le hsub64 hs1
      (by simp only [arm64_norm, hd.x19])
      (by simpa only [arm64_norm] using hd.trace)
      hhist hans hrej)
  rw [hsp]
  exact r3b_perm
    (r3b_perm_post
      (sepConj_mono (r3b_call7_to_memRegion56 g.call cw)
        (Entails.refl (runResAt A cliWrOk g.res (some none) ∗
          storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          addrNameHeap A peerG ∗ runSaved s0 ∗
          memRegion fsp 0x220 ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            ((fsp + 0x230#64) ↦₆₄ cw.w3) ∗
            ((fsp + 0x238#64) ↦₆₄ cw.w4)) ∗
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)))
      (by dsimp only [fsp]; ac_rfl))
    (by dsimp only [fsp, runResAt, peerG]; ac_rfl)

/-- Shared `me = .some meV meG` dispatch-head step `R+0x214 → R+0x4b0 → R+0x7a4 .. R+0x7c8`. -/
private theorem r3b_recv_head_some {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {g : RunCall} {peerV meV : AddrV} {meG : AddrGhost}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hd : AtDispatch img ext g (.some meV meG) s0 s)
    (hcall : g.c = .recv peerV)
    (hk : ∀ (s1 : State) (peerG : AddrGhost) (cw4 hiMe : BitVec 64),
      InRun img ext s0 s1 0x7c8 →
      s1.readReg64 (.gpr 19#5) = g.stores →
      s1.readReg64 (.gpr 20#5) = g.res →
      s1.readReg64 (.gpr 21#5) = meG.name.cap →
      s1.readReg64 (.gpr 23#5) = g.inp →
      s1.readReg64 (.gpr 24#5) = BitVec.ofNat 64 (inputOf g.i g.c).length →
      s1.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64 →
      s1.readReg64 (.gpr 27#5) = runFsp s0 + 0x1750#64 →
      s1.readReg64 (.gpr 28#5) = meG.name.ptr →
      s1.trace = s.trace →
      s1.fs = s.fs →
      peerG.val = addrValOf peerV →
      meG.val = addrValOf meV →
      cw4.setWidth 8 = peerG.device →
      hiMe.setWidth 8 = meG.device →
      SepWPp (mProg img ext) (s0.readReg64 .lr) s1
        (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
          CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ logOff img ∗
          addrNameHeap A meG ∗ addrNameHeap A peerG ∗
          runSaved s0 ∗
          memRegion (runFsp s0) 0x220 ∗
          (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            ((runFsp s0 + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
            ((runFsp s0 + 0x238#64) ↦₆₄ cw4)) ∗
          memRegion (runFsp s0 + 0x240#64) 0x20 ∗
          (((runFsp s0 + 0x260#64) ↦₆₄ meG.name.cap) ∗
            ((runFsp s0 + 0x268#64) ↦₆₄ meG.name.ptr) ∗
            ((runFsp s0 + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
            ((runFsp s0 + 0x278#64) ↦₆₄ hiMe)) ∗
          memRegion (runFsp s0 + 0x280#64) (runLocalBytes - 0x280) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool)
        Q Qp (runOom s0)) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (dispatchMem A img g (.some meV meG) s0 resStack) Q Qp (runOom s0) := by
  let fsp := runFsp s0
  rcases hd.meRegs with ⟨hx21, hx28, hme_bytes, _, hme_dev⟩
  have hme_val : meG.val = addrValOf meV := by
    cases meG with
    | mk nm dv =>
      dsimp only [AddrGhost.val, addrValOf] at hme_bytes hme_dev ⊢
      rw [hme_bytes, hme_dev]
  dsimp only [dispatchMem, dispatchMeHeap, dispatchCells]
  rw [hcall]
  dsimp only [callAt, callHeap, addrWords]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply r3b_sepWPp_exists_left; intro cw
  let peerG : AddrGhost := ⟨⟨cw.w1, cw.w2, peerV.name⟩, peerV.device⟩
  have hloc_split :
      runLocals fsp [(0x1d0, 16, addrUpperAt (fsp + 0x1d0#64) meG)] =
        memRegion fsp 0x1d0 ∗ addrUpperAt (fsp + 0x1d0#64) meG ∗
          memRegion (fsp + 0x1e0#64) 0x40 ∗ memRegion (fsp + 0x220#64) 32 ∗
          memRegion (fsp + 0x240#64) 0x20 ∗ memRegion (fsp + 0x260#64) 32 ∗
          memRegion (fsp + 0x280#64) (runLocalBytes - 0x280) := by
    have hwf : RunLocalsFromWf 0x1e0
        [(0x220, 32, memRegion (fsp + 0x220#64) 32),
         (0x260, 32, memRegion (fsp + 0x260#64) 32)] := by
      dsimp only [RunLocalsFromWf, runLocalBytes]; omega
    have htail := r3b_memRegion_to_runLocalsFrom fsp 0x1e0
      [(0x220, 32, memRegion (fsp + 0x220#64) 32),
       (0x260, 32, memRegion (fsp + 0x260#64) 32)]
      hwf (by intro c hc; simp at hc; rcases hc with rfl | rfl <;> rfl)
    dsimp only [runLocals, runLocalsFrom] at htail ⊢
    have hz : fsp + BitVec.ofNat 64 0 = fsp := by bv_omega
    rw [hz, ← htail]
  rw [hloc_split]
  have hprep :
      (memRegion g.res runResSize ∗
        ((g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
          ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
          ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6) ∗
          ⌜cw.w0 = 0x8000000000000003#64⌝ ∗
          (ownedBytes A cw.w1 cw.w2 cw.w3 peerV.name ∗ ⌜cw.w4.setWidth 8 = peerV.device⌝)) ∗
        storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i (.recv peerV)) ∗
        coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ logOff img ∗
        addrNameHeap A meG ∗ runSaved s0 ∗
        (memRegion fsp 0x1d0 ∗ addrUpperAt (fsp + 0x1d0#64) meG ∗
          memRegion (fsp + 0x1e0#64) 0x40 ∗ memRegion (fsp + 0x220#64) 32 ∗
          memRegion (fsp + 0x240#64) 0x20 ∗ memRegion (fsp + 0x260#64) 32 ∗
          memRegion (fsp + 0x280#64) (runLocalBytes - 0x280)) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool) ⊢
      ∃∗ hiMe, ∃∗ u0, ∃∗ u1, ∃∗ u2, ∃∗ u3, ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3,
        ⌜meG.name.cap ≠ 0xffffffffffffffff#64 ∧ cw.w3 = BitVec.ofNat 64 peerV.name.length ∧
          cw.w4.setWidth 8 = peerV.device ∧ hiMe.setWidth 8 = meG.device⌝ ∗
        memRegion g.res runResSize ∗
        (g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
        ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
        ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6) ∗
        storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ logOff img ∗
        addrNameHeap A meG ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
        memRegion fsp 0x1d0 ∗
        ((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
        ((fsp + 0x1d8#64) ↦₆₄ hiMe) ∗
        memRegion (fsp + 0x1e0#64) 0x40 ∗
        ((fsp + 0x220#64) ↦₆₄ u0) ∗ ((fsp + 0x228#64) ↦₆₄ u1) ∗
        ((fsp + 0x230#64) ↦₆₄ u2) ∗ ((fsp + 0x238#64) ↦₆₄ u3) ∗
        memRegion (fsp + 0x240#64) 0x20 ∗
        ((fsp + 0x260#64) ↦₆₄ v0) ∗ ((fsp + 0x268#64) ↦₆₄ v1) ∗
        ((fsp + 0x270#64) ↦₆₄ v2) ∗ ((fsp + 0x278#64) ↦₆₄ v3) ∗
        memRegion (fsp + 0x280#64) (runLocalBytes - 0x280) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool := by
    rw [← hcall]
    refine Entails.trans
      (r3b_perm
        (sepConj_mono
          (Entails.refl (⌜cw.w0 = 0x8000000000000003#64⌝ ∗
            ⌜cw.w4.setWidth 8 = peerV.device⌝))
          (sepConj_mono (r3b_nameHeap_cap_ne_neg1 A meG)
            (sepConj_mono (r3b_ownedBytes_entails_nameHeap A cw.w1 cw.w2 cw.w3 peerV.name)
              (sepConj_mono (r3b_addrUpperAt_words (fsp + 0x1d0#64) meG)
                (sepConj_mono (r3b_mem32_to_words4 (fsp + 0x220#64))
                  (sepConj_mono (r3b_mem32_to_words4 (fsp + 0x260#64))
                    (Entails.refl (memRegion g.res runResSize ∗
                      (g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗
                      ((g.call + 16#64) ↦₆₄ cw.w2) ∗ ((g.call + 24#64) ↦₆₄ cw.w3) ∗
                      ((g.call + 32#64) ↦₆₄ cw.w4) ∗ ((g.call + 40#64) ↦₆₄ cw.w5) ∗
                      ((g.call + 48#64) ↦₆₄ cw.w6) ∗
                      storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
                      coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
                      CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ logOff img ∗
                      runSaved s0 ∗ memRegion fsp 0x1d0 ∗ memRegion (fsp + 0x1e0#64) 0x40 ∗
                      memRegion (fsp + 0x240#64) 0x20 ∗
                      memRegion (fsp + 0x280#64) (runLocalBytes - 0x280) ∗
                      stackAt fsp (resStack - runFrame) ∗ A.pool))))))))
        (by ac_rfl))
      ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v0
    apply Entails.sepExists_elim; intro v1
    apply Entails.sepExists_elim; intro v2
    apply Entails.sepExists_elim; intro v3
    apply Entails.sepExists_elim; intro u0
    apply Entails.sepExists_elim; intro u1
    apply Entails.sepExists_elim; intro u2
    apply Entails.sepExists_elim; intro u3
    apply Entails.sepExists_elim; intro hiMe
    simp only [sepConj_assoc]
    apply Entails.pure_left; intro _
    apply Entails.pure_left; intro hdev_cw4
    apply Entails.pure_left; intro hne1
    apply r3b_pure1; intro hlen_cw3
    apply r3b_pure2; intro hhi
    rw [r3b_addrNameHeap_dev_congr A ⟨cw.w1, cw.w2, peerV.name⟩ 0#8 peerV.device]
    have hd8 : fsp + 0x1d0#64 + 8#64 = fsp + 0x1d8#64 := by bv_omega
    have hu8 : fsp + 0x220#64 + 8#64 = fsp + 0x228#64 := by bv_omega
    have hu16 : fsp + 0x220#64 + 16#64 = fsp + 0x230#64 := by bv_omega
    have hu24 : fsp + 0x220#64 + 24#64 = fsp + 0x238#64 := by bv_omega
    have hv8 : fsp + 0x260#64 + 8#64 = fsp + 0x268#64 := by bv_omega
    have hv16 : fsp + 0x260#64 + 16#64 = fsp + 0x270#64 := by bv_omega
    have hv24 : fsp + 0x260#64 + 24#64 = fsp + 0x278#64 := by bv_omega
    rw [hd8, hu8, hu16, hu24, hv8, hv16, hv24]
    exact Entails.sepExists_right hiMe (Entails.sepExists_right u0
      (Entails.sepExists_right u1 (Entails.sepExists_right u2
        (Entails.sepExists_right u3 (Entails.sepExists_right v0
          (Entails.sepExists_right v1 (Entails.sepExists_right v2
            (Entails.sepExists_right v3
              (Entails.pure_right ⟨hne1, hlen_cw3, hdev_cw4, hhi⟩
                (Entails.of_eq (by ac_rfl)))))))))))
  apply r3b_sepWPp_weaken_pre hprep
  apply r3b_sepWPp_exists_left; intro hiMe
  apply r3b_sepWPp_exists_left; intro u0
  apply r3b_sepWPp_exists_left; intro u1
  apply r3b_sepWPp_exists_left; intro u2
  apply r3b_sepWPp_exists_left; intro u3
  apply r3b_sepWPp_exists_left; intro v0
  apply r3b_sepWPp_exists_left; intro v1
  apply r3b_sepWPp_exists_left; intro v2
  apply r3b_sepWPp_exists_left; intro v3
  apply r3b_sepWPp_pure_left; rintro ⟨hne1, hlen_cw3, hdev_cw4, hhi⟩
  have hcmn : meG.name.cap + 1#64 ≠ 0#64 := fun h0 => hne1 (by bv_omega)
  have hbeq_cmn : ((meG.name.cap + 1#64) == 0#64) = false := beq_eq_false_iff_ne.mpr hcmn
  have hpc : s.pc = runPc img ext 0x214 := hd.base.pc
  have hrun : s.status = .Running := hd.base.run
  have hsp : s.sp = fsp := hd.base.sp
  have hsp_al : s.spAligned = true := hd.base.spAligned_cur
  have hx8 : s.readReg64 (.gpr 8#5) = 3#64 := by simpa [hcall, CallV.tag] using hd.x8
  have hx25 : s.readReg64 (.gpr 25#5) = g.call := hd.x25
  apply sepWPp_seq_inImage (mid := runPc img ext 0x7c8) hd.base.inv
  have hfn0 := run_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_disp1 img.base
    (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 532 8
  code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_disp2 img.base
    (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 1200 8
  code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_head img.base
    (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 1956 36
  clear hfn0
  dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc ⊢
  generalize hfn :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
  examples_hide_fetches
  rw [← hsp]
  wp_steps
  apply SepWP.done
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, hrun])
  intro hinv1
  have hs1 : InRun img ext s0 _ 0x7c8 :=
    r3b_inRun_step hd.base (by simp only [arm64_norm]; rw [← hfn])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1 (by simp only [calleeSavedVRegs, arm64_norm])
  refine r3b_sepWPp_weaken_pre ?_
    (hk _ peerG cw.w4 hiMe hs1
      (by simp only [arm64_norm, hd.x19])
      (by simp only [arm64_norm, hd.x20])
      (by simp only [arm64_norm, hx21])
      (by simp only [arm64_norm, hd.x23])
      (by simp only [arm64_norm, hd.x24])
      (by simp only [arm64_norm, hd.x26])
      (by simp only [arm64_norm, hd.x27])
      (by simp only [arm64_norm, hx28])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      rfl hme_val hdev_cw4 hhi)
  rw [hsp]
  have h1d0_collapse :
      memRegion fsp 0x1d0 ∗
        ((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
        ((fsp + 0x1d8#64) ↦₆₄ hiMe) ∗
        memRegion (fsp + 0x1e0#64) 0x40 ⊢
      memRegion fsp 0x220 := by
    have h16 :
        ((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
          ((fsp + 0x1d8#64) ↦₆₄ hiMe) ⊢ memRegion (fsp + 0x1d0#64) 16 := by
      rw [ProofLib.memRegion_split' (b := fsp + 0x1d0#64) (n := 8) (k := 8)
        (b' := fsp + 0x1d8#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
    rw [ProofLib.memRegion_split' (b := fsp) (n := 0x1d0) (k := 0x50)
          (b' := fsp + 0x1d0#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x1d0#64) (n := 16) (k := 0x40)
          (b' := fsp + 0x1e0#64) rfl (by bv_omega) (by decide)]
    exact Entails.trans (Entails.of_eq (by ac_rfl))
      (sepConj_mono_right (sepConj_mono_left h16))
  exact r3b_perm
    (r3b_perm_post
      (sepConj_mono (r3b_call7_to_memRegion56 g.call cw)
        (sepConj_mono h1d0_collapse
          (Entails.refl (memRegion g.res runResSize ∗
            storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
            CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ logOff img ∗
            addrNameHeap A meG ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
            (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
              ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
              ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
              ((fsp + 0x238#64) ↦₆₄ cw.w4)) ∗
            memRegion (fsp + 0x240#64) 0x20 ∗
            (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗
              ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
              ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
              ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
            memRegion (fsp + 0x280#64) (runLocalBytes - 0x280) ∗
            stackAt fsp (resStack - runFrame) ∗ A.pool))))
      (by dsimp only [fsp]; ac_rfl))
    (by dsimp only [fsp, peerG]; rw [hlen_cw3, hme_bytes]; ac_rfl)

/-! ## 5. Bad-Wire & Reject Hop (`run_hop_recvBad_ok`) -/

theorem run_hop_recvBad_ok_ext {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {g : RunCall} {peerV : AddrV}
    {me : MeAtDispatch} {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (_himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    (hres : runNeed B (slotsOf A img S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63)
    (he : AtRunEntry S img ext g s0)
    (hd : AtDispatch img ext g me s0 s)
    (hcall : g.c = .recv peerV)
    (hbad : g.i.stdin = [] ∨ ∃ t rest, g.i.stdin = t :: rest ∧ t ≠ 2#8 ∧ t ≠ 3#8)
    (hrej : RejectK img ext A g s0 resStack Q Qp) :
    ProofLib.SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (dispatchMem A img g me s0 resStack) Q Qp (runOom s0) := by
  cases me with
  | none => exact r3b_me_none hh hres hres64 he hd hcall hrej
  | some meV meG =>
    have hbnds := runNeed_bounds hres hres64
    have hext_le : extHookStack ≤ resStack - runFrame := by
      have := hbnds.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
    have hsub64 : resStack - runFrame ≤ 2 ^ 64 := hbnds.2.2.1
    have hans : g.a = some none := hd.recvBad_reject he hcall hbad
    refine r3b_recv_head_some hd hcall ?_
    intro s1 peerG cw4 hiMe hs1 hx19 hx20 hx21 hx23 hx24 _ _ hx28 htr1 hfs1 _ _ _ _
    let fsp := runFsp s0
    have htail_collapse :
        memRegion (fsp + 0x240#64) 0x20 ∗
          (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗
            ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
            ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
            ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
          memRegion (fsp + 0x280#64) (runLocalBytes - 0x280) ⊢
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) := by
      dsimp only [runLocalBytes]
      rw [ProofLib.memRegion_split' (b := fsp + 0x240#64) (n := 0x20) (k := 0x29f0 - 0x260)
            (b' := fsp + 0x260#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x260#64) (n := 32) (k := 0x29f0 - 0x280)
            (b' := fsp + 0x280#64) rfl (by bv_omega) (by decide)]
      exact Entails.trans (Entails.of_eq (by ac_rfl))
        (sepConj_mono_right (sepConj_mono_left (r3b_words4_entails_mem32 _ _ _ _ _)))
    apply r3b_sepWPp_weaken_pre
      (r3b_perm
        (r3b_perm_post
          (sepConj_mono htail_collapse
            (sepConj_mono
              (entails_anyHeap (coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
                CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ logOff img))
              (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
                addrNameHeap A meG ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
                memRegion fsp 0x220 ∗
                (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
                  ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                  ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
                  ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
                stackAt fsp (resStack - runFrame) ∗ A.pool))))
          (by dsimp only [fsp]))
        (by dsimp only [fsp]; ac_rfl))
    rcases hbad with hnil | ⟨t, rest, hcons, ht2, ht3⟩
    · have hinp0 : inputOf g.i g.c = [] := by simp [hcall, inputOf, CallV.tag, hnil]
      rw [hinp0] at hx24
      dsimp only [List.length] at hx24
      have hpc1 : s1.pc = runPc img ext 0x7c8 := hs1.pc
      have hrun1 : s1.status = .Running := hs1.run
      apply sepWPp_seq_inImage (mid := runPc img ext 0xfec) hs1.inv
      have hfn0 := run_fnOff
      code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_head img.base
        (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 1992 4
      clear hfn0
      dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc1 ⊢
      generalize hfn :
        (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
      examples_hide_fetches
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun1])
      intro hinv2
      have hs2 : InRun img ext s0 (r3b_stOf hinv2) 0xfec :=
        r3b_inRun_step hs1 (by simp only [arm64_norm]; rw [← hfn])
          (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv2 (by simp only [calleeSavedVRegs, arm64_norm])
      have htr2 : s0.trace <+: (r3b_stOf hinv2).trace :=
        by simpa only [arm64_norm, htr1] using hd.trace
      have hhist2 : RunHistOk g.i s0 (r3b_stOf hinv2) :=
        ⟨by simpa only [arm64_norm, hfs1] using hd.fs,
          by simpa only [arm64_norm, htr1] using hd.stdout⟩
      refine r3b_sepWPp_weaken_pre (Entails.of_eq (by ac_rfl))
        (r3b_reject_from_fec StoresGhost.opened meG peerG (BitVec.ofNat 64 peerG.name.bytes.length) cw4
          hh hext_le hsub64 hs2
          (by simp only [arm64_norm, hx19])
          (by simp only [arm64_norm, hx20])
          (by simp only [arm64_norm, hx21])
          (by simp only [arm64_norm, hx28])
          htr2 hhist2 hans hrej)
    · have hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) :=
        hcall ▸ he.parse
      have htail_lt : rest.length < 2 ^ 32 := by
        have ht0 := he.rel.2.1.2.2.1 peerV hparse
        simpa [hcons] using ht0
      have hinp_c : inputOf g.i g.c = t :: rest := by simp [hcall, inputOf, CallV.tag, hcons]
      have hlen_ne : BitVec.ofNat 64 (t :: rest).length ≠ 0#64 := by
        rw [List.length_cons]
        intro h0
        have hv := congrArg BitVec.toNat h0
        have hzero : (0#64).toNat = 0 := rfl
        rw [BitVec.toNat_ofNat, hzero] at hv
        have hmod : (rest.length + 1) % 2 ^ 64 = rest.length + 1 := Nat.mod_eq_of_lt (by omega)
        omega
      have hbeq_len : (BitVec.ofNat 64 (t :: rest).length == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hlen_ne
      have hne3 : (t.zeroExtend 32 == 3#32) = false :=
        beq_eq_false_iff_ne.mpr fun h0 => ht3 (by bv_omega)
      have hne2 : (t.zeroExtend 32 == 2#32) = false :=
        beq_eq_false_iff_ne.mpr fun h0 => ht2 (by bv_omega)
      have hne2b : (t.zeroExtend 32 != 2#32) = true :=
        bne_iff_ne.mpr fun h0 => ht2 (by bv_omega)
      rw [hinp_c] at hx24
      rw [hinp_c, pointsToBytes_cons]
      have hpc1 : s1.pc = runPc img ext 0x7c8 := hs1.pc
      have hrun1 : s1.status = .Running := hs1.run
      apply sepWPp_seq_inImage (mid := runPc img ext 0xfec) hs1.inv
      have hfn0 := run_fnOff
      code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_head img.base
        (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 1992 24
      clear hfn0
      dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc1 ⊢
      generalize hfn :
        (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
      examples_hide_fetches
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun1])
      intro hinv2
      have hs2 : InRun img ext s0 (r3b_stOf hinv2) 0xfec :=
        r3b_inRun_step hs1 (by simp only [arm64_norm]; rw [← hfn])
          (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv2 (by simp only [calleeSavedVRegs, arm64_norm])
      have htr2 : s0.trace <+: (r3b_stOf hinv2).trace := by simpa only [arm64_norm, htr1] using hd.trace
      have hhist2 : RunHistOk g.i s0 (r3b_stOf hinv2) :=
        ⟨by simpa only [arm64_norm, hfs1] using hd.fs,
          by simpa only [arm64_norm, htr1] using hd.stdout⟩
      refine r3b_sepWPp_weaken_pre ?_
        (r3b_reject_from_fec StoresGhost.opened meG peerG (BitVec.ofNat 64 peerG.name.bytes.length) cw4
          hh hext_le hsub64 hs2
          (by simp only [arm64_norm, hx19])
          (by simp only [arm64_norm, hx20])
          (by simp only [arm64_norm, hx21])
          (by simp only [arm64_norm, hx28])
          htr2 hhist2 hans hrej)
      rw [hinp_c, pointsToBytes_cons]
      exact Entails.of_eq (by ac_rfl)

/-! ## 6. PreKey Hop (`run_hop_recvP_ok`) -/

private theorem r3b_split_at (fsp : BitVec 64) (a m c : Nat)
    (hsum : m + (c - (a + m)) = c - a) (h64 : c ≤ 2 ^ 64) :
    memRegion (fsp + BitVec.ofNat 64 a) (c - a) =
      memRegion (fsp + BitVec.ofNat 64 a) m ∗
        memRegion (fsp + BitVec.ofNat 64 (a + m)) (c - (a + m)) := by
  have hs := ProofLib.memRegion_split (fsp + BitVec.ofNat 64 a) m (c - (a + m)) (by omega)
  have ha : fsp + BitVec.ofNat 64 a + BitVec.ofNat 64 m = fsp + BitVec.ofNat 64 (a + m) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  simpa only [hsum, ha] using hs

private structure r3b_W5 where
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  w4 : BitVec 64

private def r3b_slot5 (a : BitVec 64) (e : r3b_W5) : SepProp :=
  (a ↦₆₄ e.w0) ∗ ((a + 8#64) ↦₆₄ e.w1) ∗ ((a + 16#64) ↦₆₄ e.w2) ∗
    ((a + 24#64) ↦₆₄ e.w3) ∗ ((a + 32#64) ↦₆₄ e.w4)

private theorem r3b_mem40_to_slot5 (a : BitVec 64) :
    memRegion a 40 ⊢ ∃∗ e : r3b_W5, r3b_slot5 a e := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 32) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 24) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 16) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 8) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64), ProofLib.memRegion_eight (a + 24#64),
      ProofLib.memRegion_eight (a + 32#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w4
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w0
  exact Entails.sepExists_right ⟨w0, w1, w2, w3, w4⟩ (Entails.of_eq (by dsimp only [r3b_slot5]))

private theorem r3b_slot5_to_mem40 (a : BitVec 64) (e : r3b_W5) :
    r3b_slot5 a e ⊢ memRegion a 40 := by
  dsimp only [r3b_slot5]
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 32) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 24) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 16) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 8) (b' := a + 32#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))))

private structure r3b_W30 where
  b0 : r3b_W5
  b1 : r3b_W5
  b2 : r3b_W5
  b3 : r3b_W5
  b4 : r3b_W5
  b5 : r3b_W5

private def r3b_slot30 (a : BitVec 64) (w : r3b_W30) : SepProp :=
  r3b_slot5 a w.b0 ∗ r3b_slot5 (a + 40#64) w.b1 ∗ r3b_slot5 (a + 80#64) w.b2 ∗
    r3b_slot5 (a + 120#64) w.b3 ∗ r3b_slot5 (a + 160#64) w.b4 ∗ r3b_slot5 (a + 200#64) w.b5

private theorem r3b_mem240_to_slot30 (a : BitVec 64) :
    memRegion a 240 ⊢ ∃∗ w : r3b_W30, r3b_slot30 a w := by
  rw [ProofLib.memRegion_split' (b := a) (n := 40) (k := 200) (b' := a + 40#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 40#64) (n := 40) (k := 160) (b' := a + 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 80#64) (n := 40) (k := 120) (b' := a + 120#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 120#64) (n := 40) (k := 80) (b' := a + 160#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 160#64) (n := 40) (k := 40) (b' := a + 200#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans
    (sepConj_mono (r3b_mem40_to_slot5 a)
      (sepConj_mono (r3b_mem40_to_slot5 (a + 40#64))
        (sepConj_mono (r3b_mem40_to_slot5 (a + 80#64))
          (sepConj_mono (r3b_mem40_to_slot5 (a + 120#64))
            (sepConj_mono (r3b_mem40_to_slot5 (a + 160#64))
              (r3b_mem40_to_slot5 (a + 200#64))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro b5
  apply Entails.sepExists_elim; intro b4
  apply Entails.sepExists_elim; intro b3
  apply Entails.sepExists_elim; intro b2
  apply Entails.sepExists_elim; intro b1
  apply Entails.sepExists_elim; intro b0
  exact Entails.sepExists_right ⟨b0, b1, b2, b3, b4, b5⟩ (Entails.of_eq (by dsimp only [r3b_slot30]))

private theorem r3b_slot30_to_mem240 (a : BitVec 64) (w : r3b_W30) :
    r3b_slot30 a w ⊢ memRegion a 240 := by
  dsimp only [r3b_slot30]
  rw [ProofLib.memRegion_split' (b := a) (n := 40) (k := 200) (b' := a + 40#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 40#64) (n := 40) (k := 160) (b' := a + 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 80#64) (n := 40) (k := 120) (b' := a + 120#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 120#64) (n := 40) (k := 80) (b' := a + 160#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 160#64) (n := 40) (k := 40) (b' := a + 200#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (r3b_slot5_to_mem40 a w.b0)
    (sepConj_mono (r3b_slot5_to_mem40 (a + 40#64) w.b1)
      (sepConj_mono (r3b_slot5_to_mem40 (a + 80#64) w.b2)
        (sepConj_mono (r3b_slot5_to_mem40 (a + 120#64) w.b3)
          (sepConj_mono (r3b_slot5_to_mem40 (a + 160#64) w.b4)
            (r3b_slot5_to_mem40 (a + 200#64) w.b5)))))

private def r3b_Own1 (a : BitVec 64) (P : SepProp) : SepProp :=
  ∃∗ w : BitVec 64, (a ↦₆₄ w) ∗ ((a ↦₆₄ w) -∗ P)

private def r3b_Own5 (a : BitVec 64) (P : SepProp) : SepProp :=
  ∃∗ e : r3b_W5, r3b_slot5 a e ∗ (r3b_slot5 a e -∗ P)

private def r3b_Own30 (a : BitVec 64) (P : SepProp) : SepProp :=
  ∃∗ w : r3b_W30, r3b_slot30 a w ∗ (r3b_slot30 a w -∗ P)

private theorem r3b_own1_u64 (a v : BitVec 64) :
    (a ↦₆₄ v) ⊢ r3b_Own1 a (a ↦₆₄ v) :=
  Entails.sepExists_right v (r3b_ws_u64 a a v)

private theorem r3b_own1_mem8 (a : BitVec 64) :
    memRegion a 8 ⊢ r3b_Own1 a (memRegion a 8) :=
  r3b_ws_mem8 a a

private theorem r3b_own1_u8pad7 (a b1 : BitVec 64) (b0 : BitVec 8) (hb1 : a + 1#64 = b1) :
    ((a ↦₈ b0) ∗ memRegion b1 7) ⊢ r3b_Own1 a ((a ↦₈ b0) ∗ memRegion b1 7) := by
  subst hb1; exact r3b_ws_u8pad7 a a b0

private theorem r3b_own1_u32x2 (a b4 : BitVec 64) (c1 c2 : BitVec 32) (hb4 : a + 4#64 = b4) :
    ((a ↦₃₂ c1) ∗ (b4 ↦₃₂ c2)) ⊢ r3b_Own1 a ((a ↦₃₂ c1) ∗ (b4 ↦₃₂ c2)) := by
  subst hb4; exact Entails.sepExists_right (c2 ++ c1) (r3b_ws_u32x2 a a c1 c2)

private theorem r3b_own1_u32pad4 (a b4 : BitVec 64) (c1 : BitVec 32) (hb4 : a + 4#64 = b4) :
    ((a ↦₃₂ c1) ∗ memRegion b4 4) ⊢ r3b_Own1 a ((a ↦₃₂ c1) ∗ memRegion b4 4) := by
  subst hb4
  have hm4 : memRegion (a + 4#64) 4 ⊢ ∃∗ c2 : BitVec 32, (a + 4#64) ↦₃₂ c2 := by
    rw [ProofLib.memRegion_split' (b := a + 4#64) (n := 1) (k := 3) (b' := a + 5#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 5#64) (n := 1) (k := 2) (b' := a + 6#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 6#64) (n := 1) (k := 1) (b' := a + 7#64) rfl (by bv_omega) (by decide)]
    simp only [Path.Helpers.memRegion_1_eq_pointsTo8, sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro d3
    apply Entails.sepExists_elim; intro d2
    apply Entails.sepExists_elim; intro d1
    apply Entails.sepExists_elim; intro d0
    refine Entails.sepExists_right (d3 ++ d2 ++ d1 ++ d0) ?_
    rw [← pointsToBytes4_eq_pointsTo32 (a + 4#64) d0 d1 d2 d3]
    simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
    have h1 : a + 4#64 + 1#64 = a + 5#64 := by bv_omega
    have h2 : a + 5#64 + 1#64 = a + 6#64 := by bv_omega
    have h3 : a + 6#64 + 1#64 = a + 7#64 := by bv_omega
    rw [h1, h2, h3]
    exact Entails.of_eq (by ac_rfl)
  refine Entails.trans (sepConj_mono_right hm4) ?_
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro c2
  refine Entails.sepExists_right (c2 ++ c1) ?_
  exact Entails.trans (r3b_ws_u32x2 a a c1 c2)
    (sepConj_mono_right (r3b_wand_post (sepConj_mono_right (pointsTo32_entails_memRegion _ _))))

private theorem r3b_own1_bytes8 (a : BitVec 64) (bs : List (BitVec 8)) (hlen : bs.length = 8) :
    (a ↦ₛ bs) ⊢ r3b_Own1 a (a ↦ₛ bs) := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals simp only [List.length_cons, List.length_nil] at hlen; try omega
  rw [pointsToBytes8_eq_pointsTo64 a b0 b1 b2 b3 b4 b5 b6 b7]
  exact r3b_own1_u64 a _

private theorem r3b_bytes32_split4 (a a1 a2 a3 : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length = 32) (h1 : a + 8#64 = a1) (h2 : a + 16#64 = a2) (h3 : a + 24#64 = a3) :
    (a ↦ₛ bs) =
      (a ↦ₛ bs.take 8) ∗ (a1 ↦ₛ (bs.drop 8).take 8) ∗
        (a2 ↦ₛ ((bs.drop 8).drop 8).take 8) ∗ (a3 ↦ₛ ((bs.drop 8).drop 8).drop 8) := by
  subst h1; subst h2; subst h3
  have hsplit : bs = bs.take 8 ++ (bs.drop 8).take 8 ++ ((bs.drop 8).drop 8).take 8 ++
      (((bs.drop 8).drop 8).drop 8) := by
    simp only [List.append_assoc, List.take_append_drop]
  have l0 : (bs.take 8).length = 8 := by simp [hlen]
  have l1 : ((bs.drop 8).take 8).length = 8 := by simp [hlen]
  have l2 : (((bs.drop 8).drop 8).take 8).length = 8 := by simp [hlen]
  conv_lhs => rw [hsplit]
  simp only [pointsToBytes_append, List.length_append, l0, l1, l2]
  have ha16 : a + BitVec.ofNat 64 (8 + 8) = a + 16#64 := rfl
  have ha24 : a + BitVec.ofNat 64 (8 + 8 + 8) = a + 24#64 := rfl
  rw [ha16, ha24]
  ac_rfl

private theorem r3b_own5_mk {a a1 a2 a3 a4 : BitVec 64} {P0 P1 P2 P3 P4 : SepProp}
    (e1 : a + 8#64 = a1) (e2 : a + 16#64 = a2) (e3 : a + 24#64 = a3) (e4 : a + 32#64 = a4)
    (h0 : P0 ⊢ r3b_Own1 a P0) (h1 : P1 ⊢ r3b_Own1 a1 P1) (h2 : P2 ⊢ r3b_Own1 a2 P2)
    (h3 : P3 ⊢ r3b_Own1 a3 P3) (h4 : P4 ⊢ r3b_Own1 a4 P4) :
    (P0 ∗ P1 ∗ P2 ∗ P3 ∗ P4) ⊢ r3b_Own5 a (P0 ∗ P1 ∗ P2 ∗ P3 ∗ P4) := by
  subst e1; subst e2; subst e3; subst e4
  refine Entails.trans
    (sepConj_mono h0 (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 h4)))) ?_
  dsimp only [r3b_Own1, r3b_Own5]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w4
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w0
  refine Entails.sepExists_right ⟨w0, w1, w2, w3, w4⟩ ?_
  dsimp only [r3b_slot5]
  let W : SepProp :=
    ((a ↦₆₄ w0) -∗ P0) ∗ (((a + 8#64) ↦₆₄ w1) -∗ P1) ∗ (((a + 16#64) ↦₆₄ w2) -∗ P2) ∗
      (((a + 24#64) ↦₆₄ w3) -∗ P3) ∗ (((a + 32#64) ↦₆₄ w4) -∗ P4)
  refine Entails.trans
    (Entails.of_eq (show
      (((a ↦₆₄ w0) ∗ ((a ↦₆₄ w0) -∗ P0)) ∗
        (((a + 8#64) ↦₆₄ w1) ∗ (((a + 8#64) ↦₆₄ w1) -∗ P1)) ∗
        (((a + 16#64) ↦₆₄ w2) ∗ (((a + 16#64) ↦₆₄ w2) -∗ P2)) ∗
        (((a + 24#64) ↦₆₄ w3) ∗ (((a + 24#64) ↦₆₄ w3) -∗ P3)) ∗
        (((a + 32#64) ↦₆₄ w4) ∗ (((a + 32#64) ↦₆₄ w4) -∗ P4))) =
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
        ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4)) ∗ W by dsimp only [W]; ac_rfl))
    (sepConj_mono_right (Entails.wand_intro ?_))
  refine Entails.trans
    (Entails.of_eq (show
      W ∗ ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
        ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4)) =
      ((a ↦₆₄ w0) ∗ ((a ↦₆₄ w0) -∗ P0)) ∗
        (((a + 8#64) ↦₆₄ w1) ∗ (((a + 8#64) ↦₆₄ w1) -∗ P1)) ∗
        (((a + 16#64) ↦₆₄ w2) ∗ (((a + 16#64) ↦₆₄ w2) -∗ P2)) ∗
        (((a + 24#64) ↦₆₄ w3) ∗ (((a + 24#64) ↦₆₄ w3) -∗ P3)) ∗
        (((a + 32#64) ↦₆₄ w4) ∗ (((a + 32#64) ↦₆₄ w4) -∗ P4)) by dsimp only [W]; ac_rfl))
    (sepConj_mono (Entails.wand_elim _ _)
      (sepConj_mono (Entails.wand_elim _ _)
        (sepConj_mono (Entails.wand_elim _ _)
          (sepConj_mono (Entails.wand_elim _ _) (Entails.wand_elim _ _)))))

private theorem r3b_own30_mk {a a1 a2 a3 a4 a5 : BitVec 64} {B0 B1 B2 B3 B4 B5 H : SepProp}
    (e1 : a + 40#64 = a1) (e2 : a + 80#64 = a2) (e3 : a + 120#64 = a3)
    (e4 : a + 160#64 = a4) (e5 : a + 200#64 = a5)
    (h0 : B0 ⊢ r3b_Own5 a B0) (h1 : B1 ⊢ r3b_Own5 a1 B1) (h2 : B2 ⊢ r3b_Own5 a2 B2)
    (h3 : B3 ⊢ r3b_Own5 a3 B3) (h4 : B4 ⊢ r3b_Own5 a4 B4) (h5 : B5 ⊢ r3b_Own5 a5 B5) :
    (B0 ∗ B1 ∗ B2 ∗ B3 ∗ B4 ∗ B5 ∗ H) ⊢ r3b_Own30 a (B0 ∗ B1 ∗ B2 ∗ B3 ∗ B4 ∗ B5 ∗ H) := by
  subst e1; subst e2; subst e3; subst e4; subst e5
  refine Entails.trans
    (sepConj_mono h0 (sepConj_mono h1 (sepConj_mono h2
      (sepConj_mono h3 (sepConj_mono h4 (sepConj_mono h5 (Entails.refl H))))))) ?_
  dsimp only [r3b_Own5, r3b_Own30]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro b5
  apply Entails.sepExists_elim; intro b4
  apply Entails.sepExists_elim; intro b3
  apply Entails.sepExists_elim; intro b2
  apply Entails.sepExists_elim; intro b1
  apply Entails.sepExists_elim; intro b0
  refine Entails.sepExists_right ⟨b0, b1, b2, b3, b4, b5⟩ ?_
  dsimp only [r3b_slot30]
  let W : SepProp :=
    (r3b_slot5 a b0 -∗ B0) ∗ (r3b_slot5 (a + 40#64) b1 -∗ B1) ∗
      (r3b_slot5 (a + 80#64) b2 -∗ B2) ∗ (r3b_slot5 (a + 120#64) b3 -∗ B3) ∗
      (r3b_slot5 (a + 160#64) b4 -∗ B4) ∗ (r3b_slot5 (a + 200#64) b5 -∗ B5) ∗ H
  refine Entails.trans
    (Entails.of_eq (show
      ((r3b_slot5 a b0 ∗ (r3b_slot5 a b0 -∗ B0)) ∗
        (r3b_slot5 (a + 40#64) b1 ∗ (r3b_slot5 (a + 40#64) b1 -∗ B1)) ∗
        (r3b_slot5 (a + 80#64) b2 ∗ (r3b_slot5 (a + 80#64) b2 -∗ B2)) ∗
        (r3b_slot5 (a + 120#64) b3 ∗ (r3b_slot5 (a + 120#64) b3 -∗ B3)) ∗
        (r3b_slot5 (a + 160#64) b4 ∗ (r3b_slot5 (a + 160#64) b4 -∗ B4)) ∗
        (r3b_slot5 (a + 200#64) b5 ∗ (r3b_slot5 (a + 200#64) b5 -∗ B5)) ∗ H) =
      (r3b_slot5 a b0 ∗ r3b_slot5 (a + 40#64) b1 ∗ r3b_slot5 (a + 80#64) b2 ∗
        r3b_slot5 (a + 120#64) b3 ∗ r3b_slot5 (a + 160#64) b4 ∗ r3b_slot5 (a + 200#64) b5) ∗ W
      by dsimp only [W]; ac_rfl))
    (sepConj_mono_right (Entails.wand_intro ?_))
  refine Entails.trans
    (Entails.of_eq (show
      W ∗ (r3b_slot5 a b0 ∗ r3b_slot5 (a + 40#64) b1 ∗ r3b_slot5 (a + 80#64) b2 ∗
        r3b_slot5 (a + 120#64) b3 ∗ r3b_slot5 (a + 160#64) b4 ∗ r3b_slot5 (a + 200#64) b5) =
      (r3b_slot5 a b0 ∗ (r3b_slot5 a b0 -∗ B0)) ∗
        (r3b_slot5 (a + 40#64) b1 ∗ (r3b_slot5 (a + 40#64) b1 -∗ B1)) ∗
        (r3b_slot5 (a + 80#64) b2 ∗ (r3b_slot5 (a + 80#64) b2 -∗ B2)) ∗
        (r3b_slot5 (a + 120#64) b3 ∗ (r3b_slot5 (a + 120#64) b3 -∗ B3)) ∗
        (r3b_slot5 (a + 160#64) b4 ∗ (r3b_slot5 (a + 160#64) b4 -∗ B4)) ∗
        (r3b_slot5 (a + 200#64) b5 ∗ (r3b_slot5 (a + 200#64) b5 -∗ B5)) ∗ H
      by dsimp only [W]; ac_rfl))
    (sepConj_mono (Entails.wand_elim _ _)
      (sepConj_mono (Entails.wand_elim _ _)
        (sepConj_mono (Entails.wand_elim _ _)
          (sepConj_mono (Entails.wand_elim _ _)
            (sepConj_mono (Entails.wand_elim _ _)
              (sepConj_mono (Entails.wand_elim _ _) (Entails.refl H)))))))

private theorem r3b_own1_optU32 (a : BitVec 64) (o : Option (BitVec 32)) :
    optU32At a o ⊢ r3b_Own1 a (optU32At a o) := by
  cases o with
  | none => exact r3b_own1_u32pad4 a (a + 4#64) 0#32 rfl
  | some v => exact r3b_own1_u32x2 a (a + 4#64) 1#32 v rfl

/-- Decompose `preKeyMsgAt A pmG a pm` (`248` bytes) into word 0 `pmG.msg.pqCap` (`< 2 ^ 63`) +
30 words at `a + 8#64` + a magic wand restoring `preKeyMsgAt A pmG a pm` once the shuffle restores
all 31 words at `[a .. a + 248)`. -/
private theorem r3b_pkm_to_words (A : RustAlloc) (pmG : PreKeyMsgGhost) (a : BitVec 64)
    (pm : PreKeySignalMessage) :
    preKeyMsgAt A pmG a pm ⊢
      ∃∗ w : r3b_W30,
        ⌜pmG.msg.pqCap.toNat < 2 ^ 63⌝ ∗
        (a ↦₆₄ pmG.msg.pqCap) ∗
        r3b_slot30 (a + 8#64) w ∗
        (((a ↦₆₄ pmG.msg.pqCap) ∗ r3b_slot30 (a + 8#64) w) -∗ preKeyMsgAt A pmG a pm) := by
  have hsrk_len : pm.message.senderRatchetKey.bytes.toList.length = 32 :=
    pm.message.senderRatchetKey.bytes.toList_length
  have hbk_len : pm.baseKey.bytes.toList.length = 32 := pm.baseKey.bytes.toList_length
  have hik_len : pm.identityKey.publicKey.bytes.toList.length = 32 :=
    pm.identityKey.publicKey.bytes.toList_length
  have hsrk := r3b_bytes32_split4 (a + 56#64) (a + 64#64) (a + 72#64) (a + 80#64)
    pm.message.senderRatchetKey.bytes.toList hsrk_len (by bv_omega) (by bv_omega) (by bv_omega)
  have hbk := r3b_bytes32_split4 (a + 168#64) (a + 176#64) (a + 184#64) (a + 192#64)
    pm.baseKey.bytes.toList hbk_len (by bv_omega) (by bv_omega) (by bv_omega)
  have hik := r3b_bytes32_split4 (a + 200#64) (a + 208#64) (a + 216#64) (a + 224#64)
    pm.identityKey.publicKey.bytes.toList hik_len (by bv_omega) (by bv_omega) (by bv_omega)
  have haddr : ∃ (A0 A1 AH : SepProp),
      optBoxU8At A (a + 88#64) pmG.msg.addrPtr pm.message.addresses = A0 ∗ A1 ∗ AH ∧
        (A0 ⊢ r3b_Own1 (a + 88#64) A0) ∧ (A1 ⊢ r3b_Own1 (a + 96#64) A1) := by
    cases pm.message.addresses with
    | none =>
      refine ⟨(a + 88#64) ↦₆₄ 0#64, memRegion (a + 96#64) 8, emp, ?_,
        r3b_own1_u64 _ _, r3b_own1_mem8 _⟩
      dsimp only [optBoxU8At]
      have ha96 : a + 88#64 + 8#64 = a + 96#64 := by bv_omega
      rw [ha96]; ac_rfl
    | some ad =>
      refine ⟨(a + 88#64) ↦₆₄ pmG.msg.addrPtr,
        (a + 96#64) ↦₆₄ BitVec.ofNat 64 ad.length,
        ⌜pmG.msg.addrPtr ≠ 0 ∧ ad.length < 2 ^ 63⌝ ∗
          (if ad = [] then emp else A.live pmG.msg.addrPtr ad.length 1 ∗ (pmG.msg.addrPtr ↦ₛ ad)),
        ?_, r3b_own1_u64 _ _, r3b_own1_u64 _ _⟩
      dsimp only [optBoxU8At, boxU8At]
      have ha96 : a + 88#64 + 8#64 = a + 96#64 := by bv_omega
      rw [ha96]
  have hkyb : ∃ (K0 K1 K2 KH : SepProp),
      optKyberAt A (a + 144#64) pmG.kyberPtr pm.kyberPayload = K0 ∗ K1 ∗ K2 ∗ KH ∧
        (K0 ⊢ r3b_Own1 (a + 144#64) K0) ∧ (K1 ⊢ r3b_Own1 (a + 152#64) K1) ∧
        (K2 ⊢ r3b_Own1 (a + 160#64) K2) := by
    cases pm.kyberPayload with
    | none =>
      refine ⟨(a + 144#64) ↦₆₄ 0#64, memRegion (a + 152#64) 8, memRegion (a + 160#64) 8, emp,
        ?_, r3b_own1_u64 _ _, r3b_own1_mem8 _, r3b_own1_mem8 _⟩
      dsimp only [optKyberAt]
      have ha152 : a + 144#64 + 8#64 = a + 152#64 := by bv_omega
      rw [ha152, ProofLib.memRegion_split' (b := a + 152#64) (n := 8) (k := 8)
        (b' := a + 160#64) rfl (by bv_omega) (by decide)]
      ac_rfl
    | some k =>
      refine ⟨(a + 144#64) ↦₆₄ pmG.kyberPtr,
        (a + 152#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length,
        ((a + 160#64) ↦₃₂ k.preKeyId) ∗ memRegion (a + 164#64) 4,
        ⌜pmG.kyberPtr ≠ 0 ∧ k.ciphertext.length < 2 ^ 63⌝ ∗
          (if k.ciphertext = [] then emp
           else A.live pmG.kyberPtr k.ciphertext.length 1 ∗ (pmG.kyberPtr ↦ₛ k.ciphertext)),
        ?_, r3b_own1_u64 _ _, r3b_own1_u64 _ _, r3b_own1_u32pad4 _ _ _ (by bv_omega)⟩
      dsimp only [optKyberAt, boxU8At]
      have ha152 : a + 144#64 + 8#64 = a + 152#64 := by bv_omega
      have ha160 : a + 144#64 + 0x10#64 = a + 160#64 := by bv_omega
      have ha164 : a + 144#64 + 0x14#64 = a + 164#64 := by bv_omega
      rw [ha152, ha160, ha164]; ac_rfl
  obtain ⟨A0, A1, AH, haddr_eq, hA0, hA1⟩ := haddr
  obtain ⟨K0, K1, K2, KH, hkyb_eq, hK0, hK1, hK2⟩ := hkyb
  let B0 : SepProp :=
    ((a + 8#64) ↦₆₄ pmG.msg.pqPtr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pm.message.pqRatchet.length) ∗
      ((a + 24#64) ↦₆₄ pmG.msg.ctPtr) ∗
      ((a + 32#64) ↦₆₄ BitVec.ofNat 64 pm.message.ciphertext.length) ∗
      ((a + 40#64) ↦₆₄ pmG.msg.serPtr)
  let B1 : SepProp :=
    ((a + 48#64) ↦₆₄ BitVec.ofNat 64 pm.message.serialized.length) ∗
      ((a + 56#64) ↦ₛ pm.message.senderRatchetKey.bytes.toList.take 8) ∗
      ((a + 64#64) ↦ₛ (pm.message.senderRatchetKey.bytes.toList.drop 8).take 8) ∗
      ((a + 72#64) ↦ₛ ((pm.message.senderRatchetKey.bytes.toList.drop 8).drop 8).take 8) ∗
      ((a + 80#64) ↦ₛ ((pm.message.senderRatchetKey.bytes.toList.drop 8).drop 8).drop 8)
  let B2 : SepProp :=
    A0 ∗ A1 ∗
      (((a + 104#64) ↦₃₂ pm.message.counter) ∗ ((a + 108#64) ↦₃₂ pm.message.previousCounter)) ∗
      (((a + 112#64) ↦₈ pm.message.messageVersion) ∗ memRegion (a + 113#64) 7) ∗
      optU32At (a + 120#64) pm.preKeyId
  let B3 : SepProp :=
    ((a + 128#64) ↦₆₄ pmG.serPtr) ∗
      ((a + 136#64) ↦₆₄ BitVec.ofNat 64 pm.serialized.length) ∗
      K0 ∗ K1 ∗ K2
  let B4 : SepProp :=
    ((a + 168#64) ↦ₛ pm.baseKey.bytes.toList.take 8) ∗
      ((a + 176#64) ↦ₛ (pm.baseKey.bytes.toList.drop 8).take 8) ∗
      ((a + 184#64) ↦ₛ ((pm.baseKey.bytes.toList.drop 8).drop 8).take 8) ∗
      ((a + 192#64) ↦ₛ ((pm.baseKey.bytes.toList.drop 8).drop 8).drop 8) ∗
      ((a + 200#64) ↦ₛ pm.identityKey.publicKey.bytes.toList.take 8)
  let B5 : SepProp :=
    ((a + 208#64) ↦ₛ (pm.identityKey.publicKey.bytes.toList.drop 8).take 8) ∗
      ((a + 216#64) ↦ₛ ((pm.identityKey.publicKey.bytes.toList.drop 8).drop 8).take 8) ∗
      ((a + 224#64) ↦ₛ ((pm.identityKey.publicKey.bytes.toList.drop 8).drop 8).drop 8) ∗
      (((a + 232#64) ↦₃₂ pm.registrationId) ∗ ((a + 236#64) ↦₃₂ pm.signedPreKeyId)) ∗
      (((a + 240#64) ↦₈ pm.messageVersion) ∗ memRegion (a + 241#64) 7)
  let H : SepProp :=
    ⌜macLength + 1 ≤ pm.message.serialized.length ∧ pm.message.serialized.length < 2 ^ 40 ∧
      pm.message.ciphertext.length < 2 ^ 40 ∧ pm.message.pqRatchet.length < 2 ^ 40 ∧
      (∀ ad, pm.message.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
    r3b_vecHeap A pmG.msg.pqCap pmG.msg.pqPtr pm.message.pqRatchet ∗
    ⌜pmG.msg.ctPtr ≠ 0 ∧ pm.message.ciphertext.length < 2 ^ 63⌝ ∗
    (if pm.message.ciphertext = [] then emp
     else A.live pmG.msg.ctPtr pm.message.ciphertext.length 1 ∗ (pmG.msg.ctPtr ↦ₛ pm.message.ciphertext)) ∗
    ⌜pmG.msg.serPtr ≠ 0 ∧ pm.message.serialized.length < 2 ^ 63⌝ ∗
    (if pm.message.serialized = [] then emp
     else A.live pmG.msg.serPtr pm.message.serialized.length 1 ∗ (pmG.msg.serPtr ↦ₛ pm.message.serialized)) ∗
    ⌜pmG.serPtr ≠ 0 ∧ pm.serialized.length < 2 ^ 63⌝ ∗
    (if pm.serialized = [] then emp
     else A.live pmG.serPtr pm.serialized.length 1 ∗ (pmG.serPtr ↦ₛ pm.serialized)) ∗
    AH ∗ KH
  have hpkm_eq : preKeyMsgAt A pmG a pm =
      (a ↦₆₄ pmG.msg.pqCap) ∗ (B0 ∗ B1 ∗ B2 ∗ B3 ∗ B4 ∗ B5 ∗ H) := by
    unfold preKeyMsgAt signalMessageAt
    rw [r3b_vecU8At_eq A a pmG.msg.pqCap pmG.msg.pqPtr pm.message.pqRatchet,
        haddr_eq, hkyb_eq, hsrk, hbk, hik]
    dsimp only [boxU8At, B0, B1, B2, B3, B4, B5, H]
    have c1 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
    have c2 : a + 40#64 + 8#64 = a + 48#64 := by bv_omega
    have c3 : a + 128#64 + 8#64 = a + 136#64 := by bv_omega
    rw [c1, c2, c3]
    ac_rfl
  have hcap_extract : preKeyMsgAt A pmG a pm ⊢
      ⌜pmG.msg.pqCap.toNat < 2 ^ 63⌝ ∗ preKeyMsgAt A pmG a pm := by
    rw [hpkm_eq]
    have hpull : ∀ (X : SepProp),
        (a ↦₆₄ pmG.msg.pqCap) ∗ (B0 ∗ B1 ∗ B2 ∗ B3 ∗ B4 ∗ B5 ∗ H) =
        r3b_vecHeap A pmG.msg.pqCap pmG.msg.pqPtr pm.message.pqRatchet ∗
          ((a ↦₆₄ pmG.msg.pqCap) ∗ B0 ∗ B1 ∗ B2 ∗ B3 ∗ B4 ∗ B5 ∗
            (⌜macLength + 1 ≤ pm.message.serialized.length ∧ pm.message.serialized.length < 2 ^ 40 ∧
              pm.message.ciphertext.length < 2 ^ 40 ∧ pm.message.pqRatchet.length < 2 ^ 40 ∧
              (∀ ad, pm.message.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
            ⌜pmG.msg.ctPtr ≠ 0 ∧ pm.message.ciphertext.length < 2 ^ 63⌝ ∗
            (if pm.message.ciphertext = [] then emp
             else A.live pmG.msg.ctPtr pm.message.ciphertext.length 1 ∗
               (pmG.msg.ctPtr ↦ₛ pm.message.ciphertext)) ∗
            ⌜pmG.msg.serPtr ≠ 0 ∧ pm.message.serialized.length < 2 ^ 63⌝ ∗
            (if pm.message.serialized = [] then emp
             else A.live pmG.msg.serPtr pm.message.serialized.length 1 ∗
               (pmG.msg.serPtr ↦ₛ pm.message.serialized)) ∗
            ⌜pmG.serPtr ≠ 0 ∧ pm.serialized.length < 2 ^ 63⌝ ∗
            (if pm.serialized = [] then emp
             else A.live pmG.serPtr pm.serialized.length 1 ∗ (pmG.serPtr ↦ₛ pm.serialized)) ∗
            AH ∗ KH)) := fun _ => by dsimp only [H]; ac_rfl
    rw [hpull emp]
    refine Entails.trans (sepConj_mono_left (r3b_vecHeap_cap_lt A _ _ _)) ?_
    exact Entails.of_eq (by ac_rfl)
  have hB0 : B0 ⊢ r3b_Own5 (a + 8#64) B0 :=
    r3b_own5_mk (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
      (r3b_own1_u64 _ _) (r3b_own1_u64 _ _) (r3b_own1_u64 _ _)
      (r3b_own1_u64 _ _) (r3b_own1_u64 _ _)
  have hB1 : B1 ⊢ r3b_Own5 (a + 48#64) B1 :=
    r3b_own5_mk (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
      (r3b_own1_u64 _ _)
      (r3b_own1_bytes8 _ _ (by simp [hsrk_len]))
      (r3b_own1_bytes8 _ _ (by simp [hsrk_len]))
      (r3b_own1_bytes8 _ _ (by simp [hsrk_len]))
      (r3b_own1_bytes8 _ _ (by simp [hsrk_len]))
  have hB2 : B2 ⊢ r3b_Own5 (a + 88#64) B2 :=
    r3b_own5_mk (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
      hA0 hA1
      (r3b_own1_u32x2 _ _ _ _ (by bv_omega))
      (r3b_own1_u8pad7 _ _ _ (by bv_omega))
      (r3b_own1_optU32 _ _)
  have hB3 : B3 ⊢ r3b_Own5 (a + 128#64) B3 :=
    r3b_own5_mk (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
      (r3b_own1_u64 _ _) (r3b_own1_u64 _ _) hK0 hK1 hK2
  have hB4 : B4 ⊢ r3b_Own5 (a + 168#64) B4 :=
    r3b_own5_mk (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
      (r3b_own1_bytes8 _ _ (by simp [hbk_len]))
      (r3b_own1_bytes8 _ _ (by simp [hbk_len]))
      (r3b_own1_bytes8 _ _ (by simp [hbk_len]))
      (r3b_own1_bytes8 _ _ (by simp [hbk_len]))
      (r3b_own1_bytes8 _ _ (by simp [hik_len]))
  have hB5 : B5 ⊢ r3b_Own5 (a + 208#64) B5 :=
    r3b_own5_mk (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
      (r3b_own1_bytes8 _ _ (by simp [hik_len]))
      (r3b_own1_bytes8 _ _ (by simp [hik_len]))
      (r3b_own1_bytes8 _ _ (by simp [hik_len]))
      (r3b_own1_u32x2 _ _ _ _ (by bv_omega))
      (r3b_own1_u8pad7 _ _ _ (by bv_omega))
  have h30 : (B0 ∗ B1 ∗ B2 ∗ B3 ∗ B4 ∗ B5 ∗ H) ⊢
      r3b_Own30 (a + 8#64) (B0 ∗ B1 ∗ B2 ∗ B3 ∗ B4 ∗ B5 ∗ H) :=
    r3b_own30_mk (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
      hB0 hB1 hB2 hB3 hB4 hB5
  refine Entails.trans hcap_extract ?_
  apply Entails.pure_left; intro hcap
  rw [hpkm_eq]
  refine Entails.trans (sepConj_mono_right h30) ?_
  dsimp only [r3b_Own30]
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w
  refine Entails.sepExists_right w (Entails.pure_right hcap ?_)
  refine sepConj_mono_right (sepConj_mono_right (Entails.wand_intro ?_))
  exact Entails.trans
    (Entails.of_eq (show
      ((r3b_slot30 (a + 8#64) w -∗ (B0 ∗ B1 ∗ B2 ∗ B3 ∗ B4 ∗ B5 ∗ H)) ∗
        ((a ↦₆₄ pmG.msg.pqCap) ∗ r3b_slot30 (a + 8#64) w)) =
      (a ↦₆₄ pmG.msg.pqCap) ∗
        (r3b_slot30 (a + 8#64) w ∗ (r3b_slot30 (a + 8#64) w -∗ (B0 ∗ B1 ∗ B2 ∗ B3 ∗ B4 ∗ B5 ∗ H)))
      by ac_rfl))
    (sepConj_mono_right (Entails.wand_elim _ _))

private theorem r3b_addr_pack (A : RustAlloc) (g : AddrGhost)
    (a a1 a2 a3 : BitVec 64) (hi : BitVec 64)
    (e1 : a + 8#64 = a1) (e2 : a + 16#64 = a2) (e3 : a + 24#64 = a3)
    (hhi : hi.setWidth 8 = g.device) :
    ((a ↦₆₄ g.name.cap) ∗ (a1 ↦₆₄ g.name.ptr) ∗
      (a2 ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗ (a3 ↦₆₄ hi) ∗
      addrNameHeap A g) ⊢
    protocolAddressAt A g a := by
  subst e1; subst e2; subst e3
  rw [protocolAddressAt_eq_parts A g a]
  have hup := r3b_words_to_addrUpperAt (a + 16#64) g hi hhi
  have ha24 : a + 16#64 + 8#64 = a + 24#64 := by bv_omega
  rw [ha24] at hup
  exact r3b_perm
    (r3b_perm_post
      (sepConj_mono hup
        (Entails.refl ((a ↦₆₄ g.name.cap) ∗ ((a + 8#64) ↦₆₄ g.name.ptr) ∗ addrNameHeap A g)))
      (by ac_rfl))
    (by ac_rfl)

private theorem r3b_addr_unpack (A : RustAlloc) (g : AddrGhost)
    (a a1 a2 a3 : BitVec 64)
    (e1 : a + 8#64 = a1) (e2 : a + 16#64 = a2) (e3 : a + 24#64 = a3) :
    protocolAddressAt A g a ⊢
      ∃∗ hi : BitVec 64,
        ⌜hi.setWidth 8 = g.device⌝ ∗
        (a ↦₆₄ g.name.cap) ∗ (a1 ↦₆₄ g.name.ptr) ∗
        (a2 ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗ (a3 ↦₆₄ hi) ∗
        addrNameHeap A g := by
  subst e1; subst e2; subst e3
  rw [protocolAddressAt_eq_parts A g a]
  have hup := r3b_addrUpperAt_words (a + 16#64) g
  have ha24 : a + 16#64 + 8#64 = a + 24#64 := by bv_omega
  rw [ha24] at hup
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hup))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro hi
  simp only [sepConj_assoc]
  apply r3b_pure2; intro hhi
  exact Entails.sepExists_right hi (Entails.pure_right hhi (Entails.of_eq (by ac_rfl)))

private def r3b_shufMid (w m : r3b_W30) : r3b_W30 :=
  { b0 := ⟨w.b3.w0, w.b3.w1, w.b3.w2, w.b3.w3, w.b3.w4⟩
    b1 := ⟨w.b4.w0, w.b4.w1, w.b4.w2, w.b4.w3, w.b4.w4⟩
    b2 := ⟨w.b5.w0, w.b5.w1, w.b5.w2, w.b5.w3, w.b5.w4⟩
    b3 := ⟨m.b3.w0, w.b1.w2, w.b1.w3, w.b1.w4, w.b2.w0⟩
    b4 := ⟨w.b2.w1, w.b2.w2, w.b2.w3, w.b2.w4, w.b0.w1⟩
    b5 := ⟨w.b0.w2, w.b0.w3, w.b0.w4, w.b1.w0, w.b1.w1⟩ }

set_option maxHeartbeats 600000 in
/-- `PreKeySignalMessage::try_from` `Err` path (`R+0x994 → R+0xeb8 → R+0xfe0 → cliDropSpeName → R+0xfec`). -/
private theorem r3b_recvP_parse_err {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {g : RunCall}
    (meG peerG : AddrGhost) (cw4 hiMe : BitVec 64)
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hstk32 : 32 + extHookStack ≤ resStack - runFrame)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRun img ext s0 s 0x994)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (hrej : RejectK img ext A g s0 resStack Q Qp) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A meG ∗ addrNameHeap A peerG ∗
        runSaved s0 ∗
        memRegion (runFsp s0) 0x220 ∗
        (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((runFsp s0 + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
          ((runFsp s0 + 0x238#64) ↦₆₄ cw4)) ∗
        memRegion (runFsp s0 + 0x240#64) 0x20 ∗
        (((runFsp s0 + 0x260#64) ↦₆₄ meG.name.cap) ∗
          ((runFsp s0 + 0x268#64) ↦₆₄ meG.name.ptr) ∗
          ((runFsp s0 + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
          ((runFsp s0 + 0x278#64) ↦₆₄ hiMe)) ∗
        memRegion (runFsp s0 + 0x280#64) (0x4d0 - 0x280) ∗
        pksmResAt A (runFsp s0 + 0x4d0#64) none ∗
        memRegion (runFsp s0 + 0x5c8#64) (runLocalBytes - 0x5c8) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      Q Qp (runOom s0) := by
  have hpc : s.pc = runPc img ext 0x994 := hs.pc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = runFsp s0 := hs.sp
  have hsp_al : s.spAligned = true := hs.spAligned_cur
  generalize hfsp : runFsp s0 = fsp at hsp hx26 ⊢
  have h280 : memRegion (fsp + 0x280#64) (0x4d0 - 0x280) =
      memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2a0#64) 40 ∗
        memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) := by
    rw [r3b_split_at fsp 0x280 0x20 0x4d0 (by omega) (by omega),
        r3b_split_at fsp 0x2a0 40 0x4d0 (by omega) (by omega)]
  rw [h280]
  have hpkm_err :
      pksmResAt A (fsp + 0x4d0#64) none ∗ memRegion (fsp + 0x2a0#64) 40 ∗ anyHeap ⊢
      ∃∗ k : RunDrop.SpeOwned, ∃∗ sw : r3b_W6, ∃∗ t : r3b_W5,
        ((fsp + 0x4d0#64) ↦₆₄ errTag) ∗
        r3b_slot6 (fsp + 0x4d8#64) sw ∗
        (r3b_slot6 (fsp + 0x4d0#64) sw -∗ RunDrop.speOwnedAt A (fsp + 0x4d0#64) k) ∗
        r3b_slot5 (fsp + 0x2a0#64) t ∗
        memRegion (fsp + 0x508#64) 192 ∗ anyHeap := by
    have ha4d8 : fsp + 0x4d0#64 + 8#64 = fsp + 0x4d8#64 := by bv_omega
    have ha508 : fsp + 0x4d0#64 + 56#64 = fsp + 0x508#64 := by bv_omega
    refine Entails.trans
      (sepConj_mono (pksmResAt_err_owned A (fsp + 0x4d0#64))
        (sepConj_mono (r3b_mem40_to_slot5 (fsp + 0x2a0#64)) (Entails.refl anyHeap)))
      ?_
    rw [ha4d8, ha508]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro t
    apply Entails.sepExists_elim; intro k
    refine Entails.trans
      (r3b_perm
        (sepConj_mono_left
          (Q := ((fsp + 0x4d0#64) ↦₆₄ errTag) ∗ memRegion (fsp + 0x508#64) 192 ∗
            anyHeap ∗ anyHeap ∗ r3b_slot5 (fsp + 0x2a0#64) t)
          (r3b_speOwnedAt_words6 A (fsp + 0x4d8#64) (fsp + 0x4d0#64) k))
        (by ac_rfl)) ?_
    simp only [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro sw
    rw [sepConj_assoc]
    apply Entails.pure_left; intro _
    refine Entails.sepExists_right k (Entails.sepExists_right sw
      (Entails.sepExists_right t ?_))
    exact r3b_perm
      (r3b_perm_post
        (sepConj_mono (entails_anyHeap (anyHeap ∗ anyHeap))
          (Entails.refl (((fsp + 0x4d0#64) ↦₆₄ errTag) ∗
            r3b_slot6 (fsp + 0x4d8#64) sw ∗
            (r3b_slot6 (fsp + 0x4d0#64) sw -∗ RunDrop.speOwnedAt A (fsp + 0x4d0#64) k) ∗
            r3b_slot5 (fsp + 0x2a0#64) t ∗
            memRegion (fsp + 0x508#64) 192)))
        (by ac_rfl))
      (by ac_rfl)
  apply r3b_sepWPp_weaken_pre
    (r3b_perm
      (sepConj_mono_left
        (Q := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          addrNameHeap A meG ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
          memRegion fsp 0x220 ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
            ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
          memRegion (fsp + 0x240#64) 0x20 ∗
          (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
            ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
            ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
          memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) ∗
          memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool)
        hpkm_err)
      (by ac_rfl))
  simp only [sepExists_sepConj_left]
  apply r3b_sepWPp_exists_left; intro k
  apply r3b_sepWPp_exists_left; intro sw
  apply r3b_sepWPp_exists_left; intro t
  have herr_eq : ((errTag + 1#64) == 0#64) = true := rfl
  apply sepWPp_seq_inImage (mid := (mProg img ext).fnAddr cliDropSpeName) hs.inv
  have hfn0 := run_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_pkchk img.base
    (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 2452 36
  code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_pkerr img.base
    (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 3768 24
  code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_dperr img.base
    (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 4064 12
  clear hfn0
  dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc ⊢
  generalize hfn :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
  examples_hide_fetches
  dsimp only [r3b_slot6, r3b_slot5]
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hx26 ⊢
  wp_steps
  apply SepWP.done
    (by simp only [arm64_norm, ← hfn, Program.fnAddr_rebase, run_fnOff, cliDropSpe_fnOff])
    (by simp only [arm64_norm, hrun])
  intro hinv_c
  refine r3b_call_inImage
    (F := ((fsp + 1280#64) ↦₆₄ sw.w5) ∗
      r3b_slot5 (fsp + 672#64) ⟨sw.w1, sw.w2, sw.w3, sw.w4, sw.w5⟩ ∗
      memRegion (fsp + 0x508#64) 192 ∗
      memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A meG ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
      memRegion fsp 0x220 ∗
      (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
        ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
        ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
      memRegion (fsp + 0x240#64) 0x20 ∗
      (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
        ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
        ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
      memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) ∗
      memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ∗ anyHeap)
    (s0 := s0) ⟨fsp + 0x4d0#64, k⟩
    (hdrop (resStack - runFrame) hstk32 hsub64) hinv_c
    (by simp only [arm64_norm, ← hfn, Program.fnAddr_rebase, run_fnOff, cliDropSpe_fnOff])
    (by simp only [arm64_norm, hrun])
    (by simpa only [State.spAligned, arm64_norm] using hsp_al)
    (retAddr := runPc img ext 0xfec)
    (by simp only [arm64_norm, runPc, mProg, tripleRatchetProgAtExt, ← hfn])
    ?_
    (hnext := fun sm _ hinv_m hpcm hrunm hspm hcsm => ?_)
  · dsimp only [RunDrop.dropSpeOwnedSpec]
    simp only [sepConj_assoc]
    apply Entails.pure_right
    · simp only [arm64_norm]; try rw [hsp]
    simp only [arm64_norm]
    try rw [hsp]
    have hwand :
        r3b_slot6 (fsp + 0x4d0#64) sw ∗
          (r3b_slot6 (fsp + 0x4d0#64) sw -∗ RunDrop.speOwnedAt A (fsp + 0x4d0#64) k) ⊢
        RunDrop.speOwnedAt A (fsp + 0x4d0#64) k := Entails.wand_elim _ _
    exact r3b_perm
      (r3b_perm_post
        (sepConj_mono hwand
          (Entails.refl (A.pool ∗ stackAt fsp (resStack - runFrame) ∗
            ((fsp + 1280#64) ↦₆₄ sw.w5) ∗
            r3b_slot5 (fsp + 672#64) ⟨sw.w1, sw.w2, sw.w3, sw.w4, sw.w5⟩ ∗
            memRegion (fsp + 0x508#64) 192 ∗
            memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            addrNameHeap A meG ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
            memRegion fsp 0x220 ∗
            (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
              ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
              ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
            memRegion (fsp + 0x240#64) 0x20 ∗
            (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
              ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
              ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
            memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) ∗
            memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ∗ anyHeap)))
        (by ac_rfl))
      (by
        dsimp only [r3b_slot6, r3b_slot5]
        have o1 : fsp + 0x4d0#64 + 8#64 = fsp + 1240#64 := by bv_omega
        have o2 : fsp + 0x4d0#64 + 16#64 = fsp + 1248#64 := by bv_omega
        have o3 : fsp + 0x4d0#64 + 24#64 = fsp + 1256#64 := by bv_omega
        have o4 : fsp + 0x4d0#64 + 32#64 = fsp + 1264#64 := by bv_omega
        have o5 : fsp + 0x4d0#64 + 40#64 = fsp + 1272#64 := by bv_omega
        have t1 : fsp + 672#64 + 8#64 = fsp + 680#64 := by bv_omega
        have t2 : fsp + 672#64 + 16#64 = fsp + 688#64 := by bv_omega
        have t3 : fsp + 672#64 + 24#64 = fsp + 696#64 := by bv_omega
        have t4 : fsp + 672#64 + 32#64 = fsp + 704#64 := by bv_omega
        have z0 : fsp + 1232#64 = fsp + 0x4d0#64 := rfl
        rw [o1, o2, o3, o4, o5, t1, t2, t3, t4, z0]
        ac_rfl)
  · dsimp only [RunDrop.dropSpeOwnedSpec]
    simp only [sepConj_assoc]
    apply r3b_sepWPp_pure_left; intro htr_m
    have htr_tot : sm.trace = s.trace := htr_m.trans (by simp only [arm64_norm])
    have hfs_tot : sm.fs.files = s.fs.files := by
      have hs_steps : Steps (mProg img ext) _ sm := ‹_›
      exact (r3b_files_of_trace_eq hh.fs hs_steps htr_m).trans (by simp only [arm64_norm])
    have hs_m : InRun img ext s0 sm 0xfec :=
      r3b_inRun_step hs hpcm hrunm (hspm.trans (by simp only [arm64_norm]))
        (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm])) hinv_m
        (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [calleeSavedVRegs, arm64_norm]))
    refine r3b_sepWPp_weaken_pre ?_
      (r3b_reject_from_fec StoresGhost.opened meG peerG
        (BitVec.ofNat 64 peerG.name.bytes.length) cw4 hh hext_le hsub64 hs_m
        (hcsm.1.trans (by simp only [arm64_norm, hx19]))
        (hcsm.2.1.trans (by simp only [arm64_norm, hx20]))
        (hcsm.2.2.1.trans (by simp only [arm64_norm, hx21]))
        (hcsm.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, hx28]))
        (htr_tot ▸ htr)
        (r3b_hist_of_eq htr_tot hfs_tot hhist)
        hans hrej)
    have hloc_back :
        memRegion (fsp + 0x240#64) 0x20 ∗
          (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
            ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
            ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
          memRegion (fsp + 0x280#64) 0x20 ∗
          r3b_slot5 (fsp + 672#64) ⟨sw.w1, sw.w2, sw.w3, sw.w4, sw.w5⟩ ∗
          memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) ∗
          memRegion (fsp + 0x4d0#64) 48 ∗
          ((fsp + 1280#64) ↦₆₄ sw.w5) ∗
          memRegion (fsp + 0x508#64) 192 ∗
          memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ⊢
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) := by
      have hpkm_back :
          memRegion (fsp + 0x4d0#64) 48 ∗ ((fsp + 1280#64) ↦₆₄ sw.w5) ∗
            memRegion (fsp + 0x508#64) 192 ⊢
          memRegion (fsp + 0x4d0#64) 248 := by
        rw [ProofLib.memRegion_split' (b := fsp + 0x4d0#64) (n := 48) (k := 200)
              (b' := fsp + 1280#64) rfl (by bv_omega) (by decide),
            ProofLib.memRegion_split' (b := fsp + 1280#64) (n := 8) (k := 192)
              (b' := fsp + 0x508#64) rfl (by bv_omega) (by decide)]
        exact sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion _ _))
      have hm1 := sepConj_mono (Entails.refl (memRegion (fsp + 0x240#64) 0x20))
        (sepConj_mono (r3b_words4_entails_mem32 (fsp + 0x260#64) meG.name.cap meG.name.ptr
              (BitVec.ofNat 64 meG.name.bytes.length) hiMe)
          (sepConj_mono (Entails.refl (memRegion (fsp + 0x280#64) 0x20))
            (sepConj_mono (r3b_slot5_to_mem40 (fsp + 672#64) ⟨sw.w1, sw.w2, sw.w3, sw.w4, sw.w5⟩)
              (sepConj_mono (Entails.refl (memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8)))
                (sepConj_mono hpkm_back
                  (Entails.refl (memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8))))))))
      have heq_all : memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) =
          memRegion (fsp + 0x240#64) 0x20 ∗
            (memRegion (fsp + 0x260#64) 32 ∗
              (memRegion (fsp + 0x280#64) 0x20 ∗
                (memRegion (fsp + 672#64) 40 ∗
                  (memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) ∗
                    (memRegion (fsp + 0x4d0#64) 248 ∗
                      memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8)))))) := by
        rw [r3b_split_at fsp 0x240 0x20 runLocalBytes (by decide) (by decide),
            r3b_split_at fsp 0x260 32 runLocalBytes (by decide) (by decide),
            r3b_split_at fsp 0x280 0x20 runLocalBytes (by decide) (by decide),
            r3b_split_at fsp 0x2a0 40 runLocalBytes (by decide) (by decide),
            r3b_split_at fsp 0x2c8 (0x4d0 - 0x2c8) runLocalBytes (by decide) (by decide),
            r3b_split_at fsp 0x4d0 248 runLocalBytes (by decide) (by decide)]
      rw [heq_all]
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm1
      exact r3b_perm hm1 (by ac_rfl)
    subst hfsp
    rw [← hspm, hs_m.sp]
    exact r3b_perm
      (r3b_perm_post
        (sepConj_mono hloc_back
          (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            addrNameHeap A meG ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
            memRegion (runFsp s0) 0x220 ∗
            (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
              ((runFsp s0 + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
              ((runFsp s0 + 0x238#64) ↦₆₄ cw4)) ∗
            stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap)))
        (by ac_rfl))
      (by ac_rfl)

private theorem r3b_pt64_eq {a b v w : BitVec 64} (ha : a = b) (hv : v = w) :
    (a ↦₆₄ v) ⊢ (b ↦₆₄ w) := by
  subst ha; subst hv; exact Entails.refl _

private theorem r3b_collapse5_flat {a a1 a2 a3 a4 : BitVec 64}
    {w0 w1 w2 w3 w4 : BitVec 64} {T R : SepProp}
    (e1 : a + 8#64 = a1) (e2 : a + 16#64 = a2) (e3 : a + 24#64 = a3) (e4 : a + 32#64 = a4)
    (hT : memRegion a 40 ∗ T ⊢ R) :
    (a ↦₆₄ w0) ∗ (a1 ↦₆₄ w1) ∗ (a2 ↦₆₄ w2) ∗ (a3 ↦₆₄ w3) ∗ (a4 ↦₆₄ w4) ∗ T ⊢ R := by
  subst e1; subst e2; subst e3; subst e4
  have h5 : (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ⊢ memRegion a 40 :=
    r3b_slot5_to_mem40 a ⟨w0, w1, w2, w3, w4⟩
  refine Entails.trans ?_ hT
  simpa only [sepConj_assoc] using sepConj_mono_left (Q := T) h5

private theorem r3b_collapse30_flat {a : BitVec 64}
    {w00 w01 w02 w03 w04 w05 w06 w07 w08 w09
     w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
     w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 : BitVec 64}
    {a01 a02 a03 a04 a05 a06 a07 a08 a09
     a10 a11 a12 a13 a14 a15 a16 a17 a18 a19
     a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 : BitVec 64}
    {T R : SepProp}
    (e01 : a + 8#64 = a01) (e02 : a + 16#64 = a02) (e03 : a + 24#64 = a03)
    (e04 : a + 32#64 = a04) (e05 : a + 40#64 = a05) (e06 : a + 48#64 = a06)
    (e07 : a + 56#64 = a07) (e08 : a + 64#64 = a08) (e09 : a + 72#64 = a09)
    (e10 : a + 80#64 = a10) (e11 : a + 88#64 = a11) (e12 : a + 96#64 = a12)
    (e13 : a + 104#64 = a13) (e14 : a + 112#64 = a14) (e15 : a + 120#64 = a15)
    (e16 : a + 128#64 = a16) (e17 : a + 136#64 = a17) (e18 : a + 144#64 = a18)
    (e19 : a + 152#64 = a19) (e20 : a + 160#64 = a20) (e21 : a + 168#64 = a21)
    (e22 : a + 176#64 = a22) (e23 : a + 184#64 = a23) (e24 : a + 192#64 = a24)
    (e25 : a + 200#64 = a25) (e26 : a + 208#64 = a26) (e27 : a + 216#64 = a27)
    (e28 : a + 224#64 = a28) (e29 : a + 232#64 = a29)
    (hT : memRegion a 240 ∗ T ⊢ R) :
    (a ↦₆₄ w00) ∗ (a01 ↦₆₄ w01) ∗ (a02 ↦₆₄ w02) ∗ (a03 ↦₆₄ w03) ∗ (a04 ↦₆₄ w04) ∗
    (a05 ↦₆₄ w05) ∗ (a06 ↦₆₄ w06) ∗ (a07 ↦₆₄ w07) ∗ (a08 ↦₆₄ w08) ∗ (a09 ↦₆₄ w09) ∗
    (a10 ↦₆₄ w10) ∗ (a11 ↦₆₄ w11) ∗ (a12 ↦₆₄ w12) ∗ (a13 ↦₆₄ w13) ∗ (a14 ↦₆₄ w14) ∗
    (a15 ↦₆₄ w15) ∗ (a16 ↦₆₄ w16) ∗ (a17 ↦₆₄ w17) ∗ (a18 ↦₆₄ w18) ∗ (a19 ↦₆₄ w19) ∗
    (a20 ↦₆₄ w20) ∗ (a21 ↦₆₄ w21) ∗ (a22 ↦₆₄ w22) ∗ (a23 ↦₆₄ w23) ∗ (a24 ↦₆₄ w24) ∗
    (a25 ↦₆₄ w25) ∗ (a26 ↦₆₄ w26) ∗ (a27 ↦₆₄ w27) ∗ (a28 ↦₆₄ w28) ∗ (a29 ↦₆₄ w29) ∗
    T ⊢ R := by
  subst e01; subst e02; subst e03; subst e04; subst e05
  subst e06; subst e07; subst e08; subst e09; subst e10
  subst e11; subst e12; subst e13; subst e14; subst e15
  subst e16; subst e17; subst e18; subst e19; subst e20
  subst e21; subst e22; subst e23; subst e24; subst e25
  subst e26; subst e27; subst e28; subst e29
  have h30 := r3b_slot30_to_mem240 a
    ⟨⟨w00, w01, w02, w03, w04⟩, ⟨w05, w06, w07, w08, w09⟩, ⟨w10, w11, w12, w13, w14⟩,
     ⟨w15, w16, w17, w18, w19⟩, ⟨w20, w21, w22, w23, w24⟩, ⟨w25, w26, w27, w28, w29⟩⟩
  dsimp only [r3b_slot30, r3b_slot5] at h30
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h30
  refine Entails.trans ?_ hT
  simpa only [sepConj_assoc] using sepConj_mono_left (Q := T) h30

/-- First half of `PreKeySignalMessage::try_from` `Ok` shuffle (`R+0x994 → R+0xaa0`):
checks `pqCap + 1 ≠ 0` twice and copies the 30 words `w` from `fsp + 0x4d8` via `fsp + 0x2a0` and
`fsp + 0x1750` into `r3b_shufMid w z` at `fsp + 0x3e0`. -/
private theorem r3b_recvP_shuf1 {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {Q Qp : State → SepProp → Prop}
    (pqCap : BitVec 64) (w : r3b_W30) (t : r3b_W5) (z m : r3b_W30) (F : SepProp)
    (hs : InRun img ext s0 s 0x994)
    (hcap : pqCap.toNat < 2 ^ 63)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx27 : s.readReg64 (.gpr 27#5) = runFsp s0 + 0x1750#64)
    (hk : ∀ s' : State,
      InRun img ext s0 s' 0xaa0 →
      s'.readReg64 (.gpr 8#5) = w.b0.w0 →
      s'.readReg64 (.gpr 9#5) = pqCap →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      s'.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) →
      s'.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) →
      s'.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) →
      s'.trace = s.trace →
      s'.fs = s.fs →
      SepWPp (mProg img ext) (s0.readReg64 .lr) s'
        (((runFsp s0 + 0x4d0#64) ↦₆₄ pqCap) ∗
          r3b_slot30 (runFsp s0 + 0x4d8#64) w ∗
          memRegion (runFsp s0 + 0x2a0#64) 40 ∗
          r3b_slot30 (runFsp s0 + 0x3e0#64) (r3b_shufMid w z) ∗
          memRegion (runFsp s0 + 0x1750#64) 240 ∗ F)
        Q Qp (runOom s0)) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (((runFsp s0 + 0x4d0#64) ↦₆₄ pqCap) ∗
        r3b_slot30 (runFsp s0 + 0x4d8#64) w ∗
        r3b_slot5 (runFsp s0 + 0x2a0#64) t ∗
        r3b_slot30 (runFsp s0 + 0x3e0#64) z ∗
        r3b_slot30 (runFsp s0 + 0x1750#64) m ∗ F)
      Q Qp (runOom s0) := by
  have hpc : s.pc = runPc img ext 0x994 := hs.pc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = runFsp s0 := hs.sp
  have hsp_al : s.spAligned = true := hs.spAligned_cur
  have hcmn : ((pqCap + 1#64) == 0#64) = false :=
    beq_eq_false_iff_ne.mpr (by intro h0; bv_omega)
  generalize hfsp : runFsp s0 = fsp at hsp hx26 hx27 ⊢
  apply sepWPp_seq_inImage (mid := runPc img ext 0xaa0) hs.inv
  have hfn0 := run_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_pkchk img.base
    (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 2452 36
  code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_shuf1 img.base
    (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 2488 232
  clear hfn0
  dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc ⊢
  generalize hfn :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
  examples_hide_fetches
  dsimp only [r3b_slot30, r3b_slot5]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hx26 hx27 ⊢
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
  intro hinv'
  subst hfsp
  let fsp := runFsp s0
  have hs' : InRun img ext s0 _ 0xaa0 :=
    r3b_inRun_step hs (by simp only [arm64_norm]; rw [← hfn])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv' (by simp only [calleeSavedVRegs, arm64_norm])
  refine r3b_sepWPp_weaken_pre ?_
    (hk _ hs'
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm]))
  try rw [hsp]
  have hc5 : ∀ (T : SepProp),
      ((fsp + 672#64) ↦₆₄ w.b0.w1) ∗ ((fsp + 680#64) ↦₆₄ w.b0.w2) ∗
      ((fsp + 688#64) ↦₆₄ w.b0.w3) ∗ ((fsp + 696#64) ↦₆₄ w.b0.w4) ∗
      ((fsp + 704#64) ↦₆₄ w.b1.w0) ∗ T ⊢ memRegion (fsp + 0x2a0#64) 40 ∗ T :=
    fun T => r3b_collapse5_flat (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
      (Entails.refl _)
  have hc30 : ∀ (T : SepProp),
      ((fsp + 5968#64) ↦₆₄ w.b0.w1) ∗ ((fsp + 5976#64) ↦₆₄ w.b0.w2) ∗
      ((fsp + 5984#64) ↦₆₄ w.b0.w3) ∗ ((fsp + 5992#64) ↦₆₄ w.b0.w4) ∗
      ((fsp + 6000#64) ↦₆₄ w.b1.w0) ∗ ((fsp + 6008#64) ↦₆₄ w.b1.w1) ∗
      ((fsp + 6016#64) ↦₆₄ w.b1.w2) ∗ ((fsp + 6024#64) ↦₆₄ w.b1.w3) ∗
      ((fsp + 6032#64) ↦₆₄ w.b1.w4) ∗ ((fsp + 6040#64) ↦₆₄ w.b2.w0) ∗
      ((fsp + 6048#64) ↦₆₄ w.b2.w1) ∗ ((fsp + 6056#64) ↦₆₄ w.b2.w2) ∗
      ((fsp + 6064#64) ↦₆₄ w.b2.w3) ∗ ((fsp + 6072#64) ↦₆₄ w.b2.w4) ∗
      ((fsp + 6080#64) ↦₆₄ w.b3.w0) ∗ ((fsp + 6088#64) ↦₆₄ w.b3.w1) ∗
      ((fsp + 6096#64) ↦₆₄ w.b3.w2) ∗ ((fsp + 6104#64) ↦₆₄ w.b3.w3) ∗
      ((fsp + 6112#64) ↦₆₄ w.b3.w4) ∗ ((fsp + 6120#64) ↦₆₄ w.b4.w0) ∗
      ((fsp + 6128#64) ↦₆₄ w.b4.w1) ∗ ((fsp + 6136#64) ↦₆₄ w.b4.w2) ∗
      ((fsp + 6144#64) ↦₆₄ w.b4.w3) ∗ ((fsp + 6152#64) ↦₆₄ w.b4.w4) ∗
      ((fsp + 6160#64) ↦₆₄ w.b5.w0) ∗ ((fsp + 6168#64) ↦₆₄ w.b5.w1) ∗
      ((fsp + 6176#64) ↦₆₄ w.b5.w2) ∗ ((fsp + 6184#64) ↦₆₄ w.b5.w3) ∗
      ((fsp + 6192#64) ↦₆₄ w.b5.w4) ∗ ((fsp + 6200#64) ↦₆₄ m.b5.w4) ∗ T ⊢
      memRegion (fsp + 0x1750#64) 240 ∗ T :=
    fun T => r3b_collapse30_flat
      (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
      (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
      (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
      (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
      (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
      (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
      (Entails.refl _)
  dsimp only [fsp, r3b_slot30, r3b_slot5, r3b_shufMid] at hc5 hc30 ⊢
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hc5 hc30 ⊢
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (Entails.trans (hc5 _) (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (hc30 _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxHeartbeats 1200000 in
/-- Second half of `PreKeySignalMessage::try_from` `Ok` shuffle (`R+0xaa0 → wrapDecryptPrekeyName`,
returning to `R+0xb78`): restores all 31 words of `preKeyMsgAt` at `fsp + 0x4d0`, writes the 5 stack
arguments at `[fsp .. fsp + 40)`, collapses `[fsp + 0x3e0 .. +240)`, and sets ABI registers `x0..x8`. -/
private theorem r3b_recvP_shuf2 {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {Q Qp : State → SepProp → Prop}
    (stores pqCap : BitVec 64) (t0 : r3b_W5) (w z : r3b_W30) (F : SepProp)
    (hb : (img.base &&& 0xfff#64) = 0#64)
    (hs : InRun img ext s0 s 0xaa0)
    (hx8 : s.readReg64 (.gpr 8#5) = w.b0.w0)
    (hx9 : s.readReg64 (.gpr 9#5) = pqCap)
    (hx19 : s.readReg64 (.gpr 19#5) = stores)
    (hk : ∀ sc : State,
      ImgCallInv img sc →
      sc.pc = (mProg img ext).fnAddr wrapDecryptPrekeyName →
      sc.status = .Running →
      sc.sp = runFsp s0 →
      sc.spAligned = true →
      sc.readReg64 Reg.lr = runPc img ext 0xb78 →
      sc.readReg64 .x0 = runFsp s0 + 0x4d0#64 →
      sc.readReg64 .x1 = runFsp s0 + 0x220#64 →
      sc.readReg64 .x2 = runFsp s0 + 0x260#64 →
      sc.readReg64 .x3 = stores + 0xf0#64 →
      sc.readReg64 .x4 = sessVt img →
      sc.readReg64 .x5 = stores →
      sc.readReg64 .x6 = idVt img →
      sc.readReg64 .x7 = stores + 0xc8#64 →
      sc.readReg64 .x8 = runFsp s0 + 0x320#64 →
      sc.readReg64 (.gpr 19#5) = stores →
      sc.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      sc.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) →
      sc.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) →
      sc.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) →
      sc.readReg64 .fp = s.readReg64 .fp →
      calleeSavedVRegs sc = calleeSavedVRegs s →
      sc.trace = s.trace →
      sc.fs = s.fs →
      SepWPp (mProg img ext) (s0.readReg64 .lr) sc
        ((runFsp s0 ↦₆₄ oneTimeVt img) ∗
          ((runFsp s0 + 8#64) ↦₆₄ (stores + 0x50#64)) ∗
          ((runFsp s0 + 16#64) ↦₆₄ signedVt img) ∗
          ((runFsp s0 + 24#64) ↦₆₄ (stores + 0x78#64)) ∗
          ((runFsp s0 + 32#64) ↦₆₄ kyberVt img) ∗
          memRegion (runFsp s0 + 0x3e0#64) 240 ∗
          ((runFsp s0 + 0x4d0#64) ↦₆₄ pqCap) ∗
          r3b_slot30 (runFsp s0 + 0x4d8#64) w ∗ F)
        Q Qp (runOom s0)) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (r3b_slot5 (runFsp s0) t0 ∗
        r3b_slot30 (runFsp s0 + 0x3e0#64) (r3b_shufMid w z) ∗
        ((runFsp s0 + 0x4d0#64) ↦₆₄ pqCap) ∗
        r3b_slot30 (runFsp s0 + 0x4d8#64) w ∗ F)
      Q Qp (runOom s0) := by
  have hpc : s.pc = runPc img ext 0xaa0 := hs.pc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = runFsp s0 := hs.sp
  have hsp_al : s.spAligned = true := hs.spAligned_cur
  generalize hfsp : runFsp s0 = fsp at hsp ⊢
  apply sepWPp_seq_inImage (mid := (mProg img ext).fnAddr wrapDecryptPrekeyName) hs.inv
  have hfn0 := run_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_shuf2 img.base
    (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 2720 216
  clear hfn0
  dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc ⊢
  generalize hfn :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
  examples_hide_fetches
  dsimp only [r3b_slot30, r3b_slot5, r3b_shufMid]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  apply SepWP.done
    (by simp only [arm64_norm, ← hfn, Program.fnAddr_rebase, run_fnOff, r3b_decpk_fnOff])
    (by simp only [arm64_norm, hrun])
  intro hinv_c
  subst hfsp
  let fsp := runFsp s0
  have hfn_eq : fnBase = img.base + bv% (ls_off% "libsignal_cli::run") := by
    rw [← hfn, Program.fnAddr_rebase, run_fnOff]
  refine r3b_sepWPp_weaken_pre ?_
    (hk _ hinv_c
      (by simp only [arm64_norm, mProg, tripleRatchetProgAtExt, ← hfn,
            Program.fnAddr_rebase, run_fnOff, r3b_decpk_fnOff])
      (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm]; try rw [hsp])
      (by simpa only [State.spAligned, arm64_norm] using hsp_al)
      (by simp only [arm64_norm, runPc, mProg, tripleRatchetProgAtExt, ← hfn])
      (by simp only [arm64_norm]; try rw [hsp])
      (by simp only [arm64_norm]; try rw [hsp])
      (by simp only [arm64_norm]; try rw [hsp])
      (by simp only [arm64_norm]; try rw [hx19])
      (by simp only [arm64_norm]; exact r3b_sessVt_eq hb hfn_eq)
      (by simp only [arm64_norm]; try rw [hx19])
      (by simp only [arm64_norm]; exact r3b_idVt_eq hb hfn_eq)
      (by simp only [arm64_norm]; try rw [hx19])
      (by simp only [arm64_norm]; try rw [hsp])
      (by simp only [arm64_norm]; try rw [hx19])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [calleeSavedVRegs, arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm]))
  try rw [hsp]
  dsimp only [fsp, r3b_slot30, r3b_slot5]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine sepConj_mono (r3b_pt64_eq rfl (r3b_oneTimeVt_eq hb hfn_eq))
    (sepConj_mono (r3b_pt64_eq rfl rfl)
      (sepConj_mono (r3b_pt64_eq rfl (r3b_signedVt_eq hb hfn_eq))
        (sepConj_mono (r3b_pt64_eq rfl rfl)
          (sepConj_mono (r3b_pt64_eq rfl (r3b_kyberVt_eq hb hfn_eq))
            (r3b_collapse30_flat
              (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
              (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
              (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
              (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
              (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
              (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
              (Entails.refl _))))))

private theorem r3b_mem48_to_slot6 (a : BitVec 64) :
    memRegion a 48 ⊢ ∃∗ e : r3b_W6, r3b_slot6 a e := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 40) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_eight a]
  refine Entails.trans (sepConj_mono_right (r3b_mem40_to_slot5 (a + 8#64))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro t
  apply Entails.sepExists_elim; intro w0
  refine Entails.sepExists_right ⟨w0, t.w0, t.w1, t.w2, t.w3, t.w4⟩ ?_
  dsimp only [r3b_slot5, r3b_slot6]
  have o1 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  have o2 : a + 8#64 + 16#64 = a + 24#64 := by bv_omega
  have o3 : a + 8#64 + 24#64 = a + 32#64 := by bv_omega
  have o4 : a + 8#64 + 32#64 = a + 40#64 := by bv_omega
  rw [o1, o2, o3, o4]
  exact Entails.of_eq (by ac_rfl)

private theorem r3b_slot6_to_mem48 (a : BitVec 64) (e : r3b_W6) :
    r3b_slot6 a e ⊢ memRegion a 48 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 40) (b' := a + 8#64) rfl rfl (by decide)]
  have h5 := r3b_slot5_to_mem40 (a + 8#64) ⟨e.w1, e.w2, e.w3, e.w4, e.w5⟩
  dsimp only [r3b_slot5, r3b_slot6] at h5 ⊢
  have o1 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  have o2 : a + 8#64 + 16#64 = a + 24#64 := by bv_omega
  have o3 : a + 8#64 + 24#64 = a + 32#64 := by bv_omega
  have o4 : a + 8#64 + 32#64 = a + 40#64 := by bv_omega
  rw [o1, o2, o3, o4] at h5
  exact Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono (pointsTo64_entails_memRegion a e.w0) h5)

/-- `decrypt_prekey` `Err` tail from `R+0xd94` (`R+0xd94 → R+0xfc4 → cliDropSpeName → R+0xfec → R+0x2c7c`). -/
private theorem r3b_recvP_dec_err {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {g : RunCall}
    (g' : StoresGhost) (err : ApiError AddrVal Unit) (peerG meG : AddrGhost)
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hstk32 : 32 + extHookStack ≤ resStack - runFrame)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRun img ext s0 s 0xd94)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (hrej : RejectK img ext A g s0 resStack Q Qp) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        protocolAddressAt A peerG (runFsp s0 + 0x220#64) ∗
        protocolAddressAt A meG (runFsp s0 + 0x260#64) ∗
        runSaved s0 ∗
        memRegion (runFsp s0) 0x220 ∗
        memRegion (runFsp s0 + 0x240#64) 0x20 ∗
        memRegion (runFsp s0 + 0x280#64) 0xa0 ∗
        decResAt A (runFsp s0 + 0x320#64) (.error err) ∗
        memRegion (runFsp s0 + 0x350#64) (runLocalBytes - 0x350) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      Q Qp (runOom s0) := by
  have hpc : s.pc = runPc img ext 0xd94 := hs.pc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = runFsp s0 := hs.sp
  have hsp_al : s.spAligned = true := hs.spAligned_cur
  generalize hfsp : runFsp s0 = fsp at hsp hx26 ⊢
  have h350 : memRegion (fsp + 0x350#64) (runLocalBytes - 0x350) =
      memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
        memRegion (fsp + 0x4d0#64) 48 ∗
        memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) := by
    rw [r3b_split_at fsp 0x350 (0x4d0 - 0x350) runLocalBytes (by decide) (by decide),
        r3b_split_at fsp 0x4d0 48 runLocalBytes (by decide) (by decide)]
  have hprep :
      decResAt A (fsp + 0x320#64) (.error err) ∗ memRegion (fsp + 0x4d0#64) 48 ⊢
        ∃∗ k : RunDrop.SpeOwned, ∃∗ sw : r3b_W6, ∃∗ d0 : r3b_W6,
          ⌜sw.w0 ≠ pendingTag ∧ sw.w0 ≠ okTagVec⌝ ∗
          r3b_slot6 (fsp + 0x320#64) sw ∗
          r3b_slot6 (fsp + 0x4d0#64) d0 ∗
          (r3b_slot6 (fsp + 0x4d0#64) sw -∗ RunDrop.speOwnedAt A (fsp + 0x4d0#64) k) := by
    dsimp only [decResAt]
    refine Entails.trans (sepConj_mono_right (r3b_mem48_to_slot6 (fsp + 0x4d0#64))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro d0
    apply Entails.sepExists_elim; intro k
    refine Entails.trans
      (sepConj_mono_left (r3b_speOwnedAt_words6 A (fsp + 0x320#64) (fsp + 0x4d0#64) k)) ?_
    simp only [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro sw
    rw [sepConj_assoc]
    apply Entails.pure_left; intro htags
    exact Entails.sepExists_right k (Entails.sepExists_right sw
      (Entails.sepExists_right d0 (Entails.pure_right htags (Entails.of_eq (by ac_rfl)))))
  rw [h350]
  apply r3b_sepWPp_weaken_pre
    (r3b_perm
      (sepConj_mono_left
        (Q := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          protocolAddressAt A peerG (fsp + 0x220#64) ∗
          protocolAddressAt A meG (fsp + 0x260#64) ∗
          runSaved s0 ∗
          memRegion fsp 0x220 ∗
          memRegion (fsp + 0x240#64) 0x20 ∗
          memRegion (fsp + 0x280#64) 0xa0 ∗
          memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
          memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)
        hprep)
      (by ac_rfl))
  simp only [sepExists_sepConj_left]
  apply r3b_sepWPp_exists_left; intro k
  apply r3b_sepWPp_exists_left; intro sw
  apply r3b_sepWPp_exists_left; intro d0
  rw [sepConj_assoc]
  apply r3b_sepWPp_pure_left; rintro ⟨hnot_pend, hnot_ok⟩
  have hcmn3 : ((sw.w0 + 3#64) == 0#64) = false :=
    beq_eq_false_iff_ne.mpr (by intro h0; apply hnot_pend; unfold pendingTag; bv_omega)
  have hcmn2_eq : ((sw.w0 + 2#64) == 0#64) = false :=
    beq_eq_false_iff_ne.mpr (by intro h0; apply hnot_ok; unfold okTagVec; bv_omega)
  have hcmn2_ne : ((sw.w0 + 2#64) != 0#64) = true :=
    bne_iff_ne.mpr (by intro h0; apply hnot_ok; unfold okTagVec; bv_omega)
  apply sepWPp_seq_inImage (mid := (mProg img ext).fnAddr cliDropSpeName) hs.inv
  have hfn0 := run_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_dpchk img.base
    (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 3476 20
  code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_dperr img.base
    (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 4036 40
  clear hfn0
  dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc ⊢
  generalize hfn :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
  examples_hide_fetches
  dsimp only [r3b_slot6]
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hx26 ⊢
  wp_steps
  apply SepWP.done
    (by simp only [arm64_norm, ← hfn, Program.fnAddr_rebase, run_fnOff, cliDropSpe_fnOff])
    (by simp only [arm64_norm, hrun])
  intro hinv_c
  refine r3b_call_inImage
    (F := memRegion (fsp + 0x320#64) 48 ∗
      memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      protocolAddressAt A peerG (fsp + 0x220#64) ∗
      protocolAddressAt A meG (fsp + 0x260#64) ∗
      runSaved s0 ∗
      memRegion fsp 0x220 ∗
      memRegion (fsp + 0x240#64) 0x20 ∗
      memRegion (fsp + 0x280#64) 0xa0 ∗
      memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
      memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) ∗ anyHeap)
    (s0 := s0) ⟨fsp + 0x4d0#64, k⟩
    (hdrop (resStack - runFrame) hstk32 hsub64) hinv_c
    (by simp only [arm64_norm, ← hfn, Program.fnAddr_rebase, run_fnOff, cliDropSpe_fnOff])
    (by simp only [arm64_norm, hrun])
    (by simpa only [State.spAligned, arm64_norm] using hsp_al)
    (retAddr := runPc img ext 0xfec)
    (by simp only [arm64_norm, runPc, mProg, tripleRatchetProgAtExt, ← hfn])
    ?_
    (hnext := fun sm _ hinv_m hpcm hrunm hspm hcsm => ?_)
  · dsimp only [RunDrop.dropSpeOwnedSpec]
    simp only [sepConj_assoc]
    apply Entails.pure_right
    · simp only [arm64_norm]; try rw [hsp]
    simp only [arm64_norm]
    try rw [hsp]
    have hwand :
        r3b_slot6 (fsp + 0x4d0#64) sw ∗
          (r3b_slot6 (fsp + 0x4d0#64) sw -∗ RunDrop.speOwnedAt A (fsp + 0x4d0#64) k) ⊢
        RunDrop.speOwnedAt A (fsp + 0x4d0#64) k := Entails.wand_elim _ _
    exact r3b_perm
      (r3b_perm_post
        (sepConj_mono hwand
          (sepConj_mono (r3b_slot6_to_mem48 (fsp + 0x320#64) sw)
            (Entails.refl (A.pool ∗ stackAt fsp (resStack - runFrame) ∗
              memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              protocolAddressAt A peerG (fsp + 0x220#64) ∗
              protocolAddressAt A meG (fsp + 0x260#64) ∗
              runSaved s0 ∗
              memRegion fsp 0x220 ∗
              memRegion (fsp + 0x240#64) 0x20 ∗
              memRegion (fsp + 0x280#64) 0xa0 ∗
              memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
              memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) ∗ anyHeap))))
        (by ac_rfl))
      (by
        dsimp only [r3b_slot6]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        ac_rfl)
  · dsimp only [RunDrop.dropSpeOwnedSpec]
    simp only [sepConj_assoc]
    apply r3b_sepWPp_pure_left; intro htr_m
    have htr_tot : sm.trace = s.trace := htr_m.trans (by simp only [arm64_norm])
    have hfs_tot : sm.fs.files = s.fs.files := by
      have hs_steps : Steps (mProg img ext) _ sm := ‹_›
      exact (r3b_files_of_trace_eq hh.fs hs_steps htr_m).trans (by simp only [arm64_norm])
    have hs_m : InRun img ext s0 sm 0xfec :=
      r3b_inRun_step hs hpcm hrunm (hspm.trans (by simp only [arm64_norm]))
        (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm])) hinv_m
        (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [calleeSavedVRegs, arm64_norm]))
    have hunp :
        protocolAddressAt A peerG (fsp + 0x220#64) ∗ protocolAddressAt A meG (fsp + 0x260#64) ⊢
          ∃∗ hiP : BitVec 64,
            (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
              ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
              ((fsp + 0x238#64) ↦₆₄ hiP)) ∗
            memRegion (fsp + 0x260#64) 32 ∗
            addrNameHeap A meG ∗ addrNameHeap A peerG := by
      refine Entails.trans
        (sepConj_mono
          (r3b_addr_unpack A peerG (fsp + 0x220#64) (fsp + 0x228#64) (fsp + 0x230#64) (fsp + 0x238#64)
            (by bv_omega) (by bv_omega) (by bv_omega))
          (r3b_addr_unpack A meG (fsp + 0x260#64) (fsp + 0x268#64) (fsp + 0x270#64) (fsp + 0x278#64)
            (by bv_omega) (by bv_omega) (by bv_omega))) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply Entails.sepExists_elim; intro hiM
      apply Entails.sepExists_elim; intro hiP
      simp only [sepConj_assoc]
      apply Entails.pure_left; intro _
      apply r3b_pure5; intro _
      have hm4 := r3b_words4_entails_mem32 (fsp + 0x260#64) meG.name.cap meG.name.ptr
        (BitVec.ofNat 64 meG.name.bytes.length) hiM
      have o1 : fsp + 0x260#64 + 8#64 = fsp + 0x268#64 := by bv_omega
      have o2 : fsp + 0x260#64 + 16#64 = fsp + 0x270#64 := by bv_omega
      have o3 : fsp + 0x260#64 + 24#64 = fsp + 0x278#64 := by bv_omega
      rw [o1, o2, o3] at hm4
      refine Entails.sepExists_right hiP ?_
      exact r3b_perm
        (r3b_perm_post
          (sepConj_mono hm4
            (Entails.refl ((((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
              ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
              ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
              ((fsp + 0x238#64) ↦₆₄ hiP)) ∗
              addrNameHeap A meG ∗ addrNameHeap A peerG)))
          (by ac_rfl))
        (by ac_rfl)
    simp only [arm64_norm, hsp]
    apply r3b_sepWPp_weaken_pre
      (r3b_perm
        (sepConj_mono_left
          (Q := memRegion (fsp + 0x4d0#64) 48 ∗ A.pool ∗ stackAt fsp (resStack - runFrame) ∗
            memRegion (fsp + 0x320#64) 48 ∗
            memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            runSaved s0 ∗
            memRegion fsp 0x220 ∗
            memRegion (fsp + 0x240#64) 0x20 ∗
            memRegion (fsp + 0x280#64) 0xa0 ∗
            memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
            memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) ∗ anyHeap)
          hunp)
        (by ac_rfl))
    simp only [sepExists_sepConj_left]
    apply r3b_sepWPp_exists_left; intro hiP
    have hloc_back :
        memRegion (fsp + 0x240#64) 0x20 ∗
          memRegion (fsp + 0x260#64) 32 ∗
          memRegion (fsp + 0x280#64) 0xa0 ∗
          memRegion (fsp + 0x320#64) 48 ∗
          memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
          memRegion (fsp + 0x4d0#64) 48 ∗
          memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) =
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) := by
      rw [r3b_split_at fsp 0x240 0x20 runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x260 32 runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x280 0xa0 runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x320 48 runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x350 (0x4d0 - 0x350) runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x4d0 48 runLocalBytes (by decide) (by decide)]
    refine r3b_sepWPp_weaken_pre ?_
      (r3b_reject_from_fec g' meG peerG
        (BitVec.ofNat 64 peerG.name.bytes.length) hiP hh hext_le hsub64 hs_m
        (hcsm.1.trans (by simp only [arm64_norm, hx19]))
        (hcsm.2.1.trans (by simp only [arm64_norm, hx20]))
        (hcsm.2.2.1.trans (by simp only [arm64_norm, hx21]))
        (hcsm.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, hx28]))
        (htr_tot ▸ htr)
        (r3b_hist_of_eq htr_tot hfs_tot hhist)
        hans
        hrej)
    subst hfsp
    rw [← hloc_back]
    exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 1200000 in
/-- `decrypt_prekey` `Ok(pt)` tail from `R+0xd94` (`R+0xd94 → R+0xdcc → R+0xde0 → R+0xf8c` `AtJoin`). -/
private theorem r3b_recvP_dec_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {g : RunCall}
    (g' : StoresGhost) (pt : Bytes) (peerG meG : AddrGhost)
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRun img ext s0 s 0xd94)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, pt)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (hjoin : JoinK img ext A g s0 resStack Q Qp) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        protocolAddressAt A peerG (runFsp s0 + 0x220#64) ∗
        protocolAddressAt A meG (runFsp s0 + 0x260#64) ∗
        runSaved s0 ∗
        memRegion (runFsp s0) 0x220 ∗
        memRegion (runFsp s0 + 0x240#64) 0x20 ∗
        memRegion (runFsp s0 + 0x280#64) 0xa0 ∗
        decResAt A (runFsp s0 + 0x320#64) (.ok pt) ∗
        memRegion (runFsp s0 + 0x350#64) (runLocalBytes - 0x350) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      Q Qp (runOom s0) := by
  let fsp := runFsp s0
  have hfrom_de0 : ∀ sd : State,
      InRun img ext s0 sd 0xde0 →
      sd.readReg64 (.gpr 19#5) = g.stores →
      sd.readReg64 (.gpr 20#5) = g.res →
      sd.trace = s.trace →
      sd.fs = s.fs →
      SepWPp (mProg img ext) (s0.readReg64 .lr) sd
        (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          addrNameHeap A peerG ∗
          runSaved s0 ∗
          memRegion fsp 0x208 ∗
          vecU8 A (fsp + 0x208#64) pt ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x230#64) 16) ∗
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)
        Q Qp (runOom s0) := by
    intro sd hsd hx19d hx20d htrd hfsd
    have hjoin_loc :
        memRegion fsp 0x208 ∗
          vecU8 A (fsp + 0x208#64) pt ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x230#64) 16) ∗
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ⊢
        runLocals fsp [(0x208, 24, vecU8 A (fsp + 0x208#64) pt)] := by
      have hp32 :
          ((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x230#64) 16 ⊢
          memRegion (fsp + 0x220#64) 32 := by
        rw [ProofLib.memRegion_split' (b := fsp + 0x220#64) (n := 8) (k := 24)
              (b' := fsp + 0x228#64) rfl (by bv_omega) (by decide),
            ProofLib.memRegion_split' (b := fsp + 0x228#64) (n := 8) (k := 16)
              (b' := fsp + 0x230#64) rfl (by bv_omega) (by decide)]
        exact Entails.trans (Entails.of_eq (by ac_rfl))
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))
      have h220 :
          memRegion (fsp + 0x220#64) (runLocalBytes - 0x220) =
            memRegion (fsp + 0x220#64) 32 ∗ memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) :=
        r3b_split_at fsp 0x220 32 runLocalBytes (by decide) (by decide)
      dsimp only [runLocals, runLocalsFrom, Nat.sub_zero]
      have hz : fsp + BitVec.ofNat 64 0 = fsp := by bv_omega
      rw [hz, show BitVec.ofNat 64 (0x208 + 24) = 0x220#64 from rfl, h220]
      exact Entails.trans (Entails.of_eq (by ac_rfl))
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hp32)))
    by_cases hcapP : peerG.name.cap = 0#64
    · have hpcd : sd.pc = runPc img ext 0xde0 := hsd.pc
      have hrund : sd.status = .Running := hsd.run
      have hspd : sd.sp = fsp := hsd.sp
      have hsp_ald : sd.spAligned = true := hsd.spAligned_cur
      apply sepWPp_seq_inImage (mid := runPc img ext 0xf8c) hsd.inv
      have hfn0 := run_fnOff
      code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_dpchk img.base
        (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 3552 8
      code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_pjoin img.base
        (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 3972 8
      clear hfn0
      dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpcd ⊢
      generalize hfn :
        (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
      examples_hide_fetches
      rw [hcapP, ← hspd]
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrund])
      intro hinv'
      have hsj : InRun img ext s0 (r3b_stOf hinv') 0xf8c :=
        r3b_inRun_step hsd (by simp only [arm64_norm]; rw [← hfn])
          (by simp only [arm64_norm, hrund]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv' (by simp only [calleeSavedVRegs, arm64_norm])
      have htrj : (r3b_stOf hinv').trace = s.trace :=
        (by simp only [arm64_norm] : (r3b_stOf hinv').trace = sd.trace).trans htrd
      have hfsj : (r3b_stOf hinv').fs = s.fs :=
        (by simp only [arm64_norm] : (r3b_stOf hinv').fs = sd.fs).trans hfsd
      have hat : AtJoin img ext g g' pt s0 (r3b_stOf hinv') :=
        { base := hsj
          x19 := by simp only [arm64_norm, hx19d]
          x20 := by simp only [arm64_norm, hx20d]
          trace := htrj ▸ htr
          hist := r3b_hist_of_eq htrj (congrArg FsState.files hfsj) hhist
          ans := hans
          wrOk := hwr }
      refine r3b_sepWPp_weaken_pre ?_ (hjoin (r3b_stOf hinv') g' pt hat)
      rw [hspd, ← hcapP]
      exact r3b_perm
        (r3b_perm_post
          (sepConj_mono (r3b_nameHeap_zero A peerG hcapP)
            (sepConj_mono hjoin_loc
              (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
                runSaved s0 ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap))))
          (by rw [emp_sepConj]; dsimp only [joinMem, fsp]; ac_rfl))
        (by ac_rfl)
    · have hbeqP : (peerG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcapP
      have hpcd : sd.pc = runPc img ext 0xde0 := hsd.pc
      have hrund : sd.status = .Running := hsd.run
      have hspd : sd.sp = fsp := hsd.sp
      have hsp_ald : sd.spAligned = true := hsd.spAligned_cur
      apply r3b_sepWPp_weaken_pre
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left (r3b_nameHeap_dealloc A peerG hcapP))))))
      rw [show (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          (⌜LayoutOk peerG.name.cap.toNat 1⌝ ∗
            A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
            memRegion peerG.name.ptr peerG.name.cap.toNat) ∗
          runSaved s0 ∗ memRegion fsp 0x208 ∗ vecU8 A (fsp + 0x208#64) pt ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x230#64) 16) ∗
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap) =
        ⌜LayoutOk peerG.name.cap.toNat 1⌝ ∗
          (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
            memRegion peerG.name.ptr peerG.name.cap.toNat ∗
            runSaved s0 ∗ memRegion fsp 0x208 ∗ vecU8 A (fsp + 0x208#64) pt ∗
            (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
              ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
              memRegion (fsp + 0x230#64) 16) ∗
            memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
            stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap) by ac_rfl]
      apply r3b_sepWPp_pure_left; intro hlayP
      apply sepWPp_seq_inImage (mid := (mProg img ext).fnAddr deallocName) hsd.inv
      have hfn0 := run_fnOff
      code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_dpchk img.base
        (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 3552 16
      code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_pjoin img.base
        (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 3972 8
      clear hfn0
      dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpcd ⊢
      generalize hfn :
        (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
      examples_hide_fetches
      rw [← hspd]
      wp_steps
      apply SepWP.done
        (by simp only [arm64_norm, ← hfn, Program.fnAddr_rebase, run_fnOff, rustDealloc_fnOff])
        (by simp only [arm64_norm, hrund])
      intro hinv_c
      have hstk_split := r3b_stackAt_split_ge sd.sp hext_le hsub64
      refine r3b_call_inImage
        (F := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗ memRegion fsp 0x208 ∗ vecU8 A (fsp + 0x208#64) pt ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x230#64) 16) ∗
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
          memRegion (fsp - BitVec.ofNat 64 (resStack - runFrame))
            (resStack - runFrame - extHookStack) ∗
          anyHeap)
        (s0 := s0) (peerG.name.ptr, peerG.name.cap.toNat, 1)
        hh.allocFs.dealloc hinv_c
        (by simp only [arm64_norm, ← hfn, Program.fnAddr_rebase, run_fnOff, rustDealloc_fnOff])
        (by simp only [arm64_norm, hrund])
        (by simpa only [State.spAligned, arm64_norm] using hsp_ald)
        (retAddr := runPc img ext 0xf8c)
        (by simp only [arm64_norm, runPc, mProg, tripleRatchetProgAtExt, ← hfn])
        ?_
        (hnext := fun sm _ hinv_m hpcm hrunm hspm hcsm => ?_)
      · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
        simp only [sepConj_assoc]
        apply Entails.pure_right
        · exact ⟨by simp only [arm64_norm], by simp only [arm64_norm],
            by simp only [arm64_norm], hlayP⟩
        rw [hspd] at hstk_split ⊢
        rw [hstk_split]
        simp only [arm64_norm, hspd]
        exact Entails.of_eq (by dsimp only [fsp]; simp only [arm64_norm]; ac_rfl)
      · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
        simp only [sepConj_assoc]
        apply r3b_sepWPp_pure_left; intro hfs_m
        apply r3b_sepWPp_pure_left; intro htr_m
        have hs_m : InRun img ext s0 sm 0xf8c :=
          r3b_inRun_step hsd hpcm hrunm (hspm.trans (by simp only [arm64_norm]))
            (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm])) hinv_m
            (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [calleeSavedVRegs, arm64_norm]))
        have htr_tot : sm.trace = s.trace :=
          (htr_m.trans (by simp only [arm64_norm] : _ = sd.trace)).trans htrd
        have hfs_tot : sm.fs = s.fs :=
          (hfs_m.trans (by simp only [arm64_norm] : _ = sd.fs)).trans hfsd
        have hat : AtJoin img ext g g' pt s0 sm :=
          { base := hs_m
            x19 := hcsm.1.trans (by simp only [arm64_norm, hx19d])
            x20 := hcsm.2.1.trans (by simp only [arm64_norm, hx20d])
            trace := htr_tot ▸ htr
            hist := r3b_hist_of_eq htr_tot (congrArg FsState.files hfs_tot) hhist
            ans := hans
            wrOk := hwr }
        refine r3b_sepWPp_weaken_pre ?_ (hjoin sm g' pt hat)
        rw [hspd] at hstk_split
        dsimp only [joinMem, fsp] at hjoin_loc hstk_split ⊢
        rw [hstk_split]
        simp only [arm64_norm, hspd]
        exact r3b_perm
          (r3b_perm_post
            (sepConj_mono hjoin_loc
              (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
                runSaved s0 ∗
                memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
                  (resStack - runFrame - extHookStack) ∗
                stackAt (runFsp s0) extHookStack ∗ A.pool ∗ anyHeap)))
            (by simp only [arm64_norm]; ac_rfl))
          (by simp only [arm64_norm]; ac_rfl)
  have hfrom_dcc : ∀ s_dcc : State,
      InRun img ext s0 s_dcc 0xdcc →
      s_dcc.readReg64 (.gpr 19#5) = g.stores →
      s_dcc.readReg64 (.gpr 20#5) = g.res →
      s_dcc.readReg64 (.gpr 21#5) = meG.name.cap →
      s_dcc.readReg64 (.gpr 28#5) = meG.name.ptr →
      s_dcc.trace = s.trace →
      s_dcc.fs = s.fs →
      SepWPp (mProg img ext) (s0.readReg64 .lr) s_dcc
        (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          addrNameHeap A meG ∗ addrNameHeap A peerG ∗
          runSaved s0 ∗
          memRegion fsp 0x208 ∗
          vecU8 A (fsp + 0x208#64) pt ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x230#64) 16) ∗
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)
        Q Qp (runOom s0) := by
    intro s_dcc hs_c1 hx19_c1 hx20_c1 hx21_c1 hx28_c1 htr_c1 hfs_c1
    by_cases hcapM : meG.name.cap = 0#64
    · have hpc1 : s_dcc.pc = runPc img ext 0xdcc := hs_c1.pc
      have hrun1 : s_dcc.status = .Running := hs_c1.run
      apply sepWPp_seq_inImage (mid := runPc img ext 0xde0) hs_c1.inv
      have hfn0 := run_fnOff
      code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_dpchk img.base
        (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 3532 4
      clear hfn0
      dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc1 ⊢
      generalize hfn1 :
        (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase1 at *
      examples_hide_fetches
      rw [hcapM] at hx21_c1
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun1])
      intro hinv_d
      have hs_d : InRun img ext s0 _ 0xde0 :=
        r3b_inRun_step hs_c1 (by simp only [arm64_norm]; rw [← hfn1])
          (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv_d (by simp only [calleeSavedVRegs, arm64_norm])
      refine r3b_sepWPp_weaken_pre ?_
        (hfrom_de0 _ hs_d
          (by simp only [arm64_norm, hx19_c1])
          (by simp only [arm64_norm, hx20_c1])
          ((by simp only [arm64_norm] : _ = s_dcc.trace).trans htr_c1)
          ((by simp only [arm64_norm] : _ = s_dcc.fs).trans hfs_c1))
      exact r3b_perm
        (r3b_perm_post
          (sepConj_mono (r3b_nameHeap_zero A meG hcapM)
            (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              addrNameHeap A peerG ∗ runSaved s0 ∗
              memRegion fsp 0x208 ∗ vecU8 A (fsp + 0x208#64) pt ∗
              (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
                ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                memRegion (fsp + 0x230#64) 16) ∗
              memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
              stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)))
          (by rw [emp_sepConj]))
        (by ac_rfl)
    · have hbeqM : (meG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcapM
      have hbeq21 : (s_dcc.readReg64 (.gpr 21#5) == 0#64) = false := by rw [hx21_c1]; exact hbeqM
      have hpc1 : s_dcc.pc = runPc img ext 0xdcc := hs_c1.pc
      have hrun1 : s_dcc.status = .Running := hs_c1.run
      have hsp1 : s_dcc.sp = fsp := hs_c1.sp
      have hsp_al1 : s_dcc.spAligned = true := hs_c1.spAligned_cur
      apply r3b_sepWPp_weaken_pre
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left (r3b_nameHeap_dealloc A meG hcapM))))))
      rw [show (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          (⌜LayoutOk meG.name.cap.toNat 1⌝ ∗
            A.live meG.name.ptr meG.name.cap.toNat 1 ∗
            memRegion meG.name.ptr meG.name.cap.toNat) ∗
          addrNameHeap A peerG ∗ runSaved s0 ∗
          memRegion fsp 0x208 ∗ vecU8 A (fsp + 0x208#64) pt ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x230#64) 16) ∗
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap) =
        ⌜LayoutOk meG.name.cap.toNat 1⌝ ∗
          (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            A.live meG.name.ptr meG.name.cap.toNat 1 ∗
            memRegion meG.name.ptr meG.name.cap.toNat ∗
            addrNameHeap A peerG ∗ runSaved s0 ∗
            memRegion fsp 0x208 ∗ vecU8 A (fsp + 0x208#64) pt ∗
            (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
              ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
              memRegion (fsp + 0x230#64) 16) ∗
            memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
            stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap) by ac_rfl]
      apply r3b_sepWPp_pure_left; intro hlayM
      apply sepWPp_seq_inImage (mid := (mProg img ext).fnAddr deallocName) hs_c1.inv
      have hfn0 := run_fnOff
      code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_dpchk img.base
        (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 3532 20
      clear hfn0
      dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc1 ⊢
      generalize hfn1 :
        (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase1 at *
      examples_hide_fetches
      wp_steps
      apply SepWP.done
        (by simp only [arm64_norm, ← hfn1, Program.fnAddr_rebase, run_fnOff, rustDealloc_fnOff])
        (by simp only [arm64_norm, hrun1])
      intro hinv_c2
      have hstk_split := r3b_stackAt_split_ge s_dcc.sp hext_le hsub64
      refine r3b_call_inImage
        (F := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          addrNameHeap A peerG ∗ runSaved s0 ∗
          memRegion fsp 0x208 ∗ vecU8 A (fsp + 0x208#64) pt ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x230#64) 16) ∗
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
          memRegion (fsp - BitVec.ofNat 64 (resStack - runFrame))
            (resStack - runFrame - extHookStack) ∗
          anyHeap)
        (s0 := s0) (meG.name.ptr, meG.name.cap.toNat, 1)
        hh.allocFs.dealloc hinv_c2
        (by simp only [arm64_norm, ← hfn1, Program.fnAddr_rebase, run_fnOff, rustDealloc_fnOff])
        (by simp only [arm64_norm, hrun1])
        (by simpa only [State.spAligned, arm64_norm] using hsp_al1)
        (retAddr := runPc img ext 0xde0)
        (by simp only [arm64_norm, runPc, mProg, tripleRatchetProgAtExt, ← hfn1])
        ?_
        (hnext := fun sm _ hinv_m hpcm hrunm hspm hcsm => ?_)
      · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
        simp only [sepConj_assoc]
        apply Entails.pure_right
        · exact ⟨by simp only [arm64_norm]; try rw [hx28_c1],
            by simp only [arm64_norm]; try rw [hx21_c1], by simp only [arm64_norm], hlayM⟩
        rw [hsp1] at hstk_split
        rw [hstk_split]
        simp only [arm64_norm, hsp1]
        exact Entails.of_eq (by dsimp only [fsp]; simp only [arm64_norm]; ac_rfl)
      · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
        simp only [sepConj_assoc]
        apply r3b_sepWPp_pure_left; intro hfs_m
        apply r3b_sepWPp_pure_left; intro htr_m
        have hs_m : InRun img ext s0 sm 0xde0 :=
          r3b_inRun_step hs_c1 hpcm hrunm (hspm.trans (by simp only [arm64_norm]))
            (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm])) hinv_m
            (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [calleeSavedVRegs, arm64_norm]))
        refine r3b_sepWPp_weaken_pre ?_
          (hfrom_de0 sm hs_m
            (hcsm.1.trans (by simp only [arm64_norm, hx19_c1]))
            (hcsm.2.1.trans (by simp only [arm64_norm, hx20_c1]))
            ((htr_m.trans (by simp only [arm64_norm] : _ = s_dcc.trace)).trans htr_c1)
            ((hfs_m.trans (by simp only [arm64_norm] : _ = s_dcc.fs)).trans hfs_c1))
        rw [hsp1] at hstk_split
        rw [hstk_split]
        simp only [arm64_norm, hsp1]
        exact Entails.of_eq (by dsimp only [fsp]; simp only [arm64_norm]; ac_rfl)
  have h220_split : memRegion fsp 0x220 =
      memRegion fsp 0x208 ∗
        memRegion (fsp + 0x208#64) 8 ∗ memRegion (fsp + 0x210#64) 8 ∗ memRegion (fsp + 0x218#64) 8 := by
    rw [ProofLib.memRegion_split' (b := fsp) (n := 0x208) (k := 24) (b' := fsp + 0x208#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x208#64) (n := 8) (k := 16) (b' := fsp + 0x210#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x210#64) (n := 8) (k := 8) (b' := fsp + 0x218#64) rfl (by bv_omega) (by decide)]
  have h350_split : memRegion (fsp + 0x350#64) (runLocalBytes - 0x350) =
      memRegion (fsp + 0x350#64) 0x30 ∗
        memRegion (fsp + 0x380#64) 8 ∗ memRegion (fsp + 0x388#64) 8 ∗
        memRegion (fsp + 0x390#64) (runLocalBytes - 0x390) := by
    rw [r3b_split_at fsp 0x350 0x30 runLocalBytes (by decide) (by decide),
        r3b_split_at fsp 0x380 8 runLocalBytes (by decide) (by decide),
        r3b_split_at fsp 0x388 8 runLocalBytes (by decide) (by decide)]
  have hprep :
      decResAt A (fsp + 0x320#64) (.ok pt) ∗
        (memRegion (fsp + 0x208#64) 8 ∗ memRegion (fsp + 0x210#64) 8 ∗ memRegion (fsp + 0x218#64) 8) ∗
        (memRegion (fsp + 0x380#64) 8 ∗ memRegion (fsp + 0x388#64) 8) ∗
        protocolAddressAt A peerG (fsp + 0x220#64) ∗
        protocolAddressAt A meG (fsp + 0x260#64) ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ∃∗ o0 : BitVec 64, ∃∗ o1 : BitVec 64, ∃∗ o2 : BitVec 64,
        ∃∗ s0w : BitVec 64, ∃∗ s1w : BitVec 64,
          ⌜cap.toNat < 2 ^ 63⌝ ∗
          ((fsp + 0x320#64) ↦₆₄ okTagVec) ∗
          ((fsp + 0x328#64) ↦₆₄ cap) ∗
          ((fsp + 0x330#64) ↦₆₄ ptr) ∗
          ((fsp + 0x338#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
          memRegion (fsp + 0x340#64) 16 ∗
          r3b_vecHeap A cap ptr pt ∗
          ((fsp + 0x208#64) ↦₆₄ o0) ∗ ((fsp + 0x210#64) ↦₆₄ o1) ∗ ((fsp + 0x218#64) ↦₆₄ o2) ∗
          ((fsp + 0x380#64) ↦₆₄ s0w) ∗ ((fsp + 0x388#64) ↦₆₄ s1w) ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x230#64) 16) ∗
          memRegion (fsp + 0x260#64) 32 ∗
          addrNameHeap A meG ∗ addrNameHeap A peerG := by
    dsimp only [decResAt, vecResultAt, vecU8]
    rw [ProofLib.memRegion_eight (fsp + 0x208#64), ProofLib.memRegion_eight (fsp + 0x210#64),
        ProofLib.memRegion_eight (fsp + 0x218#64), ProofLib.memRegion_eight (fsp + 0x380#64),
        ProofLib.memRegion_eight (fsp + 0x388#64),
        protocolAddressAt_eq_parts A peerG (fsp + 0x220#64),
        protocolAddressAt_eq_parts A meG (fsp + 0x260#64)]
    have hp_up : addrUpperAt (fsp + 0x220#64 + 16#64) peerG ⊢ memRegion (fsp + 0x230#64) 16 := by
      rw [show fsp + 0x220#64 + 16#64 = fsp + 0x230#64 by bv_omega]
      exact addrUpperAt_entails_memRegion _ _
    have hm_32 :
        ((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x260#64 + 8#64) ↦₆₄ meG.name.ptr) ∗
          addrUpperAt (fsp + 0x260#64 + 16#64) meG ⊢ memRegion (fsp + 0x260#64) 32 := by
      have hm_up : addrUpperAt (fsp + 0x260#64 + 16#64) meG ⊢ memRegion (fsp + 0x270#64) 16 := by
        rw [show fsp + 0x260#64 + 16#64 = fsp + 0x270#64 by bv_omega]
        exact addrUpperAt_entails_memRegion _ _
      rw [show fsp + 0x260#64 + 8#64 = fsp + 0x268#64 by bv_omega,
          ProofLib.memRegion_split' (b := fsp + 0x260#64) (n := 8) (k := 24)
            (b' := fsp + 0x268#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x268#64) (n := 8) (k := 16)
            (b' := fsp + 0x270#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _) hm_up)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro s1w
    apply Entails.sepExists_elim; intro s0w
    apply Entails.sepExists_elim; intro o2
    apply Entails.sepExists_elim; intro o1
    apply Entails.sepExists_elim; intro o0
    apply Entails.sepExists_elim; intro cap
    apply Entails.sepExists_elim; intro ptr
    rw [r3b_vecU8At_eq A (fsp + 0x320#64 + 8#64) cap ptr pt]
    refine Entails.trans
      (r3b_perm
        (sepConj_mono (r3b_vecHeap_cap_lt A cap ptr pt)
          (sepConj_mono hp_up (sepConj_mono hm_32
            (Entails.refl (((fsp + 0x320#64) ↦₆₄ okTagVec) ∗
              ((fsp + 0x320#64 + 8#64) ↦₆₄ cap) ∗
              ((fsp + 0x320#64 + 8#64 + 8#64) ↦₆₄ ptr) ∗
              ((fsp + 0x320#64 + 8#64 + 16#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
              memRegion (fsp + 0x320#64 + 32#64) 16 ∗
              ((fsp + 0x208#64) ↦₆₄ o0) ∗ ((fsp + 0x210#64) ↦₆₄ o1) ∗
              ((fsp + 0x218#64) ↦₆₄ o2) ∗
              ((fsp + 0x380#64) ↦₆₄ s0w) ∗ ((fsp + 0x388#64) ↦₆₄ s1w) ∗
              ((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
              ((fsp + 0x220#64 + 8#64) ↦₆₄ peerG.name.ptr) ∗
              addrNameHeap A meG ∗ addrNameHeap A peerG)))))
        (by ac_rfl)) ?_
    rw [sepConj_assoc]
    apply Entails.pure_left; intro hcap_lt
    refine Entails.sepExists_right cap (Entails.sepExists_right ptr
      (Entails.sepExists_right o0 (Entails.sepExists_right o1
        (Entails.sepExists_right o2 (Entails.sepExists_right s0w
          (Entails.sepExists_right s1w (Entails.pure_right hcap_lt ?_)))))))
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.of_eq (by ac_rfl)
  rw [show runFsp s0 = fsp from rfl, h220_split, h350_split]
  apply r3b_sepWPp_weaken_pre
    (r3b_perm
      (sepConj_mono_left
        (Q := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗
          memRegion fsp 0x208 ∗
          memRegion (fsp + 0x240#64) 0x20 ∗
          memRegion (fsp + 0x280#64) 0xa0 ∗
          memRegion (fsp + 0x350#64) 0x30 ∗
          memRegion (fsp + 0x390#64) (runLocalBytes - 0x390) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)
        hprep)
      (by ac_rfl))
  simp only [sepExists_sepConj_left]
  apply r3b_sepWPp_exists_left; intro cap
  apply r3b_sepWPp_exists_left; intro ptr
  apply r3b_sepWPp_exists_left; intro o0
  apply r3b_sepWPp_exists_left; intro o1
  apply r3b_sepWPp_exists_left; intro o2
  apply r3b_sepWPp_exists_left; intro s0w
  apply r3b_sepWPp_exists_left; intro s1w
  rw [sepConj_assoc]
  apply r3b_sepWPp_pure_left; intro hcap_lt
  have hok3 : ((okTagVec + 3#64) == 0#64) = false := rfl
  have hok2 : ((okTagVec + 2#64) != 0#64) = false := rfl
  have hcap_cmn : ((cap + 1#64) == 0#64) = false :=
    beq_eq_false_iff_ne.mpr (by intro h0; bv_omega)
  have hpc : s.pc = runPc img ext 0xd94 := hs.pc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp
  have hsp_al : s.spAligned = true := hs.spAligned_cur
  have hpack_c1 :
      (((fsp + 520#64) ↦₆₄ cap) ∗ ((fsp + 528#64) ↦₆₄ ptr) ∗
        ((fsp + 536#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗ r3b_vecHeap A cap ptr pt) ∗
      (((fsp + 800#64) ↦₆₄ okTagVec) ∗ ((fsp + 808#64) ↦₆₄ cap) ∗
        ((fsp + 816#64) ↦₆₄ ptr) ∗ ((fsp + 824#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
        memRegion (fsp + 832#64) 16 ∗
        memRegion (fsp + 576#64) 0x20 ∗ memRegion (fsp + 608#64) 32 ∗
        memRegion (fsp + 640#64) 0xa0 ∗ memRegion (fsp + 848#64) 0x30 ∗
        ((fsp + 896#64) ↦₆₄ ptr) ∗ ((fsp + 904#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
        memRegion (fsp + 912#64) (runLocalBytes - 0x390)) ⊢
      vecU8 A (fsp + 0x208#64) pt ∗ memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) := by
    have hv :
        ((fsp + 520#64) ↦₆₄ cap) ∗ ((fsp + 528#64) ↦₆₄ ptr) ∗
          ((fsp + 536#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗ r3b_vecHeap A cap ptr pt ⊢
        vecU8 A (fsp + 0x208#64) pt := by
      dsimp only [vecU8]
      refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
      rw [r3b_vecU8At_eq A (fsp + 0x208#64) cap ptr pt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Entails.refl _
    have hm320 :
        ((fsp + 800#64) ↦₆₄ okTagVec) ∗ ((fsp + 808#64) ↦₆₄ cap) ∗
          ((fsp + 816#64) ↦₆₄ ptr) ∗ ((fsp + 824#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
          memRegion (fsp + 832#64) 16 ⊢
        memRegion (fsp + 0x320#64) 48 := by
      have h32 := r3b_words4_entails_mem32 (fsp + 800#64) okTagVec cap ptr (BitVec.ofNat 64 pt.length)
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at h32
      rw [ProofLib.memRegion_split' (b := fsp + 0x320#64) (n := 32) (k := 16)
            (b' := fsp + 832#64) rfl (by bv_omega) (by decide)]
      exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left h32)
    have hm380 :
        ((fsp + 896#64) ↦₆₄ ptr) ∗ ((fsp + 904#64) ↦₆₄ BitVec.ofNat 64 pt.length) ⊢
        memRegion (fsp + 0x380#64) 16 := by
      rw [ProofLib.memRegion_split' (b := fsp + 0x380#64) (n := 8) (k := 8)
            (b' := fsp + 904#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
    have hback :
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) =
          memRegion (fsp + 576#64) 0x20 ∗
            (memRegion (fsp + 608#64) 32 ∗
              (memRegion (fsp + 640#64) 0xa0 ∗
                (memRegion (fsp + 0x320#64) 48 ∗
                  (memRegion (fsp + 848#64) 0x30 ∗
                    (memRegion (fsp + 0x380#64) 16 ∗
                      memRegion (fsp + 912#64) (runLocalBytes - 0x390)))))) := by
      rw [r3b_split_at fsp 0x240 0x20 runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x260 32 runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x280 0xa0 runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x320 48 runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x350 0x30 runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x380 16 runLocalBytes (by decide) (by decide)]
    rw [hback]
    exact sepConj_mono hv
      (r3b_perm
        (r3b_perm_post
          (sepConj_mono hm320 (sepConj_mono hm380
            (Entails.refl (memRegion (fsp + 576#64) 0x20 ∗ memRegion (fsp + 608#64) 32 ∗
              memRegion (fsp + 640#64) 0xa0 ∗ memRegion (fsp + 848#64) 0x30 ∗
              memRegion (fsp + 912#64) (runLocalBytes - 0x390)))))
          (by ac_rfl))
        (by ac_rfl))
  apply sepWPp_seq_inImage (mid := runPc img ext 0xdcc) hs.inv
  have hfn0 := run_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_dpchk img.base
    (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 3476 56
  clear hfn0
  dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc ⊢
  generalize hfn :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
  examples_hide_fetches
  rw [← hsp]
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
  intro hinv_c1
  have hs_c1 : InRun img ext s0 (r3b_stOf hinv_c1) 0xdcc :=
    r3b_inRun_step hs (by simp only [arm64_norm]; rw [← hfn])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv_c1 (by simp only [calleeSavedVRegs, arm64_norm])
  have hx19_c1 : (r3b_stOf hinv_c1).readReg64 (.gpr 19#5) = g.stores := by simp only [arm64_norm, hx19]
  have hx20_c1 : (r3b_stOf hinv_c1).readReg64 (.gpr 20#5) = g.res := by simp only [arm64_norm, hx20]
  have hx21_c1 : (r3b_stOf hinv_c1).readReg64 (.gpr 21#5) = meG.name.cap := by simp only [arm64_norm, hx21]
  have hx28_c1 : (r3b_stOf hinv_c1).readReg64 (.gpr 28#5) = meG.name.ptr := by simp only [arm64_norm, hx28]
  have htr_c1 : (r3b_stOf hinv_c1).trace = s.trace := by simp only [arm64_norm]
  have hfs_c1 : (r3b_stOf hinv_c1).fs = s.fs := by simp only [arm64_norm]
  refine r3b_sepWPp_weaken_pre ?_
    (hfrom_dcc _ hs_c1 hx19_c1 hx20_c1 hx21_c1 hx28_c1 htr_c1 hfs_c1)
  rw [hsp]
  exact r3b_perm
    (r3b_perm_post
      (sepConj_mono hpack_c1
        (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          addrNameHeap A meG ∗ addrNameHeap A peerG ∗
          runSaved s0 ∗
          memRegion fsp 0x208 ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x230#64) 16) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)))
      (by ac_rfl))
    (by ac_rfl)

set_option maxHeartbeats 1200000 in
theorem run_hop_recvP_ok_ext {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {g : RunCall} {peerV : AddrV} {rest : Bytes}
    {me : MeAtDispatch} {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    (hc : RunCallees img A ext B (slotsOf A img S needs))
    (hpksm : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromName)
      (pksmSlotSpec A img S))
    (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hres : runNeed B (slotsOf A img S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63)
    (hspb : resStack ≤ s0.sp.toNat)
    (he : AtRunEntry S img ext g s0)
    (hd : AtDispatch img ext g me s0 s)
    (hcall : g.c = .recv peerV)
    (hstdin : g.i.stdin = 3#8 :: rest)
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectK img ext A g s0 resStack Q Qp)
    (hjoin : JoinK img ext A g s0 resStack Q Qp) :
    ProofLib.SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (dispatchMem A img g me s0 resStack) Q Qp (runOom s0) := by
  cases me with
  | none => exact r3b_me_none hh hres hres64 he hd hcall hrej
  | some meV meG =>
    have hb : (img.base &&& 0xfff#64) = 0#64 := base_aligned himg
    have hbnds := runNeed_bounds hres hres64
    rcases hbnds with ⟨hrf_le, hsub63, hsub64, _, _, _, _, _, _, _, _, _, _,
      hpk_stk, hstk32, _, hext_le, _, _, _, hdp_stk, _⟩
    obtain ⟨hrest32, hcoins63, _, hfilesOk, hdecPkOk, hga⟩ :=
      hd.recvP_facts he hcall hstdin
    refine r3b_recv_head_some hd hcall ?_
    intro s1 peerG cw4 hiMe hs1 hx19_1 hx20_1 hx21_1 hx23_1 hx24_1 hx26_1 hx27_1 hx28_1
      htr1 hfs1 hpeer_val hme_val hdev_cw4 hhi
    let fsp := runFsp s0
    have hfsp_sub : resStack - runFrame ≤ fsp.toNat := by
      dsimp only [fsp, runFsp, runFrame] at hrf_le ⊢
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 0x2a50 ≤ s0.sp.toNat; omega))]
      change resStack - 0x2a50 ≤ s0.sp.toNat - 0x2a50
      omega
    have hinp_c : inputOf g.i g.c = 3#8 :: rest := by simp [hcall, inputOf, CallV.tag, hstdin]
    have hlen_ne : BitVec.ofNat 64 (3#8 :: rest).length ≠ 0#64 := by
      rw [List.length_cons]
      intro h0
      have hv := congrArg BitVec.toNat h0
      have hzero : (0#64).toNat = 0 := rfl
      rw [BitVec.toNat_ofNat, hzero] at hv
      have hmod : (rest.length + 1) % 2 ^ 64 = rest.length + 1 := Nat.mod_eq_of_lt (by omega)
      omega
    have hbeq_len : (BitVec.ofNat 64 (3#8 :: rest).length == 0#64) = false :=
      beq_eq_false_iff_ne.mpr hlen_ne
    have hsub1_nat : (BitVec.ofNat 64 (3#8 :: rest).length - 1#64).toNat = rest.length := by
      rw [List.length_cons]
      have h1 : BitVec.ofNat 64 (rest.length + 1) - 1#64 = BitVec.ofNat 64 rest.length := by
        rw [BitVec.ofNat_add]; bv_omega
      rw [h1, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have h280_pkm : memRegion (fsp + 0x280#64) (runLocalBytes - 0x280) =
        memRegion (fsp + 0x280#64) (0x4d0 - 0x280) ∗
          memRegion (fsp + 0x4d0#64) 248 ∗
          memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) := by
      rw [r3b_split_at fsp 0x280 (0x4d0 - 0x280) runLocalBytes (by decide) (by decide),
          r3b_split_at fsp 0x4d0 248 runLocalBytes (by decide) (by decide)]
    rw [hinp_c] at hx24_1
    rw [hinp_c, pointsToBytes_cons, h280_pkm]
    have hpc1 : s1.pc = runPc img ext 0x7c8 := hs1.pc
    have hrun1 : s1.status = .Running := hs1.run
    have hsp1 : s1.sp = fsp := hs1.sp
    have hsp1_al : s1.spAligned = true := hs1.spAligned_cur
    apply sepWPp_seq_inImage
      (mid := (mProg img ext).fnAddr CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromName)
      hs1.inv
    have hfn0 := run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_head img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 1992 16
    code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_pkpre img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 2436 16
    clear hfn0
    dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc1 ⊢
    generalize hfn :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
    examples_hide_fetches
    rw [← hsp1]
    wp_steps
    apply SepWP.done
      (by simp only [arm64_norm, ← hfn, Program.fnAddr_rebase, run_fnOff, r3b_pksm_fnOff])
      (by simp only [arm64_norm, hrun1])
    intro hinv_pk
    have hstk_pk := r3b_stackAt_split_ge s1.sp hpk_stk hsub64
    have htr_pre_pk : s0.trace <+: s1.trace := htr1 ▸ hd.trace
    refine r3b_call_raw
      (F := memRegion g.res runResSize ∗
        memRegion g.call 56 ∗
        storesAt A g.stores StoresGhost.opened ∗
        (g.inp ↦₈ 3#8) ∗
        coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        addrNameHeap A meG ∗
        addrNameHeap A peerG ∗
        runSaved s0 ∗
        memRegion fsp 0x220 ∗
        (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
          ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
        memRegion (fsp + 0x240#64) 0x20 ∗
        (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗
          ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
          ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
          ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
        memRegion (fsp + 0x280#64) (0x4d0 - 0x280) ∗
        memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ∗
        memRegion (fsp - BitVec.ofNat 64 (resStack - runFrame))
          (resStack - runFrame - CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromStack))
      (s0 := s0)
      ({ ptr := g.inp + 1#64, bytes := rest, ret := fsp + 0x4d0#64 } : PksmGhost)
      hpksm hinv_pk
      (by simp only [arm64_norm, tripleRatchetProgAtExt, ← hfn,
            Program.fnAddr_rebase, run_fnOff, r3b_pksm_fnOff])
      (by simp only [arm64_norm, hrun1])
      (by simpa only [State.spAligned, arm64_norm] using hsp1_al)
      (retAddr := runPc img ext 0x994)
      (by simp only [arm64_norm, runPc, mProg, tripleRatchetProgAtExt, ← hfn])
      ?_
      (hpanic := fun sf R' _ hp => by
        dsimp only [pksmSlotSpec, Spec.inImage] at hp
        rw [sepConj_assoc, satisfies_pure_sepConj] at hp
        exact hpanic sf _ (Or.inr (allocFailedIn_of_prefix htr_pre_pk hp.1.1)))
      (hoom := fun _ _ _ ho => by
        dsimp only [pksmSlotSpec, Spec.inImage] at ho
        exact (not_satisfies_false_sepConj ho).elim)
      (hnext := fun s2 hsteps_pk hinv2 hpcm2 hrun2 hsp2 hcsm2 => ?_)
    · dsimp only [pksmSlotSpec, Spec.inImage]
      simp only [sepConj_assoc]
      apply Entails.pure_right
      · exact hinv_pk
      apply Entails.pure_right
      · exact ⟨by simp only [arm64_norm]; try rw [hx23_1],
          by simp only [arm64_norm]; exact hsub1_nat,
          hrest32,
          by simp only [arm64_norm]; try rw [hsp1],
          by
            have hpk_spb : CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromStack ≤ fsp.toNat :=
              Nat.le_trans hpk_stk hfsp_sub
            simpa only [arm64_norm, hsp1] using hpk_spb⟩
      rw [hsp1] at hstk_pk
      rw [hstk_pk]
      simp only [arm64_norm]
      try rw [hsp1]
      exact Entails.of_eq (by dsimp only [fsp]; simp only [arm64_norm]; ac_rfl)
    · dsimp only [pksmSlotSpec, Spec.inImage]
      simp only [sepConj_assoc]
      apply r3b_sepWPp_pure_left; intro htr_pk
      have hs2 : InRun img ext s0 s2 0x994 :=
        r3b_inRun_step hs1 hpcm2 hrun2 (hsp2.trans (by simp only [arm64_norm]))
          (hcsm2.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm])) hinv2
          (hcsm2.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [calleeSavedVRegs, arm64_norm]))
      have hx19_2 : s2.readReg64 (.gpr 19#5) = g.stores := hcsm2.1.trans (by simp only [arm64_norm, hx19_1])
      have hx20_2 : s2.readReg64 (.gpr 20#5) = g.res := hcsm2.2.1.trans (by simp only [arm64_norm, hx20_1])
      have hx21_2 : s2.readReg64 (.gpr 21#5) = meG.name.cap := hcsm2.2.2.1.trans (by simp only [arm64_norm, hx21_1])
      have hx26_2 : s2.readReg64 (.gpr 26#5) = fsp + 0x4d0#64 :=
        hcsm2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm]; exact hx26_1)
      have hx27_2 : s2.readReg64 (.gpr 27#5) = fsp + 0x1750#64 :=
        hcsm2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm]; exact hx27_1)
      have hx28_2 : s2.readReg64 (.gpr 28#5) = meG.name.ptr :=
        hcsm2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm]; exact hx28_1)
      have htr2_eq : s2.trace = s.trace :=
        (htr_pk.trans (by simp only [arm64_norm])).trans htr1
      have hfs2_files : s2.fs.files = runFiles g.i :=
        ((r3b_files_of_trace_eq hh.fs hsteps_pk htr_pk).trans
          (by simp only [arm64_norm])).trans ((congrArg FsState.files hfs1).trans hd.fs)
      have htr2 : s0.trace <+: s2.trace := htr2_eq ▸ hd.trace
      have hhist2 : RunHistOk g.i s0 s2 :=
        ⟨hfs2_files, htr2_eq ▸ hd.stdout⟩
      rw [← hsp2, hs2.sp]
      rw [hsp1] at hstk_pk
      clear hfn
      apply r3b_sepWPp_weaken_pre
        (r3b_perm
          (sepConj_mono_left
            (Q := pksmResAt A (fsp + 0x4d0#64) (S.pksmParse rest) ∗
              ((g.inp + 1#64) ↦ₛ rest) ∗ logOff img ∗ A.pool ∗
              memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦₈ 3#8) ∗
              coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
              CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
              addrNameHeap A meG ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
              memRegion fsp 0x220 ∗
              (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
                ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
              memRegion (fsp + 0x240#64) 0x20 ∗
              (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
                ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
                ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
              memRegion (fsp + 0x280#64) (0x4d0 - 0x280) ∗
              memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8))
            (Entails.of_eq hstk_pk.symm))
          (by dsimp only [fsp]; ac_rfl))
      rcases _hparse : S.pksmParse rest with _ | pm
      ·
        (try rw [_hparse] at hga); dsimp only at hga
        refine r3b_sepWPp_weaken_pre ?_
          (r3b_recvP_parse_err meG peerG cw4 hiMe hh hdrop hstk32 hext_le hsub64 hs2
            hx19_2 hx20_2 hx21_2 hx26_2 hx28_2 htr2 hhist2 hga hrej)
        rw [hinp_c, pointsToBytes_cons]
        have hany :
            coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
              CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ logOff img ⊢ anyHeap :=
          entails_anyHeap _
        exact r3b_perm
          (r3b_perm_post
            (sepConj_mono hany
              (Entails.refl (pksmResAt A (fsp + 0x4d0#64) none ∗
                (g.inp ↦₈ 3#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
                stackAt fsp (resStack - runFrame) ∗ A.pool ∗
                memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                storesAt A g.stores StoresGhost.opened ∗
                addrNameHeap A meG ∗ addrNameHeap A peerG ∗ runSaved s0 ∗
                memRegion fsp 0x220 ∗
                (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                  ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
                  ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
                memRegion (fsp + 0x240#64) 0x20 ∗
                (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
                  ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
                  ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
                memRegion (fsp + 0x280#64) (0x4d0 - 0x280) ∗
                memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8))))
            (by dsimp only [fsp]; ac_rfl))
          (by dsimp only [fsp, pksmResAt]; ac_rfl)
      ·
        (try rw [_hparse] at hga); dsimp only at hga
        have hdp_ok : S.decPkOk (runFiles g.i) (addrValOf peerV) (addrValOf meV) pm :=
          hdecPkOk pm (by first | exact rfl | exact _hparse)
        have hloc_shuf :
            pksmResAt A (fsp + 0x4d0#64) (some pm) ∗
              (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
                ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
              (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
                ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
                ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
              addrNameHeap A peerG ∗ addrNameHeap A meG ∗
              memRegion fsp 0x220 ∗
              memRegion (fsp + 0x280#64) (0x4d0 - 0x280) ∗
              memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ⊢
            ∃∗ pmG : PreKeyMsgGhost, ∃∗ w : r3b_W30,
              ∃∗ t0 : r3b_W5, ∃∗ t : r3b_W5, ∃∗ z : r3b_W30, ∃∗ m : r3b_W30,
                ⌜pmG.msg.pqCap.toNat < 2 ^ 63⌝ ∗
                ((fsp + 0x4d0#64) ↦₆₄ pmG.msg.pqCap) ∗
                r3b_slot30 (fsp + 0x4d8#64) w ∗
                r3b_slot5 (fsp + 0x2a0#64) t ∗
                r3b_slot30 (fsp + 0x3e0#64) z ∗
                r3b_slot30 (fsp + 0x1750#64) m ∗
                r3b_slot5 fsp t0 ∗
                ((((fsp + 0x4d0#64) ↦₆₄ pmG.msg.pqCap) ∗ r3b_slot30 (fsp + 0x4d8#64) w) -∗
                  preKeyMsgAt A pmG (fsp + 0x4d0#64) pm) ∗
                protocolAddressAt A peerG (fsp + 0x220#64) ∗
                protocolAddressAt A meG (fsp + 0x260#64) ∗
                memRegion (fsp + 0x28#64) (0x220 - 0x28) ∗
                memRegion (fsp + 0x280#64) 0x20 ∗
                memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) ∗
                memRegion (fsp + 0x320#64) 48 ∗
                memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
                memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
                memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840) ∗
                anyHeap := by
          dsimp only [pksmResAt]
          have hf0 : memRegion fsp 0x220 =
              memRegion fsp 40 ∗ memRegion (fsp + 0x28#64) (0x220 - 0x28) :=
            ProofLib.memRegion_split' (b := fsp) (n := 40) (k := 0x220 - 0x28)
              (b' := fsp + 0x28#64) rfl (by bv_omega) (by decide)
          have hf280 : memRegion (fsp + 0x280#64) (0x4d0 - 0x280) =
              memRegion (fsp + 0x280#64) 0x20 ∗
                memRegion (fsp + 0x2a0#64) 40 ∗
                memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) ∗
                memRegion (fsp + 0x320#64) 48 ∗
                memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
                memRegion (fsp + 0x3e0#64) 240 := by
            rw [r3b_split_at fsp 0x280 0x20 0x4d0 (by decide) (by decide),
                r3b_split_at fsp 0x2a0 40 0x4d0 (by decide) (by decide),
                r3b_split_at fsp 0x2c8 (0x320 - 0x2c8) 0x4d0 (by decide) (by decide),
                r3b_split_at fsp 0x320 48 0x4d0 (by decide) (by decide),
                r3b_split_at fsp 0x350 (0x3e0 - 0x350) 0x4d0 (by decide) (by decide)]
          have hf5c8 : memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) =
              memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
                memRegion (fsp + 0x1750#64) 240 ∗
                memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840) := by
            rw [r3b_split_at fsp 0x5c8 (0x1750 - 0x5c8) runLocalBytes (by decide) (by decide),
                r3b_split_at fsp 0x1750 240 runLocalBytes (by decide) (by decide)]
          rw [hf0, hf280, hf5c8]
          have hp_pack := r3b_addr_pack A peerG (fsp + 0x220#64) (fsp + 0x228#64)
            (fsp + 0x230#64) (fsp + 0x238#64) cw4 (by bv_omega) (by bv_omega) (by bv_omega) hdev_cw4
          have hm_pack := r3b_addr_pack A meG (fsp + 0x260#64) (fsp + 0x268#64)
            (fsp + 0x270#64) (fsp + 0x278#64) hiMe (by bv_omega) (by bv_omega) (by bv_omega) hhi
          simp only [sepExists_sepConj_left]
          apply Entails.sepExists_elim; intro pmG
          refine Entails.trans
            (r3b_perm
              (sepConj_mono (r3b_pkm_to_words A pmG (fsp + 0x4d0#64) pm)
                (sepConj_mono (r3b_mem40_to_slot5 fsp)
                  (sepConj_mono (r3b_mem40_to_slot5 (fsp + 0x2a0#64))
                    (sepConj_mono (r3b_mem240_to_slot30 (fsp + 0x3e0#64))
                      (sepConj_mono (r3b_mem240_to_slot30 (fsp + 0x1750#64))
                        (sepConj_mono hp_pack (sepConj_mono hm_pack
                          (Entails.refl (memRegion (fsp + 0x28#64) (0x220 - 0x28) ∗
                            memRegion (fsp + 0x280#64) 0x20 ∗
                            memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) ∗
                            memRegion (fsp + 0x320#64) 48 ∗
                            memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
                            memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
                            memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840) ∗
                            anyHeap)))))))))
              (by ac_rfl)) ?_
          simp only [sepExists_sepConj_left, sepExists_sepConj_right]
          apply Entails.sepExists_elim; intro m
          apply Entails.sepExists_elim; intro z
          apply Entails.sepExists_elim; intro t
          apply Entails.sepExists_elim; intro t0
          apply Entails.sepExists_elim; intro w
          simp only [sepConj_assoc]
          apply Entails.pure_left; intro hcap_pm
          have ha4d8 : fsp + 0x4d0#64 + 8#64 = fsp + 0x4d8#64 := by bv_omega
          rw [ha4d8]
          exact Entails.sepExists_right pmG (Entails.sepExists_right w
            (Entails.sepExists_right t0 (Entails.sepExists_right t
              (Entails.sepExists_right z (Entails.sepExists_right m
                (Entails.pure_right hcap_pm (Entails.of_eq (by ac_rfl))))))))
        apply r3b_sepWPp_weaken_pre
          (r3b_perm
            (sepConj_mono_left
              (Q := (g.inp ↦₈ 3#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
                stackAt fsp (resStack - runFrame) ∗ A.pool ∗
                coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
                CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ logOff img ∗
                memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                storesAt A g.stores StoresGhost.opened ∗
                runSaved s0 ∗ memRegion (fsp + 0x240#64) 0x20)
              hloc_shuf)
            (by dsimp only [fsp]; ac_rfl))
        simp only [sepExists_sepConj_left]
        apply r3b_sepWPp_exists_left; intro pmG
        apply r3b_sepWPp_exists_left; intro w
        apply r3b_sepWPp_exists_left; intro t0
        apply r3b_sepWPp_exists_left; intro t
        apply r3b_sepWPp_exists_left; intro z
        apply r3b_sepWPp_exists_left; intro m
        simp only [sepConj_assoc]
        apply r3b_sepWPp_pure_left; intro hcap_pm
        refine r3b_sepWPp_weaken_pre (Entails.of_eq (by dsimp only [fsp]))
          (r3b_recvP_shuf1 pmG.msg.pqCap w t z m _ hs2 hcap_pm hx26_2 hx27_2 ?_)
        intro s3 hs3 hx8_3 hx9_3 hx19_3 hx20_3 hx21_3 hx26_3 hx28_3 htr3 hfs3
        rw [hx19_2] at hx19_3
        rw [hx20_2] at hx20_3
        rw [hx21_2] at hx21_3
        rw [hx26_2] at hx26_3
        rw [hx28_2] at hx28_3
        let shuf2F : SepProp :=
          (((runFsp s0 + 1232#64) ↦₆₄ pmG.msg.pqCap ∗ r3b_slot30 (runFsp s0 + 1240#64) w) -∗
            preKeyMsgAt A pmG (runFsp s0 + 1232#64) pm) ∗
          memRegion (runFsp s0 + 672#64) 40 ∗
          memRegion (runFsp s0 + 5968#64) 240 ∗
          protocolAddressAt A peerG (runFsp s0 + 544#64) ∗
          protocolAddressAt A meG (runFsp s0 + 608#64) ∗
          memRegion (runFsp s0 + 40#64) (544 - 40) ∗
          memRegion (runFsp s0 + 640#64) 32 ∗
          memRegion (runFsp s0 + 712#64) (800 - 712) ∗
          memRegion (runFsp s0 + 800#64) 48 ∗
          memRegion (runFsp s0 + 848#64) (992 - 848) ∗
          memRegion (runFsp s0 + 1480#64) (5968 - 1480) ∗
          memRegion (runFsp s0 + 6208#64) (runLocalBytes - 6208) ∗
          anyHeap ∗
          (g.inp ↦₈ 3#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool ∗
          coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
          CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
          logOff img ∗
          memRegion g.res runResSize ∗
          memRegion g.call 56 ∗
          storesAt A g.stores StoresGhost.opened ∗
          runSaved s0 ∗
          memRegion (runFsp s0 + 576#64) 32
        refine r3b_sepWPp_weaken_pre (Entails.of_eq (by dsimp only [fsp, shuf2F]; ac_rfl))
          (r3b_recvP_shuf2 g.stores pmG.msg.pqCap t0 w z shuf2F hb hs3 hx8_3 hx9_3 hx19_3 ?_)
        intro sc hinv_c hpc_c hrun_c hsp_c hsp_al_c hlr_c
          hx0_c hx1_c hx2_c hx3_c hx4_c hx5_c hx6_c hx7_c hx8_c
          hx19_c hx20_c hx21_c hx26_c hx28_c hfp_c hvregs_c htr_c hfs_c
        rw [hx20_3] at hx20_c
        rw [hx21_3] at hx21_c
        rw [hx26_3] at hx26_c
        rw [hx28_3] at hx28_c
        have htr_sc_eq : sc.trace = s2.trace := htr_c.trans htr3
        have hfs_sc_files : sc.fs.files = runFiles g.i :=
          (congrArg FsState.files (hfs_c.trans hfs3)).trans hfs2_files
        have htr_sc : s0.trace <+: sc.trace := htr_sc_eq ▸ htr2
        let dpX : DecPkGhost :=
          { peer := peerG
            peerA := fsp + 0x220#64
            me := meG
            meA := fsp + 0x260#64
            stores := g.stores
            ret := fsp + 0x320#64
            coinsP := g.coins
            F := runFiles g.i
            coins := MainHops.coinsOf g.i
            msgA := fsp + 0x4d0#64
            msgG := pmG
            msg := pm }
        refine r3b_call_raw
          (F := memRegion (fsp + 0x3e0#64) 240 ∗
            memRegion (fsp + 0x2a0#64) 40 ∗
            memRegion (fsp + 0x1750#64) 240 ∗
            memRegion (fsp + 0x28#64) (0x220 - 0x28) ∗
            memRegion (fsp + 0x280#64) 0x20 ∗
            memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) ∗
            memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
            memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
            memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840) ∗
            anyHeap ∗
            (g.inp ↦₈ 3#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
            memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            runSaved s0 ∗ memRegion (fsp + 0x240#64) 0x20)
          (s0 := s0) dpX
          (hc.decryptPrekey (resStack - runFrame) hdp_stk hsub63) hinv_c
          hpc_c hrun_c hsp_al_c (retAddr := runPc img ext 0xb78) hlr_c
          ?_
          (hpanic := fun sf R' _ hp => by
            dsimp only [slotsOf, mkSlot, decPkSlotSpec, Spec.inImage, dpX] at hp
            rw [sepConj_assoc, satisfies_pure_sepConj] at hp
            rcases hp.1 with hnone | halloc
            · rw [hpeer_val, hme_val] at hnone
              apply hpanic sf _ (Or.inl ?_)
              rw [hga, hnone]; rfl
            · exact hpanic sf _ (Or.inr (allocFailedIn_of_prefix htr_sc halloc)))
          (hoom := fun _ _ _ ho => by
            dsimp only [slotsOf, mkSlot, decPkSlotSpec, Spec.inImage, dpX] at ho
            exact (not_satisfies_false_sepConj ho).elim)
          (hnext := fun s4 _ hinv4 hpcm4 hrun4 hsp4 hcsm4 => ?_)
        · dsimp only [slotsOf, mkSlot, decPkSlotSpec, Spec.inImage, slotFrame, dpX]
          simp only [sepConj_assoc]
          apply Entails.pure_right
          · exact hinv_c
          apply Entails.pure_right
          · exact ⟨hx0_c, hx1_c, hx2_c, hx3_c, hx4_c, hx5_c, hx6_c, hx7_c, hx8_c, hfs_sc_files,
              by rw [hpeer_val, hme_val]; exact hfilesOk,
              by rw [hpeer_val, hme_val]; exact hdp_ok,
              hsp_c ▸ hfsp_sub⟩
          apply Entails.pure_right
          · exact hcoins63
          rw [hsp_c]
          have hpkm_restore :
              ((fsp + 0x4d0#64) ↦₆₄ pmG.msg.pqCap) ∗ r3b_slot30 (fsp + 0x4d8#64) w ∗
                ((((fsp + 0x4d0#64) ↦₆₄ pmG.msg.pqCap) ∗ r3b_slot30 (fsp + 0x4d8#64) w) -∗
                  preKeyMsgAt A pmG (fsp + 0x4d0#64) pm) ⊢
              preKeyMsgAt A pmG (fsp + 0x4d0#64) pm := by
            rw [← sepConj_assoc]
            exact Entails.wand_elim _ _
          exact r3b_perm
            (r3b_perm_post
              (sepConj_mono hpkm_restore
                (Entails.refl ((fsp ↦₆₄ oneTimeVt img) ∗ ((fsp + 8#64) ↦₆₄ (g.stores + 0x50#64)) ∗
                  ((fsp + 16#64) ↦₆₄ signedVt img) ∗ ((fsp + 24#64) ↦₆₄ (g.stores + 0x78#64)) ∗
                  ((fsp + 32#64) ↦₆₄ kyberVt img) ∗
                  memRegion (fsp + 0x3e0#64) 240 ∗
                  memRegion (fsp + 0x2a0#64) 40 ∗ memRegion (fsp + 0x1750#64) 240 ∗
                  protocolAddressAt A peerG (fsp + 0x220#64) ∗
                  protocolAddressAt A meG (fsp + 0x260#64) ∗
                  memRegion (fsp + 0x28#64) (0x220 - 0x28) ∗
                  memRegion (fsp + 0x280#64) 0x20 ∗
                  memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) ∗
                  memRegion (fsp + 0x320#64) 48 ∗
                  memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
                  memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
                  memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840) ∗
                  anyHeap ∗
                  (g.inp ↦₈ 3#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
                  stackAt fsp (resStack - runFrame) ∗ A.pool ∗
                  coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
                  CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ logOff img ∗
                  memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                  storesAt A g.stores StoresGhost.opened ∗
                  runSaved s0 ∗ memRegion (fsp + 0x240#64) 0x20)))
              (by dsimp only [fsp, shuf2F]; ac_rfl))
            (by dsimp only [fsp, shuf2F]; ac_rfl)
        · dsimp only [slotsOf, mkSlot, decPkSlotSpec, Spec.inImage, dpX]
          simp only [sepExists_sepConj_left]
          apply r3b_sepWPp_exists_left; intro g'
          apply r3b_sepWPp_exists_left; intro e
          simp only [sepConj_assoc]
          apply r3b_sepWPp_pure_left; rintro ⟨⟨htr_dp, hfs_dp, hout_str_dp⟩, hout_dp⟩
          have hs4 : InRun img ext s0 s4 0xb78 :=
            r3b_inRun_step hs3 hpcm4 hrun4 (hsp4.trans (hsp_c.trans hs3.sp.symm))
              (hcsm4.2.2.2.2.2.2.2.2.2.2.1.trans hfp_c) hinv4
              (hcsm4.2.2.2.2.2.2.2.2.2.2.2.trans hvregs_c)
          have htr4 : s0.trace <+: s4.trace := htr_sc.trans htr_dp
          have hhist4 : RunHistOk g.i s0 s4 :=
            ⟨hfs_dp.trans hfs_sc_files, hout_str_dp.trans (htr_sc_eq ▸ htr2_eq ▸ hd.stdout)⟩
          have hx19_4 : s4.readReg64 (.gpr 19#5) = g.stores := hcsm4.1.trans hx19_c
          have hx20_4 : s4.readReg64 (.gpr 20#5) = g.res := hcsm4.2.1.trans hx20_c
          have hx21_4 : s4.readReg64 (.gpr 21#5) = meG.name.cap := hcsm4.2.2.1.trans hx21_c
          have hx26_4 : s4.readReg64 (.gpr 26#5) = fsp + 0x4d0#64 :=
            hcsm4.2.2.2.2.2.2.2.1.trans hx26_c
          have hx28_4 : s4.readReg64 (.gpr 28#5) = meG.name.ptr :=
            hcsm4.2.2.2.2.2.2.2.2.2.1.trans hx28_c
          rw [hsp_c]
          have hpc4 : s4.pc = runPc img ext 0xb78 := hs4.pc
          have hrun4' : s4.status = .Running := hs4.run
          have hsp4' : s4.sp = fsp := hs4.sp
          have hsp4_al : s4.spAligned = true := hs4.spAligned_cur
          apply sepWPp_seq_inImage (mid := (mProg img ext).fnAddr cliDropPreKeyMsgName) hs4.inv
          have hfn0 := run_fnOff
          code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_pkdrop img.base
            (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 2936 8
          clear hfn0
          dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc4 ⊢
          generalize hfn2 :
            (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase2 at *
          examples_hide_fetches
          wp_steps
          apply SepWP.done
            (by simp only [arm64_norm, ← hfn2, Program.fnAddr_rebase, run_fnOff, r3b_dropPkm_fnOff])
            (by simp only [arm64_norm, hrun4'])
          intro hinv_dm
          refine r3b_call_inImage
            (F := storesAt A g.stores g' ∗
              decResAt A (fsp + 0x320#64) e ∗
              protocolAddressAt A peerG (fsp + 0x220#64) ∗
              protocolAddressAt A meG (fsp + 0x260#64) ∗
              (fsp ↦₆₄ oneTimeVt img) ∗ ((fsp + 8#64) ↦₆₄ (g.stores + 0x50#64)) ∗
              ((fsp + 16#64) ↦₆₄ signedVt img) ∗ ((fsp + 24#64) ↦₆₄ (g.stores + 0x78#64)) ∗
              ((fsp + 32#64) ↦₆₄ kyberVt img) ∗
              logOff img ∗ anyHeap ∗
              memRegion (fsp + 0x3e0#64) 240 ∗
              memRegion (fsp + 0x2a0#64) 40 ∗
              memRegion (fsp + 0x1750#64) 240 ∗
              memRegion (fsp + 0x28#64) (0x220 - 0x28) ∗
              memRegion (fsp + 0x280#64) 0x20 ∗
              memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) ∗
              memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
              memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
              memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840) ∗
              anyHeap ∗
              (g.inp ↦₈ 3#8) ∗ ((g.inp + 1#64) ↦ₛ rest) ∗
              memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              runSaved s0 ∗ memRegion (fsp + 0x240#64) 0x20)
            (s0 := s0) ⟨fsp + 0x4d0#64, pmG, pm⟩
            (cliDropPreKeyMsg_ok hh.alloc (resStack - runFrame) hstk32 hsub64) hinv_dm
            (by simp only [arm64_norm, ← hfn2, Program.fnAddr_rebase, run_fnOff, r3b_dropPkm_fnOff])
            (by simp only [arm64_norm, hrun4'])
            (by simpa only [State.spAligned, arm64_norm] using hsp4_al)
            (retAddr := runPc img ext 0xb80)
            (by simp only [arm64_norm, runPc, mProg, tripleRatchetProgAtExt, ← hfn2])
            ?_
            (hnext := fun s5 hsteps_dm hinv5 hpcm5 hrun5 hsp5 hcsm5 => ?_)
          · dsimp only [dropPreKeyMsgSpec]
            simp only [sepConj_assoc]
            apply Entails.pure_right
            · dsimp only [fsp]; simp only [arm64_norm]
            simp only [arm64_norm]
            try rw [hsp4']
            exact Entails.of_eq (by dsimp only [fsp]; simp only [arm64_norm]; ac_rfl)
          · dsimp only [dropPreKeyMsgSpec]
            simp only [sepConj_assoc]
            apply r3b_sepWPp_pure_left; intro htr_dm
            have htr5_eq : s5.trace = s4.trace := htr_dm.trans (by simp only [arm64_norm])
            have hfs5_eq : s5.fs.files = s4.fs.files :=
              (r3b_files_of_trace_eq hh.fs hsteps_dm htr_dm).trans (by simp only [arm64_norm])
            have hs5_pre : InRun img ext s0 s5 0xb80 :=
              r3b_inRun_step hs4 hpcm5 hrun5 (hsp5.trans (by simp only [arm64_norm]))
                (hcsm5.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm])) hinv5
                (hcsm5.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [calleeSavedVRegs, arm64_norm]))
            have hx19_5 : s5.readReg64 (.gpr 19#5) = g.stores := hcsm5.1.trans (by simp only [arm64_norm, hx19_4])
            have hx20_5 : s5.readReg64 (.gpr 20#5) = g.res := hcsm5.2.1.trans (by simp only [arm64_norm, hx20_4])
            have hx21_5 : s5.readReg64 (.gpr 21#5) = meG.name.cap := hcsm5.2.2.1.trans (by simp only [arm64_norm, hx21_4])
            have hx26_5 : s5.readReg64 (.gpr 26#5) = fsp + 0x4d0#64 :=
              hcsm5.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm]; exact hx26_4)
            have hx28_5 : s5.readReg64 (.gpr 28#5) = meG.name.ptr :=
              hcsm5.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, hx28_4])
            rw [← hsp5, hs5_pre.sp]
            clear hfn2
            have hpc5 : s5.pc = runPc img ext 0xb80 := hs5_pre.pc
            have hrun5' : s5.status = .Running := hs5_pre.run
            apply sepWPp_seq_inImage (mid := runPc img ext 0xd94) hs5_pre.inv
            have hfn0 := run_fnOff
            code_fetches_range CryptoVerification.libsignalSessionCode r3b_dec_pkdrop img.base
              (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 2944 4
            clear hfn0
            dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc5 ⊢
            generalize hfn3 :
              (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase3 at *
            examples_hide_fetches
            wp_steps
            apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun5'])
            intro hinv6
            have hs6 : InRun img ext s0 (r3b_stOf hinv6) 0xd94 :=
              r3b_inRun_step hs5_pre (by simp only [arm64_norm, runPc, mProg, tripleRatchetProgAtExt, ← hfn3])
                (by simp only [arm64_norm, hrun5']) (by simp only [arm64_norm])
                (by simp only [arm64_norm]) hinv6 (by simp only [calleeSavedVRegs, arm64_norm])
            have htr6_eq : (r3b_stOf hinv6).trace = s4.trace :=
              (by simp only [arm64_norm] : (r3b_stOf hinv6).trace = s5.trace).trans htr5_eq
            have hfs6_eq : (r3b_stOf hinv6).fs.files = s4.fs.files :=
              (by simp only [arm64_norm] : (r3b_stOf hinv6).fs.files = s5.fs.files).trans hfs5_eq
            have htr6 : s0.trace <+: (r3b_stOf hinv6).trace := htr6_eq ▸ htr4
            have hhist6 : RunHistOk g.i s0 (r3b_stOf hinv6) := r3b_hist_of_eq htr6_eq hfs6_eq hhist4
            have hclean6 :
                (memRegion (fsp + 0x4d0#64) 248 ∗
                  (fsp ↦₆₄ oneTimeVt img) ∗ ((fsp + 8#64) ↦₆₄ (g.stores + 0x50#64)) ∗
                  ((fsp + 16#64) ↦₆₄ signedVt img) ∗ ((fsp + 24#64) ↦₆₄ (g.stores + 0x78#64)) ∗
                  ((fsp + 32#64) ↦₆₄ kyberVt img) ∗
                  memRegion (fsp + 0x28#64) (0x220 - 0x28) ∗
                  memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2a0#64) 40 ∗
                  memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) ∗
                  memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
                  memRegion (fsp + 0x3e0#64) 240 ∗
                  memRegion (fsp + 0x1750#64) 240 ∗
                  memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
                  memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840)) ∗
                (logOff img ∗ anyHeap ∗ anyHeap) ⊢
                memRegion fsp 0x220 ∗
                  memRegion (fsp + 0x280#64) 0xa0 ∗
                  memRegion (fsp + 0x350#64) (runLocalBytes - 0x350) ∗
                  anyHeap := by
              have h0_220 :
                  (fsp ↦₆₄ oneTimeVt img) ∗ ((fsp + 8#64) ↦₆₄ (g.stores + 0x50#64)) ∗
                    ((fsp + 16#64) ↦₆₄ signedVt img) ∗ ((fsp + 24#64) ↦₆₄ (g.stores + 0x78#64)) ∗
                    ((fsp + 32#64) ↦₆₄ kyberVt img) ∗
                    memRegion (fsp + 0x28#64) (0x220 - 0x28) ⊢
                  memRegion fsp 0x220 := by
                have h40 := r3b_slot5_to_mem40 fsp
                  ⟨oneTimeVt img, g.stores + 0x50#64, signedVt img, g.stores + 0x78#64, kyberVt img⟩
                dsimp only [r3b_slot5] at h40
                rw [ProofLib.memRegion_split' (b := fsp) (n := 40) (k := 0x220 - 0x28)
                      (b' := fsp + 0x28#64) rfl (by bv_omega) (by decide)]
                exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left h40)
              have h280_a0 :
                  memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2a0#64) 40 ∗
                    memRegion (fsp + 0x2c8#64) (0x320 - 0x2c8) =
                  memRegion (fsp + 0x280#64) 0xa0 := by
                rw [r3b_split_at fsp 0x280 0x20 0x320 (by decide) (by decide),
                    r3b_split_at fsp 0x2a0 40 0x320 (by decide) (by decide)]
              have h350_all :
                  memRegion (fsp + 0x4d0#64) 248 ∗
                    memRegion (fsp + 0x350#64) (0x3e0 - 0x350) ∗
                    memRegion (fsp + 0x3e0#64) 240 ∗
                    memRegion (fsp + 0x1750#64) 240 ∗
                    memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
                    memRegion (fsp + 0x1840#64) (runLocalBytes - 0x1840) =
                  memRegion (fsp + 0x350#64) (runLocalBytes - 0x350) := by
                rw [r3b_split_at fsp 0x350 (0x3e0 - 0x350) runLocalBytes (by decide) (by decide),
                    r3b_split_at fsp 0x3e0 240 runLocalBytes (by decide) (by decide),
                    r3b_split_at fsp 0x4d0 248 runLocalBytes (by decide) (by decide),
                    r3b_split_at fsp 0x5c8 (0x1750 - 0x5c8) runLocalBytes (by decide) (by decide),
                    r3b_split_at fsp 0x1750 240 runLocalBytes (by decide) (by decide)]
                ac_rfl
              exact r3b_perm
                (sepConj_mono h0_220
                  (sepConj_mono (Entails.of_eq h280_a0)
                    (sepConj_mono (Entails.of_eq h350_all)
                      (entails_anyHeap (logOff img ∗ anyHeap ∗ anyHeap)))))
                (by ac_rfl)
            have hinp_back : (g.inp ↦₈ 3#8) ∗ ((g.inp + 1#64) ↦ₛ rest) = (g.inp ↦ₛ inputOf g.i g.c) := by
              rw [hinp_c, pointsToBytes_cons]
            cases e with
            | error err =>
              have hans_err : g.a = some none := by
                have hnone := hout_dp.2.2
                rw [hpeer_val, hme_val] at hnone
                rw [hga, hnone]; rfl
              refine r3b_sepWPp_weaken_pre ?_
                (r3b_recvP_dec_err g' err peerG meG hh hdrop hstk32 hext_le hsub64 hs6
                  (by simp only [arm64_norm, hx19_5])
                  (by simp only [arm64_norm, hx20_5])
                  (by simp only [arm64_norm, hx21_5])
                  (by dsimp only [fsp] at hx26_5; simp only [arm64_norm, hx26_5])
                  (by simp only [arm64_norm, hx28_5])
                  htr6 hhist6 hans_err hrej)
              exact r3b_perm
                (r3b_perm_post
                  (sepConj_mono hclean6
                    (sepConj_mono (Entails.of_eq hinp_back)
                      (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                        storesAt A g.stores g' ∗
                        protocolAddressAt A peerG (fsp + 0x220#64) ∗
                        protocolAddressAt A meG (fsp + 0x260#64) ∗
                        runSaved s0 ∗ memRegion (fsp + 0x240#64) 0x20 ∗
                        decResAt A (fsp + 0x320#64) (.error err) ∗
                        stackAt fsp (resStack - runFrame) ∗ A.pool))))
                  (by dsimp only [fsp]; ac_rfl))
                (by dsimp only [fsp]; ac_rfl)
            | ok pt =>
              have hout_ok : g.a = some (some (namedWrites g'.writes, pt)) ∧
                  ∀ pw ∈ g'.writes, cliWrOk pw.1 := by
                rcases hout_dp.2.2 with ⟨hsome, hwrok⟩
                rw [hpeer_val, hme_val] at hsome
                exact ⟨by rw [hga, hsome]; rfl, hwrok⟩
              refine r3b_sepWPp_weaken_pre ?_
                (r3b_recvP_dec_ok g' pt peerG meG hh hext_le hsub64 hs6
                  (by simp only [arm64_norm, hx19_5])
                  (by simp only [arm64_norm, hx20_5])
                  (by simp only [arm64_norm, hx21_5])
                  (by simp only [arm64_norm, hx28_5])
                  htr6 hhist6 hout_ok.1 hout_ok.2 hjoin)
              exact r3b_perm
                (r3b_perm_post
                  (sepConj_mono hclean6
                    (sepConj_mono (Entails.of_eq hinp_back)
                      (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                        storesAt A g.stores g' ∗
                        protocolAddressAt A peerG (fsp + 0x220#64) ∗
                        protocolAddressAt A meG (fsp + 0x260#64) ∗
                        runSaved s0 ∗ memRegion (fsp + 0x240#64) 0x20 ∗
                        decResAt A (fsp + 0x320#64) (.ok pt) ∗
                        stackAt fsp (resStack - runFrame) ∗ A.pool))))
                  (by dsimp only [fsp]; ac_rfl))
                (by dsimp only [fsp]; ac_rfl)

theorem run_hop_recvBad_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {g : RunCall} {peerV : AddrV}
    {me : MeAtDispatch} {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A ext)
    (hres : runNeed B (slotsOf A img S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63)
    (he : AtRunEntry S img ext g s0)
    (hd : AtDispatch img ext g me s0 s)
    (hcall : g.c = .recv peerV)
    (hbad : g.i.stdin = [] ∨ ∃ t rest, g.i.stdin = t :: rest ∧ t ≠ 2#8 ∧ t ≠ 3#8)
    (hrej : RejectK img ext A g s0 resStack Q Qp) :
    ProofLib.SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (dispatchMem A img g me s0 resStack) Q Qp (runOom s0) :=
  run_hop_recvBad_ok_ext himg hh.toExt hres hres64 he hd hcall hbad hrej

theorem run_hop_recvP_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {g : RunCall} {peerV : AddrV} {rest : Bytes}
    {me : MeAtDispatch} {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A ext)
    (hc : RunCallees img A ext B (slotsOf A img S needs))
    (hpksm : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromName)
      (pksmSlotSpec A img S))
    (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hres : runNeed B (slotsOf A img S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63)
    (hspb : resStack ≤ s0.sp.toNat)
    (he : AtRunEntry S img ext g s0)
    (hd : AtDispatch img ext g me s0 s)
    (hcall : g.c = .recv peerV)
    (hstdin : g.i.stdin = 3#8 :: rest)
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectK img ext A g s0 resStack Q Qp)
    (hjoin : JoinK img ext A g s0 resStack Q Qp) :
    ProofLib.SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (dispatchMem A img g me s0 resStack) Q Qp (runOom s0) :=
  run_hop_recvP_ok_ext himg hh.toExt hc hpksm hdrop hres hres64 hspb he hd hcall hstdin hpanic hrej hjoin

end CryptoVerification.SignalSession.Cli.RunCompose



