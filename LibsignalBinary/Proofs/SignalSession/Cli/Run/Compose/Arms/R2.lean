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
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.EncResBridge
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SpeOwnedBridges
import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonCalleesExt
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Specifications.AsmConstants
import ProofLib.Disproof.Basic
public meta import Lean -- shake: keep

/-!
# `signal_session::run` Send Arm (`run_hop_send_ok`)

Proves `run_hop_send_ok` (`R+0x214 → R+0xf8c / R+0x2c7c`) on `signal_session::run` for
`g.c = .send peerV`:
- Unpacks `peerV` from `g.call` into `fsp + 0x320` and rejects immediately when `me = .none`.
- When `me = .some meV meG`, stages `meG` at `fsp + 0x23b0` and `UNIX_EPOCH` at `fsp`, then calls
  `hc.encrypt` at `R + 0x518`.
- On `Err`, drops the returned `SignalProtocolError`, writes `-1` to `[g.res]`, frees the address
  buffers, and reaches `AtReject .postDispatch` (`R + 0x2c7c`).
- On `Ok (.signalMessage m)` or `Ok (.preKeySignalMessage m)`, prepends wire tag `0x02` or `0x03`
  via `concat`, drops the message and address buffers, and reaches `AtJoin` (`R + 0xf8c`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Arm64.Process
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunSkeleton

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] ProofLib.bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

local macro "r2_eq" : tactic => `(tactic| (
  (try dsimp only [calleeSavedVRegs])
  (try simp only [calleeSavedVRegs])
  (try simp only [arm64_norm])
  (try rfl)))

local macro "r2_run" h:ident : tactic => `(tactic| (
  (try simp only [arm64_norm])
  exact $h))

local macro "r2_cond" : tactic => `(tactic| first
  | (simp only [arm64_norm, conditionHolds_mi_subsPState64, conditionHolds_pl_subsPState64,
        conditionHolds_mi_addsPState64, conditionHolds_pl_addsPState64,
        conditionHolds_mi_subsPState32, conditionHolds_pl_subsPState32,
        conditionHolds_mi_addsPState32, conditionHolds_pl_addsPState32])
  | (simp only [arm64_norm, conditionHolds_mi_subsPState64, conditionHolds_pl_subsPState64,
        conditionHolds_mi_addsPState64, conditionHolds_pl_addsPState64,
        conditionHolds_mi_subsPState32, conditionHolds_pl_subsPState32,
        conditionHolds_mi_addsPState32, conditionHolds_pl_addsPState32]
     decide))

/-! ## 1. Split Decode Trees, Callee Offsets, and Relocation Helpers -/

gen_decodes CryptoVerification.libsignalSessionCode_tree r2_dec
  [(ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]") →
   (ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]" + 364),
   (ls_off% "libsignal_cli::run" + 532) → (ls_off% "libsignal_cli::run" + 540),
   (ls_off% "libsignal_cli::run" + 1200) → (ls_off% "libsignal_cli::run" + 1612),
   (ls_off% "libsignal_cli::run" + 2132) → (ls_off% "libsignal_cli::run" + 2144),
   (ls_off% "libsignal_cli::run" + 2948) → (ls_off% "libsignal_cli::run" + 3000),
   (ls_off% "libsignal_cli::run" + 3792) → (ls_off% "libsignal_cli::run" + 3864),
   (ls_off% "libsignal_cli::run" + 3932) → (ls_off% "libsignal_cli::run" + 3980),
   (ls_off% "libsignal_cli::run" + 11380) → (ls_off% "libsignal_cli::run" + 11388)]

private theorem r2_wrapEncrypt_fnOff :
    libsignalSessionCode.fnOff wrapEncryptName =
      num% (ls_off% "libsignal_cli_ratchet::encrypt") :=
  ls_lemma% fnOff "libsignal_cli_ratchet::encrypt"

private theorem r2_cliConcat_fnOff :
    libsignalSessionCode.fnOff cliConcatName =
      num% (ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]") :=
  ls_lemma% fnOff "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"

private theorem r2_cliDropSpe_fnOff :
    libsignalSessionCode.fnOff cliDropSpeName =
      num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]"

private theorem r2_cliDropPreKeyMsg_fnOff :
    libsignalSessionCode.fnOff cliDropPreKeyMsgName =
      num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::PreKeySignalMessage>") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::protocol::PreKeySignalMessage>"

private theorem r2_run_fnAddr_rel {img : Obj.Image} {ext : String → Option (State → State)}
    {target : String} {off : BitVec 64}
    (h : BitVec.ofNat 64 (libsignalSessionCode.fnOff runName) + off =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff target)) :
    (mProg img ext).fnAddr runName + off = (mProg img ext).fnAddr target := by
  simp only [mProg, tripleRatchetProgAtExt, Program.fnAddr_rebase, BitVec.add_assoc, h]

private theorem r2_sessVt_eq (img : Obj.Image) : sessVt img = img.base + 625720#64 :=
  sessVt_eq img

private theorem r2_idVt_eq (img : Obj.Image) : idVt img = img.base + 625760#64 :=
  idVt_eq img

private theorem r2_loads_base_aligned {li : Obj.LinkedImage} {img : Obj.Image}
    (himg : Obj.Loads li img) :
    (img.base &&& 0xfff#64) = 0#64 := by
  obtain ⟨_, _, hmod, _, _, _⟩ := ProofLib.ObjectLoad.load_eq_ok himg
  dsimp only [Obj.pageSize] at hmod
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change (img.base.toNat &&& (2 ^ 12 - 1)) = 0
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact hmod

/-! ## 2. Pure / `SepWPp` / Stack Helpers & Extended `concat` (`≤ 2 ^ 63`) -/

private theorem r2_sepWPp_exists_left {α : Sort _} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x : α, SepWPp prog ret s (P x) Q Qp oom) :
    SepWPp prog ret s (∃∗ x, P x) Q Qp oom := by
  intro R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨x, hx⟩ := hm
  exact h x R hx hL

private theorem r2_sepWPp_pure_left {φ : Prop} {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : φ → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s (⌜φ⌝ ∗ P) Q Qp oom := by
  intro R hm hL
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL

private class R2Peel (P : SepProp) (α : outParam (Sort _)) (R : outParam (α → SepProp)) : Prop where
  entails : P ⊢ ∃∗ x : α, R x

private instance (priority := 100) {α : Sort _} {P : α → SepProp} : R2Peel (∃∗ x : α, P x) α P :=
  ⟨Entails.refl _⟩

private instance (priority := 90) {α : Sort _} {A B : SepProp} {R : α → SepProp} [h : R2Peel A α R] :
    R2Peel (A ∗ B) α (fun x => R x ∗ B) :=
  ⟨by rw [← sepExists_sepConj_left]; exact sepConj_mono_left h.entails⟩

private instance (priority := 80) {α : Sort _} {A B : SepProp} {R : α → SepProp} [h : R2Peel B α R] :
    R2Peel (A ∗ B) α (fun x => A ∗ R x) :=
  ⟨by rw [← sepExists_sepConj_right]; exact sepConj_mono_right h.entails⟩

private theorem r2_peel {α : Sort _} {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {R : α → SepProp} [h : R2Peel P α R]
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (k : ∀ x : α, SepWPp prog ret s (R x) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  sepWPp_weaken_pre h.entails (r2_sepWPp_exists_left k)

private class R2PeelPure (P : SepProp) (φ : outParam Prop) (R : outParam SepProp) : Prop where
  entails : P ⊢ ⌜φ⌝ ∗ R

private instance (priority := 100) {φ : Prop} : R2PeelPure ⌜φ⌝ φ emp :=
  ⟨Entails.of_eq (sepConj_emp _).symm⟩

private instance (priority := 90) {φ : Prop} {A B R : SepProp} [h : R2PeelPure A φ R] :
    R2PeelPure (A ∗ B) φ (R ∗ B) :=
  ⟨Entails.trans (sepConj_mono_left h.entails) (Entails.of_eq (sepConj_assoc _ _ _))⟩

private instance (priority := 80) {φ : Prop} {A B R : SepProp} [h : R2PeelPure B φ R] :
    R2PeelPure (A ∗ B) φ (A ∗ R) :=
  ⟨Entails.trans (sepConj_mono_right h.entails) (Entails.of_eq (sepConj_left_comm _ _ _))⟩

private theorem r2_peel_pure {φ : Prop} {prog : Program} {ret : BitVec 64} {s : State}
    {P R : SepProp} [h : R2PeelPure P φ R]
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (k : φ → SepWPp prog ret s R Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  sepWPp_weaken_pre h.entails (r2_sepWPp_pure_left k)

private theorem r2_call_inImage_steps {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {s0 s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (x : α)
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hinv : ImgCallInv img s)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
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
    (hnext : ∀ sf : State,
      Steps prog s sf →
      ImgCallInv img sf →
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp (runOom s0)) :
    SepWPp prog ret s P Q Qp (runOom s0) := by
  intro R hm hL
  have hm_pre : s.mem ⊨ (spec.pre x s ∗ F) ∗ R :=
    Satisfies.mono (sepConj_mono_left hP) hm
  have hpre : s.mem ⊨ (spec.inImage img).pre x s ∗ (F ∗ R) := by
    dsimp only [Spec.inImage]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, by simpa only [sepConj_assoc] using hm_pre⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
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

private theorem r2_call_inImage {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {s0 s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (x : α)
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hinv : ImgCallInv img s)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
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
    (hnext : ∀ sf : State,
      ImgCallInv img sf →
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp (runOom s0)) :
    SepWPp prog ret s P Q Qp (runOom s0) :=
  r2_call_inImage_steps x hcall hinv hpc hrun hsp hlr hP
    (hpanic := hpanic) (hexit := hexit) (hoom := hoom)
    (hnext := fun sf _ => hnext sf)

private theorem r2_histOk_of_trace_files {i : Inputs} {s0 s1 s2 : State}
    (htr : s2.trace = s1.trace) (hfs : s2.fs.files = s1.fs.files)
    (h : RunHistOk i s0 s1) :
    RunHistOk i s0 s2 :=
  ⟨hfs.trans h.1, by rw [htr]; exact h.2⟩

private theorem r2_files_of_trace_eq {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {s1 s2 : State}
    (hh : RunHooksExt img A ext) (hsteps : Steps (mProg img ext) s1 s2)
    (htr : s2.trace = s1.trace) :
    s2.fs.files = s1.fs.files :=
  hh.fs.files_eq hsteps (htr.trans (List.append_nil s1.trace).symm) NoFsEv.nil

private theorem r2_histOk_of_slotTrace {i : Inputs} {s0 s1 s2 : State}
    (hfiles1 : s1.fs.files = runFiles i)
    (hout1 : ProcessOutcome.traceStreamBytes .stdout s1.trace = [])
    (hpre : s0.trace <+: s1.trace)
    (hst : slotTrace s1 s2) :
    s0.trace <+: s2.trace ∧ RunHistOk i s0 s2 :=
  ⟨hpre.trans hst.1, hst.2.1.trans hfiles1, hst.2.2.trans hout1⟩

private theorem r2_inRun_mk {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s s' : State} {k k' : Nat}
    (h : InRun img ext s0 s k)
    (hpc : s'.pc = runPc img ext k')
    (hrun : s'.status = .Running)
    (hsp : s'.sp = s.sp)
    (hfp : s'.readReg64 .fp = s.readReg64 .fp)
    (hinv : ImgCallInv img s')
    (hv : calleeSavedVRegs s' = calleeSavedVRegs s) :
    InRun img ext s0 s' k' :=
  { pc := hpc
    run := hrun
    sp := hsp.trans h.sp
    fp := hfp.trans h.fp
    inv := hinv
    vregs := hv.trans h.vregs
    spAligned := h.spAligned }

private theorem r2_csm_refl (s : State) : CalleeSavedPreserved s s := by
  simp [CalleeSavedPreserved]

private theorem r2_csm_trans {s1 s2 s3 : State}
    (h1 : CalleeSavedPreserved s1 s2) (h2 : CalleeSavedPreserved s2 s3) :
    CalleeSavedPreserved s1 s3 := by
  unfold CalleeSavedPreserved at *; simp_all

private theorem r2_csm_fp {s sf : State} (h : CalleeSavedPreserved s sf) :
    sf.readReg64 .fp = s.readReg64 .fp := by
  unfold CalleeSavedPreserved at h; simp_all

private theorem r2_csm_vregs {s sf : State} (h : CalleeSavedPreserved s sf) :
    calleeSavedVRegs sf = calleeSavedVRegs s := by
  unfold CalleeSavedPreserved at h; simp_all

private theorem r2_csm_x19 {s sf : State} (h : CalleeSavedPreserved s sf) :
    sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) := by
  unfold CalleeSavedPreserved at h; simp_all

private theorem r2_csm_x20 {s sf : State} (h : CalleeSavedPreserved s sf) :
    sf.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) := by
  unfold CalleeSavedPreserved at h; simp_all

private theorem r2_csm_x21 {s sf : State} (h : CalleeSavedPreserved s sf) :
    sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) := by
  unfold CalleeSavedPreserved at h; simp_all

private theorem r2_csm_x22 {s sf : State} (h : CalleeSavedPreserved s sf) :
    sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) := by
  unfold CalleeSavedPreserved at h; simp_all

private theorem r2_csm_x23 {s sf : State} (h : CalleeSavedPreserved s sf) :
    sf.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := by
  unfold CalleeSavedPreserved at h; simp_all

private theorem r2_csm_x24 {s sf : State} (h : CalleeSavedPreserved s sf) :
    sf.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) := by
  unfold CalleeSavedPreserved at h; simp_all

private theorem r2_csm_x26 {s sf : State} (h : CalleeSavedPreserved s sf) :
    sf.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) := by
  unfold CalleeSavedPreserved at h; simp_all

private theorem r2_csm_x27 {s sf : State} (h : CalleeSavedPreserved s sf) :
    sf.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by
  unfold CalleeSavedPreserved at h; simp_all

private theorem r2_csm_x28 {s sf : State} (h : CalleeSavedPreserved s sf) :
    sf.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := by
  unfold CalleeSavedPreserved at h; simp_all

private theorem r2_stackAt_split_ge (sp : BitVec 64) {k sub : Nat}
    (hle : k ≤ sub) (h64 : sub ≤ 2 ^ 64) :
    stackAt sp sub = stackAt sp k ∗ memRegion (sp - BitVec.ofNat 64 sub) (sub - k) := by
  have hb := ProofLib.stackAt_split_bottom sp k (sub - k) (by omega)
  have hsum : k + (sub - k) = sub := by omega
  rw [hsum] at hb
  rw [hb, sepConj_comm]

/-- Inner spec of `encSlotSpec` (`(r2_encInnerSpec A img S stk).inImage img = encSlotSpec A img S stk`
definitionally by `rfl`). -/
private def r2_encInnerSpec (A : RustAlloc) (img : Obj.Image) (S : RunSem) (stk : Nat) :
    Spec EncGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ptA ∧ (s.readReg64 .x1).toNat = x.ptext.length ∧
      x.ptext.length < 2 ^ 32 ∧ s.readReg64 .x2 = x.peerA ∧ s.readReg64 .x3 = x.meA ∧
      s.readReg64 .x4 = x.stores + 0xf0#64 ∧ s.readReg64 .x5 = sessVt img ∧
      s.readReg64 .x6 = x.stores ∧ s.readReg64 .x7 = idVt img ∧
      s.readReg64 .x8 = x.ret ∧ s.fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
      S.encOk x.F x.peer.val x.coins ∧ stk ≤ s.sp.toNat ∧ x.meA ≠ 0#64⌝ ∗
    slotFrame A img x.toSlotCtx ∗ (x.ptA ↦ₛ x.ptext) ∗ nowCellAt s.sp unixEpoch ∗
    memRegion x.ret 248 ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ∃∗ g' : StoresGhost, ∃∗ e : Except (ApiError AddrVal Unit) CiphertextMessage,
      ⌜slotTrace s0 sf ∧
        slotOut (S.encrypt x.F x.peer.val x.me.val x.ptext x.coins) g' e s0 sf ∧
        (∀ m : PreKeySignalMessage, e = .ok (.preKeySignalMessage m) →
          m.serialized.length < 2 ^ 42)⌝ ∗
      storesAt A x.stores g' ∗ encResAt A x.ret e ∗
      protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
      (x.ptA ↦ₛ x.ptext) ∗ nowCellAt s0.sp unixEpoch ∗ logOff img ∗ A.pool ∗
      stackAt s0.sp stk ∗ anyHeap
  onPanic := fun x s0 sf =>
    ⌜S.encrypt x.F x.peer.val x.me.val x.ptext x.coins = none ∨ allocFailedIn s0 sf⌝ ∗
      anyHeap

private theorem r2_encInnerSpec_inImage (A : RustAlloc) (img : Obj.Image) (S : RunSem) (stk : Nat) :
    (r2_encInnerSpec A img S stk).inImage img = encSlotSpec A img S stk := rfl

private abbrev r2_concatExactStack : Nat := 96 + extHookStack

private theorem r2_memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, ProofLib.memRegion_split a 8 (8 + 8) (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide), ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem r2_stackAt_concat (sp : BitVec 64) :
    stackAt sp r2_concatExactStack =
      stackAt (sp - 96#64) extHookStack ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
  have h1 := ProofLib.stackAt_split_cells sp 16384 12 (by decide)
  have hsum : 16384 + 8 * 12 = r2_concatExactStack := by decide
  rw [hsum] at h1
  change stackAt sp r2_concatExactStack =
    stackAt (sp - 96#64) extHookStack ∗ cells (sp - 96#64) 12 at h1
  have hc12 : cells (sp - 96#64) 12 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
    cells_unfold
  rw [h1, hc12]

/-- Exact-stack (`96 + extHookStack`) overflow case `bs0.length = 1 ∧ bs1.length = 2 ^ 63 - 1` of
`concat [local#3]`, which computes total length `0x8000000000000000#64` (`C = 0`, bit 63 = `1`) and
calls `alloc::raw_vec::handle_error` (`allocFailedIn`). -/
private def r2_concat2EqSpec (A : RustAlloc) (stk : Nat) :
    Spec SpqrV1.ChainProofs.SliceConcat2Ghost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.outVec ∧ s.readReg64 .x1 = x.slicesA ∧ s.readReg64 .x2 = 2#64 ∧
      x.bs0.length = 1 ∧ x.bs1.length = 2 ^ 63 - 1⌝ ∗
      memRegion x.outVec 24 ∗
      (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
      ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
      SpqrV1.ChainProofs.bytesAt x.ro0 x.p0 x.bs0 ∗ SpqrV1.ChainProofs.bytesAt x.ro1 x.p1 x.bs1 ∗
      A.pool ∗ stackAt s.sp stk
  post := (RunProofs.cliConcat2Spec A stk).post
  onPanic := (RunProofs.cliConcat2Spec A stk).onPanic

/-- Verified behavior of `<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]` at the
`isize::MAX` boundary `bs0.length = 1 ∧ bs1.length = 2 ^ 63 - 1` (`ctWire` length `2 ^ 63`):
the compiled binary never returns normally (`post := ⌜False⌝`) and always aborts via
`alloc::raw_vec::handle_error` (`Rust.panicked`) with `sf.trace = s0.trace` and
`¬ allocFailedIn s0 sf` (because capacity overflow aborts before calling `__rust_alloc`). -/
private def concat2EqPanicsSpec (A : RustAlloc) (stk : Nat) :
    Spec SpqrV1.ChainProofs.SliceConcat2Ghost where
  pre := (r2_concat2EqSpec A stk).pre
  post := fun _ _ _ => ⌜False⌝
  onPanic := fun _ s0 sf => ⌜¬ allocFailedIn s0 sf ∧ sf.trace = s0.trace⌝ ∗ anyHeap

private theorem r2_concat_no_allocFailed {s0 s_pre : State} {P R : SepProp}
    (htr : s_pre.trace = s0.trace)
    (hm : (Rust.panicked s_pre).mem ⊨ P ∗ R) :
    (Rust.panicked s_pre).mem ⊨
      (⌜¬ allocFailedIn s0 (Rust.panicked s_pre) ∧
        (Rust.panicked s_pre).trace = s0.trace⌝ ∗
        anyHeap) ∗ R := by
  have htr_p : (Rust.panicked s_pre).trace = s0.trace := by
    simp only [Rust.panicked, htr]
  have hnot : ¬ allocFailedIn s0 (Rust.panicked s_pre) := by
    unfold allocFailedIn
    rw [htr_p, List.drop_length]
    exact List.not_mem_nil
  exact Satisfies.mono (sepConj_mono_left (Entails.pure_right ⟨hnot, htr_p⟩ (entails_anyHeap P))) hm

/-- At `bs0.length = 1 ∧ bs1.length = 2 ^ 63 - 1`, `cliConcatName` in `libsignalSessionCode`
panics via `alloc::raw_vec::handle_error` with unchanged trace (`¬ allocFailedIn s0 sf`). -/
private theorem concat2_eq_panics_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr cliConcatName)
      ((concat2EqPanicsSpec A r2_concatExactStack).inImage img) := by
  unfold mProg Spec.inImage concat2EqPanicsSpec r2_concat2EqSpec
  simp only [r2_memRegion_24_cells, r2_stackAt_concat, sepExists_sepConj_left, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff cliConcatName =
      ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]" :=
    r2_cliConcat_fnOff
  have hpan := panic_at_handle_error_norm_ext
    (b := img.base) (ext := ext) (name := cliConcatName)
    (k := ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
      "alloc::raw_vec::handle_error")
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]")) 0 364
  dsimp only [tripleRatchetProgAtExt] at hpan ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr cliConcatName = entry
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨outVec, slicesA, ro0, p0, bs0, ro1, p1, bs1⟩ := x
  dsimp only at *
  have hb0 : BitVec.ofNat 64 bs0.length = 1#64 := by rw [‹bs0.length = 1›]
  have hb1 : BitVec.ofNat 64 bs1.length = 0x7fffffffffffffff#64 := by
    rw [‹bs1.length = 2 ^ 63 - 1›]; rfl
  rw [hb0, hb1]
  apply SepWPp.of_sepWP
    (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
      "alloc::raw_vec::handle_error"))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
  exact r2_concat_no_allocFailed (by simp only [wp_norm, arm64_norm]) hm

private theorem concat2_eq_panics_at_stk {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (stk : Nat) (hstk : 96 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr cliConcatName)
      ((concat2EqPanicsSpec A stk).inImage img) := by
  refine DropPreKeyMsgHelpers.subroutine_ok_map_frame_weaken
    id (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - r2_concatExactStack))
    (concat2_eq_panics_ok (img := img) (A := A) (ext := ext)) ?_ ?_ ?_ (fun _ _ _ _ => rfl)
  · intro x s0
    dsimp only [Spec.inImage, concat2EqPanicsSpec, r2_concat2EqSpec, id]
    rw [r2_stackAt_split_ge s0.sp hstk hstk64]
    exact Entails.of_eq (by ac_rfl)
  · intro _ _ _
    dsimp only [Spec.inImage, concat2EqPanicsSpec, id]
    exact Entails.pure_left False.elim
  · intro _ _ _
    dsimp only [Spec.inImage, concat2EqPanicsSpec, id]
    rw [sepConj_assoc]
    exact sepConj_mono_right (entails_anyHeap _)

/-- Exact `isize::MAX` wire-concatenation boundary condition on `signal_session::run` (`Send`):
`encrypt` returns `Ok(ct)` with serialized payload length `2 ^ 63 - 1`, so `ctWire ct`
(`tag :: serialized`) has byte length `2 ^ 63 > isize::MAX` and `concat` aborts at
`alloc::raw_vec::handle_error` before calling `__rust_alloc` (`sf.trace = s_cat.trace`). -/
def SendConcatOverflow (g : RunCall) : Prop :=
  ∃ writes out, g.a = some (some (writes, out)) ∧ out.length = 2 ^ 63

/-- `SepWPp` execution at `bs0.length = 1 ∧ bs1.length = 2 ^ 63 - 1`: `cliConcatName` never
returns normally and reaches `Rust.panicked` with `¬ allocFailedIn s0 sf ∧ sf.trace = s0.trace`. -/
private theorem r2_concat2_eq_wpp {img : Obj.Image}
    {ext : String → Option (State → State)} (A : RustAlloc)
    (stk : Nat) (hstk : 96 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (x : SpqrV1.ChainProofs.SliceConcat2Ghost) (s0 : State)
    (hpc : s0.pc = (mProg img ext).fnAddr cliConcatName)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true) :
    SepWPp (mProg img ext) (s0.readReg64 Reg.lr) s0
      (((r2_concat2EqSpec A stk).inImage img).pre x s0)
      (fun _ _ => False)
      (fun sf _ => ¬ allocFailedIn s0 sf ∧ sf.trace = s0.trace) := by
  refine SepWPp.weaken_pre (P' :=
      (((r2_concat2EqSpec A r2_concatExactStack).inImage img).pre x s0) ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - r2_concatExactStack))
    (by
      dsimp only [Spec.inImage, r2_concat2EqSpec]
      rw [r2_stackAt_split_ge s0.sp hstk hstk64]
      exact Entails.of_eq (by ac_rfl)) ?_
  dsimp only [Spec.inImage, r2_concat2EqSpec]
  rw [sepConj_assoc]
  apply SepWPp.pure_left; intro _himgInv
  rw [sepConj_assoc]
  obtain ⟨outVec, slicesA, ro0, p0, bs0, ro1, p1, bs1⟩ := x
  dsimp only at *
  apply SepWPp.pure_left; rintro ⟨hx0, hx1, hx2, hb0_len, hb1_len⟩
  unfold mProg at hpc ⊢
  simp only [r2_memRegion_24_cells, r2_stackAt_concat, sepExists_sepConj_left, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff cliConcatName =
      ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]" :=
    r2_cliConcat_fnOff
  have hpan := panic_at_handle_error_norm_ext
    (b := img.base) (ext := ext) (name := cliConcatName)
    (k := ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
      "alloc::raw_vec::handle_error")
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]")) 0 364
  dsimp only [tripleRatchetProgAtExt] at hpan hpc ⊢
  clear hfn
  let _ := hsp
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr cliConcatName = entry
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?]
  examples_hide_fetches
  have hb0 : BitVec.ofNat 64 bs0.length = 1#64 := by rw [hb0_len]
  have hb1 : BitVec.ofNat 64 bs1.length = 0x7fffffffffffffff#64 := by
    rw [hb1_len]; rfl
  rw [hb0, hb1]
  repeat (apply r2_peel; intro _)
  apply SepWPp.of_sepWP
    (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
      "alloc::raw_vec::handle_error"))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) ?_
  refine ⟨?_, by simp only [Rust.panicked, wp_norm, arm64_norm]⟩
  unfold allocFailedIn
  simp only [Rust.panicked, wp_norm, arm64_norm, List.drop_length]
  exact List.not_mem_nil

/-- At `bs0.length = 1 ∧ bs1.length = 2 ^ 63 - 1`, `cliConcatName` panics via
`alloc::raw_vec::handle_error` with unchanged trace (`¬ allocFailedIn s0 sf`), refuting
`subroutine_ok` under `(RunProofs.cliConcat2Spec A stk).onPanic` (`allocFailedIn s0 sf`). -/
private theorem not_concat2_eq_subroutine_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (stk : Nat) (hstk : 96 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (x : SpqrV1.ChainProofs.SliceConcat2Ghost) (R : SepProp) (s0 : State)
    (hentry : AapcsEntry s0 ((mProg img ext).fnAddr cliConcatName))
    (hcode : (mProg img ext).CodeLoaded s0.mem)
    (hpre : s0.mem ⊨ ((r2_concat2EqSpec A stk).inImage img).pre x s0 ∗ R)
    (hlr : ProofLib.Disproof.HaltsAtReturn (mProg img ext) s0) :
    ¬ subroutine_ok (mProg img ext) ((mProg img ext).fnAddr cliConcatName)
        ((r2_concat2EqSpec A stk).inImage img) := by
  have hwp := r2_concat2_eq_wpp A stk hstk hstk64 x s0 hentry.1 hentry.2.1 hentry.2.2
  obtain ⟨sf, hsteps, ⟨_, _, _, _, hfalse⟩ | ⟨hpan, _, _, hnoAlloc, _⟩ | ⟨_, hmo⟩⟩ :=
    hwp R hpre hcode
  · exact hfalse.elim
  · refine ProofLib.Disproof.not_subroutine_ok_of_panic_post_false x R hentry hcode hpre
      hsteps hpan (fun hon => ?_) hlr
    simp only [Spec.inImage, r2_concat2EqSpec, RunProofs.cliConcat2Spec,
      sepConj_assoc, satisfies_pure_sepConj] at hon
    exact hnoAlloc hon.1.1
  · exact (not_satisfies_false_sepConj hmo).elim

/-- Total contract for `<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]` across ALL
`bs0.length = 1 ∧ bs1.length < 2 ^ 63`: unifies `< 2 ^ 63` (`RunSkeleton.concat_ok`) and
`= 2 ^ 63` (`concat2_eq_panics_at_stk`, capacity-overflow panic with `sf.trace = s0.trace`). -/
private def r2_concat2LeSpec (A : RustAlloc) (stk : Nat) :
    Spec SpqrV1.ChainProofs.SliceConcat2Ghost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.outVec ∧ s.readReg64 .x1 = x.slicesA ∧ s.readReg64 .x2 = 2#64 ∧
      x.bs0.length = 1 ∧ x.bs1.length < 2 ^ 63⌝ ∗
      memRegion x.outVec 24 ∗
      (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
      ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
      SpqrV1.ChainProofs.bytesAt x.ro0 x.p0 x.bs0 ∗ SpqrV1.ChainProofs.bytesAt x.ro1 x.p1 x.bs1 ∗
      A.pool ∗ stackAt s.sp stk
  post := (RunProofs.cliConcat2Spec A stk).post
  onPanic := fun x s0 sf =>
    ⌜(allocFailedIn s0 sf ∨ (x.bs0.length + x.bs1.length = 2 ^ 63 ∧ sf.trace = s0.trace)) ∧
      s0.trace <+: sf.trace⌝ ∗ anyHeap

private theorem r2_concat2_le_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hh : RunHooksExt img A ext)
    (stk : Nat) (hstk : 96 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr cliConcatName)
      ((r2_concat2LeSpec A stk).inImage img) := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp _hL
  have hpre_pure :
      s0.readReg64 .x0 = x.outVec ∧ s0.readReg64 .x1 = x.slicesA ∧ s0.readReg64 .x2 = 2#64 ∧
        x.bs0.length = 1 ∧ x.bs1.length < 2 ^ 63 := by
    have hpre' := hpre
    simp only [Spec.inImage, r2_concat2LeSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre'
    exact hpre'.2.1
  rcases hpre_pure with ⟨hx0, hx1, hx2, hb0, hb1⟩
  by_cases hsum : x.bs0.length + x.bs1.length < 2 ^ 63
  · refine (RunSkeleton.concat_ok_ext hh stk hstk hstk64).mono_outcome x R s0 hpc hrun ?_ hsp ?_
    · refine Satisfies.mono (sepConj_mono_left ?_) hpre
      dsimp only [Spec.inImage, r2_concat2LeSpec, RunProofs.cliConcat2Spec]
      exact sepConj_mono_right
        (Entails.pure_left fun _ => Entails.pure_right ⟨hx0, hx1, hx2, hsum⟩ (Entails.refl _))
    · intro sf hout
      rcases hout with hret | ⟨hpan, hon⟩ | hrest
      · exact Or.inl hret
      · refine Or.inr (Or.inl ⟨hpan, Satisfies.mono (sepConj_mono_left ?_) hon⟩)
        dsimp only [Spec.inImage, r2_concat2LeSpec, RunProofs.cliConcat2Spec]
        exact Entails.pure_left fun h =>
          Entails.pure_right ⟨Or.inl h.1, h.2⟩ (Entails.refl _)
      · exact Or.inr (Or.inr hrest)
  · have hb1_eq : x.bs1.length = 2 ^ 63 - 1 := by omega
    have hsum_eq : x.bs0.length + x.bs1.length = 2 ^ 63 := by omega
    refine (concat2_eq_panics_at_stk (img := img) (A := A) (ext := ext) stk hstk hstk64).mono_outcome
      x R s0 hpc hrun ?_ hsp ?_
    · refine Satisfies.mono (sepConj_mono_left ?_) hpre
      dsimp only [Spec.inImage, r2_concat2LeSpec, concat2EqPanicsSpec, r2_concat2EqSpec]
      exact sepConj_mono_right
        (Entails.pure_left fun _ =>
          Entails.pure_right ⟨hx0, hx1, hx2, hb0, hb1_eq⟩ (Entails.refl _))
    · intro sf hout
      rcases hout with ⟨_, _, hpost⟩ | ⟨hpan, hon⟩ | hrest
      · simp only [Spec.inImage, concat2EqPanicsSpec, satisfies_pure_sepConj] at hpost
        exact hpost.1.elim
      · refine Or.inr (Or.inl ⟨hpan, Satisfies.mono (sepConj_mono_left ?_) hon⟩)
        dsimp only [Spec.inImage, r2_concat2LeSpec, concat2EqPanicsSpec]
        exact Entails.pure_left fun h =>
          Entails.pure_right ⟨Or.inr ⟨hsum_eq, h.2⟩, h.2 ▸ List.prefix_refl _⟩ (Entails.refl _)
      · exact Or.inr (Or.inr hrest)

/-! ## 3. Word, Struct, 31-Word Slot, and Stack-Frame Open/Close Helpers -/

private def r2_pack8 : List (BitVec 8) → BitVec 64
  | [b0, b1, b2, b3, b4, b5, b6, b7] =>
    b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0
  | _ => 0#64

private theorem r2_unpack64_pack8 (bs : List (BitVec 8)) (h : bs.length = 8) :
    unpack64 (r2_pack8 bs) = bs := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try simp at h
  unfold r2_pack8 unpack64
  simp only [List.cons.injEq, and_true]
  exact ⟨by bv_bits, by bv_bits, by bv_bits, by bv_bits,
         by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩

private theorem r2_pointsToBytes8_eq_word (a : BitVec 64) (bs : List (BitVec 8))
    (h : bs.length = 8) :
    (a ↦ₛ bs) = (a ↦₆₄ r2_pack8 bs) := by
  rw [pointsTo64_eq_pointsToBytes, r2_unpack64_pack8 bs h]

private theorem r2_pointsToBytes32_eq_words4 (a : BitVec 64) (bs : List (BitVec 8))
    (h : bs.length = 32) :
    (a ↦ₛ bs) =
      ((a ↦₆₄ r2_pack8 (bs.take 8)) ∗
       ((a + 8#64) ↦₆₄ r2_pack8 ((bs.drop 8).take 8)) ∗
       ((a + 16#64) ↦₆₄ r2_pack8 ((bs.drop 16).take 8)) ∗
       ((a + 24#64) ↦₆₄ r2_pack8 (bs.drop 24))) := by
  have hsplit :
      bs = bs.take 8 ++ ((bs.drop 8).take 8 ++ ((bs.drop 16).take 8 ++ bs.drop 24)) := by
    have h24 : bs.drop 24 = (bs.drop 16).drop 8 := by simp [List.drop_drop]
    have h16 : bs.drop 16 = (bs.drop 8).drop 8 := by simp [List.drop_drop]
    rw [h24, List.take_append_drop, h16, List.take_append_drop, List.take_append_drop]
  have h0 : (bs.take 8).length = 8 := by simp [h]
  have h1 : ((bs.drop 8).take 8).length = 8 := by simp [h]
  have h2 : ((bs.drop 16).take 8).length = 8 := by simp [h]
  have h3 : (bs.drop 24).length = 8 := by simp [h]
  conv => lhs; rw [hsplit]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
      h0, h1, h2,
      r2_pointsToBytes8_eq_word a (bs.take 8) h0,
      r2_pointsToBytes8_eq_word _ ((bs.drop 8).take 8) h1,
      r2_pointsToBytes8_eq_word _ ((bs.drop 16).take 8) h2,
      r2_pointsToBytes8_eq_word _ (bs.drop 24) h3]
  have ha8 : a + BitVec.ofNat 64 8 = a + 8#64 := rfl
  have ha16 : a + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = a + 16#64 := by bv_omega
  have ha24 : a + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = a + 24#64 := by
    bv_omega
  rw [ha24, ha16, ha8]

private theorem r2_u32_pair_eq_word (a : BitVec 64) (lo hi : BitVec 32) :
    ((a ↦₃₂ lo) ∗ ((a + 4#64) ↦₃₂ hi)) = (a ↦₆₄ r2_pack8 (unpack32 lo ++ unpack32 hi)) := by
  have hl : (unpack32 lo).length = 4 := rfl
  have hl8 : (unpack32 lo ++ unpack32 hi).length = 8 := rfl
  rw [pointsTo32_eq_pointsToBytes, pointsTo32_eq_pointsToBytes]
  have hcat := pointsToBytes_append a (unpack32 lo) (unpack32 hi)
  rw [hl] at hcat
  rw [← hcat, r2_pointsToBytes8_eq_word a _ hl8]

private theorem r2_memRegion4_eq_exists_u32 (a : BitVec 64) :
    memRegion a 4 = ∃∗ v : BitVec 32, a ↦₃₂ v :=
  IsBlock.eq (IsBlock.memRegion a 4) (IsBlock.sepExists fun v => IsBlock.pointsTo32 a v)
    fun m => ⟨fun _ => ⟨m.read32 a, rfl⟩, fun _ => trivial⟩

private theorem r2_word64_to_u8_pad7 (a w : BitVec 64) :
    (a ↦₆₄ w) ⊢ (a ↦₈ w.setWidth 8) ∗ memRegion (a + 1#64) 7 := by
  have hunp : unpack64 w = w.setWidth 8 :: (unpack64 w).tail := by
    unfold unpack64
    simp only [List.tail_cons]
    congr 1
  have htl : ((unpack64 w).tail).length = 7 := rfl
  rw [pointsTo64_eq_pointsToBytes, hunp, pointsToBytes_cons]
  exact sepConj_mono_right (htl ▸ ProofLib.pointsToBytes_entails_memRegion (a + 1#64) _)

private theorem r2_u8_pad7_reloc {F : BitVec 64 → SepProp} (b0 : BitVec 8)
    (hF : ∀ a, F a = (a ↦₈ b0) ∗ memRegion (a + 1#64) 7) (src : BitVec 64) :
    F src ⊢ ∃∗ w : BitVec 64, ⌜∀ dst, (dst ↦₆₄ w) ⊢ F dst⌝ ∗ (src ↦₆₄ w) := by
  have heq : ∀ a, F a = ∃∗ w : BitVec 64, ⌜w.setWidth 8 = b0⌝ ∗ (a ↦₆₄ w) := by
    intro a
    rw [hF a]
    refine IsBlock.eq
      (IsBlock.sepConj (IsBlock.pointsTo8 a b0) (IsBlock.memRegion (a + 1#64) 7) rfl (by decide))
      (IsBlock.sepExists fun w => IsBlock.pure_sepConj fun _ => IsBlock.pointsTo64 a w)
      fun m => ⟨fun ⟨hb, _⟩ => ⟨m.read64 a, ?_, rfl⟩, fun ⟨w, hw, hm64⟩ => ⟨?_, trivial⟩⟩
    · rw [← hb]
      unfold Memory.read64 Memory.read8
      simp only [BitVec.add_zero]
      bv_bits
    · rw [← hw, ← hm64]
      unfold Memory.read64 Memory.read8
      simp only [BitVec.add_zero]
      bv_bits
  rw [heq src]
  apply Entails.sepExists_mono; intro w
  apply Entails.pure_left; intro hw
  refine Entails.pure_right (fun dst => ?_) (Entails.refl _)
  rw [heq dst]
  exact Entails.sepExists_right w (Entails.pure_right hw (Entails.refl _))

/-- `addrUpperAt a g` opens into two 64-bit words `(u0, u1)` with exact relocation to any `b`. -/
private theorem r2_addrUpperAt_reloc (src : BitVec 64) (g : AddrGhost) :
    addrUpperAt src g ⊢
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64,
        ⌜∀ dst, (dst ↦₆₄ u0) ∗ ((dst + 8#64) ↦₆₄ u1) ⊢ addrUpperAt dst g⌝ ∗
          (src ↦₆₄ u0) ∗ ((src + 8#64) ↦₆₄ u1) := by
  unfold addrUpperAt
  have h1 := r2_u8_pad7_reloc g.device (fun a => rfl) (src + 8#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
  refine Entails.trans (sepConj_mono_right h1) ?_
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro u1
  rw [sepConj_left_comm]
  apply Entails.pure_left; intro hu1
  refine Entails.sepExists_right (BitVec.ofNat 64 g.name.bytes.length)
    (Entails.sepExists_right u1 ?_)
  refine Entails.pure_right (fun dst => ?_) (Entails.refl _)
  have hu1' := hu1 (dst + 8#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hu1'
  exact sepConj_mono_right hu1'

/-- Unpacking `callAt A g.call (.send peerV)`: yields a concrete `peerG : AddrGhost` with
`peerG.val = addrValOf peerV`, the 7 words of `g.call`, `addrNameHeap A peerG`, and the pure facts
needed to build `protocolAddressAt A peerG (fsp + 0x320#64)` and release `memRegion g.call 56`. -/
private theorem r2_callAt_send_unpack (A : RustAlloc) (callPtr : BitVec 64) (peerV : AddrV) :
    callAt A callPtr (.send peerV) ⊢
      ∃∗ peerG : AddrGhost, ∃∗ w : CallW,
        ⌜peerG.val = addrValOf peerV ∧ peerG.name.cap = w.w1 ∧ peerG.name.ptr = w.w2 ∧
          w.w3 = BitVec.ofNat 64 peerG.name.bytes.length ∧ w.w4.setWidth 8 = peerG.device⌝ ∗
        ((callPtr ↦₆₄ w.w0) ∗ ((callPtr + 8#64) ↦₆₄ w.w1) ∗ ((callPtr + 16#64) ↦₆₄ w.w2) ∗
          ((callPtr + 24#64) ↦₆₄ w.w3) ∗ ((callPtr + 32#64) ↦₆₄ w.w4) ∗
          ((callPtr + 40#64) ↦₆₄ w.w5) ∗ ((callPtr + 48#64) ↦₆₄ w.w6)) ∗
        addrNameHeap A peerG := by
  unfold callAt callHeap addrWords ownedBytes
  apply Entails.sepExists_elim; intro w
  let peerG : AddrGhost :=
    { name := { cap := w.w1, ptr := w.w2, bytes := peerV.name }, device := peerV.device }
  refine Entails.sepExists_right peerG (Entails.sepExists_right w ?_)
  have hassoc1 :
      (callPtr ↦₆₄ w.w0) ∗ ((callPtr + 8#64) ↦₆₄ w.w1) ∗ ((callPtr + 16#64) ↦₆₄ w.w2) ∗
        ((callPtr + 24#64) ↦₆₄ w.w3) ∗ ((callPtr + 32#64) ↦₆₄ w.w4) ∗
        ((callPtr + 40#64) ↦₆₄ w.w5) ∗ ((callPtr + 48#64) ↦₆₄ w.w6) ∗
        ⌜w.w0 = 0x8000000000000002#64⌝ ∗
        ((⌜w.w3 = BitVec.ofNat 64 peerV.name.length ∧ peerV.name.length ≤ w.w1.toNat ∧
            w.w1.toNat < 2 ^ 63 ∧ w.w2 ≠ 0⌝ ∗
          if w.w1 = 0 then emp
          else A.live w.w2 w.w1.toNat 1 ∗ (w.w2 ↦ₛ peerV.name) ∗
            memRegion (w.w2 + BitVec.ofNat 64 peerV.name.length)
              (w.w1.toNat - peerV.name.length)) ∗
          ⌜w.w4.setWidth 8 = peerV.device⌝) =
      ⌜w.w0 = 0x8000000000000002#64⌝ ∗
      ⌜w.w3 = BitVec.ofNat 64 peerV.name.length ∧ peerV.name.length ≤ w.w1.toNat ∧
        w.w1.toNat < 2 ^ 63 ∧ w.w2 ≠ 0⌝ ∗
      ⌜w.w4.setWidth 8 = peerV.device⌝ ∗
      (((callPtr ↦₆₄ w.w0) ∗ ((callPtr + 8#64) ↦₆₄ w.w1) ∗ ((callPtr + 16#64) ↦₆₄ w.w2) ∗
          ((callPtr + 24#64) ↦₆₄ w.w3) ∗ ((callPtr + 32#64) ↦₆₄ w.w4) ∗
          ((callPtr + 40#64) ↦₆₄ w.w5) ∗ ((callPtr + 48#64) ↦₆₄ w.w6)) ∗
        if w.w1 = 0 then emp
        else A.live w.w2 w.w1.toNat 1 ∗ (w.w2 ↦ₛ peerV.name) ∗
          memRegion (w.w2 + BitVec.ofNat 64 peerV.name.length)
            (w.w1.toNat - peerV.name.length)) := by
    ac_rfl
  rw [hassoc1]
  apply Entails.pure_left; intro _
  apply Entails.pure_left; rintro ⟨hw3, hle, hlt, hne⟩
  apply Entails.pure_left; intro hw4
  refine Entails.pure_right ⟨rfl, rfl, rfl, hw3, hw4⟩ ?_
  unfold addrNameHeap
  dsimp only [peerG]
  exact sepConj_mono_right (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))

private theorem r2_callWords_to_memRegion56 (callPtr : BitVec 64) (w : CallW) :
    ((callPtr ↦₆₄ w.w0) ∗ ((callPtr + 8#64) ↦₆₄ w.w1) ∗ ((callPtr + 16#64) ↦₆₄ w.w2) ∗
      ((callPtr + 24#64) ↦₆₄ w.w3) ∗ ((callPtr + 32#64) ↦₆₄ w.w4) ∗
      ((callPtr + 40#64) ↦₆₄ w.w5) ∗ ((callPtr + 48#64) ↦₆₄ w.w6)) ⊢
      memRegion callPtr 56 := by
  rw [ProofLib.memRegion_split callPtr 8 48 (by decide),
      ProofLib.memRegion_split (callPtr + 8#64) 8 40 (by decide),
      ProofLib.memRegion_split _ 8 32 (by decide),
      ProofLib.memRegion_split _ 8 24 (by decide),
      ProofLib.memRegion_split _ 8 16 (by decide),
      ProofLib.memRegion_split _ 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo64_entails_memRegion _ _))))))

private theorem r2_peerWords_pack (A : RustAlloc) (a : BitVec 64) (peerG : AddrGhost) (w : CallW)
    (hw1 : peerG.name.cap = w.w1) (hw2 : peerG.name.ptr = w.w2)
    (hw3 : w.w3 = BitVec.ofNat 64 peerG.name.bytes.length)
    (hw4 : w.w4.setWidth 8 = peerG.device) :
    (a ↦₆₄ w.w1) ∗ ((a + 8#64) ↦₆₄ w.w2) ∗ ((a + 16#64) ↦₆₄ w.w3) ∗
      ((a + 24#64) ↦₆₄ w.w4) ∗ addrNameHeap A peerG ⊢
      protocolAddressAt A peerG a := by
  rw [protocolAddressAt_eq_parts A peerG a, hw1, hw2, hw3,
      ← sepConj_assoc ((a + 16#64) ↦₆₄ _)]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_))
  unfold addrUpperAt
  have ha24 : a + 16#64 + 8#64 = a + 24#64 := by bv_omega
  have ha25 : a + 16#64 + 9#64 = a + 25#64 := by bv_omega
  rw [ha24, ha25]
  refine sepConj_mono_right ?_
  have hpad := r2_word64_to_u8_pad7 (a + 24#64) w.w4
  have ha1 : a + 24#64 + 1#64 = a + 25#64 := by bv_omega
  rw [hw4, ha1] at hpad
  exact hpad

private theorem r2_addrNameHeap_cap_lt (A : RustAlloc) (g : AddrGhost) :
    addrNameHeap A g ⊢ ⌜g.name.cap.toNat < 2 ^ 63⌝ ∗ addrNameHeap A g := by
  unfold addrNameHeap
  apply Entails.pure_left; rintro ⟨hle, hlt, hne⟩
  exact Entails.pure_right hlt (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))

private theorem r2_addrNameHeap_eq_ownedBytes (A : RustAlloc) (g : AddrGhost) :
    addrNameHeap A g =
      ownedBytes A g.name.cap g.name.ptr (BitVec.ofNat 64 g.name.bytes.length) g.name.bytes := by
  unfold addrNameHeap ownedBytes
  have hp :
      (g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0) =
      (BitVec.ofNat 64 g.name.bytes.length = BitVec.ofNat 64 g.name.bytes.length ∧
        g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0) :=
    propext ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  conv => lhs; rw [hp]

private theorem r2_protocolAddress_to_mem32_heap (A : RustAlloc) (g : AddrGhost) (a : BitVec 64) :
    protocolAddressAt A g a ⊢ memRegion a 32 ∗ addrNameHeap A g := by
  rw [protocolAddressAt_eq_parts A g a, ← sepConj_assoc (a ↦₆₄ g.name.cap)]
  have h16 : (a ↦₆₄ g.name.cap) ∗ ((a + 8#64) ↦₆₄ g.name.ptr) ⊢ memRegion a 16 := by
    rw [ProofLib.memRegion_split a 8 8 (by decide)]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
  refine Entails.trans
    (sepConj_mono h16 (sepConj_mono_left (addrUpperAt_entails_memRegion (a + 16#64) g))) ?_
  rw [← sepConj_assoc, ProofLib.memRegion_split a 16 16 (by decide)]
  exact Entails.refl _

/-- 31 contiguous 64-bit words (`248` bytes = `31 * 8` bytes), matching `R + 0x530..0x5bc`. -/
private structure r2_SlotWords where
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  w4 : BitVec 64
  w5 : BitVec 64
  w6 : BitVec 64
  w7 : BitVec 64
  w8 : BitVec 64
  w9 : BitVec 64
  w10 : BitVec 64
  w11 : BitVec 64
  w12 : BitVec 64
  w13 : BitVec 64
  w14 : BitVec 64
  w15 : BitVec 64
  w16 : BitVec 64
  w17 : BitVec 64
  w18 : BitVec 64
  w19 : BitVec 64
  w20 : BitVec 64
  w21 : BitVec 64
  w22 : BitVec 64
  w23 : BitVec 64
  w24 : BitVec 64
  w25 : BitVec 64
  w26 : BitVec 64
  w27 : BitVec 64
  w28 : BitVec 64
  w29 : BitVec 64
  w30 : BitVec 64

private def r2_words31 (a : BitVec 64) (w : r2_SlotWords) : SepProp :=
  (a ↦₆₄ w.w0) ∗ ((a + 8#64) ↦₆₄ w.w1) ∗ ((a + 16#64) ↦₆₄ w.w2) ∗ ((a + 24#64) ↦₆₄ w.w3) ∗
  ((a + 32#64) ↦₆₄ w.w4) ∗ ((a + 40#64) ↦₆₄ w.w5) ∗ ((a + 48#64) ↦₆₄ w.w6) ∗
  ((a + 56#64) ↦₆₄ w.w7) ∗ ((a + 64#64) ↦₆₄ w.w8) ∗ ((a + 72#64) ↦₆₄ w.w9) ∗
  ((a + 80#64) ↦₆₄ w.w10) ∗ ((a + 88#64) ↦₆₄ w.w11) ∗ ((a + 96#64) ↦₆₄ w.w12) ∗
  ((a + 104#64) ↦₆₄ w.w13) ∗ ((a + 112#64) ↦₆₄ w.w14) ∗ ((a + 120#64) ↦₆₄ w.w15) ∗
  ((a + 128#64) ↦₆₄ w.w16) ∗ ((a + 136#64) ↦₆₄ w.w17) ∗ ((a + 144#64) ↦₆₄ w.w18) ∗
  ((a + 152#64) ↦₆₄ w.w19) ∗ ((a + 160#64) ↦₆₄ w.w20) ∗ ((a + 168#64) ↦₆₄ w.w21) ∗
  ((a + 176#64) ↦₆₄ w.w22) ∗ ((a + 184#64) ↦₆₄ w.w23) ∗ ((a + 192#64) ↦₆₄ w.w24) ∗
  ((a + 200#64) ↦₆₄ w.w25) ∗ ((a + 208#64) ↦₆₄ w.w26) ∗ ((a + 216#64) ↦₆₄ w.w27) ∗
  ((a + 224#64) ↦₆₄ w.w28) ∗ ((a + 232#64) ↦₆₄ w.w29) ∗ ((a + 240#64) ↦₆₄ w.w30)

private theorem r2_memRegion248_open (a : BitVec 64) :
    memRegion a 248 ⊢ ∃∗ w : r2_SlotWords, r2_words31 a w := by
  have heq : memRegion a 248 = cells a 31 := ProofLib.memRegion_cells a 31 (by decide)
  rw [heq]
  simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w0; apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w2; apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w4; apply Entails.sepExists_elim; intro w5
  apply Entails.sepExists_elim; intro w6; apply Entails.sepExists_elim; intro w7
  apply Entails.sepExists_elim; intro w8; apply Entails.sepExists_elim; intro w9
  apply Entails.sepExists_elim; intro w10; apply Entails.sepExists_elim; intro w11
  apply Entails.sepExists_elim; intro w12; apply Entails.sepExists_elim; intro w13
  apply Entails.sepExists_elim; intro w14; apply Entails.sepExists_elim; intro w15
  apply Entails.sepExists_elim; intro w16; apply Entails.sepExists_elim; intro w17
  apply Entails.sepExists_elim; intro w18; apply Entails.sepExists_elim; intro w19
  apply Entails.sepExists_elim; intro w20; apply Entails.sepExists_elim; intro w21
  apply Entails.sepExists_elim; intro w22; apply Entails.sepExists_elim; intro w23
  apply Entails.sepExists_elim; intro w24; apply Entails.sepExists_elim; intro w25
  apply Entails.sepExists_elim; intro w26; apply Entails.sepExists_elim; intro w27
  apply Entails.sepExists_elim; intro w28; apply Entails.sepExists_elim; intro w29
  apply Entails.sepExists_elim; intro w30
  exact Entails.sepExists_right
    ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15,
     w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30⟩
    (Entails.refl _)

private theorem r2_words31_to_memRegion248 (a : BitVec 64) (w : r2_SlotWords) :
    r2_words31 a w ⊢ memRegion a 248 := by
  have heq : memRegion a 248 = cells a 31 := ProofLib.memRegion_cells a 31 (by decide)
  rw [heq]
  simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_right]
  exact Entails.sepExists_right w.w0 (Entails.sepExists_right w.w1 (Entails.sepExists_right w.w2
    (Entails.sepExists_right w.w3 (Entails.sepExists_right w.w4 (Entails.sepExists_right w.w5
    (Entails.sepExists_right w.w6 (Entails.sepExists_right w.w7 (Entails.sepExists_right w.w8
    (Entails.sepExists_right w.w9 (Entails.sepExists_right w.w10 (Entails.sepExists_right w.w11
    (Entails.sepExists_right w.w12 (Entails.sepExists_right w.w13 (Entails.sepExists_right w.w14
    (Entails.sepExists_right w.w15 (Entails.sepExists_right w.w16 (Entails.sepExists_right w.w17
    (Entails.sepExists_right w.w18 (Entails.sepExists_right w.w19 (Entails.sepExists_right w.w20
    (Entails.sepExists_right w.w21 (Entails.sepExists_right w.w22 (Entails.sepExists_right w.w23
    (Entails.sepExists_right w.w24 (Entails.sepExists_right w.w25 (Entails.sepExists_right w.w26
    (Entails.sepExists_right w.w27 (Entails.sepExists_right w.w28 (Entails.sepExists_right w.w29
      (Entails.sepExists_right w.w30 (Entails.refl _)))))))))))))))))))))))))))))))


private def r2_boxLive (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  if bs = [] then emp else A.live ptr bs.length 1

private theorem r2_boxU8At_eq (A : RustAlloc) (a ptr : BitVec 64) (bs : List (BitVec 8)) :
    boxU8At A a ptr bs =
      ⌜ptr ≠ 0 ∧ bs.length < 2 ^ 63⌝ ∗
        (a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ r2_boxLive A ptr bs := by
  unfold boxU8At r2_boxLive
  have ha : a + asm64% boxSliceLenOff = a + 8#64 := rfl
  rw [ha]
  cases bs with
  | nil =>
    simp only [↓reduceIte, pointsToBytes_nil]
    ac_rfl
  | cons b tl =>
    have hne : b :: tl ≠ [] := List.cons_ne_nil b tl
    simp only [hne, ↓reduceIte]
    ac_rfl

private theorem r2_boxLive_to_sliceDeallocX (A : RustAlloc) (ptr : BitVec 64)
    (bs : List (BitVec 8)) (hlen : bs.length < 2 ^ 63) :
    (ptr ↦ₛ bs) ∗ r2_boxLive A ptr bs ⊢
      DropPreKeyMsgHelpers.sliceDeallocX A ptr (BitVec.ofNat 64 bs.length) := by
  unfold r2_boxLive DropPreKeyMsgHelpers.sliceDeallocX
  cases bs with
  | nil =>
    simp only [List.length_nil, ↓reduceIte, pointsToBytes_nil, emp_sepConj, beq_self_eq_true]
    exact Entails.refl emp
  | cons b tl =>
    have hne : b :: tl ≠ [] := List.cons_ne_nil b tl
    have hpos : 0 < (b :: tl).length := List.length_pos_of_ne_nil hne
    have h64 : (b :: tl).length < 2 ^ 64 := by omega
    have hto : (BitVec.ofNat 64 (b :: tl).length).toNat = (b :: tl).length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]
    have hbeq : (BitVec.ofNat 64 (b :: tl).length == 0#64) = false :=
      beq_eq_false_iff_ne.mpr fun h => by rw [h] at hto; simp at hto
    simp only [hne, hbeq, Bool.false_eq_true, ↓reduceIte, hto]
    refine Entails.pure_right ⟨hpos, hlen⟩ ?_
    rw [sepConj_comm]
    exact sepConj_mono_right (ProofLib.pointsToBytes_entails_memRegion ptr (b :: tl))

private theorem r2_u32_pad4_eq (a : BitVec 64) (lo : BitVec 32) :
    ((a ↦₃₂ lo) ∗ memRegion (a + 4#64) 4) =
      ∃∗ hi : BitVec 32, a ↦₆₄ r2_pack8 (unpack32 lo ++ unpack32 hi) := by
  rw [r2_memRegion4_eq_exists_u32 (a + 4#64), sepExists_sepConj_right]
  simp only [r2_u32_pair_eq_word]

/-- Open `encResAt A r (.ok (.signalMessage m))` into 31 words `ws` at `r` plus the owned
serialized slice `(g.serPtr ↦ₛ m.serialized)` and deallocation tokens for all four buffers. -/
private theorem r2_open_signalMessage (A : RustAlloc) (r : BitVec 64)
    (g : SignalMessageGhost) (m : SignalMessage) :
    (r ↦₆₄ ctSignalTag) ∗ signalMessageAt A g (r + 8#64) m ∗ memRegion (r + 0x80#64) 120 ⊢
      ∃∗ ws : r2_SlotWords, ∃∗ adPtr : BitVec 64, ∃∗ adLen : BitVec 64,
        ⌜ws.w0 = ctSignalTag ∧ ws.w1 = g.pqCap ∧ ws.w2 = g.pqPtr ∧
          ws.w4 = g.ctPtr ∧ ws.w5 = BitVec.ofNat 64 m.ciphertext.length ∧
          ws.w6 = g.serPtr ∧ ws.w7 = BitVec.ofNat 64 m.serialized.length ∧
          ws.w12 = adPtr ∧ ws.w13 = adLen ∧
          m.serialized.length < 2 ^ 40 ∧ g.serPtr ≠ 0⌝ ∗
        r2_words31 r ws ∗
        (g.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A g.serPtr m.serialized ∗
        DropPreKeyMsgHelpers.sliceDeallocX A g.ctPtr (BitVec.ofNat 64 m.ciphertext.length) ∗
        DropPreKeyMsgHelpers.sliceDeallocX A g.pqPtr g.pqCap ∗
        DropPreKeyMsgHelpers.optSliceDeallocX A adPtr adLen := by
  unfold signalMessageAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  rw [sepConj_left_comm]
  apply Entails.pure_left; intro hsm
  have hpq := DropPreKeyMsgHelpers.vecU8At_entails_sliceDeallocX A (r + 8#64) g.pqCap g.pqPtr m.pqRatchet
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpq
  have hct := DropPreKeyMsgHelpers.boxU8At_entails_sliceDeallocX A (r + 32#64) g.ctPtr m.ciphertext
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hct
  have had := DropPreKeyMsgHelpers.optBoxU8At_entails_optSliceDeallocX A (r + 96#64) g.addrPtr m.addresses
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at had
  have hsrk : ((r + 64#64) ↦ₛ m.senderRatchetKey.bytes.toList) ⊢ cells (r + 64#64) 4 := by
    rw [← ProofLib.memRegion_cells (r + 64#64) 4 (by decide)]
    exact DropPreKeyMsgHelpers.pkBytes_entails_memRegion32 (r + 64#64) m.senderRatchetKey
  have htail :
      ((r + 112#64) ↦₃₂ m.counter) ∗ ((r + 116#64) ↦₃₂ m.previousCounter) ∗
        ((r + 120#64) ↦₈ m.messageVersion) ∗ memRegion (r + 121#64) 7 ∗
        memRegion (r + 128#64) 120 ⊢
      cells (r + 112#64) 17 := by
    rw [← ProofLib.memRegion_cells (r + 112#64) 17 (by decide)]
    have ht := DropPreKeyMsgHelpers.trailer16_entails_memRegion16 (r + 112#64)
      m.counter m.previousCounter m.messageVersion
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at ht
    have hgrp_t :
        ((r + 112#64) ↦₃₂ m.counter) ∗ ((r + 116#64) ↦₃₂ m.previousCounter) ∗
          ((r + 120#64) ↦₈ m.messageVersion) ∗ memRegion (r + 121#64) 7 ∗
          memRegion (r + 128#64) 120 =
        (((r + 112#64) ↦₃₂ m.counter) ∗ ((r + 116#64) ↦₃₂ m.previousCounter) ∗
          ((r + 120#64) ↦₈ m.messageVersion) ∗ memRegion (r + 121#64) 7) ∗
          memRegion (r + 128#64) 120 := by
      ac_rfl
    rw [hgrp_t, show (8 * 17 : Nat) = 136 from rfl,
        ProofLib.memRegion_split' (b := r + 112#64) (n := 16) (k := 120)
          (b' := r + 128#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left ht
  rw [r2_boxU8At_eq A (r + 48#64) g.serPtr m.serialized]
  refine Entails.trans
    (sepConj_mono_right
      (sepConj_mono hpq
        (sepConj_mono hct
          (sepConj_mono_right
            (sepConj_mono hsrk (sepConj_mono had htail)))))) ?_
  rw [ProofLib.memRegion_eight (r + 24#64)]
  simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  simp only [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w8
  apply Entails.sepExists_elim; intro w9
  apply Entails.sepExists_elim; intro w10
  apply Entails.sepExists_elim; intro w11
  apply Entails.sepExists_elim; intro adPtr
  apply Entails.sepExists_elim; intro adLen
  apply Entails.sepExists_elim; intro w14
  apply Entails.sepExists_elim; intro w15
  apply Entails.sepExists_elim; intro w16
  apply Entails.sepExists_elim; intro w17
  apply Entails.sepExists_elim; intro w18
  apply Entails.sepExists_elim; intro w19
  apply Entails.sepExists_elim; intro w20
  apply Entails.sepExists_elim; intro w21
  apply Entails.sepExists_elim; intro w22
  apply Entails.sepExists_elim; intro w23
  apply Entails.sepExists_elim; intro w24
  apply Entails.sepExists_elim; intro w25
  apply Entails.sepExists_elim; intro w26
  apply Entails.sepExists_elim; intro w27
  apply Entails.sepExists_elim; intro w28
  apply Entails.sepExists_elim; intro w29
  apply Entails.sepExists_elim; intro w30
  let ws : r2_SlotWords :=
    ⟨ctSignalTag, g.pqCap, g.pqPtr, w3, g.ctPtr, BitVec.ofNat 64 m.ciphertext.length,
     g.serPtr, BitVec.ofNat 64 m.serialized.length, w8, w9, w10, w11, adPtr, adLen,
     w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30⟩
  refine Entails.trans (Q :=
        ⌜g.ctPtr ≠ 0⌝ ∗ ⌜g.serPtr ≠ 0 ∧ m.serialized.length < 2 ^ 63⌝ ∗
          (r2_words31 r ws ∗
            (g.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A g.serPtr m.serialized ∗
            DropPreKeyMsgHelpers.sliceDeallocX A g.ctPtr (BitVec.ofNat 64 m.ciphertext.length) ∗
            DropPreKeyMsgHelpers.sliceDeallocX A g.pqPtr g.pqCap ∗
            DropPreKeyMsgHelpers.optSliceDeallocX A adPtr adLen))
      (by unfold r2_words31; dsimp only [ws]; exact Entails.of_eq (by ac_rfl)) ?_
  apply Entails.pure_left; intro _
  apply Entails.pure_left; rintro ⟨hser_ne, _⟩
  refine Entails.sepExists_right ws
    (Entails.sepExists_right adPtr (Entails.sepExists_right adLen ?_))
  exact Entails.pure_right ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hsm.2.1, hser_ne⟩
    (Entails.refl _)

private def r2_words15 (a : BitVec 64) (w : r2_SlotWords) : SepProp :=
  (a ↦₆₄ w.w0) ∗ ((a + 8#64) ↦₆₄ w.w1) ∗ ((a + 16#64) ↦₆₄ w.w2) ∗ ((a + 24#64) ↦₆₄ w.w3) ∗
  ((a + 32#64) ↦₆₄ w.w4) ∗ ((a + 40#64) ↦₆₄ w.w5) ∗ ((a + 48#64) ↦₆₄ w.w6) ∗
  ((a + 56#64) ↦₆₄ w.w7) ∗ ((a + 64#64) ↦₆₄ w.w8) ∗ ((a + 72#64) ↦₆₄ w.w9) ∗
  ((a + 80#64) ↦₆₄ w.w10) ∗ ((a + 88#64) ↦₆₄ w.w11) ∗ ((a + 96#64) ↦₆₄ w.w12) ∗
  ((a + 104#64) ↦₆₄ w.w13) ∗ ((a + 112#64) ↦₆₄ w.w14)

private def r2_words3 (a : BitVec 64) (w : r2_SlotWords) : SepProp :=
  (a ↦₆₄ w.w15) ∗ ((a + 8#64) ↦₆₄ w.w16) ∗ ((a + 16#64) ↦₆₄ w.w17)

private def r2_words13 (a : BitVec 64) (w : r2_SlotWords) : SepProp :=
  (a ↦₆₄ w.w18) ∗ ((a + 8#64) ↦₆₄ w.w19) ∗ ((a + 16#64) ↦₆₄ w.w20) ∗ ((a + 24#64) ↦₆₄ w.w21) ∗
  ((a + 32#64) ↦₆₄ w.w22) ∗ ((a + 40#64) ↦₆₄ w.w23) ∗ ((a + 48#64) ↦₆₄ w.w24) ∗
  ((a + 56#64) ↦₆₄ w.w25) ∗ ((a + 64#64) ↦₆₄ w.w26) ∗ ((a + 72#64) ↦₆₄ w.w27) ∗
  ((a + 80#64) ↦₆₄ w.w28) ∗ ((a + 88#64) ↦₆₄ w.w29) ∗ ((a + 96#64) ↦₆₄ w.w30)

private theorem r2_words31_split (a : BitVec 64) (w : r2_SlotWords) :
    r2_words31 a w =
      r2_words15 a w ∗ r2_words3 (a + 120#64) w ∗ r2_words13 (a + 144#64) w := by
  unfold r2_words31 r2_words15 r2_words3 r2_words13
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem r2_optBox_reloc (A : RustAlloc) (src ptr : BitVec 64)
    (optBs : Option (List (BitVec 8))) :
    optBoxU8At A src ptr optBs ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ H : SepProp,
        ⌜∀ dst, (dst ↦₆₄ w0) ∗ ((dst + 8#64) ↦₆₄ w1) ∗ H ⊢ optBoxU8At A dst ptr optBs⌝ ∗
          (src ↦₆₄ w0) ∗ ((src + 8#64) ↦₆₄ w1) ∗ H := by
  cases optBs with
  | none =>
    dsimp only [optBoxU8At]
    rw [ProofLib.memRegion_eight (src + 8#64), sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro w1
    refine Entails.sepExists_right 0#64 (Entails.sepExists_right w1 (Entails.sepExists_right emp ?_))
    rw [sepConj_emp]
    refine Entails.pure_right (fun dst => ?_) (Entails.refl _)
    rw [sepConj_emp]
    exact sepConj_mono_right (pointsTo64_entails_memRegion (dst + 8#64) w1)
  | some bs =>
    dsimp only [optBoxU8At]
    rw [r2_boxU8At_eq A src ptr bs]
    apply Entails.pure_left; intro hp
    refine Entails.sepExists_right ptr
      (Entails.sepExists_right (BitVec.ofNat 64 bs.length)
        (Entails.sepExists_right ((ptr ↦ₛ bs) ∗ r2_boxLive A ptr bs) ?_))
    refine Entails.pure_right (fun dst => ?_) (Entails.of_eq (by ac_rfl))
    rw [r2_boxU8At_eq A dst ptr bs]
    exact Entails.pure_right hp (Entails.of_eq (by ac_rfl))

private theorem r2_optU32_reloc (src : BitVec 64) (o : Option (BitVec 32)) :
    optU32At src o ⊢
      ∃∗ w : BitVec 64, ⌜∀ dst, (dst ↦₆₄ w) ⊢ optU32At dst o⌝ ∗ (src ↦₆₄ w) := by
  cases o with
  | none =>
    dsimp only [optU32At]
    rw [r2_u32_pad4_eq src 0#32]
    apply Entails.sepExists_elim; intro hi
    refine Entails.sepExists_right (r2_pack8 (unpack32 0#32 ++ unpack32 hi)) ?_
    refine Entails.pure_right (fun dst => ?_) (Entails.refl _)
    rw [r2_u32_pad4_eq dst 0#32]
    exact Entails.sepExists_right hi (Entails.refl _)
  | some v =>
    dsimp only [optU32At]
    rw [r2_u32_pair_eq_word src 1#32 v]
    refine Entails.sepExists_right (r2_pack8 (unpack32 1#32 ++ unpack32 v)) ?_
    refine Entails.pure_right (fun dst => ?_) (Entails.refl _)
    rw [r2_u32_pair_eq_word dst 1#32 v]
    exact Entails.refl _

private theorem r2_optKyber_reloc (A : RustAlloc) (src ptr : BitVec 64)
    (optK : Option KyberPayload) :
    optKyberAt A src ptr optK ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ H : SepProp,
        ⌜∀ dst,
          (dst ↦₆₄ w0) ∗ ((dst + 8#64) ↦₆₄ w1) ∗ ((dst + 16#64) ↦₆₄ w2) ∗ H ⊢
            optKyberAt A dst ptr optK⌝ ∗
        (src ↦₆₄ w0) ∗ ((src + 8#64) ↦₆₄ w1) ∗ ((src + 16#64) ↦₆₄ w2) ∗ H := by
  cases optK with
  | none =>
    dsimp only [optKyberAt]
    rw [ProofLib.memRegion_split (src + 8#64) 8 8 (by decide),
        ProofLib.memRegion_eight (src + 8#64), ProofLib.memRegion_eight _]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    simp only [sepExists_sepConj_left]
    simp only [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro w1
    apply Entails.sepExists_elim; intro w2
    refine Entails.sepExists_right 0#64 (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right emp ?_)))
    simp only [sepConj_emp]
    refine Entails.pure_right (fun dst => ?_) (Entails.refl _)
    rw [ProofLib.memRegion_split (dst + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono_right
      (sepConj_mono (pointsTo64_entails_memRegion _ w1) (pointsTo64_entails_memRegion _ w2))
  | some k =>
    dsimp only [optKyberAt]
    have ha20 : src + 0x10#64 + 4#64 = src + 0x14#64 := by bv_omega
    rw [← ha20, r2_u32_pad4_eq (src + 0x10#64) k.preKeyId,
        r2_boxU8At_eq A src ptr k.ciphertext]
    simp only [sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro hi
    apply Entails.pure_left; intro hp
    let w2 := r2_pack8 (unpack32 k.preKeyId ++ unpack32 hi)
    let Hk := (ptr ↦ₛ k.ciphertext) ∗ r2_boxLive A ptr k.ciphertext
    refine Entails.sepExists_right ptr
      (Entails.sepExists_right (BitVec.ofNat 64 k.ciphertext.length)
        (Entails.sepExists_right w2 (Entails.sepExists_right Hk ?_)))
    refine Entails.pure_right (fun dst => ?_) (Entails.of_eq (by dsimp only [Hk, w2]; ac_rfl))
    have hd20 : dst + 0x10#64 + 4#64 = dst + 0x14#64 := by bv_omega
    rw [← hd20, r2_u32_pad4_eq (dst + 0x10#64) k.preKeyId,
        r2_boxU8At_eq A dst ptr k.ciphertext]
    have hhi :
        ((dst + 16#64) ↦₆₄ w2) ⊢
          ∃∗ hi' : BitVec 32, (dst + 0x10#64) ↦₆₄ r2_pack8 (unpack32 k.preKeyId ++ unpack32 hi') :=
      Entails.sepExists_right hi (Entails.refl _)
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hhi))) ?_
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono_left (Entails.pure_right hp (Entails.refl _)))
    dsimp only [Hk, w2]; ac_rfl

private theorem r2_pk32_eq_words4 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    (a ↦ₛ bs) =
      ((a ↦₆₄ r2_pack8 (bs.take 8)) ∗
       ((a + 8#64) ↦₆₄ r2_pack8 ((bs.drop 8).take 8)) ∗
       ((a + 16#64) ↦₆₄ r2_pack8 ((bs.drop 16).take 8)) ∗
       ((a + 24#64) ↦₆₄ r2_pack8 (bs.drop 24))) :=
  r2_pointsToBytes32_eq_words4 a bs h

private def r2_pqHeap (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

private theorem r2_vecU8At_eq_pqHeap (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
        r2_pqHeap A cap ptr bs := rfl

private theorem r2_sigMsg_reloc (A : RustAlloc) (src : BitVec 64)
    (g : SignalMessageGhost) (m : SignalMessage) :
    signalMessageAt A g src m ⊢
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
      ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64,
      ∃∗ w11 : BitVec 64, ∃∗ w12 : BitVec 64, ∃∗ w13 : BitVec 64, ∃∗ w14 : BitVec 64,
      ∃∗ H : SepProp,
        ⌜g.pqCap.toNat < 2 ^ 63 ∧
          ∀ dst,
            ((dst ↦₆₄ g.pqCap) ∗ ((dst + 8#64) ↦₆₄ g.pqPtr) ∗
              ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 m.pqRatchet.length) ∗
              ((dst + 24#64) ↦₆₄ w3) ∗ ((dst + 32#64) ↦₆₄ w4) ∗
              ((dst + 40#64) ↦₆₄ w5) ∗ ((dst + 48#64) ↦₆₄ w6) ∗
              ((dst + 56#64) ↦₆₄ w7) ∗ ((dst + 64#64) ↦₆₄ w8) ∗
              ((dst + 72#64) ↦₆₄ w9) ∗ ((dst + 80#64) ↦₆₄ w10) ∗
              ((dst + 88#64) ↦₆₄ w11) ∗ ((dst + 96#64) ↦₆₄ w12) ∗
              ((dst + 104#64) ↦₆₄ w13) ∗ ((dst + 112#64) ↦₆₄ w14)) ∗ H ⊢
              signalMessageAt A g dst m⌝ ∗
        (((src ↦₆₄ g.pqCap) ∗ ((src + 8#64) ↦₆₄ g.pqPtr) ∗
          ((src + 16#64) ↦₆₄ BitVec.ofNat 64 m.pqRatchet.length) ∗
          ((src + 24#64) ↦₆₄ w3) ∗ ((src + 32#64) ↦₆₄ w4) ∗
          ((src + 40#64) ↦₆₄ w5) ∗ ((src + 48#64) ↦₆₄ w6) ∗
          ((src + 56#64) ↦₆₄ w7) ∗ ((src + 64#64) ↦₆₄ w8) ∗
          ((src + 72#64) ↦₆₄ w9) ∗ ((src + 80#64) ↦₆₄ w10) ∗
          ((src + 88#64) ↦₆₄ w11) ∗ ((src + 96#64) ↦₆₄ w12) ∗
          ((src + 104#64) ↦₆₄ w13) ∗ ((src + 112#64) ↦₆₄ w14)) ∗ H) := by
  unfold signalMessageAt
  apply Entails.pure_left; intro hdes
  have hsrk_len : m.senderRatchetKey.bytes.toList.length = 32 := by simp
  have hpq_lt :
      r2_pqHeap A g.pqCap g.pqPtr m.pqRatchet ⊢
        ⌜g.pqCap.toNat < 2 ^ 63⌝ ∗ r2_pqHeap A g.pqCap g.pqPtr m.pqRatchet := by
    unfold r2_pqHeap
    apply Entails.pure_left; rintro ⟨hle, hlt, hne⟩
    exact Entails.pure_right hlt (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))
  rw [r2_vecU8At_eq_pqHeap A src g.pqCap g.pqPtr m.pqRatchet]
  try simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hc_prev :
      ((src + 104#64) ↦₃₂ m.counter) ∗ ((src + 108#64) ↦₃₂ m.previousCounter) =
        ((src + 104#64) ↦₆₄ r2_pack8 (unpack32 m.counter ++ unpack32 m.previousCounter)) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r2_u32_pair_eq_word (src + 104#64) m.counter m.previousCounter
  have hv_pad :=
    r2_u8_pad7_reloc m.messageVersion (fun _ => rfl) (src + 112#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hv_pad
  have had_rel := r2_optBox_reloc A (src + 88#64) g.addrPtr m.addresses
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at had_rel
  rw [r2_boxU8At_eq A (src + 24#64) g.ctPtr m.ciphertext,
      r2_boxU8At_eq A (src + 40#64) g.serPtr m.serialized,
      r2_pk32_eq_words4 (src + 56#64) m.senderRatchetKey.bytes.toList hsrk_len]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans (Entails.of_eq (Q :=
      optBoxU8At A (src + 88#64) g.addrPtr m.addresses ∗
        (((src + 112#64) ↦₈ m.messageVersion) ∗ memRegion (src + 113#64) 7) ∗
        r2_pqHeap A g.pqCap g.pqPtr m.pqRatchet ∗
        (((src + 104#64) ↦₃₂ m.counter) ∗ ((src + 108#64) ↦₃₂ m.previousCounter)) ∗
        (⌜g.ctPtr ≠ 0 ∧ m.ciphertext.length < 2 ^ 63⌝ ∗
          ⌜g.serPtr ≠ 0 ∧ m.serialized.length < 2 ^ 63⌝ ∗
          ((src ↦₆₄ g.pqCap) ∗ ((src + 8#64) ↦₆₄ g.pqPtr) ∗
            ((src + 16#64) ↦₆₄ BitVec.ofNat 64 m.pqRatchet.length) ∗
            ((src + 24#64) ↦₆₄ g.ctPtr) ∗
            ((src + 32#64) ↦₆₄ BitVec.ofNat 64 m.ciphertext.length) ∗
            ((src + 40#64) ↦₆₄ g.serPtr) ∗
            ((src + 48#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
            ((src + 56#64) ↦₆₄ r2_pack8 (m.senderRatchetKey.bytes.toList.take 8)) ∗
            ((src + 64#64) ↦₆₄ r2_pack8 ((m.senderRatchetKey.bytes.toList.drop 8).take 8)) ∗
            ((src + 72#64) ↦₆₄ r2_pack8 ((m.senderRatchetKey.bytes.toList.drop 16).take 8)) ∗
            ((src + 80#64) ↦₆₄ r2_pack8 (m.senderRatchetKey.bytes.toList.drop 24))) ∗
          ((g.ctPtr ↦ₛ m.ciphertext) ∗ r2_boxLive A g.ctPtr m.ciphertext ∗
            (g.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A g.serPtr m.serialized)))
    (by ac_rfl)) ?_
  rw [hc_prev]
  refine Entails.trans
    (sepConj_mono had_rel (sepConj_mono hv_pad (sepConj_mono_left hpq_lt))) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w11
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w12
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro Had
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w14
  let srk := m.senderRatchetKey.bytes.toList
  let w7 := r2_pack8 (srk.take 8)
  let w8 := r2_pack8 ((srk.drop 8).take 8)
  let w9 := r2_pack8 ((srk.drop 16).take 8)
  let w10 := r2_pack8 (srk.drop 24)
  let w13 := r2_pack8 (unpack32 m.counter ++ unpack32 m.previousCounter)
  let Htot : SepProp :=
    r2_pqHeap A g.pqCap g.pqPtr m.pqRatchet ∗
      (g.ctPtr ↦ₛ m.ciphertext) ∗ r2_boxLive A g.ctPtr m.ciphertext ∗
      (g.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A g.serPtr m.serialized ∗ Had
  refine Entails.trans (Q :=
      ⌜g.pqCap.toNat < 2 ^ 63⌝ ∗
        ⌜∀ dst, ((dst ↦₆₄ w11) ∗ ((dst + 8#64) ↦₆₄ w12) ∗ Had) ⊢
          optBoxU8At A dst g.addrPtr m.addresses⌝ ∗
        ⌜∀ dst, (dst ↦₆₄ w14) ⊢ (dst ↦₈ m.messageVersion) ∗ memRegion (dst + 1#64) 7⌝ ∗
        ⌜g.ctPtr ≠ 0 ∧ m.ciphertext.length < 2 ^ 63⌝ ∗
        ⌜g.serPtr ≠ 0 ∧ m.serialized.length < 2 ^ 63⌝ ∗
        (((src ↦₆₄ g.pqCap) ∗ ((src + 8#64) ↦₆₄ g.pqPtr) ∗
          ((src + 16#64) ↦₆₄ BitVec.ofNat 64 m.pqRatchet.length) ∗
          ((src + 24#64) ↦₆₄ g.ctPtr) ∗
          ((src + 32#64) ↦₆₄ BitVec.ofNat 64 m.ciphertext.length) ∗
          ((src + 40#64) ↦₆₄ g.serPtr) ∗
          ((src + 48#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
          ((src + 56#64) ↦₆₄ w7) ∗ ((src + 64#64) ↦₆₄ w8) ∗
          ((src + 72#64) ↦₆₄ w9) ∗ ((src + 80#64) ↦₆₄ w10) ∗
          ((src + 88#64) ↦₆₄ w11) ∗ ((src + 96#64) ↦₆₄ w12) ∗
          ((src + 104#64) ↦₆₄ w13) ∗ ((src + 112#64) ↦₆₄ w14)) ∗ Htot))
    (by dsimp only [Htot, srk, w7, w8, w9, w10, w13]; exact Entails.of_eq (by ac_rfl)) ?_
  apply Entails.pure_left; intro hpq_cap
  apply Entails.pure_left; intro hclose_ad
  apply Entails.pure_left; intro hclose_ver
  apply Entails.pure_left; intro hct_p
  apply Entails.pure_left; intro hser_p
  refine Entails.sepExists_right g.ctPtr (Entails.sepExists_right
    (BitVec.ofNat 64 m.ciphertext.length) (Entails.sepExists_right g.serPtr
    (Entails.sepExists_right (BitVec.ofNat 64 m.serialized.length)
    (Entails.sepExists_right w7 (Entails.sepExists_right w8
    (Entails.sepExists_right w9 (Entails.sepExists_right w10
    (Entails.sepExists_right w11 (Entails.sepExists_right w12
    (Entails.sepExists_right w13 (Entails.sepExists_right w14
    (Entails.sepExists_right Htot ?_))))))))))))
  refine Entails.pure_right ⟨hpq_cap, fun dst => ?_⟩ (Entails.refl _)
  rw [r2_vecU8At_eq_pqHeap A dst g.pqCap g.pqPtr m.pqRatchet]
  try simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hdc_prev :
      ((dst + 104#64) ↦₃₂ m.counter) ∗ ((dst + 108#64) ↦₃₂ m.previousCounter) =
        ((dst + 104#64) ↦₆₄ w13) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r2_u32_pair_eq_word (dst + 104#64) m.counter m.previousCounter
  rw [r2_boxU8At_eq A (dst + 24#64) g.ctPtr m.ciphertext,
      r2_boxU8At_eq A (dst + 40#64) g.serPtr m.serialized,
      r2_pk32_eq_words4 (dst + 56#64) srk hsrk_len]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hd_ver : ((dst + 112#64) ↦₆₄ w14) ⊢
      ((dst + 112#64) ↦₈ m.messageVersion) ∗ memRegion (dst + 113#64) 7 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hclose_ver (dst + 112#64)
  have hd_ad :
      ((dst + 88#64) ↦₆₄ w11) ∗ ((dst + 96#64) ↦₆₄ w12) ∗ Had ⊢
        optBoxU8At A (dst + 88#64) g.addrPtr m.addresses := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hclose_ad (dst + 88#64)
  have hd_ct :
      (((dst + 24#64) ↦₆₄ g.ctPtr) ∗
          ((dst + 32#64) ↦₆₄ BitVec.ofNat 64 m.ciphertext.length) ∗
          (g.ctPtr ↦ₛ m.ciphertext) ∗ r2_boxLive A g.ctPtr m.ciphertext) ⊢
        ⌜g.ctPtr ≠ 0 ∧ m.ciphertext.length < 2 ^ 63⌝ ∗
          ((dst + 24#64) ↦₆₄ g.ctPtr) ∗
          ((dst + 32#64) ↦₆₄ BitVec.ofNat 64 m.ciphertext.length) ∗
          (g.ctPtr ↦ₛ m.ciphertext) ∗ r2_boxLive A g.ctPtr m.ciphertext :=
    Entails.pure_right hct_p (Entails.refl _)
  have hd_ser :
      (((dst + 40#64) ↦₆₄ g.serPtr) ∗
          ((dst + 48#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
          (g.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A g.serPtr m.serialized) ⊢
        ⌜g.serPtr ≠ 0 ∧ m.serialized.length < 2 ^ 63⌝ ∗
          ((dst + 40#64) ↦₆₄ g.serPtr) ∗
          ((dst + 48#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
          (g.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A g.serPtr m.serialized :=
    Entails.pure_right hser_p (Entails.refl _)
  refine Entails.trans (Entails.of_eq (Q :=
      (((dst + 88#64) ↦₆₄ w11) ∗ ((dst + 96#64) ↦₆₄ w12) ∗ Had) ∗
        ((dst + 112#64) ↦₆₄ w14) ∗
        (((dst + 24#64) ↦₆₄ g.ctPtr) ∗
          ((dst + 32#64) ↦₆₄ BitVec.ofNat 64 m.ciphertext.length) ∗
          (g.ctPtr ↦ₛ m.ciphertext) ∗ r2_boxLive A g.ctPtr m.ciphertext) ∗
        (((dst + 40#64) ↦₆₄ g.serPtr) ∗
          ((dst + 48#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
          (g.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A g.serPtr m.serialized) ∗
        (((dst + 104#64) ↦₆₄ w13) ∗
          ((dst ↦₆₄ g.pqCap) ∗ ((dst + 8#64) ↦₆₄ g.pqPtr) ∗
            ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 m.pqRatchet.length)) ∗
          r2_pqHeap A g.pqCap g.pqPtr m.pqRatchet ∗
          ((dst + 56#64) ↦₆₄ w7) ∗ ((dst + 64#64) ↦₆₄ w8) ∗
          ((dst + 72#64) ↦₆₄ w9) ∗ ((dst + 80#64) ↦₆₄ w10)))
    (by dsimp only [Htot]; ac_rfl)) ?_
  rw [← hdc_prev]
  refine Entails.trans
    (sepConj_mono hd_ad (sepConj_mono hd_ver (sepConj_mono hd_ct (sepConj_mono_left hd_ser)))) ?_
  exact Entails.pure_right hdes (Entails.of_eq (by ac_rfl))

/-- Open `preKeyMsgAt A g r m` into 31 words `ws` at `r`, `(g.serPtr ↦ₛ m.serialized)`, and a
relocation frame `H` that rebuilds `preKeyMsgAt A g dst m` at ANY destination `dst`. -/
private theorem r2_open_preKeyMessage (A : RustAlloc) (r : BitVec 64)
    (g : PreKeyMsgGhost) (m : PreKeySignalMessage) :
    preKeyMsgAt A g r m ⊢
      ∃∗ ws : r2_SlotWords, ∃∗ H : SepProp,
        ⌜ws.w0.toNat < 2 ^ 63 ∧
          ws.w16 = g.serPtr ∧ ws.w17 = BitVec.ofNat 64 m.serialized.length ∧
          g.serPtr ≠ 0 ∧ m.serialized.length < 2 ^ 63 ∧
          (∀ dst : BitVec 64,
            r2_words31 dst ws ∗ (g.serPtr ↦ₛ m.serialized) ∗ H ⊢
              preKeyMsgAt A g dst m)⌝ ∗
        r2_words31 r ws ∗ (g.serPtr ↦ₛ m.serialized) ∗ H := by
  unfold preKeyMsgAt
  have h15 := r2_sigMsg_reloc A r g.msg m.message
  have hu32 := r2_optU32_reloc (r + 0x78#64) m.preKeyId
  have hkyb := r2_optKyber_reloc A (r + 0x90#64) g.kyberPtr m.kyberPayload
  have hbk_len : m.baseKey.bytes.toList.length = 32 := by simp
  have hik_len : m.identityKey.publicKey.bytes.toList.length = 32 := by simp
  have hreg_spk :
      ((r + 0xe8#64) ↦₃₂ m.registrationId) ∗ ((r + 0xec#64) ↦₃₂ m.signedPreKeyId) =
        ((r + 232#64) ↦₆₄ r2_pack8 (unpack32 m.registrationId ++ unpack32 m.signedPreKeyId)) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r2_u32_pair_eq_word (r + 232#64) m.registrationId m.signedPreKeyId
  have hver := r2_u8_pad7_reloc m.messageVersion (fun _ => rfl) (r + 0xf0#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hkyb hver
  rw [r2_boxU8At_eq A (r + 0x80#64) g.serPtr m.serialized,
      r2_pk32_eq_words4 (r + 0xa8#64) m.baseKey.bytes.toList hbk_len,
      r2_pk32_eq_words4 (r + 0xc8#64) m.identityKey.publicKey.bytes.toList hik_len]
  refine Entails.trans (Entails.of_eq (Q :=
      signalMessageAt A g.msg r m.message ∗
        optU32At (r + 0x78#64) m.preKeyId ∗
        optKyberAt A (r + 144#64) g.kyberPtr m.kyberPayload ∗
        (((r + 240#64) ↦₈ m.messageVersion) ∗ memRegion (r + 241#64) 7) ∗
        (((r + 0xe8#64) ↦₃₂ m.registrationId) ∗ ((r + 0xec#64) ↦₃₂ m.signedPreKeyId)) ∗
        (⌜g.serPtr ≠ 0 ∧ m.serialized.length < 2 ^ 63⌝ ∗
          ((r + 128#64) ↦₆₄ g.serPtr) ∗
          ((r + 136#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
          (g.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A g.serPtr m.serialized ∗
          ((r + 168#64) ↦₆₄ r2_pack8 (m.baseKey.bytes.toList.take 8)) ∗
          ((r + 176#64) ↦₆₄ r2_pack8 ((m.baseKey.bytes.toList.drop 8).take 8)) ∗
          ((r + 184#64) ↦₆₄ r2_pack8 ((m.baseKey.bytes.toList.drop 16).take 8)) ∗
          ((r + 192#64) ↦₆₄ r2_pack8 (m.baseKey.bytes.toList.drop 24)) ∗
          ((r + 200#64) ↦₆₄ r2_pack8 (m.identityKey.publicKey.bytes.toList.take 8)) ∗
          ((r + 208#64) ↦₆₄ r2_pack8 ((m.identityKey.publicKey.bytes.toList.drop 8).take 8)) ∗
          ((r + 216#64) ↦₆₄ r2_pack8 ((m.identityKey.publicKey.bytes.toList.drop 16).take 8)) ∗
          ((r + 224#64) ↦₆₄ r2_pack8 (m.identityKey.publicKey.bytes.toList.drop 24))))
    (by (try simp only [BitVec.add_assoc, BitVec.reduceAdd]); ac_rfl)) ?_
  rw [hreg_spk]
  refine Entails.trans
    (sepConj_mono h15 (sepConj_mono hu32 (sepConj_mono hkyb (sepConj_mono_left hver)))) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w3
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w4
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w5
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w6
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w7
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w8
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w9
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w10
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w11
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w12
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w13
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w14
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro H15
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w15
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w18
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w19
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w20
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro Hkyb
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w30
  let bk := m.baseKey.bytes.toList
  let ik := m.identityKey.publicKey.bytes.toList
  let ws : r2_SlotWords :=
    ⟨g.msg.pqCap, g.msg.pqPtr, BitVec.ofNat 64 m.message.pqRatchet.length,
     w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
     w15, g.serPtr, BitVec.ofNat 64 m.serialized.length,
     w18, w19, w20,
     r2_pack8 (bk.take 8), r2_pack8 ((bk.drop 8).take 8),
     r2_pack8 ((bk.drop 16).take 8), r2_pack8 (bk.drop 24),
     r2_pack8 (ik.take 8), r2_pack8 ((ik.drop 8).take 8),
     r2_pack8 ((ik.drop 16).take 8), r2_pack8 (ik.drop 24),
     r2_pack8 (unpack32 m.registrationId ++ unpack32 m.signedPreKeyId), w30⟩
  let Htot : SepProp := H15 ∗ r2_boxLive A g.serPtr m.serialized ∗ Hkyb
  refine Entails.trans (Q :=
      ⌜g.msg.pqCap.toNat < 2 ^ 63 ∧
        ∀ dst : BitVec 64,
          ((dst ↦₆₄ g.msg.pqCap) ∗ ((dst + 8#64) ↦₆₄ g.msg.pqPtr) ∗
            ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 m.message.pqRatchet.length) ∗
            ((dst + 24#64) ↦₆₄ w3) ∗ ((dst + 32#64) ↦₆₄ w4) ∗
            ((dst + 40#64) ↦₆₄ w5) ∗ ((dst + 48#64) ↦₆₄ w6) ∗
            ((dst + 56#64) ↦₆₄ w7) ∗ ((dst + 64#64) ↦₆₄ w8) ∗
            ((dst + 72#64) ↦₆₄ w9) ∗ ((dst + 80#64) ↦₆₄ w10) ∗
            ((dst + 88#64) ↦₆₄ w11) ∗ ((dst + 96#64) ↦₆₄ w12) ∗
            ((dst + 104#64) ↦₆₄ w13) ∗ ((dst + 112#64) ↦₆₄ w14) ∗ H15) ⊢
            signalMessageAt A g.msg dst m.message⌝ ∗
        ⌜∀ dst, (dst ↦₆₄ w15) ⊢ optU32At dst m.preKeyId⌝ ∗
        ⌜g.serPtr ≠ 0 ∧ m.serialized.length < 2 ^ 63⌝ ∗
        ⌜∀ dst,
          (dst ↦₆₄ w18) ∗ ((dst + 8#64) ↦₆₄ w19) ∗ ((dst + 16#64) ↦₆₄ w20) ∗ Hkyb ⊢
            optKyberAt A dst g.kyberPtr m.kyberPayload⌝ ∗
        ⌜∀ dst, (dst ↦₆₄ w30) ⊢ (dst ↦₈ m.messageVersion) ∗ memRegion (dst + 1#64) 7⌝ ∗
        r2_words31 r ws ∗ (g.serPtr ↦ₛ m.serialized) ∗ Htot)
    (by unfold r2_words31; dsimp only [ws, Htot, bk, ik]
        exact Entails.of_eq (by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨hpq_lt, hclose15⟩
  apply Entails.pure_left; intro hclose_u32
  apply Entails.pure_left; rintro ⟨hser_ne, hser_lt⟩
  apply Entails.pure_left; intro hclose_kyb
  apply Entails.pure_left; intro hclose_ver
  refine Entails.sepExists_right ws (Entails.sepExists_right Htot ?_)
  refine Entails.pure_right ⟨hpq_lt, rfl, rfl, hser_ne, hser_lt, fun dst => ?_⟩ (Entails.refl _)
  rw [r2_words31_split dst ws]
  have hd_reg_spk :
      ((dst + 0xe8#64) ↦₃₂ m.registrationId) ∗ ((dst + 0xec#64) ↦₃₂ m.signedPreKeyId) =
        ((dst + 232#64) ↦₆₄ r2_pack8 (unpack32 m.registrationId ++ unpack32 m.signedPreKeyId)) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r2_u32_pair_eq_word (dst + 232#64) m.registrationId m.signedPreKeyId
  rw [r2_boxU8At_eq A (dst + 0x80#64) g.serPtr m.serialized,
      r2_pk32_eq_words4 (dst + 0xa8#64) bk hbk_len,
      r2_pk32_eq_words4 (dst + 0xc8#64) ik hik_len]
  have hd_u32 : ((dst + 120#64) ↦₆₄ w15) ⊢ optU32At (dst + 0x78#64) m.preKeyId :=
    hclose_u32 (dst + 0x78#64)
  have hd_kyb :
      ((dst + 144#64) ↦₆₄ w18) ∗ ((dst + 152#64) ↦₆₄ w19) ∗ ((dst + 160#64) ↦₆₄ w20) ∗ Hkyb ⊢
        optKyberAt A (dst + 0x90#64) g.kyberPtr m.kyberPayload := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hclose_kyb (dst + 0x90#64)
  have hd_ver :
      ((dst + 240#64) ↦₆₄ w30) ⊢
        ((dst + 0xf0#64) ↦₈ m.messageVersion) ∗ memRegion (dst + 0xf1#64) 7 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hclose_ver (dst + 0xf0#64)
  have hd_ser :
      ((dst + 128#64) ↦₆₄ g.serPtr) ∗ ((dst + 136#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
          (g.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A g.serPtr m.serialized ⊢
        ⌜g.serPtr ≠ 0 ∧ m.serialized.length < 2 ^ 63⌝ ∗
          ((dst + 0x80#64) ↦₆₄ g.serPtr) ∗
          ((dst + 0x80#64 + 8#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
          (g.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A g.serPtr m.serialized := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.pure_right ⟨hser_ne, hser_lt⟩ (Entails.refl _)
  have hd_15 : r2_words15 dst ws ∗ H15 ⊢ signalMessageAt A g.msg dst m.message := by
    unfold r2_words15; dsimp only [ws]
    exact Entails.trans (Entails.of_eq (by ac_rfl)) (hclose15 dst)
  refine Entails.trans (Entails.of_eq (Q :=
      (r2_words15 dst ws ∗ H15) ∗
        ((dst + 120#64) ↦₆₄ w15) ∗
        (((dst + 128#64) ↦₆₄ g.serPtr) ∗
          ((dst + 136#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
          (g.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A g.serPtr m.serialized) ∗
        (((dst + 144#64) ↦₆₄ w18) ∗ ((dst + 152#64) ↦₆₄ w19) ∗ ((dst + 160#64) ↦₆₄ w20) ∗ Hkyb) ∗
        ((dst + 240#64) ↦₆₄ w30) ∗
        (((dst + 232#64) ↦₆₄ r2_pack8 (unpack32 m.registrationId ++ unpack32 m.signedPreKeyId)) ∗
          ((dst + 0xa8#64) ↦₆₄ r2_pack8 (bk.take 8)) ∗
          ((dst + 0xa8#64 + 8#64) ↦₆₄ r2_pack8 ((bk.drop 8).take 8)) ∗
          ((dst + 0xa8#64 + 16#64) ↦₆₄ r2_pack8 ((bk.drop 16).take 8)) ∗
          ((dst + 0xa8#64 + 24#64) ↦₆₄ r2_pack8 (bk.drop 24)) ∗
          ((dst + 0xc8#64) ↦₆₄ r2_pack8 (ik.take 8)) ∗
          ((dst + 0xc8#64 + 8#64) ↦₆₄ r2_pack8 ((ik.drop 8).take 8)) ∗
          ((dst + 0xc8#64 + 16#64) ↦₆₄ r2_pack8 ((ik.drop 16).take 8)) ∗
          ((dst + 0xc8#64 + 24#64) ↦₆₄ r2_pack8 (ik.drop 24))))
    (by unfold r2_words3 r2_words13; dsimp only [ws, Htot]
        (try simp only [BitVec.add_assoc, BitVec.reduceAdd]); ac_rfl)) ?_
  rw [← hd_reg_spk]
  refine Entails.trans
    (sepConj_mono hd_15
      (sepConj_mono hd_u32
        (sepConj_mono hd_ser
          (sepConj_mono hd_kyb (sepConj_mono_left hd_ver))))) ?_
  exact Entails.of_eq (by ac_rfl)

/-! ## 4. Stack Frame Equalities, Shared Cleanup Tails, Arms, and `run_hop_send_ok` -/

private theorem r2_fnBase_eq (img : Obj.Image) (ext : String → Option (State → State)) :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName =
      img.base + bv% (ls_off% "libsignal_cli::run") := by
  simp only [Program.fnAddr_rebase, MainHops.run_fnOff]

private theorem r2_dealloc_addr (img : Obj.Image) (ext : String → Option (State → State)) :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr deallocName =
      img.base + bv% (ls_off% "__rustc::__rust_dealloc") := by
  simp only [Program.fnAddr_rebase, MainHops.rustDealloc_fnOff]

private theorem r2_encrypt_addr (img : Obj.Image) (ext : String → Option (State → State)) :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr wrapEncryptName =
      img.base + bv% (ls_off% "libsignal_cli_ratchet::encrypt") := by
  simp only [Program.fnAddr_rebase, r2_wrapEncrypt_fnOff]

private theorem r2_concat_addr (img : Obj.Image) (ext : String → Option (State → State)) :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr cliConcatName =
      img.base + bv% (ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]") := by
  simp only [Program.fnAddr_rebase, r2_cliConcat_fnOff]

private theorem r2_dropSpe_addr (img : Obj.Image) (ext : String → Option (State → State)) :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr cliDropSpeName =
      img.base +
        bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]") := by
  simp only [Program.fnAddr_rebase, r2_cliDropSpe_fnOff]

private theorem r2_dropPk_addr (img : Obj.Image) (ext : String → Option (State → State)) :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr cliDropPreKeyMsgName =
      img.base +
        bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::PreKeySignalMessage>") := by
  simp only [Program.fnAddr_rebase, r2_cliDropPreKeyMsg_fnOff]

private theorem r2_bind_eq {α : Sort _} {P : α → Prop} (e : α) (h : ∀ x : α, x = e → P x) : P e :=
  h e rfl

section R2GenEq
open Lean Meta Elab Tactic

private meta def r2GenEqRun (e : Term) (x hx : Ident) (consts : Array Name) : TacticM Unit :=
  withMainContext do
    let eExpr ← elabTerm e none
    let mut letToClear : Array FVarId := #[]
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail && decl.isLet then
        let ty ← instantiateMVars decl.type
        if (ty.find? fun sub => consts.any sub.isConstOf).isSome then
          letToClear := letToClear.push decl.fvarId
    if !letToClear.isEmpty then
      let mut g ← getMainGoal
      for fv in letToClear.reverse do
        g ← g.clearValue fv
      replaceMainGoal [g]
    withMainContext do
      let lctx ← getLCtx
      let mut toRevert : Array FVarId := #[]
      for decl in lctx do
        if !decl.isImplementationDetail && !decl.isLet then
          let ty ← instantiateMVars decl.type
          if (ty.find? fun sub => consts.any sub.isConstOf).isSome then
            toRevert := toRevert.push decl.fvarId
      let (reverted, mvarId) ← (← getMainGoal).revert toRevert true
      mvarId.withContext do
        let target ← instantiateMVars (← mvarId.getType)
        let targetAbst ← kabstract target eExpr
        let eType ← inferType eExpr
        let u ← getLevel eType
        let pLam := Lean.mkLambda x.getId BinderInfo.default eType targetAbst
        let newGoalType ← withLocalDeclD x.getId eType fun xFVar => do
          let eqTy ← mkEq xFVar eExpr
          withLocalDeclD hx.getId eqTy fun hFVar => do
            let pBody := targetAbst.instantiate1 xFVar
            mkForallFVars #[xFVar, hFVar] pBody
        let newMVar ← mkFreshExprSyntheticOpaqueMVar newGoalType (← mvarId.getTag)
        let proof := mkApp4 (mkConst ``r2_bind_eq [u]) eType pLam eExpr newMVar
        mvarId.assign proof
        let (_, mvarId1) ← newMVar.mvarId!.intro1P
        let (_, mvarId2) ← mvarId1.intro1P
        let (_, mvarId3) ← mvarId2.introNP reverted.size
        replaceMainGoal [mvarId3]

scoped elab "r2_gen_eq " e:term:51 " => " x:ident ", " hx:ident " [" cs:ident,* "]" : tactic => do
  let mut names : Array Name := #[]
  for c in cs.getElems do
    names := names.push (← realizeGlobalConstNoOverloadWithInfo c)
  r2GenEqRun e x hx names

scoped elab "r2_prep_norm " rp:ident h1:ident h2:ident h3:ident h4:ident h5:ident h6:ident h7:ident :
    tactic =>
  withMainContext do
    let rpExpr ← elabTerm rp none
    let rpId := rpExpr.fvarId!
    let lctx ← getLCtx
    let mut toRevert : Array FVarId := #[]
    for decl in lctx do
      if !decl.isImplementationDetail && !decl.isLet then
        let ty ← instantiateMVars decl.type
        if (ty.find? fun sub =>
            sub.isConstOf ``Arm64.Program.fetch ||
            sub.isConstOf ``Arm64.Program.externAt? ||
            sub.isConstOf ``Arm64.State.pc).isSome ||
            (ty.containsFVar rpId && decl.userName != `hrprog &&
             decl.userName != `hrfn1 && decl.userName != `hrfn2 &&
             decl.userName != `hrfn3 && decl.userName != `hrfn4 &&
             decl.userName != `hrfn5 && decl.userName != `hrfn6 &&
             decl.userName != `hrfn7) then
          toRevert := toRevert.push decl.fvarId
    let (reverted, mvarId) ← (← getMainGoal).revert toRevert true
    replaceMainGoal [mvarId]
    evalTactic (← `(tactic|
      (try simp only [$h1:ident, $h2:ident, $h3:ident, $h4:ident, $h5:ident, $h6:ident, $h7:ident,
        BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero])))
    let (_, mvarId2) ← (← getMainGoal).introNP reverted.size
    replaceMainGoal [mvarId2]

scoped elab "r2_clear_deps " x:ident hx:ident : tactic => withMainContext do
  let xExpr ← elabTerm x none
  let hxExpr ← elabTerm hx none
  let xId := xExpr.fvarId!
  let hxId := hxExpr.fvarId!
  let lctx ← getLCtx
  let mut fvars : Array FVarId := #[]
  for decl in lctx do
    if !decl.isAuxDecl && decl.fvarId != xId && decl.fvarId != hxId then
      let ty ← instantiateMVars decl.type
      let valHas ← match decl.value? with
        | some v => pure ((← instantiateMVars v).containsFVar xId)
        | none => pure false
      if ty.containsFVar xId || valHas then
        fvars := fvars.push decl.fvarId
  let mut g ← getMainGoal
  for fv in fvars.reverse do
    g ← g.tryClear fv
  replaceMainGoal [g]

@[irreducible] private def R2SpMask (P : Prop) : Prop := P

private theorem r2_sp_mask_in {P : Prop} (h : P) : R2SpMask P := by
  unfold R2SpMask; exact h

private theorem r2_sp_mask_out {P : Prop} (h : R2SpMask P) : P := by
  unfold R2SpMask at h; exact h

scoped elab "r2_hide_sp" : tactic => withMainContext do
  let lctx ← getLCtx
  let mut toMask : Array (FVarId × Expr) := #[]
  for decl in lctx do
    if !decl.isImplementationDetail && !decl.isLet then
      let ty ← instantiateMVars decl.type
      if ty.isAppOfArity ``Eq 3 && (ty.getArg! 1).isAppOfArity ``Arm64.State.sp 1 then
        toMask := toMask.push (decl.fvarId, ty)
  let mut g ← getMainGoal
  for (fv, ty) in toMask.reverse do
    let res ← g.replace fv (mkApp2 (mkConst ``r2_sp_mask_in) ty (mkFVar fv))
    g := res.mvarId
  replaceMainGoal [g]

scoped elab "r2_show_sp" : tactic => withMainContext do
  let lctx ← getLCtx
  let mut toUnmask : Array (FVarId × Expr) := #[]
  for decl in lctx do
    if !decl.isImplementationDetail && !decl.isLet then
      let ty ← instantiateMVars decl.type
      if ty.isAppOfArity ``R2SpMask 1 then
        toUnmask := toUnmask.push (decl.fvarId, ty.getArg! 0)
  let mut g ← getMainGoal
  for (fv, p) in toUnmask.reverse do
    let res ← g.replace fv (mkApp2 (mkConst ``r2_sp_mask_out) p (mkFVar fv))
    g := res.mvarId
  replaceMainGoal [g]

end R2GenEq

private theorem r2_rprog_fnAddr_eq {rprog : Program} {img : Obj.Image}
    {ext : String → Option (State → State)} {sym : String} {addr : BitVec 64}
    (hr : rprog = libsignalSessionCode.rebase img.base (Rust.withPanics ext))
    (h : (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr sym = addr) :
    rprog.fnAddr sym = addr := hr ▸ h

local elab "r2_prep_steps" : tactic => do
  let img := Lean.mkIdent `img
  let ext := Lean.mkIdent `ext
  let rprog := Lean.mkIdent `rprog
  let hrprog := Lean.mkIdent `hrprog
  let hrfn1 := Lean.mkIdent `hrfn1
  let hrfn2 := Lean.mkIdent `hrfn2
  let hrfn3 := Lean.mkIdent `hrfn3
  let hrfn4 := Lean.mkIdent `hrfn4
  let hrfn5 := Lean.mkIdent `hrfn5
  let hrfn6 := Lean.mkIdent `hrfn6
  let hrfn7 := Lean.mkIdent `hrfn7
  Lean.Elab.Tactic.evalTactic (← `(tactic| (
    r2_hide_sp
    dsimp only [mProg, runPc, tripleRatchetProgAtExt] at *
    r2_gen_eq (libsignalSessionCode.rebase ($img).base (Rust.withPanics $ext)) => $rprog, $hrprog
      [Program.fetch, Program.externAt?, Program.fnAddr]
    have $hrfn1 : ($rprog).fnAddr "libsignal_cli::run" = ($img).base + bv% (ls_off% "libsignal_cli::run") :=
      r2_rprog_fnAddr_eq $hrprog (r2_fnBase_eq $img $ext)
    have $hrfn2 : ($rprog).fnAddr runName = ($img).base + bv% (ls_off% "libsignal_cli::run") := $hrfn1
    have $hrfn3 : ($rprog).fnAddr deallocName = ($img).base + bv% (ls_off% "__rustc::__rust_dealloc") :=
      r2_rprog_fnAddr_eq $hrprog (r2_dealloc_addr $img $ext)
    have $hrfn4 : ($rprog).fnAddr wrapEncryptName = ($img).base + bv% (ls_off% "libsignal_cli_ratchet::encrypt") :=
      r2_rprog_fnAddr_eq $hrprog (r2_encrypt_addr $img $ext)
    have $hrfn5 : ($rprog).fnAddr cliConcatName =
        ($img).base + bv% (ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]") :=
      r2_rprog_fnAddr_eq $hrprog (r2_concat_addr $img $ext)
    have $hrfn6 : ($rprog).fnAddr cliDropSpeName =
        ($img).base + bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]") :=
      r2_rprog_fnAddr_eq $hrprog (r2_dropSpe_addr $img $ext)
    have $hrfn7 : ($rprog).fnAddr cliDropPreKeyMsgName =
        ($img).base + bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::PreKeySignalMessage>") :=
      r2_rprog_fnAddr_eq $hrprog (r2_dropPk_addr $img $ext)
    r2_prep_norm $rprog $hrfn1 $hrfn2 $hrfn3 $hrfn4 $hrfn5 $hrfn6 $hrfn7
    clear $hrfn7 $hrfn6 $hrfn5 $hrfn4 $hrfn3 $hrfn2 $hrfn1)))

@[irreducible] private def r2_hold (P : SepProp) : SepProp := P

private theorem r2_hold_eq (P : SepProp) : r2_hold P = P := by
  unfold r2_hold
  rfl

local elab "r2_post_steps" : tactic => do
  let rprog := Lean.mkIdent `rprog
  let hrprog := Lean.mkIdent `hrprog
  Lean.Elab.Tactic.evalTactic (← `(tactic| (
    r2_clear_deps $rprog $hrprog
    rw [$hrprog:ident] at *
    clear $hrprog $rprog
    r2_show_sp)))

local elab "r2_pc_done" : tactic => do
  let hrprog := Lean.mkIdent `hrprog
  Lean.Elab.Tactic.evalTactic (← `(tactic| (
    (try simp only [arm64_norm])
    (try simp only [$hrprog:ident])
    (try simp only [mProg, runPc, tripleRatchetProgAtExt,
      r2_fnBase_eq, r2_dealloc_addr, r2_encrypt_addr,
      r2_concat_addr, r2_dropSpe_addr, r2_dropPk_addr,
      BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero])
    (try rfl))))

private def r2_localGaps (fsp : BitVec 64) : SepProp :=
  memRegion (fsp + 0x10#64) (0x1d0 - 0x10) ∗
  memRegion (fsp + 0x1e0#64) (0x208 - 0x1e0) ∗
  memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
  memRegion (fsp + 0x2a8#64) (0x320 - 0x2a8) ∗
  memRegion (fsp + 0x340#64) (0x4d0 - 0x340) ∗
  memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
  memRegion (fsp + 0x1848#64) (0x23b0 - 0x1848) ∗
  memRegion (fsp + 0x23d0#64) (0x29f0 - 0x23d0)

private theorem r2_tail_split_220 (fsp : BitVec 64) :
    memRegion (fsp + 0x220#64) (runLocalBytes - 0x220) =
      memRegion (fsp + 0x2a0#64) 8 ∗
      memRegion (fsp + 0x320#64) 32 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗
      memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗
      (memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
       memRegion (fsp + 0x2a8#64) (0x320 - 0x2a8) ∗
       memRegion (fsp + 0x340#64) (0x4d0 - 0x340) ∗
       memRegion (fsp + 0x5c8#64) (0x1750 - 0x5c8) ∗
       memRegion (fsp + 0x1848#64) (0x23b0 - 0x1848) ∗
       memRegion (fsp + 0x23d0#64) (0x29f0 - 0x23d0)) := by
  dsimp only [runLocalBytes]
  rw [ProofLib.memRegion_split' (b := fsp + 0x220#64) (n := 0x2a0 - 0x220) (k := 0x29f0 - 0x2a0)
        (b' := fsp + 0x2a0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x2a0#64) (n := 8) (k := 0x29f0 - 0x2a8)
        (b' := fsp + 0x2a8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x2a8#64) (n := 0x320 - 0x2a8) (k := 0x29f0 - 0x320)
        (b' := fsp + 0x320#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x320#64) (n := 32) (k := 0x29f0 - 0x340)
        (b' := fsp + 0x340#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x340#64) (n := 0x4d0 - 0x340) (k := 0x29f0 - 0x4d0)
        (b' := fsp + 0x4d0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x4d0#64) (n := 248) (k := 0x29f0 - 0x5c8)
        (b' := fsp + 0x5c8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x5c8#64) (n := 0x1750 - 0x5c8) (k := 0x29f0 - 0x1750)
        (b' := fsp + 0x1750#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x1750#64) (n := 248) (k := 0x29f0 - 0x1848)
        (b' := fsp + 0x1848#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x1848#64) (n := 0x23b0 - 0x1848) (k := 0x29f0 - 0x23b0)
        (b' := fsp + 0x23b0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x23b0#64) (n := 32) (k := 0x29f0 - 0x23d0)
        (b' := fsp + 0x23d0#64) rfl (by bv_omega) (by decide)]
  ac_rfl

private theorem r2_locals_some_eq (fsp : BitVec 64) (p1d0 : SepProp) :
    runLocals fsp [(0x1d0, 16, p1d0)] =
      memRegion fsp 16 ∗ p1d0 ∗ memRegion (fsp + 0x208#64) 24 ∗
      memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x320#64) 32 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp := by
  dsimp only [runLocals, runLocalsFrom, runLocalBytes]
  have hf0 : fsp + BitVec.ofNat 64 0 = fsp := by bv_omega
  have hf1e0 : fsp + BitVec.ofNat 64 (0x1d0 + 16) = fsp + 0x1e0#64 := by bv_omega
  rw [hf0, hf1e0,
      ProofLib.memRegion_split' (b := fsp) (n := 16) (k := 0x1d0 - 0x10)
        (b' := fsp + 0x10#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x1e0#64) (n := 0x208 - 0x1e0) (k := 0x29f0 - 0x208)
        (b' := fsp + 0x208#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x208#64) (n := 24) (k := 0x29f0 - 0x220)
        (b' := fsp + 0x220#64) rfl (by bv_omega) (by decide),
      (r2_tail_split_220 fsp : memRegion (fsp + 0x220#64) (0x29f0 - 0x220) = _)]
  unfold r2_localGaps
  ac_rfl

private theorem r2_locals_none_eq (fsp : BitVec 64) :
    runLocals fsp [] =
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x208#64) 24 ∗
      memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x320#64) 32 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp := by
  rw [runLocals_empty_eq]
  have heq : memRegion fsp runLocalBytes =
      runLocals fsp [(0x1d0, 16, memRegion (fsp + 0x1d0#64) 16)] := by
    dsimp only [runLocals, runLocalsFrom, runLocalBytes]
    have hf0 : fsp + BitVec.ofNat 64 0 = fsp := by bv_omega
    have hf1e0 : fsp + BitVec.ofNat 64 (0x1d0 + 16) = fsp + 0x1e0#64 := by bv_omega
    rw [hf0, hf1e0,
        ProofLib.memRegion_split' (b := fsp) (n := 0x1d0) (k := 0x29f0 - 0x1d0)
          (b' := fsp + 0x1d0#64) rfl rfl (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x1d0#64) (n := 16) (k := 0x29f0 - 0x1e0)
          (b' := fsp + 0x1e0#64) rfl (by bv_omega) (by decide)]
  rw [heq, r2_locals_some_eq]

private theorem r2_locals_join_eq (fsp : BitVec 64) (outP : SepProp) :
    runLocals fsp [(0x208, 24, outP)] =
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗ outP ∗
      memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x320#64) 32 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp := by
  dsimp only [runLocals, runLocalsFrom]
  have hf0 : fsp + BitVec.ofNat 64 0 = fsp := by bv_omega
  have hf220 : fsp + BitVec.ofNat 64 (0x208 + 24) = fsp + 0x220#64 := by bv_omega
  rw [hf0, hf220,
      ProofLib.memRegion_split' (b := fsp) (n := 16) (k := 0x208 - 16)
        (b' := fsp + 0x10#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x10#64) (n := 0x1d0 - 0x10) (k := 0x208 - 0x1d0)
        (b' := fsp + 0x1d0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x1d0#64) (n := 16) (k := 0x208 - 0x1e0)
        (b' := fsp + 0x1e0#64) rfl (by bv_omega) (by decide),
      r2_tail_split_220 fsp]
  unfold r2_localGaps
  ac_rfl

private theorem r2_memRegion32_words4 (a : BitVec 64) :
    memRegion a 32 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 24) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16)
        (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 8)
        (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a,
      ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64),
      ProofLib.memRegion_eight (a + 24#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.sepExists_elim fun w3 => Entails.sepExists_elim fun w2 =>
    Entails.sepExists_elim fun w1 => Entails.sepExists_elim fun w0 =>
      Entails.sepExists_right w0 (Entails.sepExists_right w1
        (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.refl _))))

private theorem r2_peerSlot_rejoin (a w0 w1 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ memRegion (a + 16#64) 16 ⊢ memRegion a 32 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 24) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16)
        (b' := a + 16#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left (pointsTo64_entails_memRegion _ _))

private theorem r2_res_write_none (A : RustAlloc) (res w0 : BitVec 64)
    (hw0 : w0 = 0xffffffffffffffff#64) :
    (res ↦₆₄ w0) ∗ memRegion (res + 8#64) (runResSize - 8) ⊢
      runResAt A cliWrOk res (some none) := by
  subst hw0; exact Entails.refl _

private theorem r2_res_open (res : BitVec 64) :
    memRegion res runResSize ⊢
      ∃∗ r0 : BitVec 64, (res ↦₆₄ r0) ∗ memRegion (res + 8#64) (runResSize - 8) := by
  rw [ProofLib.memRegion_split' (b := res) (n := 8) (k := runResSize - 8)
        (b' := res + 8#64) (by decide) rfl (by decide),
      ProofLib.memRegion_eight res, sepExists_sepConj_left]
  exact Entails.refl _

private theorem r2_now_open (fsp : BitVec 64) :
    memRegion fsp 16 ⊢
      ∃∗ n0 : BitVec 64, ∃∗ n1 : BitVec 32,
        (fsp ↦₆₄ n0) ∗ ((fsp + 8#64) ↦₃₂ n1) ∗ memRegion (fsp + 12#64) 4 := by
  rw [ProofLib.memRegion_split' (b := fsp) (n := 8) (k := 8)
        (b' := fsp + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_eight fsp,
      ProofLib.memRegion_split' (b := fsp + 8#64) (n := 4) (k := 4)
        (b' := fsp + 12#64) rfl (by bv_omega) (by decide),
      r2_memRegion4_eq_exists_u32 (fsp + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.sepExists_elim fun n1 => Entails.sepExists_elim fun n0 =>
    Entails.sepExists_right n0 (Entails.sepExists_right n1 (Entails.refl _))

private theorem r2_now_to_mem16 (fsp : BitVec 64) :
    nowCellAt fsp unixEpoch ⊢ memRegion fsp 16 := by
  unfold nowCellAt unixEpoch
  rw [ProofLib.memRegion_split' (b := fsp) (n := 8) (k := 8)
        (b' := fsp + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := fsp + 8#64) (n := 4) (k := 4)
        (b' := fsp + 12#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left
      (IsBlock.entails (IsBlock.pointsTo32 (fsp + 8#64) 0#32)
        (IsBlock.memRegion (fsp + 8#64) 4) fun _ _ => trivial))

private theorem r2_tag8_open (a : BitVec 64) :
    memRegion a 8 ⊢ ∃∗ b0 : BitVec 8, (a ↦₈ b0) ∗ memRegion (a + 1#64) 7 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 1) (k := 7) (b' := a + 1#64) rfl rfl (by decide),
      Path.Helpers.memRegion_1_eq_pointsTo8, sepExists_sepConj_left]
  exact Entails.refl _

private theorem r2_tag8_close (a : BitVec 64) (b : BitVec 8) :
    SpqrV1.ChainProofs.bytesAt false a [b] ∗ memRegion (a + 1#64) 7 ⊢ memRegion a 8 := by
  dsimp only [SpqrV1.ChainProofs.bytesAt]
  rw [ProofLib.memRegion_split' (b := a) (n := 1) (k := 7) (b' := a + 1#64) rfl rfl (by decide)]
  exact sepConj_mono_left (ProofLib.pointsToBytes_entails_memRegion a [b])

private theorem r2_pointsTo8_to_bytesAt (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) = SpqrV1.ChainProofs.bytesAt false a [b] :=
  (ProofLib.pointsToBytes_singleton a b).symm

private theorem r2_ans_of_trace_eq {P : Prop} {s1 s2 : State}
    (_htr : s2.trace = s1.trace) (h : P) : P :=
  h

/-- Universal wrapper around `__rust_dealloc(ptr, sz, 1)` inside `signal_session::run`, preserving
`InRun`, `CalleeSavedPreserved`, `sf.trace = s.trace`, `s0.trace <+: sf.trace`, and `RunHistOk`. -/
private theorem r2_call_dealloc {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {i : Inputs}
    {s0 sRef s : State} {refOff nextOff sub : Nat} {ptr sz : BitVec 64}
    {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hextNeed : extHookStack ≤ sub) (hsub64 : sub ≤ 2 ^ 64)
    (href : InRun img ext s0 sRef refOff)
    (hinv : ImgCallInv img s)
    (hpc : s.pc = (mProg img ext).fnAddr deallocName)
    (hrun : s.status = .Running)
    (hsp : s.sp = sRef.sp)
    (hfp : s.readReg64 .fp = sRef.readReg64 .fp)
    (hv : calleeSavedVRegs s = calleeSavedVRegs sRef)
    (hlr : s.readReg64 .lr = runPc img ext nextOff)
    (hx0 : s.readReg64 .x0 = ptr)
    (hx1 : s.readReg64 .x1 = sz)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hpos : 0 < sz.toNat) (hlt : sz.toNat < 2 ^ 63)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk i s0 s)
    (hnext : ∀ sf : State,
      sf.trace = s.trace →
      InRun img ext s0 sf nextOff →
      CalleeSavedPreserved s sf →
      s0.trace <+: sf.trace →
      RunHistOk i s0 sf →
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        (A.pool ∗ stackAt (runFsp s0) sub ∗ F) Q Qp (runOom s0)) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (A.live ptr sz.toNat 1 ∗ memRegion ptr sz.toNat ∗
        A.pool ∗ stackAt (runFsp s0) sub ∗ F) Q Qp (runOom s0) := by
  have hlay : LayoutOk sz.toNat 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
  have hsp_eq : s.sp = runFsp s0 := hsp.trans href.sp
  have hsp_al : s.spAligned = true := by
    have hr := href.spAligned_cur
    simpa only [State.spAligned, hsp] using hr
  rw [r2_stackAt_split_ge (runFsp s0) hextNeed hsub64]
  refine r2_call_inImage (s0 := s0) (ptr, sz.toNat, 1)
    hh.allocFs.dealloc hinv hpc hrun hsp_al
    (ret_pc := runPc img ext nextOff) hlr
    (F := memRegion (runFsp s0 - BitVec.ofNat 64 sub) (sub - extHookStack) ∗ F)
    ?_
    (hnext := fun sf hinv_f hpcm hrunm hspm hcsm => ?_)
  · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
    have hx2' : (s.readReg64 .x2).toNat = 1 := by rw [hx2]; rfl
    (try simp only [hx0])
    (try simp only [hx1])
    (try simp only [hx2'])
    (try simp only [true_and])
    (try simp only [sepConj_assoc])
    refine Entails.pure_right hlay ?_
    rw [hsp_eq]
    exact Entails.of_eq (by ac_rfl)
  · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
    rw [sepConj_assoc, sepConj_assoc]
    apply SepWPp.pure_left; intro hfs_f
    rw [sepConj_assoc]
    apply SepWPp.pure_left; intro htr_f
    have hin_f : InRun img ext s0 sf nextOff :=
      r2_inRun_mk href hpcm hrunm (hspm.trans hsp)
        ((r2_csm_fp hcsm).trans hfp) hinv_f
        ((r2_csm_vregs hcsm).trans hv)
    have htr_sf : s0.trace <+: sf.trace := htr_f ▸ htr
    have hhist_sf : RunHistOk i s0 sf :=
      r2_histOk_of_trace_files htr_f (congrArg FsState.files hfs_f) hhist
    have hrestore :
        A.pool ∗ stackAt s.sp extHookStack ∗
          (memRegion (runFsp s0 - BitVec.ofNat 64 sub) (sub - extHookStack) ∗ F) ⊢
        A.pool ∗ stackAt (runFsp s0) sub ∗ F := by
      rw [hsp_eq, r2_stackAt_split_ge (runFsp s0) hextNeed hsub64]
      exact Entails.of_eq (by ac_rfl)
    exact sepWPp_weaken_pre hrestore (hnext sf htr_f hin_f hcsm htr_sf hhist_sf)

attribute [local irreducible] Program.rebase CryptoVerification.libsignalSessionCode

set_option maxHeartbeats 800000 in
/-- Shared reject epilogue tail starting at `R + 0xba8` (`2984`): frees `peerG.name` and invokes
`hrej` at `AtReject .postDispatch` (`R + 0x2c7c`). -/
private theorem r2_free_peer_reject {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {g : RunCall} {peerG : AddrGhost}
    {g' : StoresGhost} {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hextNeed : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hin : InRun img ext s0 s 2984)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A peerG ∗ runSaved s0 ∗
        ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x330#64) 16 ∗
        memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
        memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
        memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
        memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      Q Qp (runOom s0) := by
  intro fsp
  let restPeer : SepProp :=
    runSaved s0 ∗ memRegion (fsp + 0x330#64) 16 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap
  let peerRest : SepProp :=
    runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
      storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap
  refine sepWPp_weaken_pre
    (P' := runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
      storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A peerG ∗
      ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
      restPeer)
    (by dsimp only [restPeer]; exact Entails.of_eq (by ac_rfl)) ?_
  rw [r2_addrNameHeap_eq_ownedBytes A peerG]
  have hpc : s.pc = runPc img ext 2984 := hin.pc
  have hrun0 : s.status = .Running := hin.run
  have hsp0 : s.sp = runFsp s0 := hin.sp
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  let _ := hsp_al
  by_cases hcap : peerG.name.cap = 0#64
  · rw [hcap]
    refine sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left
          (ownedBytes_zero_entails_emp A _ _ _)))))) ?_
    rw [emp_sepConj]
    apply sepWPp_seq_inImage (mid := runPc img ext 11388) hin.inv
    rw [← r2_hold_eq restPeer]
    dsimp only [fsp]
    rw [← hsp0]
    have hfn0 := MainHops.run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 2948 52
    clear hfn0
    r2_prep_steps
    wp_steps
    apply SepWP.done (by r2_pc_done) (by r2_run hrun0)
    intro hinv1
    r2_post_steps
    rw [hsp0]
    rw [r2_hold_eq]
    have hin1 : InRun img ext s0 _ 11388 :=
      r2_inRun_mk hin (by r2_pc_done)
        (by r2_run hrun0) (by r2_eq)
        (by r2_eq) hinv1 (by r2_eq)
    have hatRej : AtReject img ext g g' .postDispatch s0 _ :=
      { base := hin1
        x19 := by (try simp only [arm64_norm]); exact hx19
        preRegs := fun h => by cases h
        trace := by (try simp only [arm64_norm]); exact htr
        hist := r2_histOk_of_trace_files (by r2_eq) (by r2_eq) hhist
        ans := hans }
    refine sepWPp_weaken_pre ?_ (hrej _ g' .postDispatch hatRej)
    dsimp only [rejectMem, restPeer]
    have hp32 := r2_peerSlot_rejoin (fsp + 0x320#64) 0#64 peerG.name.ptr
    dsimp only [fsp] at hp32
    (try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp32)
    rw [r2_locals_none_eq fsp]
    refine Entails.trans (Entails.of_eq ?_)
      (Entails.trans (sepConj_mono_left (Q := peerRest) hp32) (Entails.of_eq ?_))
    · dsimp only [peerRest, fsp]; ac_rfl
    · dsimp only [peerRest, fsp]; ac_rfl
  · refine sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (ownedBytes_dealloc A hcap)))))) ?_
    have hpull :
        runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          (⌜LayoutOk peerG.name.cap.toNat 1⌝ ∗ A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
            memRegion peerG.name.ptr peerG.name.cap.toNat) ∗
          ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
          restPeer =
        ⌜LayoutOk peerG.name.cap.toNat 1⌝ ∗
          (((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
            (A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
              memRegion peerG.name.ptr peerG.name.cap.toNat ∗
              runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
              storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              restPeer)) := by
      ac_rfl
    rw [hpull]
    apply SepWPp.pure_left; rintro ⟨hpos, _, hlt⟩
    have hlt63 : peerG.name.cap.toNat < 2 ^ 63 := by omega
    have hbeq : (peerG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    let _ := hbeq
    apply sepWPp_seq_inImage (mid := (mProg img ext).fnAddr deallocName) hin.inv
    rw [← r2_hold_eq (A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗ _)]
    dsimp only [fsp]
    rw [← hsp0]
    have hfn0 := MainHops.run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 2948 52
    code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 11380 8
    clear hfn0
    r2_prep_steps
    wp_steps
    apply SepWP.done (by r2_pc_done) (by r2_run hrun0)
    intro hinv1
    r2_post_steps
    rw [hsp0]
    rw [r2_hold_eq]
    refine sepWPp_weaken_pre
      (P' := A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
        memRegion peerG.name.ptr peerG.name.cap.toNat ∗
        A.pool ∗ stackAt fsp (resStack - runFrame) ∗
        (runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗
          (((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗
            ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x330#64) 16) ∗
          memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
          memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
          memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
          memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗ anyHeap))
      (by dsimp only [restPeer, fsp]; exact Entails.of_eq (by ac_rfl)) ?_
    refine r2_call_dealloc (nextOff := 11388) hh hextNeed hsub64 hin hinv1
      (by r2_pc_done)
      (by r2_run hrun0)
      (by r2_eq)
      (by r2_eq)
      (by r2_eq)
      (by r2_pc_done)
      (by r2_eq)
      (by r2_eq)
      (by r2_eq)
      hpos hlt63
      (by (try simp only [arm64_norm]); exact htr)
      (r2_histOk_of_trace_files (by r2_eq) (by r2_eq) hhist)
      fun sf htr_eq hin_f hcsm htr_f hhist_f => ?_
    have hatRej : AtReject img ext g g' .postDispatch s0 sf :=
      { base := hin_f
        x19 := by rw [hcsm.1]; (try simp only [arm64_norm]); exact hx19
        preRegs := fun h => by cases h
        trace := htr_f
        hist := hhist_f
        ans := r2_ans_of_trace_eq (htr_eq.trans (by r2_eq)) hans }
    refine sepWPp_weaken_pre ?_ (hrej sf g' .postDispatch hatRej)
    dsimp only [rejectMem]
    have hp32 := r2_peerSlot_rejoin (fsp + 0x320#64) peerG.name.cap peerG.name.ptr
    dsimp only [fsp] at hp32
    (try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp32)
    rw [r2_locals_none_eq fsp]
    refine Entails.trans (Entails.of_eq ?_)
      (Entails.trans (sepConj_mono_left (Q := peerRest) hp32) (Entails.of_eq ?_))
    · dsimp only [peerRest, fsp]; ac_rfl
    · dsimp only [peerRest, fsp]; ac_rfl

set_option maxHeartbeats 800000 in
/-- Helper starting at `R + 0xf78` (`3960`): frees `peerG.name` and finishes into `AtJoin`
(`R + 0xf8c` = `3980`). -/
private theorem r2_free_peer_join {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {g : RunCall} {peerG : AddrGhost}
    {g' : StoresGhost} {out : Bytes} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hextNeed : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hin : InRun img ext s0 s 3960)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, out)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (hjoin : JoinK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A peerG ∗ runSaved s0 ∗
        ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x330#64) 16 ∗
        memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
        vecU8 A (fsp + 0x208#64) out ∗ memRegion (fsp + 0x2a0#64) 8 ∗
        memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
        memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      Q Qp (runOom s0) := by
  intro fsp
  let restJoin : SepProp :=
    runSaved s0 ∗
      memRegion (fsp + 0x330#64) 16 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      vecU8 A (fsp + 0x208#64) out ∗ memRegion (fsp + 0x2a0#64) 8 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap
  let joinRest : SepProp :=
    memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      vecU8 A (fsp + 0x208#64) out ∗ memRegion (fsp + 0x2a0#64) 8 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap
  refine sepWPp_weaken_pre
    (P' := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A peerG ∗
      ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
      restJoin)
    (by dsimp only [restJoin]; exact Entails.of_eq (by ac_rfl)) ?_
  rw [r2_addrNameHeap_eq_ownedBytes A peerG]
  have hpc : s.pc = runPc img ext 3960 := hin.pc
  have hrun0 : s.status = .Running := hin.run
  have hsp0 : s.sp = runFsp s0 := hin.sp
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  let _ := hsp_al
  by_cases hcap : peerG.name.cap = 0#64
  · rw [hcap]
    refine sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left
          (ownedBytes_zero_entails_emp A _ _ _)))))) ?_
    rw [emp_sepConj]
    apply sepWPp_seq_inImage (mid := runPc img ext 3980) hin.inv
    rw [← r2_hold_eq restJoin]
    dsimp only [fsp]
    rw [← hsp0]
    have hfn0 := MainHops.run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 3932 48
    clear hfn0
    r2_prep_steps
    wp_steps
    apply SepWP.done (by r2_pc_done) (by r2_run hrun0)
    intro hinv1
    r2_post_steps
    rw [hsp0]
    rw [r2_hold_eq]
    have hin1 : InRun img ext s0 _ 3980 :=
      r2_inRun_mk hin (by r2_pc_done)
        (by r2_run hrun0) (by r2_eq)
        (by r2_eq) hinv1 (by r2_eq)
    have hatJoin : AtJoin img ext g g' out s0 _ :=
      { base := hin1
        x19 := by (try simp only [arm64_norm]); exact hx19
        x20 := by (try simp only [arm64_norm]); exact hx20
        trace := by (try simp only [arm64_norm]); exact htr
        hist := r2_histOk_of_trace_files (by r2_eq) (by r2_eq) hhist
        ans := hans
        wrOk := hwr }
    refine sepWPp_weaken_pre ?_ (hjoin _ g' out hatJoin)
    dsimp only [joinMem, restJoin]
    have hp32 := r2_peerSlot_rejoin (fsp + 0x320#64) 0#64 peerG.name.ptr
    dsimp only [fsp] at hp32
    (try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp32)
    rw [r2_locals_join_eq fsp (vecU8 A (fsp + 0x208#64) out)]
    refine Entails.trans (Entails.of_eq ?_)
      (Entails.trans (sepConj_mono_left (Q := joinRest) hp32) (Entails.of_eq ?_))
    · dsimp only [joinRest, fsp]; ac_rfl
    · dsimp only [joinRest, fsp]; ac_rfl
  · refine sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (ownedBytes_dealloc A hcap)))))) ?_
    have hpull :
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          (⌜LayoutOk peerG.name.cap.toNat 1⌝ ∗ A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
            memRegion peerG.name.ptr peerG.name.cap.toNat) ∗
          ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
          restJoin =
        ⌜LayoutOk peerG.name.cap.toNat 1⌝ ∗
          (((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
            (A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
              memRegion peerG.name.ptr peerG.name.cap.toNat ∗
              memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              restJoin)) := by
      ac_rfl
    rw [hpull]
    apply SepWPp.pure_left; rintro ⟨hpos, _, hlt⟩
    have hlt63 : peerG.name.cap.toNat < 2 ^ 63 := by omega
    have hbeq : (peerG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    let _ := hbeq
    apply sepWPp_seq_inImage (mid := (mProg img ext).fnAddr deallocName) hin.inv
    rw [← r2_hold_eq (A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗ _)]
    dsimp only [fsp]
    rw [← hsp0]
    have hfn0 := MainHops.run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 3932 48
    clear hfn0
    r2_prep_steps
    wp_steps
    apply SepWP.done (by r2_pc_done) (by r2_run hrun0)
    intro hinv1
    r2_post_steps
    rw [hsp0]
    rw [r2_hold_eq]
    refine sepWPp_weaken_pre
      (P' := A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
        memRegion peerG.name.ptr peerG.name.cap.toNat ∗
        A.pool ∗ stackAt fsp (resStack - runFrame) ∗
        (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗
          (((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗
            ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x330#64) 16) ∗
          memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
          vecU8 A (fsp + 0x208#64) out ∗ memRegion (fsp + 0x2a0#64) 8 ∗
          memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
          memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗ anyHeap))
      (by dsimp only [restJoin, fsp]; exact Entails.of_eq (by ac_rfl)) ?_
    refine r2_call_dealloc (nextOff := 3980) hh hextNeed hsub64 hin hinv1
      (by r2_pc_done)
      (by r2_run hrun0)
      (by r2_eq)
      (by r2_eq)
      (by r2_eq)
      (by r2_pc_done)
      (by r2_eq)
      (by r2_eq)
      (by r2_eq)
      hpos hlt63
      (by (try simp only [arm64_norm]); exact htr)
      (r2_histOk_of_trace_files (by r2_eq) (by r2_eq) hhist)
      fun sf htr_eq hin_f hcsm htr_f hhist_f => ?_
    have hatJoin : AtJoin img ext g g' out s0 sf :=
      { base := hin_f
        x19 := by rw [hcsm.1]; (try simp only [arm64_norm]); exact hx19
        x20 := by rw [hcsm.2.1]; (try simp only [arm64_norm]); exact hx20
        trace := htr_f
        hist := hhist_f
        ans := r2_ans_of_trace_eq (htr_eq.trans (by r2_eq)) hans
        wrOk := hwr }
    refine sepWPp_weaken_pre ?_ (hjoin sf g' out hatJoin)
    dsimp only [joinMem]
    have hp32 := r2_peerSlot_rejoin (fsp + 0x320#64) peerG.name.cap peerG.name.ptr
    dsimp only [fsp] at hp32
    (try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp32)
    rw [r2_locals_join_eq fsp (vecU8 A (fsp + 0x208#64) out)]
    refine Entails.trans (Entails.of_eq ?_)
      (Entails.trans (sepConj_mono_left (Q := joinRest) hp32) (Entails.of_eq ?_))
    · dsimp only [joinRest, fsp]; ac_rfl
    · dsimp only [joinRest, fsp]; ac_rfl

set_option maxHeartbeats 800000 in
/-- Shared accept join tail starting at `R + 0xf64` (`3940`): frees `meG.name` then `peerG.name`
and finishes into `AtJoin` (`R + 0xf8c` = `3980`). -/
private theorem r2_free_me_peer_join {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {g : RunCall} {peerG meG : AddrGhost}
    {g' : StoresGhost} {out : Bytes} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hextNeed : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hin : InRun img ext s0 s 3940)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, out)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (hjoin : JoinK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (addrNameHeap A meG ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A peerG ∗ runSaved s0 ∗
        ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x330#64) 16 ∗
        memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
        vecU8 A (fsp + 0x208#64) out ∗ memRegion (fsp + 0x2a0#64) 8 ∗
        memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
        memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      Q Qp (runOom s0) := by
  intro fsp
  let tailMeJoin : SepProp :=
    memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A peerG ∗ runSaved s0 ∗
      ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗
      ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x330#64) 16 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      vecU8 A (fsp + 0x208#64) out ∗ memRegion (fsp + 0x2a0#64) 8 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap
  change SepWPp (mProg img ext) (s0.readReg64 .lr) s (addrNameHeap A meG ∗ tailMeJoin) Q Qp (runOom s0)
  rw [r2_addrNameHeap_eq_ownedBytes A meG]
  have hpc : s.pc = runPc img ext 3940 := hin.pc
  have hrun0 : s.status = .Running := hin.run
  have hsp0 : s.sp = runFsp s0 := hin.sp
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  let _ := hsp_al; let _ := hsp0
  by_cases hcap : meG.name.cap = 0#64
  · rw [hcap]
    refine sepWPp_weaken_pre (sepConj_mono_left (ownedBytes_zero_entails_emp A _ _ _)) ?_
    rw [emp_sepConj]
    apply sepWPp_seq_inImage (mid := runPc img ext 3960) hin.inv
    rw [← r2_hold_eq tailMeJoin]
    have hfn0 := MainHops.run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 3932 48
    clear hfn0
    have hx21_0 : s.readReg64 (.gpr 21#5) = 0#64 := hx21.trans hcap
    let _ := hx21_0
    r2_prep_steps
    wp_steps
    apply SepWP.done (by r2_pc_done) (by r2_run hrun0)
    intro hinv1
    r2_post_steps
    rw [r2_hold_eq]
    have hin1 : InRun img ext s0 _ 3960 :=
      r2_inRun_mk hin (by r2_pc_done)
        (by r2_run hrun0) (by r2_eq)
        (by r2_eq) hinv1 (by r2_eq)
    exact r2_free_peer_join (peerG := peerG) hh hextNeed hsub64 hin1
      (by (try simp only [arm64_norm]); exact hx19)
      (by (try simp only [arm64_norm]); exact hx20)
      (by (try simp only [arm64_norm]); exact htr)
      (r2_histOk_of_trace_files (by r2_eq) (by r2_eq) hhist)
      hans
      hwr hjoin
  · refine sepWPp_weaken_pre (sepConj_mono_left (ownedBytes_dealloc A hcap)) ?_
    rw [sepConj_assoc, sepConj_assoc]
    apply SepWPp.pure_left; rintro ⟨hpos, _, hlt⟩
    have hlt63 : meG.name.cap.toNat < 2 ^ 63 := by omega
    have hbeq : (meG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hx21_b : (s.readReg64 (.gpr 21#5) == 0#64) = false := hx21.symm ▸ hbeq
    let _ := hx21_b
    apply sepWPp_seq_inImage (mid := (mProg img ext).fnAddr deallocName) hin.inv
    rw [← r2_hold_eq (A.live meG.name.ptr meG.name.cap.toNat 1 ∗ _)]
    have hfn0 := MainHops.run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 3932 48
    clear hfn0
    r2_prep_steps
    wp_steps
    apply SepWP.done (by r2_pc_done) (by r2_run hrun0)
    intro hinv1
    r2_post_steps
    rw [r2_hold_eq]
    have hreord :
        A.live meG.name.ptr meG.name.cap.toNat 1 ∗
          (memRegion meG.name.ptr meG.name.cap.toNat ∗ tailMeJoin) =
        A.live meG.name.ptr meG.name.cap.toNat 1 ∗
          memRegion meG.name.ptr meG.name.cap.toNat ∗
          A.pool ∗ stackAt fsp (resStack - runFrame) ∗
          (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            addrNameHeap A peerG ∗ runSaved s0 ∗
            ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x330#64) 16 ∗
            memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
            vecU8 A (fsp + 0x208#64) out ∗ memRegion (fsp + 0x2a0#64) 8 ∗
            memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
            memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗ anyHeap) := by
      dsimp only [tailMeJoin]; ac_rfl
    rw [hreord]
    refine r2_call_dealloc (nextOff := 3960) hh hextNeed hsub64 hin hinv1
      (by r2_pc_done)
      (by r2_run hrun0)
      (by r2_eq)
      (by r2_eq)
      (by r2_eq)
      (by r2_pc_done)
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by r2_eq)
      hpos hlt63
      (by (try simp only [arm64_norm]); exact htr)
      (r2_histOk_of_trace_files (by r2_eq) (by r2_eq) hhist)
      fun sf htr_eq hin_f hcsm htr_f hhist_f => ?_
    have hback :
        A.pool ∗ stackAt fsp (resStack - runFrame) ∗
          (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            addrNameHeap A peerG ∗ runSaved s0 ∗
            ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x330#64) 16 ∗
            memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
            vecU8 A (fsp + 0x208#64) out ∗ memRegion (fsp + 0x2a0#64) 8 ∗
            memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
            memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗ anyHeap) ⊢
        tailMeJoin := by
      dsimp only [tailMeJoin]; exact Entails.of_eq (by ac_rfl)
    exact sepWPp_weaken_pre hback
      (r2_free_peer_join (peerG := peerG) hh hextNeed hsub64 hin_f
        (by rw [hcsm.1]; (try simp only [arm64_norm]); exact hx19)
        (by rw [hcsm.2.1]; (try simp only [arm64_norm]); exact hx20)
        htr_f hhist_f
        (r2_ans_of_trace_eq (htr_eq.trans (by r2_eq)) hans)
        hwr hjoin)

private theorem r2_allocFailedIn_of_trace_eq {s0 s1 sf : State}
    (h : s1.trace = s0.trace) (ha : allocFailedIn s1 sf) : allocFailedIn s0 sf := by
  unfold allocFailedIn at ha ⊢; rw [← h]; exact ha

private theorem r2_allocFailedIn_congr_right {s0 s1 sf : State}
    (h : sf.trace = s1.trace) (ha : allocFailedIn s0 s1) : allocFailedIn s0 sf := by
  unfold allocFailedIn at ha ⊢; rw [h]; exact ha

set_option maxHeartbeats 800000 in
/-- Post-`encrypt` error path (`R + 0x51c → 0xb84 → drop_glue<SPE> → 0xb8c → 0xba8 → 0x2c7c`). -/
private theorem r2_err_arm {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {g : RunCall} {peerG meG : AddrGhost}
    {g' : StoresGhost} {err : ApiError AddrVal Unit}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hdropNeed : 32 + extHookStack ≤ resStack - runFrame)
    (hextNeed : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hin : InRun img ext s0 s 1308)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx22 : s.readReg64 (.gpr 22#5) = runFsp s0 + 0x4d0#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hneStore : err ≠ .store ())
    (hans : g.a = some none)
    (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (encResAt A (fsp + 0x4d0#64) (.error err) ∗
        addrNameHeap A meG ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A peerG ∗ runSaved s0 ∗
        ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x330#64) 16 ∗
        memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
        memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
        memRegion (fsp + 0x1750#64) 248 ∗
        memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      Q Qp (runOom s0) := by
  intro fsp
  let tailErr : SepProp :=
    addrNameHeap A meG ∗
      memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A peerG ∗ runSaved s0 ∗
      ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗
      ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x330#64) 16 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
      memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap
  let tailErrPost : SepProp :=
    memRegion g.call 56 ∗ storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A peerG ∗ runSaved s0 ∗
      ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗
      ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x330#64) 16 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap
  let tailErrPostNoPool : SepProp :=
    memRegion g.call 56 ∗ storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A peerG ∗ runSaved s0 ∗
      ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗
      ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x330#64) 16 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗ anyHeap
  refine sepWPp_weaken_pre
    (sepConj_mono_left (RunProofs.encResAt_err_owned A (fsp + 0x4d0#64) err hneStore)) ?_
  have hpull_k :
      (((fsp + 0x4d0#64) ↦₆₄ errTag) ∗
          (∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A ((fsp + 0x4d0#64) + 8#64) k) ∗
          memRegion ((fsp + 0x4d0#64) + 56#64) 192) ∗
        tailErr =
      (∃∗ k : RunDrop.SpeOwned,
        ((fsp + 0x4d0#64) ↦₆₄ errTag) ∗
          RunDrop.speOwnedAt A ((fsp + 0x4d0#64) + 8#64) k ∗
          memRegion ((fsp + 0x4d0#64) + 56#64) 192 ∗ tailErr) := by
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  rw [hpull_k]
  apply r2_sepWPp_exists_left; intro k
  have hpc : s.pc = runPc img ext 1308 := hin.pc
  have hrun0 : s.status = .Running := hin.run
  have hsp0 : s.sp = runFsp s0 := hin.sp
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  let _ := hsp_al
  have herr_val : errTag = 0xffffffffffffffff#64 := rfl
  have he_eq2 : ConditionHolds .EQ (addsPState64 0xffffffffffffffff#64 2#64) = false := by r2_cond
  have he_ne2 : ConditionHolds .NE (addsPState64 0xffffffffffffffff#64 2#64) = true := by r2_cond
  have he_eq1 : ConditionHolds .EQ (addsPState64 0xffffffffffffffff#64 1#64) = true := by r2_cond
  have he_ne1 : ConditionHolds .NE (addsPState64 0xffffffffffffffff#64 1#64) = false := by r2_cond
  have hmi_e : ConditionHolds .MI (subsPState64 0xffffffffffffffff#64 0#64) = true := by r2_cond
  have hpl_e : ConditionHolds .PL (subsPState64 0xffffffffffffffff#64 0#64) = false := by r2_cond
  let _ := he_eq2; let _ := he_ne2; let _ := he_eq1; let _ := he_ne1
  let _ := hmi_e; let _ := hpl_e
  apply sepWPp_seq_inImage (mid := (mProg img ext).fnAddr cliDropSpeName) hin.inv
  rw [herr_val, ← r2_hold_eq (RunDrop.speOwnedAt A ((fsp + 0x4d0#64) + 8#64) k ∗ _)]
  dsimp only [fsp] at hx22 ⊢
  rw [← hsp0] at hx22 ⊢
  (try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hx22 ⊢)
  have hfn0 := MainHops.run_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
    (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 1308 20
  code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
    (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 2948 52
  clear hfn0
  r2_prep_steps
  wp_steps
  apply SepWP.done (by r2_pc_done) (by r2_run hrun0)
  intro hinv1
  clear hpc
  r2_post_steps
  rw [hsp0] at hinv1 ⊢
  rw [r2_hold_eq]
  have hdrop_call := hdrop (resStack - runFrame) hdropNeed hsub64
  refine r2_call_inImage_steps (s0 := s0)
    (RunDrop.DropSpeOwnedGhost.mk ((fsp + 0x4d0#64) + 8#64) k)
    hdrop_call hinv1
    (by r2_pc_done)
    (by r2_run hrun0)
    (by simp only [arm64_norm]; exact hsp_al)
    (ret_pc := runPc img ext 2956)
    (by r2_pc_done)
    (F := ((fsp + 0x4d0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      memRegion ((fsp + 0x4d0#64) + 56#64) 192 ∗
      addrNameHeap A meG ∗
      memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A peerG ∗ runSaved s0 ∗
      ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
      memRegion (fsp + 0x330#64) 16 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
      memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗ anyHeap)
    ?_
    (hnext := fun s2 hsteps2 hinv2 hpcm2 hrun2 hsp2 hcs2 => ?_)
  · dsimp only [RunDrop.dropSpeOwnedSpec, tailErr]
    rw [sepConj_assoc]
    refine Entails.pure_right
      (by (try simp only [arm64_norm]); (try dsimp only [fsp]); bv_omega) ?_
    (try simp only [arm64_norm])
    rw [hsp0]
    dsimp only [fsp, runFsp]
    (try simp only [arm64_norm])
    exact Entails.of_eq (by ac_rfl)
  · dsimp only [RunDrop.dropSpeOwnedSpec]
    rw [sepConj_assoc]
    apply SepWPp.pure_left; intro htr2
    have hfs2 := r2_files_of_trace_eq hh hsteps2 htr2
    have htr_s2 : s0.trace <+: s2.trace := htr2 ▸ (by simpa only [arm64_norm] using htr)
    have hhist_s2 : RunHistOk g.i s0 s2 :=
      r2_histOk_of_trace_files htr2 hfs2
        (r2_histOk_of_trace_files (by r2_eq) (by r2_eq) hhist)
    have hans_s2 : g.a = some none :=
      r2_ans_of_trace_eq htr2 hans
    have hin2 : InRun img ext s0 s2 2956 :=
      r2_inRun_mk hin hpcm2 hrun2 (hsp2.trans (by r2_eq))
        ((r2_csm_fp hcs2).trans (by r2_eq)) hinv2
        ((r2_csm_vregs hcs2).trans (by r2_eq))
    have hx19_2 : s2.readReg64 (.gpr 19#5) = g.stores := by
      rw [r2_csm_x19 hcs2]; (try simp only [arm64_norm]); exact hx19
    have hx20_2 : s2.readReg64 (.gpr 20#5) = g.res := by
      rw [r2_csm_x20 hcs2]; (try simp only [arm64_norm]); exact hx20
    have hx21_2 : s2.readReg64 (.gpr 21#5) = meG.name.cap := by
      rw [r2_csm_x21 hcs2]; (try simp only [arm64_norm]); exact hx21
    have hx28_2 : s2.readReg64 (.gpr 28#5) = meG.name.ptr := by
      rw [r2_csm_x28 hcs2]; (try simp only [arm64_norm]); exact hx28
    have hsret := RunProofs.sret248_rejoin (fsp + 0x4d0#64) 0xffffffffffffffff#64
    refine sepWPp_weaken_pre
      (P' := memRegion g.res runResSize ∗ addrNameHeap A meG ∗ tailErrPost)
      (by
        dsimp only [tailErrPost]
        rw [← hsp2, (hin2.sp : s2.sp = fsp)]
        refine Entails.trans (Entails.of_eq ?_)
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hsret)))))))))))))))
        ac_rfl) ?_
    refine sepWPp_weaken_pre (sepConj_mono_left (r2_res_open g.res)) ?_
    rw [sepExists_sepConj_left]
    apply r2_sepWPp_exists_left; intro r0
    rw [r2_addrNameHeap_eq_ownedBytes A meG]
    have hpc : s2.pc = runPc img ext 2956 := hin2.pc
    have hrun2' : s2.status = .Running := hin2.run
    have hsp2_cur : s2.sp = runFsp s0 := hin2.sp
    have hsp_al2 : s2.spAligned = true := hin2.spAligned_cur
    let _ := hsp2_cur; let _ := hsp_al2
    by_cases hcap : meG.name.cap = 0#64
    · rw [hcap]
      refine sepWPp_weaken_pre
        (sepConj_mono_right (sepConj_mono_left (ownedBytes_zero_entails_emp A _ _ _))) ?_
      rw [emp_sepConj]
      apply sepWPp_seq_inImage (mid := runPc img ext 2984) hin2.inv
      rw [← r2_hold_eq tailErrPost]
      have hfn0 := MainHops.run_fnOff
      code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
        (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 2948 52
      clear hfn0
      have hx21_0 : s2.readReg64 (.gpr 21#5) = 0#64 := hx21_2.trans hcap
      let _ := hx21_0
      r2_prep_steps
      wp_steps
      apply SepWP.done (by r2_pc_done) (by r2_run hrun2')
      intro hinv3
      r2_post_steps
      rw [r2_hold_eq]
      have hin3 : InRun img ext s0 _ 2984 :=
        r2_inRun_mk hin2 (by r2_pc_done)
          (by r2_run hrun2') (by r2_eq)
          (by r2_eq) hinv3 (by r2_eq)
      refine sepWPp_weaken_pre
        (sepConj_mono_left (r2_res_write_none A g.res 0xffffffffffffffff#64 rfl)) ?_
      exact r2_free_peer_reject (peerG := peerG) hh hextNeed hsub64 hin3
        (by (try simp only [arm64_norm]); exact hx19_2)
        (by (try simp only [arm64_norm]); exact htr_s2)
        (r2_histOk_of_trace_files (by r2_eq) (by r2_eq) hhist_s2)
        hans_s2
        hrej
    · refine sepWPp_weaken_pre
        (sepConj_mono_right (sepConj_mono_left (ownedBytes_dealloc A hcap))) ?_
      have hpull_me :
          ((g.res ↦₆₄ r0) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
            (⌜LayoutOk meG.name.cap.toNat 1⌝ ∗ A.live meG.name.ptr meG.name.cap.toNat 1 ∗
              memRegion meG.name.ptr meG.name.cap.toNat) ∗
            tailErrPost =
          ⌜LayoutOk meG.name.cap.toNat 1⌝ ∗
            (((g.res ↦₆₄ r0) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
              (A.live meG.name.ptr meG.name.cap.toNat 1 ∗
                memRegion meG.name.ptr meG.name.cap.toNat ∗ tailErrPost)) := by
        ac_rfl
      rw [hpull_me]
      apply SepWPp.pure_left; rintro ⟨hpos, _, hlt⟩
      have hlt63 : meG.name.cap.toNat < 2 ^ 63 := by omega
      have hbeq : (meG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      have hx21_b : (s2.readReg64 (.gpr 21#5) == 0#64) = false := hx21_2.symm ▸ hbeq
      let _ := hx21_b
      apply sepWPp_seq_inImage (mid := (mProg img ext).fnAddr deallocName) hin2.inv
      rw [← r2_hold_eq (A.live meG.name.ptr meG.name.cap.toNat 1 ∗ _)]
      have hfn0 := MainHops.run_fnOff
      code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
        (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 2948 52
      clear hfn0
      r2_prep_steps
      wp_steps
      apply SepWP.done (by r2_pc_done) (by r2_run hrun2')
      intro hinv3
      r2_post_steps
      rw [r2_hold_eq]
      have hres_none := r2_res_write_none A g.res 0xffffffffffffffff#64 rfl
      refine sepWPp_weaken_pre (sepConj_mono_left hres_none) ?_
      have hreord_da :
          runResAt A cliWrOk g.res (some none) ∗
            (A.live meG.name.ptr meG.name.cap.toNat 1 ∗
              memRegion meG.name.ptr meG.name.cap.toNat ∗ tailErrPost) =
          A.live meG.name.ptr meG.name.cap.toNat 1 ∗
            memRegion meG.name.ptr meG.name.cap.toNat ∗
            A.pool ∗ stackAt fsp (resStack - runFrame) ∗
            (runResAt A cliWrOk g.res (some none) ∗ tailErrPostNoPool) := by
        dsimp only [tailErrPost, tailErrPostNoPool]; ac_rfl
      rw [hreord_da]
      refine r2_call_dealloc (nextOff := 2984) hh hextNeed hsub64 hin2 hinv3
        (by r2_pc_done)
        (by r2_run hrun2')
        (by r2_eq)
        (by r2_eq)
        (by r2_eq)
        (by r2_pc_done)
        (by (try simp only [arm64_norm]); try exact hx28_2)
        (by (try simp only [arm64_norm]); try exact hx21_2)
        (by r2_eq)
        hpos hlt63
        (by (try simp only [arm64_norm]); exact htr_s2)
        (r2_histOk_of_trace_files (by r2_eq) (by r2_eq) hhist_s2)
        fun sf htr_eq hin_f hcsm htr_f hhist_f => ?_
      have hback :
          A.pool ∗ stackAt fsp (resStack - runFrame) ∗
            (runResAt A cliWrOk g.res (some none) ∗ tailErrPostNoPool) ⊢
          runResAt A cliWrOk g.res (some none) ∗ tailErrPost := by
        dsimp only [tailErrPost, tailErrPostNoPool]; exact Entails.of_eq (by ac_rfl)
      exact sepWPp_weaken_pre hback
        (r2_free_peer_reject (peerG := peerG) hh hextNeed hsub64 hin_f
          (by rw [hcsm.1]; (try simp only [arm64_norm]); exact hx19_2)
          htr_f hhist_f
          (r2_ans_of_trace_eq htr_eq hans_s2)
          hrej)

set_option maxHeartbeats 800000 in
/-- Steps `R + 0x51c..0x5c0` (`1308 → 1476`) on `SignalMessage` (`ws.w0 = ctSignalTag`), copying all
31 words from `fsp + 0x4d0` to `fsp + 0x1750` over minimal spatial context. -/
private theorem r2_step_chk_copy_sig {img : Obj.Image}
    {ext : String → Option (State → State)} {ws dst0 : r2_SlotWords}
    {s0 s : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hin : InRun img ext s0 s 1308)
    (hx22 : s.readReg64 (.gpr 22#5) = runFsp s0 + 0x4d0#64)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx27 : s.readReg64 (.gpr 27#5) = runFsp s0 + 0x1750#64)
    (hw0 : ws.w0 = ctSignalTag)
    (hnext : ∀ s' : State,
      s'.trace = s.trace →
      s'.fs = s.fs →
      InRun img ext s0 s' 1476 →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      s'.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) →
      s'.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) →
      SepWPp (mProg img ext) (s0.readReg64 .lr) s'
        (r2_words31 (runFsp s0 + 0x4d0#64) ws ∗ r2_words31 (runFsp s0 + 0x1750#64) ws ∗ F)
        Q Qp (runOom s0)) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (r2_words31 (runFsp s0 + 0x4d0#64) ws ∗ r2_words31 (runFsp s0 + 0x1750#64) dst0 ∗ F)
      Q Qp (runOom s0) := by
  have hpc : s.pc = runPc img ext 1308 := hin.pc
  have hrun0 : s.status = .Running := hin.run
  have hsp0 : s.sp = runFsp s0 := hin.sp
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  let _ := hsp_al
  have hw0_val : ws.w0 = 0x8000000000000000#64 := hw0
  have hs_eq2 : ConditionHolds .EQ (addsPState64 0x8000000000000000#64 2#64) = false := by r2_cond
  have hs_ne2 : ConditionHolds .NE (addsPState64 0x8000000000000000#64 2#64) = true := by r2_cond
  have hs_eq1 : ConditionHolds .EQ (addsPState64 0x8000000000000000#64 1#64) = false := by r2_cond
  have hs_ne1 : ConditionHolds .NE (addsPState64 0x8000000000000000#64 1#64) = true := by r2_cond
  have hmi_s : ConditionHolds .MI (subsPState64 0x8000000000000000#64 0#64) = true := by r2_cond
  have hpl_s : ConditionHolds .PL (subsPState64 0x8000000000000000#64 0#64) = false := by r2_cond
  have hgt_s : ConditionHolds .GT (subsPState64 0#64 1#64) = false := by r2_cond
  have hle_s : ConditionHolds .LE (subsPState64 0#64 1#64) = true := by r2_cond
  let _ := hs_eq2; let _ := hs_ne2; let _ := hs_eq1; let _ := hs_ne1
  let _ := hmi_s; let _ := hpl_s; let _ := hgt_s; let _ := hle_s
  apply sepWPp_seq_inImage (mid := runPc img ext 1476) hin.inv
  unfold r2_words31
  rw [hw0_val, ← r2_hold_eq F]
  rw [← hsp0] at hx22 hx26 hx27 ⊢
  (try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hx22 hx26 hx27 ⊢)
  have hfn0 := MainHops.run_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
    (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 1308 20
  code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
    (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 1328 148
  clear hfn0
  r2_prep_steps
  wp_steps
  apply SepWP.done (by r2_pc_done) (by r2_run hrun0)
  intro hinv1
  r2_post_steps
  rw [hsp0]
  rw [r2_hold_eq F]
  have hin1 : InRun img ext s0 _ 1476 :=
    r2_inRun_mk hin (by r2_pc_done)
      (by r2_run hrun0) (by r2_eq)
      (by r2_eq) hinv1 (by r2_eq)
  refine sepWPp_weaken_pre
    (P' := r2_words31 (runFsp s0 + 0x4d0#64) ws ∗ r2_words31 (runFsp s0 + 0x1750#64) ws ∗ F)
    (by unfold r2_words31; rw [hw0_val]; (try simp only [BitVec.add_assoc, BitVec.reduceAdd]); exact Entails.of_eq (by ac_rfl))
    (hnext _ (by r2_eq) (by r2_eq) hin1
      (by r2_eq) (by r2_eq) (by r2_eq) (by r2_eq))

set_option maxHeartbeats 800000 in
/-- Steps `R + 0x51c..0x5c0` (`1308 → 3792`) on `PreKeySignalMessage` (`ws.w0.toNat < 2 ^ 63`),
copying all 31 words from `fsp + 0x4d0` to `fsp + 0x1750` over minimal spatial context. -/
private theorem r2_step_chk_copy_pk {img : Obj.Image}
    {ext : String → Option (State → State)} {ws dst0 : r2_SlotWords}
    {s0 s : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hin : InRun img ext s0 s 1308)
    (hx22 : s.readReg64 (.gpr 22#5) = runFsp s0 + 0x4d0#64)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx27 : s.readReg64 (.gpr 27#5) = runFsp s0 + 0x1750#64)
    (hw0 : ws.w0.toNat < 2 ^ 63)
    (hnext : ∀ s' : State,
      s'.trace = s.trace →
      s'.fs = s.fs →
      InRun img ext s0 s' 3792 →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      s'.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) →
      s'.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) →
      SepWPp (mProg img ext) (s0.readReg64 .lr) s'
        (r2_words31 (runFsp s0 + 0x4d0#64) ws ∗ r2_words31 (runFsp s0 + 0x1750#64) ws ∗ F)
        Q Qp (runOom s0)) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (r2_words31 (runFsp s0 + 0x4d0#64) ws ∗ r2_words31 (runFsp s0 + 0x1750#64) dst0 ∗ F)
      Q Qp (runOom s0) := by
  have hz2 : (ws.w0 + 2#64 == 0#64) = false := beq_eq_false_iff_ne.mpr (by bv_omega)
  have hnz2 : (ws.w0 + 2#64 != 0#64) = true := bne_iff_ne.mpr (by bv_omega)
  have hz1 : (ws.w0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr (by bv_omega)
  have hnz1 : (ws.w0 + 1#64 != 0#64) = true := bne_iff_ne.mpr (by bv_omega)
  have heq2 : ConditionHolds .EQ (addsPState64 ws.w0 2#64) = false := by
    rw [conditionHolds_eq_addsPState64]; exact hz2
  have hne2 : ConditionHolds .NE (addsPState64 ws.w0 2#64) = true := by
    rw [conditionHolds_ne_addsPState64]; exact hnz2
  have heq1 : ConditionHolds .EQ (addsPState64 ws.w0 1#64) = false := by
    rw [conditionHolds_eq_addsPState64]; exact hz1
  have hne1 : ConditionHolds .NE (addsPState64 ws.w0 1#64) = true := by
    rw [conditionHolds_ne_addsPState64]; exact hnz1
  have hmsb : ws.w0.msb = false := by bv_bits
  have hmsb0 : (ws.w0 - 0#64).msb = false := by rw [BitVec.sub_zero]; exact hmsb
  have hbit63 : ws.w0.getLsbD 63 = false := by bv_bits
  have hmi : ConditionHolds .MI (subsPState64 ws.w0 0#64) = false := by
    rw [conditionHolds_mi_subsPState64]; exact hmsb0
  have hpl : ConditionHolds .PL (subsPState64 ws.w0 0#64) = true := by
    rw [conditionHolds_pl_subsPState64, hmsb0]; rfl
  have hgt_p : ConditionHolds .GT (subsPState64 1#64 1#64) = false := by r2_cond
  have hle_p : ConditionHolds .LE (subsPState64 1#64 1#64) = true := by r2_cond
  let _ := hz2; let _ := hnz2; let _ := hz1; let _ := hnz1
  let _ := heq2; let _ := hne2; let _ := heq1; let _ := hne1
  let _ := hmsb; let _ := hmsb0; let _ := hbit63; let _ := hmi; let _ := hpl
  let _ := hgt_p; let _ := hle_p
  have hpc : s.pc = runPc img ext 1308 := hin.pc
  have hrun0 : s.status = .Running := hin.run
  have hsp0 : s.sp = runFsp s0 := hin.sp
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  let _ := hsp_al
  apply sepWPp_seq_inImage (mid := runPc img ext 3792) hin.inv
  unfold r2_words31
  rw [← r2_hold_eq F]
  rw [← hsp0] at hx22 hx26 hx27 ⊢
  (try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hx22 hx26 hx27 ⊢)
  have hfn0 := MainHops.run_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
    (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 1308 20
  code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
    (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 1328 148
  clear hfn0
  r2_prep_steps
  wp_steps
  apply SepWP.done (by r2_pc_done) (by r2_run hrun0)
  intro hinv1
  r2_post_steps
  rw [hsp0]
  rw [r2_hold_eq F]
  have hin1 : InRun img ext s0 _ 3792 :=
    r2_inRun_mk hin (by r2_pc_done)
      (by r2_run hrun0) (by r2_eq)
      (by r2_eq) hinv1 (by r2_eq)
  refine sepWPp_weaken_pre
    (P' := r2_words31 (runFsp s0 + 0x4d0#64) ws ∗ r2_words31 (runFsp s0 + 0x1750#64) ws ∗ F)
    (by unfold r2_words31; (try simp only [BitVec.add_assoc, BitVec.reduceAdd]); exact Entails.of_eq (by ac_rfl))
    (hnext _ (by r2_eq) (by r2_eq) hin1
      (by r2_eq) (by r2_eq) (by r2_eq) (by r2_eq))

set_option maxHeartbeats 800000 in
/-- `SignalMessage` cleanup step 1 (`R + 0x5fc..0x610`, `1532 → 1552`): frees `ciphertext` (`w4`, `w5`). -/
private theorem r2_sig_free_ct {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {i : Inputs} {ws : r2_SlotWords}
    {s0 s : State} {sub : Nat} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hextNeed : extHookStack ≤ sub) (hsub64 : sub ≤ 2 ^ 64)
    (hin : InRun img ext s0 s 1532)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk i s0 s)
    (hnext : ∀ sf : State,
      sf.trace = s.trace →
      InRun img ext s0 sf 1552 →
      CalleeSavedPreserved s sf →
      s0.trace <+: sf.trace →
      RunHistOk i s0 sf →
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        (r2_words31 (runFsp s0 + 0x1750#64) ws ∗ A.pool ∗ stackAt (runFsp s0) sub ∗ F)
        Q Qp (runOom s0)) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (r2_words31 (runFsp s0 + 0x1750#64) ws ∗
        DropPreKeyMsgHelpers.sliceDeallocX A ws.w4 ws.w5 ∗
        A.pool ∗ stackAt (runFsp s0) sub ∗ F)
      Q Qp (runOom s0) := by
  have hpc : s.pc = runPc img ext 1532 := hin.pc
  have hrun0 : s.status = .Running := hin.run
  have hsp0 : s.sp = runFsp s0 := hin.sp
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  let _ := hsp_al
  unfold DropPreKeyMsgHelpers.sliceDeallocX
  by_cases hzero : ws.w5 = 0#64
  · simp only [hzero, beq_self_eq_true, ↓reduceIte, emp_sepConj]
    apply sepWPp_seq_inImage (mid := runPc img ext 1552) hin.inv
    unfold r2_words31
    rw [hzero, ← r2_hold_eq (A.pool ∗ stackAt (runFsp s0) sub ∗ F), ← hsp0]
    (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
    have hfn0 := MainHops.run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 1476 136
    clear hfn0
    r2_prep_steps
    wp_steps
    apply SepWP.done (by r2_pc_done) (by r2_run hrun0)
    intro hinv1
    r2_post_steps
    rw [hsp0]
    rw [r2_hold_eq]
    have hin1 : InRun img ext s0 _ 1552 :=
      r2_inRun_mk hin (by r2_pc_done)
        (by r2_run hrun0) (by r2_eq)
        (by r2_eq) hinv1 (by r2_eq)
    refine sepWPp_weaken_pre
      (P' := r2_words31 (runFsp s0 + 0x1750#64) ws ∗ A.pool ∗ stackAt (runFsp s0) sub ∗ F)
      (by unfold r2_words31; rw [hzero]; (try simp only [BitVec.add_assoc, BitVec.reduceAdd]); exact Entails.of_eq (by ac_rfl))
      (hnext _ (by r2_eq) hin1
        (by unfold CalleeSavedPreserved; simp [calleeSavedVRegs, arm64_norm])
        (by (try simp only [arm64_norm]); exact htr)
        (r2_histOk_of_trace_files (by r2_eq) (by r2_eq) hhist))
  · have hbeq : (ws.w5 == 0#64) = false := beq_eq_false_iff_ne.mpr hzero
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    have hpull :
        r2_words31 (runFsp s0 + 0x1750#64) ws ∗
          (⌜0 < ws.w5.toNat ∧ ws.w5.toNat < 2 ^ 63⌝ ∗ A.live ws.w4 ws.w5.toNat 1 ∗
            memRegion ws.w4 ws.w5.toNat) ∗
          A.pool ∗ stackAt (runFsp s0) sub ∗ F =
        ⌜0 < ws.w5.toNat ∧ ws.w5.toNat < 2 ^ 63⌝ ∗
          (r2_words31 (runFsp s0 + 0x1750#64) ws ∗
            (A.live ws.w4 ws.w5.toNat 1 ∗ memRegion ws.w4 ws.w5.toNat ∗
              A.pool ∗ stackAt (runFsp s0) sub ∗ F)) := by
      ac_rfl
    rw [hpull]
    apply SepWPp.pure_left; rintro ⟨hpos, hlt⟩
    apply sepWPp_seq_inImage (mid := (mProg img ext).fnAddr deallocName) hin.inv
    unfold r2_words31
    rw [← r2_hold_eq (A.live ws.w4 ws.w5.toNat 1 ∗ _), ← hsp0]
    (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
    have hfn0 := MainHops.run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 1476 136
    clear hfn0
    r2_prep_steps
    wp_steps
    apply SepWP.done (by r2_pc_done) (by r2_run hrun0)
    intro hinv1
    r2_post_steps
    rw [hsp0]
    rw [r2_hold_eq]
    refine sepWPp_weaken_pre
      (P' := A.live ws.w4 ws.w5.toNat 1 ∗ memRegion ws.w4 ws.w5.toNat ∗
        A.pool ∗ stackAt (runFsp s0) sub ∗
        (r2_words31 (runFsp s0 + 0x1750#64) ws ∗ F))
      (by unfold r2_words31; (try simp only [BitVec.add_assoc, BitVec.reduceAdd]); exact Entails.of_eq (by ac_rfl)) ?_
    refine r2_call_dealloc (nextOff := 1552) hh hextNeed hsub64 hin hinv1
      (by r2_pc_done)
      (by r2_run hrun0)
      (by r2_eq)
      (by r2_eq)
      (by r2_eq)
      (by r2_pc_done)
      (by r2_eq)
      (by r2_eq)
      (by r2_eq)
      hpos hlt
      (by (try simp only [arm64_norm]); exact htr)
      (r2_histOk_of_trace_files (by r2_eq) (by r2_eq) hhist)
      fun sf htr_eq hin_f hcsm htr_f hhist_f => ?_
    have hcsm' : CalleeSavedPreserved s sf :=
      r2_csm_trans (by unfold CalleeSavedPreserved; simp [calleeSavedVRegs, arm64_norm]) hcsm
    have hback :
        A.pool ∗ stackAt (runFsp s0) sub ∗ (r2_words31 (runFsp s0 + 0x1750#64) ws ∗ F) ⊢
          r2_words31 (runFsp s0 + 0x1750#64) ws ∗ A.pool ∗ stackAt (runFsp s0) sub ∗ F :=
      Entails.of_eq (by ac_rfl)
    exact sepWPp_weaken_pre hback (hnext sf htr_eq hin_f hcsm' htr_f hhist_f)

set_option maxHeartbeats 800000 in
/-- `SignalMessage` cleanup step 2 (`R + 0x610..0x624`, `1552 → 1572`): frees `pq_ratchet` (`w2`, `w1`). -/
private theorem r2_sig_free_pq {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {i : Inputs} {ws : r2_SlotWords}
    {s0 s : State} {sub : Nat} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hextNeed : extHookStack ≤ sub) (hsub64 : sub ≤ 2 ^ 64)
    (hin : InRun img ext s0 s 1552)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk i s0 s)
    (hnext : ∀ sf : State,
      sf.trace = s.trace →
      InRun img ext s0 sf 1572 →
      CalleeSavedPreserved s sf →
      s0.trace <+: sf.trace →
      RunHistOk i s0 sf →
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        (r2_words31 (runFsp s0 + 0x1750#64) ws ∗ A.pool ∗ stackAt (runFsp s0) sub ∗ F)
        Q Qp (runOom s0)) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (r2_words31 (runFsp s0 + 0x1750#64) ws ∗
        DropPreKeyMsgHelpers.sliceDeallocX A ws.w2 ws.w1 ∗
        A.pool ∗ stackAt (runFsp s0) sub ∗ F)
      Q Qp (runOom s0) := by
  have hpc : s.pc = runPc img ext 1552 := hin.pc
  have hrun0 : s.status = .Running := hin.run
  have hsp0 : s.sp = runFsp s0 := hin.sp
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  let _ := hsp_al
  unfold DropPreKeyMsgHelpers.sliceDeallocX
  by_cases hzero : ws.w1 = 0#64
  · simp only [hzero, beq_self_eq_true, ↓reduceIte, emp_sepConj]
    apply sepWPp_seq_inImage (mid := runPc img ext 1572) hin.inv
    unfold r2_words31
    rw [hzero, ← r2_hold_eq (A.pool ∗ stackAt (runFsp s0) sub ∗ F), ← hsp0]
    (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
    have hfn0 := MainHops.run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 1476 136
    clear hfn0
    r2_prep_steps
    wp_steps
    apply SepWP.done (by r2_pc_done) (by r2_run hrun0)
    intro hinv1
    r2_post_steps
    rw [hsp0]
    rw [r2_hold_eq]
    have hin1 : InRun img ext s0 _ 1572 :=
      r2_inRun_mk hin (by r2_pc_done)
        (by r2_run hrun0) (by r2_eq)
        (by r2_eq) hinv1 (by r2_eq)
    refine sepWPp_weaken_pre
      (P' := r2_words31 (runFsp s0 + 0x1750#64) ws ∗ A.pool ∗ stackAt (runFsp s0) sub ∗ F)
      (by unfold r2_words31; rw [hzero]; (try simp only [BitVec.add_assoc, BitVec.reduceAdd]); exact Entails.of_eq (by ac_rfl))
      (hnext _ (by r2_eq) hin1
        (by unfold CalleeSavedPreserved; simp [calleeSavedVRegs, arm64_norm])
        (by (try simp only [arm64_norm]); exact htr)
        (r2_histOk_of_trace_files (by r2_eq) (by r2_eq) hhist))
  · have hbeq : (ws.w1 == 0#64) = false := beq_eq_false_iff_ne.mpr hzero
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    have hpull :
        r2_words31 (runFsp s0 + 0x1750#64) ws ∗
          (⌜0 < ws.w1.toNat ∧ ws.w1.toNat < 2 ^ 63⌝ ∗ A.live ws.w2 ws.w1.toNat 1 ∗
            memRegion ws.w2 ws.w1.toNat) ∗
          A.pool ∗ stackAt (runFsp s0) sub ∗ F =
        ⌜0 < ws.w1.toNat ∧ ws.w1.toNat < 2 ^ 63⌝ ∗
          (r2_words31 (runFsp s0 + 0x1750#64) ws ∗
            (A.live ws.w2 ws.w1.toNat 1 ∗ memRegion ws.w2 ws.w1.toNat ∗
              A.pool ∗ stackAt (runFsp s0) sub ∗ F)) := by
      ac_rfl
    rw [hpull]
    apply SepWPp.pure_left; rintro ⟨hpos, hlt⟩
    apply sepWPp_seq_inImage (mid := (mProg img ext).fnAddr deallocName) hin.inv
    unfold r2_words31
    rw [← r2_hold_eq (A.live ws.w2 ws.w1.toNat 1 ∗ _), ← hsp0]
    (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
    have hfn0 := MainHops.run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 1476 136
    clear hfn0
    r2_prep_steps
    wp_steps
    apply SepWP.done (by r2_pc_done) (by r2_run hrun0)
    intro hinv1
    r2_post_steps
    rw [hsp0]
    rw [r2_hold_eq]
    refine sepWPp_weaken_pre
      (P' := A.live ws.w2 ws.w1.toNat 1 ∗ memRegion ws.w2 ws.w1.toNat ∗
        A.pool ∗ stackAt (runFsp s0) sub ∗
        (r2_words31 (runFsp s0 + 0x1750#64) ws ∗ F))
      (by unfold r2_words31; (try simp only [BitVec.add_assoc, BitVec.reduceAdd]); exact Entails.of_eq (by ac_rfl)) ?_
    refine r2_call_dealloc (nextOff := 1572) hh hextNeed hsub64 hin hinv1
      (by r2_pc_done)
      (by r2_run hrun0)
      (by r2_eq)
      (by r2_eq)
      (by r2_eq)
      (by r2_pc_done)
      (by r2_eq)
      (by r2_eq)
      (by r2_eq)
      hpos hlt
      (by (try simp only [arm64_norm]); exact htr)
      (r2_histOk_of_trace_files (by r2_eq) (by r2_eq) hhist)
      fun sf htr_eq hin_f hcsm htr_f hhist_f => ?_
    have hcsm' : CalleeSavedPreserved s sf :=
      r2_csm_trans (by unfold CalleeSavedPreserved; simp [calleeSavedVRegs, arm64_norm]) hcsm
    have hback :
        A.pool ∗ stackAt (runFsp s0) sub ∗ (r2_words31 (runFsp s0 + 0x1750#64) ws ∗ F) ⊢
          r2_words31 (runFsp s0 + 0x1750#64) ws ∗ A.pool ∗ stackAt (runFsp s0) sub ∗ F :=
      Entails.of_eq (by ac_rfl)
    exact sepWPp_weaken_pre hback (hnext sf htr_eq hin_f hcsm' htr_f hhist_f)

set_option maxHeartbeats 800000 in
/-- `SignalMessage` cleanup step 3 (`R + 0x624..0x63c`, `1572 → 1596`): frees `addresses` (`w12`, `w13`). -/
private theorem r2_sig_free_ad {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {i : Inputs} {ws : r2_SlotWords}
    {s0 s : State} {sub : Nat} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hextNeed : extHookStack ≤ sub) (hsub64 : sub ≤ 2 ^ 64)
    (hin : InRun img ext s0 s 1572)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk i s0 s)
    (hnext : ∀ sf : State,
      sf.trace = s.trace →
      InRun img ext s0 sf 1596 →
      CalleeSavedPreserved s sf →
      s0.trace <+: sf.trace →
      RunHistOk i s0 sf →
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        (r2_words31 (runFsp s0 + 0x1750#64) ws ∗ A.pool ∗ stackAt (runFsp s0) sub ∗ F)
        Q Qp (runOom s0)) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (r2_words31 (runFsp s0 + 0x1750#64) ws ∗
        DropPreKeyMsgHelpers.optSliceDeallocX A ws.w12 ws.w13 ∗
        A.pool ∗ stackAt (runFsp s0) sub ∗ F)
      Q Qp (runOom s0) := by
  have hpc : s.pc = runPc img ext 1572 := hin.pc
  have hrun0 : s.status = .Running := hin.run
  have hsp0 : s.sp = runFsp s0 := hin.sp
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  let _ := hsp_al
  unfold DropPreKeyMsgHelpers.optSliceDeallocX
  by_cases hp0 : ws.w12 = 0#64
  · simp only [hp0, beq_self_eq_true, ↓reduceIte, emp_sepConj]
    apply sepWPp_seq_inImage (mid := runPc img ext 1596) hin.inv
    unfold r2_words31
    rw [hp0, ← r2_hold_eq (A.pool ∗ stackAt (runFsp s0) sub ∗ F), ← hsp0]
    (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
    have hfn0 := MainHops.run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 1476 136
    clear hfn0
    r2_prep_steps
    wp_steps
    apply SepWP.done (by r2_pc_done) (by r2_run hrun0)
    intro hinv1
    r2_post_steps
    rw [hsp0]
    rw [r2_hold_eq]
    have hin1 : InRun img ext s0 _ 1596 :=
      r2_inRun_mk hin (by r2_pc_done)
        (by r2_run hrun0) (by r2_eq)
        (by r2_eq) hinv1 (by r2_eq)
    refine sepWPp_weaken_pre
      (P' := r2_words31 (runFsp s0 + 0x1750#64) ws ∗ A.pool ∗ stackAt (runFsp s0) sub ∗ F)
      (by unfold r2_words31; rw [hp0]; (try simp only [BitVec.add_assoc, BitVec.reduceAdd]); exact Entails.of_eq (by ac_rfl))
      (hnext _ (by r2_eq) hin1
        (by unfold CalleeSavedPreserved; simp [calleeSavedVRegs, arm64_norm])
        (by (try simp only [arm64_norm]); exact htr)
        (r2_histOk_of_trace_files (by r2_eq) (by r2_eq) hhist))
  · have hbeqp : (ws.w12 == 0#64) = false := beq_eq_false_iff_ne.mpr hp0
    simp only [hbeqp, Bool.false_eq_true, ↓reduceIte]
    unfold DropPreKeyMsgHelpers.sliceDeallocX
    by_cases hl0 : ws.w13 = 0#64
    · simp only [hl0, beq_self_eq_true, ↓reduceIte, emp_sepConj]
      apply sepWPp_seq_inImage (mid := runPc img ext 1596) hin.inv
      unfold r2_words31
      rw [hl0, ← r2_hold_eq (A.pool ∗ stackAt (runFsp s0) sub ∗ F), ← hsp0]
      (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
      have hfn0 := MainHops.run_fnOff
      code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
        (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 1476 136
      clear hfn0
      r2_prep_steps
      wp_steps
      apply SepWP.done (by r2_pc_done) (by r2_run hrun0)
      intro hinv1
      r2_post_steps
      rw [hsp0]
      rw [r2_hold_eq]
      have hin1 : InRun img ext s0 _ 1596 :=
        r2_inRun_mk hin (by r2_pc_done)
          (by r2_run hrun0) (by r2_eq)
          (by r2_eq) hinv1 (by r2_eq)
      refine sepWPp_weaken_pre
        (P' := r2_words31 (runFsp s0 + 0x1750#64) ws ∗ A.pool ∗ stackAt (runFsp s0) sub ∗ F)
        (by unfold r2_words31; rw [hl0]; (try simp only [BitVec.add_assoc, BitVec.reduceAdd]); exact Entails.of_eq (by ac_rfl))
        (hnext _ (by r2_eq) hin1
          (by unfold CalleeSavedPreserved; simp [calleeSavedVRegs, arm64_norm])
          (by (try simp only [arm64_norm]); exact htr)
          (r2_histOk_of_trace_files (by r2_eq) (by r2_eq) hhist))
    · have hbeql : (ws.w13 == 0#64) = false := beq_eq_false_iff_ne.mpr hl0
      simp only [hbeql, Bool.false_eq_true, ↓reduceIte]
      have hpull :
          r2_words31 (runFsp s0 + 0x1750#64) ws ∗
            (⌜0 < ws.w13.toNat ∧ ws.w13.toNat < 2 ^ 63⌝ ∗ A.live ws.w12 ws.w13.toNat 1 ∗
              memRegion ws.w12 ws.w13.toNat) ∗
            A.pool ∗ stackAt (runFsp s0) sub ∗ F =
          ⌜0 < ws.w13.toNat ∧ ws.w13.toNat < 2 ^ 63⌝ ∗
            (r2_words31 (runFsp s0 + 0x1750#64) ws ∗
              (A.live ws.w12 ws.w13.toNat 1 ∗ memRegion ws.w12 ws.w13.toNat ∗
                A.pool ∗ stackAt (runFsp s0) sub ∗ F)) := by
        ac_rfl
      rw [hpull]
      apply SepWPp.pure_left; rintro ⟨hpos, hlt⟩
      apply sepWPp_seq_inImage (mid := (mProg img ext).fnAddr deallocName) hin.inv
      unfold r2_words31
      rw [← r2_hold_eq (A.live ws.w12 ws.w13.toNat 1 ∗ _), ← hsp0]
      (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
      have hfn0 := MainHops.run_fnOff
      code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
        (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 1476 136
      clear hfn0
      r2_prep_steps
      wp_steps
      apply SepWP.done (by r2_pc_done) (by r2_run hrun0)
      intro hinv1
      r2_post_steps
      rw [hsp0]
      rw [r2_hold_eq]
      refine sepWPp_weaken_pre
        (P' := A.live ws.w12 ws.w13.toNat 1 ∗ memRegion ws.w12 ws.w13.toNat ∗
          A.pool ∗ stackAt (runFsp s0) sub ∗
          (r2_words31 (runFsp s0 + 0x1750#64) ws ∗ F))
        (by unfold r2_words31; (try simp only [BitVec.add_assoc, BitVec.reduceAdd]); exact Entails.of_eq (by ac_rfl)) ?_
      refine r2_call_dealloc (nextOff := 1596) hh hextNeed hsub64 hin hinv1
        (by r2_pc_done)
        (by r2_run hrun0)
        (by r2_eq)
        (by r2_eq)
        (by r2_eq)
        (by r2_pc_done)
        (by r2_eq)
        (by r2_eq)
        (by r2_eq)
        hpos hlt
        (by (try simp only [arm64_norm]); exact htr)
        (r2_histOk_of_trace_files (by r2_eq) (by r2_eq) hhist)
        fun sf htr_eq hin_f hcsm htr_f hhist_f => ?_
      have hcsm' : CalleeSavedPreserved s sf :=
        r2_csm_trans (by unfold CalleeSavedPreserved; simp [calleeSavedVRegs, arm64_norm]) hcsm
      have hback :
          A.pool ∗ stackAt (runFsp s0) sub ∗ (r2_words31 (runFsp s0 + 0x1750#64) ws ∗ F) ⊢
            r2_words31 (runFsp s0 + 0x1750#64) ws ∗ A.pool ∗ stackAt (runFsp s0) sub ∗ F :=
        Entails.of_eq (by ac_rfl)
      exact sepWPp_weaken_pre hback (hnext sf htr_eq hin_f hcsm' htr_f hhist_f)

set_option maxHeartbeats 800000 in
/-- `SignalMessage` cleanup step 4 (`R + 0x63c..0x648` + `0xf5c..0xf60`, `1596 → 3940`): frees
`serialized` (`x23 = serPtr`, `x24 = serLen`). -/
private theorem r2_sig_free_ser {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {i : Inputs} {serPtr serLen : BitVec 64}
    {s0 s : State} {sub : Nat} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hextNeed : extHookStack ≤ sub) (hsub64 : sub ≤ 2 ^ 64)
    (hin : InRun img ext s0 s 1596)
    (hx23 : s.readReg64 (.gpr 23#5) = serPtr)
    (hx24 : s.readReg64 (.gpr 24#5) = serLen)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk i s0 s)
    (hnext : ∀ sf : State,
      sf.trace = s.trace →
      InRun img ext s0 sf 3940 →
      CalleeSavedPreserved s sf →
      s0.trace <+: sf.trace →
      RunHistOk i s0 sf →
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        (A.pool ∗ stackAt (runFsp s0) sub ∗ F)
        Q Qp (runOom s0)) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (DropPreKeyMsgHelpers.sliceDeallocX A serPtr serLen ∗
        A.pool ∗ stackAt (runFsp s0) sub ∗ F)
      Q Qp (runOom s0) := by
  have hpc : s.pc = runPc img ext 1596 := hin.pc
  have hrun0 : s.status = .Running := hin.run
  have hsp0 : s.sp = runFsp s0 := hin.sp
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  let _ := hsp0; let _ := hsp_al
  unfold DropPreKeyMsgHelpers.sliceDeallocX
  by_cases hzero : serLen = 0#64
  · simp only [hzero, beq_self_eq_true, ↓reduceIte, emp_sepConj]
    apply sepWPp_seq_inImage (mid := runPc img ext 3940) hin.inv
    rw [← r2_hold_eq (A.pool ∗ stackAt (runFsp s0) sub ∗ F)]
    have hfn0 := MainHops.run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 1476 136
    clear hfn0
    have hx24_0 : s.readReg64 (.gpr 24#5) = 0#64 := hx24.trans hzero
    let _ := hx24_0
    r2_prep_steps
    wp_steps
    apply SepWP.done (by r2_pc_done) (by r2_run hrun0)
    intro hinv1
    r2_post_steps
    rw [r2_hold_eq]
    have hin1 : InRun img ext s0 _ 3940 :=
      r2_inRun_mk hin (by r2_pc_done)
        (by r2_run hrun0) (by r2_eq)
        (by r2_eq) hinv1 (by r2_eq)
    exact hnext _ (by r2_eq) hin1
      (by unfold CalleeSavedPreserved; simp [calleeSavedVRegs, arm64_norm])
      (by (try simp only [arm64_norm]); exact htr)
      (r2_histOk_of_trace_files (by r2_eq) (by r2_eq) hhist)
  · have hbeq : (serLen == 0#64) = false := beq_eq_false_iff_ne.mpr hzero
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    rw [sepConj_assoc, sepConj_assoc]
    apply SepWPp.pure_left; rintro ⟨hpos, hlt⟩
    have hx24_b : (s.readReg64 (.gpr 24#5) == 0#64) = false := hx24.symm ▸ hbeq
    let _ := hx24_b
    apply sepWPp_seq_inImage (mid := (mProg img ext).fnAddr deallocName) hin.inv
    rw [← r2_hold_eq (A.live serPtr serLen.toNat 1 ∗ _)]
    have hfn0 := MainHops.run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 1476 136
    code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 3932 48
    clear hfn0
    r2_prep_steps
    wp_steps
    apply SepWP.done (by r2_pc_done) (by r2_run hrun0)
    intro hinv1
    r2_post_steps
    rw [r2_hold_eq]
    have hassoc :
        A.live serPtr serLen.toNat 1 ∗ (memRegion serPtr serLen.toNat ∗
          (A.pool ∗ stackAt (runFsp s0) sub ∗ F)) =
        A.live serPtr serLen.toNat 1 ∗ memRegion serPtr serLen.toNat ∗
          A.pool ∗ stackAt (runFsp s0) sub ∗ F := by
      ac_rfl
    rw [hassoc]
    refine r2_call_dealloc (nextOff := 3940) hh hextNeed hsub64 hin hinv1
      (by r2_pc_done)
      (by r2_run hrun0)
      (by r2_eq)
      (by r2_eq)
      (by r2_eq)
      (by r2_pc_done)
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by r2_eq)
      hpos hlt
      (by (try simp only [arm64_norm]); exact htr)
      (r2_histOk_of_trace_files (by r2_eq) (by r2_eq) hhist)
      fun sf htr_eq hin_f hcsm htr_f hhist_f => ?_
    have hcsm' : CalleeSavedPreserved s sf :=
      r2_csm_trans (by unfold CalleeSavedPreserved; simp [calleeSavedVRegs, arm64_norm]) hcsm
    exact hnext sf htr_eq hin_f hcsm' htr_f hhist_f

private theorem r2_words4_216_rejoin (a w0 w1 w2 w3 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
      memRegion (a + 32#64) 216 ⊢
      memRegion a 248 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 240) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 232)
        (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 224)
        (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 216)
        (b' := a + 32#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left (pointsTo64_entails_memRegion _ _))))

set_option maxHeartbeats 800000 in
/-- Post-`encrypt` `Ok (.signalMessage m)` arm (`R + 0x51c → 0x5c4 → concat → 0x5fc..0xf64 → 0xf8c`). -/
private theorem r2_sig_arm {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {g : RunCall} {peerG meG : AddrGhost}
    {g' : StoresGhost} {m : SignalMessage}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hcatNeed : 96 + extHookStack ≤ resStack - runFrame)
    (hextNeed : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hin : InRun img ext s0 s 1308)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx22 : s.readReg64 (.gpr 22#5) = runFsp s0 + 0x4d0#64)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx27 : s.readReg64 (.gpr 27#5) = runFsp s0 + 0x1750#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, [2#8] ++ m.serialized)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (hpanic : PanicK g s0 Qp)
    (hjoin : JoinK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (encResAt A (fsp + 0x4d0#64) (.ok (.signalMessage m)) ∗
        addrNameHeap A meG ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A peerG ∗ runSaved s0 ∗
        ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x330#64) 16 ∗
        memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
        memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
        memRegion (fsp + 0x1750#64) 248 ∗
        memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      Q Qp (runOom s0) := by
  intro fsp
  let sigTail : SepProp :=
    addrNameHeap A meG ∗
      memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A peerG ∗ runSaved s0 ∗
      ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗
      ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x330#64) 16 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      memRegion (fsp + 0x208#64) 24 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap
  let sigTailNoOut : SepProp :=
    addrNameHeap A meG ∗
      memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A peerG ∗ runSaved s0 ∗
      ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗
      ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x330#64) 16 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗ anyHeap
  rw [encResAt_ok]
  dsimp only [apiEncResultAt]
  have hpull_gm :
      (((fsp + 0x4d0#64) ↦₆₄ ctSignalTag) ∗
          (∃∗ gMsg : SignalMessageGhost, signalMessageAt A gMsg ((fsp + 0x4d0#64) + 8#64) m) ∗
          memRegion ((fsp + 0x4d0#64) + 0x80#64) 120) ∗
        (addrNameHeap A meG ∗
          memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          addrNameHeap A peerG ∗ runSaved s0 ∗
          ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x330#64) 16 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
          memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
          memRegion (fsp + 0x1750#64) 248 ∗
          memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap) =
      ∃∗ gMsg : SignalMessageGhost,
        (((fsp + 0x4d0#64) ↦₆₄ ctSignalTag) ∗
          signalMessageAt A gMsg ((fsp + 0x4d0#64) + 8#64) m ∗
          memRegion ((fsp + 0x4d0#64) + 0x80#64) 120) ∗
        memRegion (fsp + 0x1750#64) 248 ∗
        memRegion (fsp + 0x2a0#64) 8 ∗
        sigTail := by
    dsimp only [sigTail]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    ac_rfl
  rw [hpull_gm]
  apply r2_sepWPp_exists_left; intro gMsg
  refine sepWPp_weaken_pre
    (sepConj_mono (r2_open_signalMessage A (fsp + 0x4d0#64) gMsg m)
      (sepConj_mono (r2_memRegion248_open (fsp + 0x1750#64))
        (sepConj_mono_left (r2_tag8_open (fsp + 0x2a0#64))))) ?_
  apply r2_peel; intro ws
  apply r2_peel; intro _adPtr
  apply r2_peel; intro _adLen
  apply r2_peel; intro dst0
  apply r2_peel; intro b2a0
  apply r2_peel_pure
  rintro ⟨hw0, hw1, hw2, hw4, hw5, hw6, hw7, hw12, hw13, hser_lt, _⟩
  simp only [emp_sepConj, sepConj_assoc]
  rw [← hw4, ← hw5, ← hw2, ← hw1, ← hw12, ← hw13]
  have hcopy_pre :
      r2_words31 (fsp + 0x4d0#64) ws ∗ (gMsg.serPtr ↦ₛ m.serialized) ∗
        r2_boxLive A gMsg.serPtr m.serialized ∗
        DropPreKeyMsgHelpers.sliceDeallocX A ws.w4 ws.w5 ∗
        DropPreKeyMsgHelpers.sliceDeallocX A ws.w2 ws.w1 ∗
        DropPreKeyMsgHelpers.optSliceDeallocX A ws.w12 ws.w13 ∗
        r2_words31 (fsp + 0x1750#64) dst0 ∗ ((fsp + 0x2a0#64) ↦₈ b2a0) ∗
        memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗ sigTail =
      r2_words31 (fsp + 0x4d0#64) ws ∗ r2_words31 (fsp + 0x1750#64) dst0 ∗
        (((fsp + 0x2a0#64) ↦₈ b2a0) ∗ memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗
          (gMsg.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A gMsg.serPtr m.serialized ∗
          DropPreKeyMsgHelpers.sliceDeallocX A ws.w4 ws.w5 ∗
          DropPreKeyMsgHelpers.sliceDeallocX A ws.w2 ws.w1 ∗
          DropPreKeyMsgHelpers.optSliceDeallocX A ws.w12 ws.w13 ∗ sigTail) := by
    ac_rfl
  rw [hcopy_pre]
  refine r2_step_chk_copy_sig hin hx22 hx26 hx27 hw0
    fun s1 htr1 hfs1 hin1 hx19_1 hx20_1 hx21_1 hx28_1 => ?_
  have htr_s1 : s0.trace <+: s1.trace := htr1 ▸ htr
  have hhist_s1 : RunHistOk g.i s0 s1 :=
    r2_histOk_of_trace_files htr1 (congrArg FsState.files hfs1) hhist
  have hans_s1 : g.a = some (some (namedWrites g'.writes, [2#8] ++ m.serialized)) :=
    r2_ans_of_trace_eq htr1 hans
  have hopen_4d0 :
      r2_words31 (fsp + 0x4d0#64) ws ⊢
        (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
          ((fsp + 0x4d0#64) ↦₆₄ c0) ∗ (((fsp + 0x4d0#64) + 8#64) ↦₆₄ c1) ∗
          (((fsp + 0x4d0#64) + 16#64) ↦₆₄ c2) ∗ (((fsp + 0x4d0#64) + 24#64) ↦₆₄ c3)) ∗
        memRegion ((fsp + 0x4d0#64) + 32#64) 216 := by
    refine Entails.trans (r2_words31_to_memRegion248 (fsp + 0x4d0#64) ws) ?_
    rw [ProofLib.memRegion_split (fsp + 0x4d0#64) 32 216 (by decide)]
    exact sepConj_mono_left (r2_memRegion32_words4 (fsp + 0x4d0#64))
  refine sepWPp_weaken_pre (sepConj_mono_left hopen_4d0) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply r2_sepWPp_exists_left; intro _c0
  apply r2_sepWPp_exists_left; intro _c1
  apply r2_sepWPp_exists_left; intro _c2
  apply r2_sepWPp_exists_left; intro _c3
  have hpc : s1.pc = runPc img ext 1476 := hin1.pc
  have hrun1 : s1.status = .Running := hin1.run
  have hsp1 : s1.sp = fsp := hin1.sp
  have hsp1_al : s1.spAligned = true := hin1.spAligned_cur
  let _ := hsp1_al
  apply sepWPp_seq_inImage (mid := (mProg img ext).fnAddr cliConcatName) hin1.inv
  rw [← r2_hold_eq (memRegion ((fsp + 0x4d0#64) + 32#64) 216),
      ← r2_hold_eq (memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗ _)]
  unfold r2_words31
  dsimp only [fsp] at hsp1 ⊢
  rw [← hsp1]
  (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
  have hfn0 := MainHops.run_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
    (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 1476 136
  clear hfn0
  r2_prep_steps
  wp_steps
  apply SepWP.done (by r2_pc_done) (by r2_run hrun1)
  intro hinv2
  r2_post_steps
  rw [hsp1] at hinv2 ⊢
  rw [r2_hold_eq, r2_hold_eq]
  refine sepWPp_weaken_pre
    (P' := ((fsp + 0x4d0#64) ↦₆₄ (fsp + 0x2a0#64)) ∗
      (((fsp + 0x4d0#64) + 8#64) ↦₆₄ 1#64) ∗
      (((fsp + 0x4d0#64) + 16#64) ↦₆₄ gMsg.serPtr) ∗
      (((fsp + 0x4d0#64) + 24#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
      SpqrV1.ChainProofs.bytesAt false (fsp + 0x2a0#64) [2#8] ∗
      SpqrV1.ChainProofs.bytesAt false gMsg.serPtr m.serialized ∗
      memRegion (fsp + 0x208#64) 24 ∗
      A.pool ∗ stackAt fsp (resStack - runFrame) ∗
      (memRegion ((fsp + 0x4d0#64) + 32#64) 216 ∗
        memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗
        r2_words31 (fsp + 0x1750#64) ws ∗
        r2_boxLive A gMsg.serPtr m.serialized ∗
        DropPreKeyMsgHelpers.sliceDeallocX A ws.w4 ws.w5 ∗
        DropPreKeyMsgHelpers.sliceDeallocX A ws.w2 ws.w1 ∗
        DropPreKeyMsgHelpers.optSliceDeallocX A ws.w12 ws.w13 ∗
        sigTailNoOut))
    (by
      unfold r2_words31
      dsimp only [fsp, sigTail, sigTailNoOut]
      rw [hw6, hw7, SpqrV1.ChainProofs.bytesAt_false, SpqrV1.ChainProofs.bytesAt_false,
        ProofLib.pointsToBytes_singleton]
      (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact Entails.of_eq (by ac_rfl)) ?_
  have hhist_cat : RunHistOk g.i s0 _ :=
    r2_histOk_of_trace_files (by r2_eq) (by r2_eq) hhist_s1
  have hans_cat : g.a = some (some (namedWrites g'.writes, [2#8] ++ m.serialized)) :=
    hans_s1
  let catG : SpqrV1.ChainProofs.SliceConcat2Ghost :=
    ⟨fsp + 0x208#64, fsp + 0x4d0#64, false, fsp + 0x2a0#64, [2#8],
     false, gMsg.serPtr, m.serialized⟩
  refine r2_call_inImage_steps (s0 := s0) catG
    (r2_concat2_le_ok hh (resStack - runFrame) hcatNeed hsub64)
    hinv2
    (by r2_pc_done)
    (by r2_run hrun1)
    (by (try simp only [arm64_norm]); exact hsp1_al)
    (ret_pc := runPc img ext 1532)
    (by r2_pc_done)
    (F := memRegion ((fsp + 0x4d0#64) + 32#64) 216 ∗
      memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗
      r2_words31 (fsp + 0x1750#64) ws ∗
      r2_boxLive A gMsg.serPtr m.serialized ∗
      DropPreKeyMsgHelpers.sliceDeallocX A ws.w4 ws.w5 ∗
      DropPreKeyMsgHelpers.sliceDeallocX A ws.w2 ws.w1 ∗
      DropPreKeyMsgHelpers.optSliceDeallocX A ws.w12 ws.w13 ∗
      sigTailNoOut)
    ?_
    (hpanic := fun sf R' _ hp => by
      dsimp only [r2_concat2LeSpec] at hp
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      rcases hp.1.1 with halloc1 | ⟨hlen_eq, _⟩
      · exact hpanic sf _ (Or.inr
          (allocFailedIn_of_prefix htr_s1 (r2_allocFailedIn_of_trace_eq (by r2_eq) halloc1)))
      · exfalso
        dsimp only [catG, List.length] at hlen_eq
        omega)
    (hnext := fun s2 hsteps2 hinv_s2 hpcm2 hrun2 hsp2 hcs2 => ?_)
  · dsimp only [r2_concat2LeSpec, catG]
    rw [sepConj_assoc]
    apply Entails.pure_right
    · exact ⟨by (try simp only [arm64_norm]); dsimp only [fsp]; bv_omega,
             by (try simp only [arm64_norm]); dsimp only [fsp]; bv_omega,
             by r2_eq, rfl, by omega⟩
    · (try simp only [arm64_norm])
      rw [hsp1]
      dsimp only [fsp]
      exact Entails.of_eq (by ac_rfl)
  · dsimp only [r2_concat2LeSpec, RunProofs.cliConcat2Spec, catG]
    rw [sepConj_assoc]
    apply SepWPp.pure_left; intro htr2
    have hfs2 := r2_files_of_trace_eq hh hsteps2 htr2
    have htr_s2 : s0.trace <+: s2.trace := by rw [htr2]; exact htr_s1
    have hhist_s2 : RunHistOk g.i s0 s2 := r2_histOk_of_trace_files htr2 hfs2 hhist_cat
    have hans_s2 := r2_ans_of_trace_eq htr2 hans_cat
    have hin2 : InRun img ext s0 s2 1532 :=
      r2_inRun_mk hin1 hpcm2 hrun2 (hsp2.trans (by r2_eq))
        ((r2_csm_fp hcs2).trans (by r2_eq)) hinv_s2
        ((r2_csm_vregs hcs2).trans (by r2_eq))
    have hx19_2 : s2.readReg64 (.gpr 19#5) = g.stores := by
      rw [r2_csm_x19 hcs2]; (try simp only [arm64_norm]); exact hx19_1.trans hx19
    have hx20_2 : s2.readReg64 (.gpr 20#5) = g.res := by
      rw [r2_csm_x20 hcs2]; (try simp only [arm64_norm]); exact hx20_1.trans hx20
    have hx21_2 : s2.readReg64 (.gpr 21#5) = meG.name.cap := by
      rw [r2_csm_x21 hcs2]; (try simp only [arm64_norm]); exact hx21_1.trans hx21
    have hx23_2 : s2.readReg64 (.gpr 23#5) = gMsg.serPtr := by
      rw [r2_csm_x23 hcs2]; simp only [arm64_norm]
    have hx24_2 : s2.readReg64 (.gpr 24#5) = BitVec.ofNat 64 m.serialized.length := by
      rw [r2_csm_x24 hcs2]; simp only [arm64_norm]
    have hx28_2 : s2.readReg64 (.gpr 28#5) = meG.name.ptr := by
      rw [r2_csm_x28 hcs2]; (try simp only [arm64_norm]); exact hx28_1.trans hx28
    refine sepWPp_weaken_pre (P' :=
        r2_words31 (fsp + 0x1750#64) ws ∗
          DropPreKeyMsgHelpers.sliceDeallocX A ws.w4 ws.w5 ∗
          A.pool ∗ stackAt fsp (resStack - runFrame) ∗
          (DropPreKeyMsgHelpers.sliceDeallocX A ws.w2 ws.w1 ∗
            DropPreKeyMsgHelpers.optSliceDeallocX A ws.w12 ws.w13 ∗
            DropPreKeyMsgHelpers.sliceDeallocX A gMsg.serPtr
              (BitVec.ofNat 64 m.serialized.length) ∗
            vecU8 A (fsp + 0x208#64) ([2#8] ++ m.serialized) ∗
            memRegion (fsp + 0x2a0#64) 8 ∗
            memRegion (fsp + 0x4d0#64) 248 ∗ sigTailNoOut)) ?_ ?_
    · refine Entails.trans (Entails.of_eq (Q :=
          (((fsp + 0x4d0#64) ↦₆₄ (fsp + 0x2a0#64)) ∗
              (((fsp + 0x4d0#64) + 8#64) ↦₆₄ BitVec.ofNat 64 ([2#8] : List (BitVec 8)).length) ∗
              (((fsp + 0x4d0#64) + 16#64) ↦₆₄ gMsg.serPtr) ∗
              (((fsp + 0x4d0#64) + 24#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
              memRegion ((fsp + 0x4d0#64) + 32#64) 216) ∗
            (SpqrV1.ChainProofs.bytesAt false (fsp + 0x2a0#64) [2#8] ∗
              memRegion ((fsp + 0x2a0#64) + 1#64) 7) ∗
            ((gMsg.serPtr ↦ₛ m.serialized) ∗ r2_boxLive A gMsg.serPtr m.serialized) ∗
            (r2_words31 (fsp + 0x1750#64) ws ∗
              DropPreKeyMsgHelpers.sliceDeallocX A ws.w4 ws.w5 ∗
              A.pool ∗ stackAt fsp (resStack - runFrame) ∗
              DropPreKeyMsgHelpers.sliceDeallocX A ws.w2 ws.w1 ∗
              DropPreKeyMsgHelpers.optSliceDeallocX A ws.w12 ws.w13 ∗
              vecU8 A (fsp + 0x208#64) ([2#8] ++ m.serialized) ∗ sigTailNoOut)) ?_) ?_
      · rw [SpqrV1.ChainProofs.bytesAt_false gMsg.serPtr m.serialized]
        (try simp only [arm64_norm])
        rw [hsp1]
        dsimp only [fsp, runFsp]
        (try simp only [arm64_norm])
        ac_rfl
      · refine Entails.trans
          (sepConj_mono (r2_words4_216_rejoin (fsp + 0x4d0#64) _ _ _ _)
            (sepConj_mono (r2_tag8_close (fsp + 0x2a0#64) 2#8)
              (sepConj_mono_left
                (r2_boxLive_to_sliceDeallocX A gMsg.serPtr m.serialized (by omega))))) ?_
        exact Entails.of_eq (by ac_rfl)
    refine r2_sig_free_ct hh hextNeed hsub64 hin2 htr_s2 hhist_s2
      fun s3 htr3 hin3 hcs3 htr_s3 hhist_s3 => ?_
    have hreord_pq :
        r2_words31 (fsp + 0x1750#64) ws ∗ A.pool ∗ stackAt fsp (resStack - runFrame) ∗
          (DropPreKeyMsgHelpers.sliceDeallocX A ws.w2 ws.w1 ∗
            DropPreKeyMsgHelpers.optSliceDeallocX A ws.w12 ws.w13 ∗
            DropPreKeyMsgHelpers.sliceDeallocX A gMsg.serPtr
              (BitVec.ofNat 64 m.serialized.length) ∗
            vecU8 A (fsp + 0x208#64) ([2#8] ++ m.serialized) ∗
            memRegion (fsp + 0x2a0#64) 8 ∗
            memRegion (fsp + 0x4d0#64) 248 ∗ sigTailNoOut) ⊢
        r2_words31 (fsp + 0x1750#64) ws ∗
          DropPreKeyMsgHelpers.sliceDeallocX A ws.w2 ws.w1 ∗
          A.pool ∗ stackAt fsp (resStack - runFrame) ∗
          (DropPreKeyMsgHelpers.optSliceDeallocX A ws.w12 ws.w13 ∗
            DropPreKeyMsgHelpers.sliceDeallocX A gMsg.serPtr
              (BitVec.ofNat 64 m.serialized.length) ∗
            vecU8 A (fsp + 0x208#64) ([2#8] ++ m.serialized) ∗
            memRegion (fsp + 0x2a0#64) 8 ∗
            memRegion (fsp + 0x4d0#64) 248 ∗ sigTailNoOut) :=
      Entails.of_eq (by ac_rfl)
    refine sepWPp_weaken_pre hreord_pq ?_
    refine r2_sig_free_pq hh hextNeed hsub64 hin3 htr_s3 hhist_s3
      fun s4 htr4 hin4 hcs4 htr_s4 hhist_s4 => ?_
    have hreord_ad :
        r2_words31 (fsp + 0x1750#64) ws ∗ A.pool ∗ stackAt fsp (resStack - runFrame) ∗
          (DropPreKeyMsgHelpers.optSliceDeallocX A ws.w12 ws.w13 ∗
            DropPreKeyMsgHelpers.sliceDeallocX A gMsg.serPtr
              (BitVec.ofNat 64 m.serialized.length) ∗
            vecU8 A (fsp + 0x208#64) ([2#8] ++ m.serialized) ∗
            memRegion (fsp + 0x2a0#64) 8 ∗
            memRegion (fsp + 0x4d0#64) 248 ∗ sigTailNoOut) ⊢
        r2_words31 (fsp + 0x1750#64) ws ∗
          DropPreKeyMsgHelpers.optSliceDeallocX A ws.w12 ws.w13 ∗
          A.pool ∗ stackAt fsp (resStack - runFrame) ∗
          (DropPreKeyMsgHelpers.sliceDeallocX A gMsg.serPtr
              (BitVec.ofNat 64 m.serialized.length) ∗
            vecU8 A (fsp + 0x208#64) ([2#8] ++ m.serialized) ∗
            memRegion (fsp + 0x2a0#64) 8 ∗
            memRegion (fsp + 0x4d0#64) 248 ∗ sigTailNoOut) :=
      Entails.of_eq (by ac_rfl)
    refine sepWPp_weaken_pre hreord_ad ?_
    refine r2_sig_free_ad hh hextNeed hsub64 hin4 htr_s4 hhist_s4
      fun s5 htr5 hin5 hcs5 htr_s5 hhist_s5 => ?_
    have hreord_ser :
        r2_words31 (fsp + 0x1750#64) ws ∗ A.pool ∗ stackAt fsp (resStack - runFrame) ∗
          (DropPreKeyMsgHelpers.sliceDeallocX A gMsg.serPtr
              (BitVec.ofNat 64 m.serialized.length) ∗
            vecU8 A (fsp + 0x208#64) ([2#8] ++ m.serialized) ∗
            memRegion (fsp + 0x2a0#64) 8 ∗
            memRegion (fsp + 0x4d0#64) 248 ∗ sigTailNoOut) ⊢
        DropPreKeyMsgHelpers.sliceDeallocX A gMsg.serPtr
            (BitVec.ofNat 64 m.serialized.length) ∗
          A.pool ∗ stackAt fsp (resStack - runFrame) ∗
          (memRegion (fsp + 0x1750#64) 248 ∗
            vecU8 A (fsp + 0x208#64) ([2#8] ++ m.serialized) ∗
            memRegion (fsp + 0x2a0#64) 8 ∗
            memRegion (fsp + 0x4d0#64) 248 ∗ sigTailNoOut) := by
      refine Entails.trans (sepConj_mono_left (r2_words31_to_memRegion248 (fsp + 0x1750#64) ws)) ?_
      exact Entails.of_eq (by ac_rfl)
    refine sepWPp_weaken_pre hreord_ser ?_
    have hcs25 : CalleeSavedPreserved s2 s5 := r2_csm_trans hcs3 (r2_csm_trans hcs4 hcs5)
    have hans_s5 := r2_ans_of_trace_eq (htr5.trans (htr4.trans htr3)) hans_s2
    refine r2_sig_free_ser hh hextNeed hsub64 hin5
      ((r2_csm_x23 hcs25).trans hx23_2)
      ((r2_csm_x24 hcs25).trans hx24_2)
      htr_s5 hhist_s5
      fun s6 htr6 hin6 hcs6 htr_s6 hhist_s6 => ?_
    have hcs26 : CalleeSavedPreserved s2 s6 := r2_csm_trans hcs25 hcs6
    have hfinal :
        A.pool ∗ stackAt fsp (resStack - runFrame) ∗
          (memRegion (fsp + 0x1750#64) 248 ∗
            vecU8 A (fsp + 0x208#64) ([2#8] ++ m.serialized) ∗
            memRegion (fsp + 0x2a0#64) 8 ∗
            memRegion (fsp + 0x4d0#64) 248 ∗ sigTailNoOut) ⊢
        addrNameHeap A meG ∗
          memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          addrNameHeap A peerG ∗ runSaved s0 ∗
          ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x330#64) 16 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
          vecU8 A (fsp + 0x208#64) ([2#8] ++ m.serialized) ∗ memRegion (fsp + 0x2a0#64) 8 ∗
          memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
          memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap := by
      dsimp only [sigTailNoOut]; exact Entails.of_eq (by ac_rfl)
    exact sepWPp_weaken_pre hfinal
      (r2_free_me_peer_join (peerG := peerG) (meG := meG) hh hextNeed hsub64 hin6
        ((r2_csm_x19 hcs26).trans hx19_2)
        ((r2_csm_x20 hcs26).trans hx20_2)
        ((r2_csm_x21 hcs26).trans hx21_2)
        ((r2_csm_x28 hcs26).trans hx28_2)
        htr_s6 hhist_s6
        (r2_ans_of_trace_eq htr6 hans_s5)
        hwr hjoin)

set_option linter.unusedTactic false in
set_option maxHeartbeats 800000 in
/-- Post-`encrypt` `Ok (.preKeySignalMessage m)` arm
(`R + 0x51c → 0xed0 → concat → 0xf08 → dropPreKeyMsg → 0xf14 → 0xf64 → 0xf8c`). -/
private theorem r2_pk_arm {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {g : RunCall} {peerG meG : AddrGhost}
    {g' : StoresGhost} {m : PreKeySignalMessage}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hcatNeed : 96 + extHookStack ≤ resStack - runFrame)
    (hdpkNeed : 48 + extHookStack ≤ resStack - runFrame)
    (hextNeed : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hin : InRun img ext s0 s 1308)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx22 : s.readReg64 (.gpr 22#5) = runFsp s0 + 0x4d0#64)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx27 : s.readReg64 (.gpr 27#5) = runFsp s0 + 0x1750#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, [3#8] ++ m.serialized)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (hser42 : m.serialized.length < 2 ^ 42)
    (hpanic : PanicK g s0 Qp)
    (hjoin : JoinK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (encResAt A (fsp + 0x4d0#64) (.ok (.preKeySignalMessage m)) ∗
        addrNameHeap A meG ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A peerG ∗ runSaved s0 ∗
        ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x330#64) 16 ∗
        memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
        memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
        memRegion (fsp + 0x1750#64) 248 ∗
        memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      Q Qp (runOom s0) := by
  intro fsp
  let pkTail : SepProp :=
    addrNameHeap A meG ∗
      memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A peerG ∗ runSaved s0 ∗
      ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗
      ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x330#64) 16 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      memRegion (fsp + 0x208#64) 24 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap
  let pkTailNoOut : SepProp :=
    addrNameHeap A meG ∗
      memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A peerG ∗ runSaved s0 ∗
      ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗
      ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x330#64) 16 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗ anyHeap
  rw [encResAt_ok]
  dsimp only [apiEncResultAt]
  have hpull_gp :
      (∃∗ gPk : PreKeyMsgGhost, preKeyMsgAt A gPk (fsp + 0x4d0#64) m) ∗
        (addrNameHeap A meG ∗
          memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          addrNameHeap A peerG ∗ runSaved s0 ∗
          ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x330#64) 16 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
          memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
          memRegion (fsp + 0x1750#64) 248 ∗
          memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap) =
      ∃∗ gPk : PreKeyMsgGhost,
        preKeyMsgAt A gPk (fsp + 0x4d0#64) m ∗
        memRegion (fsp + 0x1750#64) 248 ∗
        memRegion (fsp + 0x2a0#64) 8 ∗
        pkTail := by
    dsimp only [pkTail]
    simp only [sepExists_sepConj_left]
    ac_rfl
  rw [hpull_gp]
  apply r2_sepWPp_exists_left; intro gPk
  refine sepWPp_weaken_pre
    (sepConj_mono (r2_open_preKeyMessage A (fsp + 0x4d0#64) gPk m)
      (sepConj_mono (r2_memRegion248_open (fsp + 0x1750#64))
        (sepConj_mono_left (r2_tag8_open (fsp + 0x2a0#64))))) ?_
  apply r2_peel; intro ws
  apply r2_peel; intro Hrel
  apply r2_peel; intro dst0
  apply r2_peel; intro b2a0
  apply r2_peel_pure
  rintro ⟨hw0_lt, hw16, hw17, _, hser_lt, hclose_pk⟩
  simp only [emp_sepConj, sepConj_assoc]
  have hcopy_pre :
      r2_words31 (fsp + 0x4d0#64) ws ∗ (gPk.serPtr ↦ₛ m.serialized) ∗ Hrel ∗
        r2_words31 (fsp + 0x1750#64) dst0 ∗ ((fsp + 0x2a0#64) ↦₈ b2a0) ∗
        memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗ pkTail =
      r2_words31 (fsp + 0x4d0#64) ws ∗ r2_words31 (fsp + 0x1750#64) dst0 ∗
        (((fsp + 0x2a0#64) ↦₈ b2a0) ∗ memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗
          (gPk.serPtr ↦ₛ m.serialized) ∗ Hrel ∗ pkTail) := by
    ac_rfl
  rw [hcopy_pre]
  refine r2_step_chk_copy_pk hin hx22 hx26 hx27 hw0_lt
    fun s1 htr1 hfs1 hin1 hx19_1 hx20_1 hx21_1 hx28_1 => ?_
  have htr_s1 : s0.trace <+: s1.trace := htr1 ▸ htr
  have hhist_s1 : RunHistOk g.i s0 s1 :=
    r2_histOk_of_trace_files htr1 (congrArg FsState.files hfs1) hhist
  have hans_s1 : g.a = some (some (namedWrites g'.writes, [3#8] ++ m.serialized)) :=
    r2_ans_of_trace_eq htr1 hans
  have hopen_4d0 :
      r2_words31 (fsp + 0x4d0#64) ws ⊢
        (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
          ((fsp + 0x4d0#64) ↦₆₄ c0) ∗ (((fsp + 0x4d0#64) + 8#64) ↦₆₄ c1) ∗
          (((fsp + 0x4d0#64) + 16#64) ↦₆₄ c2) ∗ (((fsp + 0x4d0#64) + 24#64) ↦₆₄ c3)) ∗
        memRegion ((fsp + 0x4d0#64) + 32#64) 216 := by
    refine Entails.trans (r2_words31_to_memRegion248 (fsp + 0x4d0#64) ws) ?_
    rw [ProofLib.memRegion_split (fsp + 0x4d0#64) 32 216 (by decide)]
    exact sepConj_mono_left (r2_memRegion32_words4 (fsp + 0x4d0#64))
  refine sepWPp_weaken_pre (sepConj_mono_left hopen_4d0) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply r2_sepWPp_exists_left; intro _c0
  apply r2_sepWPp_exists_left; intro _c1
  apply r2_sepWPp_exists_left; intro _c2
  apply r2_sepWPp_exists_left; intro _c3
  have hpc : s1.pc = runPc img ext 3792 := hin1.pc
  have hrun1 : s1.status = .Running := hin1.run
  have hsp1 : s1.sp = fsp := hin1.sp
  have hsp1_al : s1.spAligned = true := hin1.spAligned_cur
  let _ := hsp1_al
  apply sepWPp_seq_inImage (mid := (mProg img ext).fnAddr cliConcatName) hin1.inv
  rw [← r2_hold_eq (memRegion ((fsp + 0x4d0#64) + 32#64) 216),
      ← r2_hold_eq (memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗ _)]
  unfold r2_words31
  dsimp only [fsp] at hsp1 ⊢
  rw [← hsp1]
  (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
  have hfn0 := MainHops.run_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
    (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 3792 72
  clear hfn0
  r2_prep_steps
  wp_steps
  apply SepWP.done (by r2_pc_done) (by r2_run hrun1)
  intro hinv2
  r2_post_steps
  rw [hsp1] at hinv2 ⊢
  rw [r2_hold_eq, r2_hold_eq]
  clear hpc
  refine sepWPp_weaken_pre
    (P' := ((fsp + 0x4d0#64) ↦₆₄ (fsp + 0x2a0#64)) ∗
      (((fsp + 0x4d0#64) + 8#64) ↦₆₄ 1#64) ∗
      (((fsp + 0x4d0#64) + 16#64) ↦₆₄ gPk.serPtr) ∗
      (((fsp + 0x4d0#64) + 24#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
      SpqrV1.ChainProofs.bytesAt false (fsp + 0x2a0#64) [3#8] ∗
      SpqrV1.ChainProofs.bytesAt false gPk.serPtr m.serialized ∗
      memRegion (fsp + 0x208#64) 24 ∗
      A.pool ∗ stackAt fsp (resStack - runFrame) ∗
      (memRegion ((fsp + 0x4d0#64) + 32#64) 216 ∗
        memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗
        r2_words31 (fsp + 0x1750#64) ws ∗
        Hrel ∗ pkTailNoOut))
    (by
      unfold r2_words31
      dsimp only [fsp, pkTail, pkTailNoOut]
      rw [hw16, hw17, SpqrV1.ChainProofs.bytesAt_false, SpqrV1.ChainProofs.bytesAt_false,
        ProofLib.pointsToBytes_singleton]
      (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact Entails.of_eq (by ac_rfl)) ?_
  have hhist_cat : RunHistOk g.i s0 _ :=
    r2_histOk_of_trace_files (by r2_eq) (by r2_eq) hhist_s1
  have hans_cat : g.a = some (some (namedWrites g'.writes, [3#8] ++ m.serialized)) :=
    hans_s1
  let catG : SpqrV1.ChainProofs.SliceConcat2Ghost :=
    ⟨fsp + 0x208#64, fsp + 0x4d0#64, false, fsp + 0x2a0#64, [3#8],
     false, gPk.serPtr, m.serialized⟩
  refine r2_call_inImage_steps (s0 := s0) catG
    (r2_concat2_le_ok hh (resStack - runFrame) hcatNeed hsub64)
    hinv2
    (by r2_pc_done)
    (by r2_run hrun1)
    (by (try simp only [arm64_norm]); exact hsp1_al)
    (ret_pc := runPc img ext 3848)
    (by r2_pc_done)
    (F := memRegion ((fsp + 0x4d0#64) + 32#64) 216 ∗
      memRegion ((fsp + 0x2a0#64) + 1#64) 7 ∗
      r2_words31 (fsp + 0x1750#64) ws ∗
      Hrel ∗ pkTailNoOut)
    ?_
    (hpanic := fun sf R' _ hp => by
      dsimp only [r2_concat2LeSpec] at hp
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      rcases hp.1.1 with halloc1 | ⟨hlen_eq, _⟩
      · exact hpanic sf _ (Or.inr
          (allocFailedIn_of_prefix htr_s1 (r2_allocFailedIn_of_trace_eq (by r2_eq) halloc1)))
      · exfalso
        dsimp only [catG, List.length] at hlen_eq
        omega)
    (hnext := fun s2 hsteps2 hinv_s2 hpcm2 hrun2 hsp2 hcs2 => ?_)
  · dsimp only [r2_concat2LeSpec, catG]
    rw [sepConj_assoc]
    apply Entails.pure_right
    · exact ⟨by (try simp only [arm64_norm]); dsimp only [fsp]; bv_omega,
             by (try simp only [arm64_norm]); dsimp only [fsp]; bv_omega,
             by r2_eq, rfl, hser_lt⟩
    · (try simp only [arm64_norm])
      rw [hsp1]
      dsimp only [fsp]
      exact Entails.of_eq (by ac_rfl)
  · dsimp only [r2_concat2LeSpec, RunProofs.cliConcat2Spec, catG]
    rw [sepConj_assoc]
    apply SepWPp.pure_left; intro htr2
    have hfs2 := r2_files_of_trace_eq hh hsteps2 htr2
    have htr_s2 : s0.trace <+: s2.trace := by rw [htr2]; exact htr_s1
    have hhist_s2 : RunHistOk g.i s0 s2 := r2_histOk_of_trace_files htr2 hfs2 hhist_cat
    have hans_s2 := r2_ans_of_trace_eq htr2 hans_cat
    have hin2 : InRun img ext s0 s2 3848 :=
      r2_inRun_mk hin1 hpcm2 hrun2 (hsp2.trans (by r2_eq))
        ((r2_csm_fp hcs2).trans (by r2_eq)) hinv_s2
        ((r2_csm_vregs hcs2).trans (by r2_eq))
    have hx19_2 : s2.readReg64 (.gpr 19#5) = g.stores := by
      rw [r2_csm_x19 hcs2]; (try simp only [arm64_norm]); exact hx19_1.trans hx19
    have hx20_2 : s2.readReg64 (.gpr 20#5) = g.res := by
      rw [r2_csm_x20 hcs2]; (try simp only [arm64_norm]); exact hx20_1.trans hx20
    have hx21_2 : s2.readReg64 (.gpr 21#5) = meG.name.cap := by
      rw [r2_csm_x21 hcs2]; (try simp only [arm64_norm]); exact hx21_1.trans hx21
    have hx28_2 : s2.readReg64 (.gpr 28#5) = meG.name.ptr := by
      rw [r2_csm_x28 hcs2]; (try simp only [arm64_norm]); exact hx28_1.trans hx28
    refine sepWPp_weaken_pre (P' :=
        preKeyMsgAt A gPk (fsp + 0x1750#64) m ∗ A.pool ∗ stackAt fsp (resStack - runFrame) ∗
          (vecU8 A (fsp + 0x208#64) ([3#8] ++ m.serialized) ∗
            memRegion (fsp + 0x2a0#64) 8 ∗
            memRegion (fsp + 0x4d0#64) 248 ∗ pkTailNoOut)) ?_ ?_
    · refine Entails.trans (Entails.of_eq (Q :=
          (r2_words31 (fsp + 0x1750#64) ws ∗ (gPk.serPtr ↦ₛ m.serialized) ∗ Hrel) ∗
            (((fsp + 0x4d0#64) ↦₆₄ (fsp + 0x2a0#64)) ∗
              (((fsp + 0x4d0#64) + 8#64) ↦₆₄ BitVec.ofNat 64 ([3#8] : List (BitVec 8)).length) ∗
              (((fsp + 0x4d0#64) + 16#64) ↦₆₄ gPk.serPtr) ∗
              (((fsp + 0x4d0#64) + 24#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
              memRegion ((fsp + 0x4d0#64) + 32#64) 216) ∗
            (SpqrV1.ChainProofs.bytesAt false (fsp + 0x2a0#64) [3#8] ∗
              memRegion ((fsp + 0x2a0#64) + 1#64) 7) ∗
            (A.pool ∗ stackAt fsp (resStack - runFrame) ∗
              vecU8 A (fsp + 0x208#64) ([3#8] ++ m.serialized) ∗ pkTailNoOut)) ?_) ?_
      · rw [SpqrV1.ChainProofs.bytesAt_false gPk.serPtr m.serialized]
        (try simp only [arm64_norm])
        rw [hsp1]
        dsimp only [fsp, runFsp]
        (try simp only [arm64_norm])
        ac_rfl
      · refine Entails.trans
          (sepConj_mono (hclose_pk (fsp + 0x1750#64))
            (sepConj_mono (r2_words4_216_rejoin (fsp + 0x4d0#64) _ _ _ _)
              (sepConj_mono_left (r2_tag8_close (fsp + 0x2a0#64) 3#8)))) ?_
        exact Entails.of_eq (by ac_rfl)
    have hpc : s2.pc = runPc img ext 3848 := hin2.pc
    have hsp2_eq : s2.sp = fsp := hin2.sp
    have hsp2_al : s2.spAligned = true := hin2.spAligned_cur
    let _ := hsp2_al
    apply sepWPp_seq_inImage (mid := (mProg img ext).fnAddr cliDropPreKeyMsgName) hin2.inv
    rw [← r2_hold_eq (preKeyMsgAt A gPk (fsp + 0x1750#64) m ∗ _)]
    have hfn0 := MainHops.run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 3792 72
    clear hfn0
    r2_prep_steps
    wp_steps
    apply SepWP.done (by r2_pc_done) (by r2_run hrun2)
    intro hinv3
    r2_post_steps
    rw [r2_hold_eq]
    clear hpc
    refine r2_call_inImage_steps (s0 := s0)
      ⟨fsp + 0x1750#64, gPk, m⟩
      (RunSkeleton.dropPreKeyMsg_ok_ext hh (resStack - runFrame)
        (Nat.le_trans (by decide : 32 + extHookStack ≤ 48 + extHookStack) hdpkNeed) hsub64)
      hinv3
      (by r2_pc_done)
      (by r2_run hrun2)
      (by (try simp only [arm64_norm]); exact hsp2_al)
      (ret_pc := runPc img ext 3860)
      (by r2_pc_done)
      (F := vecU8 A (fsp + 0x208#64) ([3#8] ++ m.serialized) ∗
        memRegion (fsp + 0x2a0#64) 8 ∗
        memRegion (fsp + 0x4d0#64) 248 ∗ pkTailNoOut)
      ?_
      (hnext := fun s3 hsteps3 hinv_s3 hpcm3 hrun3 hsp3 hcs3 => ?_)
    · dsimp only [RunProofs.dropPreKeyMsgSpec]
      rw [sepConj_assoc]
      refine Entails.pure_right
        (by (try simp only [arm64_norm]); rw [hsp2_eq]) ?_
      (try simp only [arm64_norm])
      rw [hsp2_eq]
      dsimp only [fsp, runFsp]
      (try simp only [arm64_norm])
      exact Entails.of_eq (by ac_rfl)
    · dsimp only [RunProofs.dropPreKeyMsgSpec]
      rw [sepConj_assoc]
      apply SepWPp.pure_left; intro htr3
      have hfs3 := r2_files_of_trace_eq hh hsteps3 htr3
      have htr_s3 : s0.trace <+: s3.trace := htr3 ▸ htr_s2
      have hhist_s3 : RunHistOk g.i s0 s3 :=
        r2_histOk_of_trace_files htr3 hfs3
          (r2_histOk_of_trace_files (by r2_eq) (by r2_eq) hhist_s2)
      have hans_s3 := r2_ans_of_trace_eq htr3 hans_s2
      have hin3 : InRun img ext s0 s3 3860 :=
        r2_inRun_mk hin2 hpcm3 hrun3 (hsp3.trans (by r2_eq))
          ((r2_csm_fp hcs3).trans (by r2_eq)) hinv_s3
          ((r2_csm_vregs hcs3).trans (by r2_eq))
      have hpc : s3.pc = runPc img ext 3860 := hin3.pc
      apply sepWPp_seq_inImage (mid := runPc img ext 3940) hin3.inv
      rw [← r2_hold_eq ((memRegion (fsp + 0x1750#64) 248 ∗ _) ∗ _)]
      have hfn0 := MainHops.run_fnOff
      code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
        (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 3792 72
      clear hfn0
      r2_prep_steps
      wp_steps
      apply SepWP.done (by r2_pc_done) (by r2_run hrun3)
      intro hinv4
      r2_post_steps
      rw [r2_hold_eq]
      have hin4 : InRun img ext s0 _ 3940 :=
        r2_inRun_mk hin3 (by r2_pc_done)
          (by r2_run hrun3) (by r2_eq)
          (by r2_eq) hinv4 (by r2_eq)
      refine sepWPp_weaken_pre (P' :=
          addrNameHeap A meG ∗
            memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            addrNameHeap A peerG ∗ runSaved s0 ∗
            ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x330#64) 16 ∗
            memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
            vecU8 A (fsp + 0x208#64) ([3#8] ++ m.serialized) ∗ memRegion (fsp + 0x2a0#64) 8 ∗
            memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
            memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
            stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap) ?_ ?_
      · (try simp only [arm64_norm])
        rw [hsp2_eq]
        dsimp only [pkTailNoOut, fsp, runFsp]
        (try simp only [arm64_norm])
        exact Entails.of_eq (by ac_rfl)
      · exact r2_free_me_peer_join (peerG := peerG) (meG := meG) hh hextNeed hsub64 hin4
          (by (try simp only [arm64_norm]); exact (r2_csm_x19 hcs3).trans (by (try simp only [arm64_norm]); exact hx19_2))
          (by (try simp only [arm64_norm]); exact (r2_csm_x20 hcs3).trans (by (try simp only [arm64_norm]); exact hx20_2))
          (by (try simp only [arm64_norm]); exact (r2_csm_x21 hcs3).trans (by (try simp only [arm64_norm]); exact hx21_2))
          (by (try simp only [arm64_norm]); exact (r2_csm_x28 hcs3).trans (by (try simp only [arm64_norm]); exact hx28_2))
          (by (try simp only [arm64_norm]); exact htr_s3)
          (r2_histOk_of_trace_files (by r2_eq) (by r2_eq) hhist_s3)
          hans_s3
          hwr hjoin

set_option maxHeartbeats 1600000 in
/-- Send-arm hop theorem (`R+0x214 → R+0xf8c` or `R+0x2c7c` when `g.c = .send peerV`): unpacks
`peerV` into `sp + 0x320`, rejects when `me = .none`, calls `hc.encrypt`, and either builds
`[2] ‖ serialized` (`SignalMessage`) or `[3] ‖ serialized` (`PreKeySignalMessage`) to reach
`AtJoin` (`R + 0xf8c`), or drops any error via `hdrop` to reach `AtReject` (`R + 0x2c7c`). -/
theorem run_hop_send_ok_ext {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {g : RunCall} {peerV : AddrV}
    {me : MeAtDispatch} {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    (hc : RunCallees img A ext B (slotsOf A img S needs))
    (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hres : runNeed B (slotsOf A img S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63)
    (hspb : resStack ≤ s0.sp.toNat)
    (he : AtRunEntry S img ext g s0)
    (hd : AtDispatch img ext g me s0 s)
    (hcall : g.c = .send peerV)
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectK img ext A g s0 resStack Q Qp)
    (hjoin : JoinK img ext A g s0 resStack Q Qp) :
    ProofLib.SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (dispatchMem A img g me s0 resStack) Q Qp (runOom s0) := by
  obtain ⟨hframeLe, hsub63, hsub64, _, _, _, _, _, _, _, _, _, _, _, hdropNeed, hcatNeed, hextNeed,
    hencNeed, _, _, _, hdpkNeed⟩ := runNeed_bounds hres hres64
  let fsp := runFsp s0
  have hfsp_def : runFsp s0 = fsp := rfl
  have hpc : s.pc = runPc img ext 532 := hd.base.pc
  have hrun0 : s.status = .Running := hd.base.run
  have hsp0 : s.sp = fsp := hd.base.sp
  have hsp_al : s.spAligned = true := hd.base.spAligned_cur
  let _ := hsp_al
  have hx8 : s.readReg64 (.gpr 8#5) = 2#64 := by rw [hd.x8, hcall]; rfl
  have hx25 : s.readReg64 (.gpr 25#5) = g.call := hd.x25
  let _ := hx8; let _ := hx25
  have hd_gt : ConditionHolds .GT (subsPState64 2#64 1#64) = true := by r2_cond
  have hd_le : ConditionHolds .LE (subsPState64 2#64 1#64) = false := by r2_cond
  have hs_ne : ConditionHolds .NE (subsPState64 2#64 2#64) = false := by r2_cond
  have hs_eq : ConditionHolds .EQ (subsPState64 2#64 2#64) = true := by r2_cond
  let _ := hd_gt; let _ := hd_le; let _ := hs_ne; let _ := hs_eq
  have hhist0 : RunHistOk g.i s0 s := ⟨hd.fs, hd.stdout⟩
  refine sepWPp_weaken_pre
    (Entails.trans (Entails.of_eq (sepConj_emp _).symm)
      (sepConj_mono_right (entails_anyHeap emp))) ?_
  cases me with
  | none =>
    have hans_none : g.a = some none := AtDispatch.reject_of_me_none he hd
    have hx20 : s.readReg64 (.gpr 20#5) = g.res := hd.x20
    have hx21_none : s.readReg64 (.gpr 21#5) = 0xffffffffffffffff#64 := hd.meRegs
    let _ := hx20; let _ := hx21_none
    have hmn_eq : ConditionHolds .EQ (addsPState64 0xffffffffffffffff#64 1#64) = true := by r2_cond
    have hmn_ne : ConditionHolds .NE (addsPState64 0xffffffffffffffff#64 1#64) = false := by r2_cond
    let _ := hmn_eq; let _ := hmn_ne
    dsimp only [dispatchMem, dispatchMeHeap, dispatchCells]
    rw [hfsp_def, hcall, emp_sepConj, r2_locals_none_eq fsp]
    have hopen_none :
        (memRegion g.res runResSize ∗ callAt A g.call (.send peerV) ∗
          storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i (.send peerV)) ∗
          coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
          CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ logOff img ∗
          runSaved s0 ∗
          (memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x208#64) 24 ∗
            memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x320#64) 32 ∗
            memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
            memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool) ∗ anyHeap ⊢
        (∃∗ r0 : BitVec 64, (g.res ↦₆₄ r0) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
        (∃∗ peerG : AddrGhost, ∃∗ cw : CallW,
          ⌜peerG.val = addrValOf peerV ∧ peerG.name.cap = cw.w1 ∧ peerG.name.ptr = cw.w2 ∧
            cw.w3 = BitVec.ofNat 64 peerG.name.bytes.length ∧ cw.w4.setWidth 8 = peerG.device⌝ ∗
          ((g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
            ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
            ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6)) ∗
          addrNameHeap A peerG) ∗
        (∃∗ p0 : BitVec 64, ∃∗ p1 : BitVec 64, ∃∗ p2 : BitVec 64, ∃∗ p3 : BitVec 64,
          ((fsp + 0x320#64) ↦₆₄ p0) ∗ (((fsp + 0x320#64) + 8#64) ↦₆₄ p1) ∗
          (((fsp + 0x320#64) + 16#64) ↦₆₄ p2) ∗ (((fsp + 0x320#64) + 24#64) ↦₆₄ p3)) ∗
        (storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i (.send peerV)) ∗
          coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
          CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ logOff img ∗ runSaved s0 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x208#64) 24 ∗
          memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x4d0#64) 248 ∗
          memRegion (fsp + 0x1750#64) 248 ∗ memRegion (fsp + 0x23b0#64) 32 ∗
          r2_localGaps fsp ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap) := by
      refine Entails.trans (Entails.of_eq (Q :=
          memRegion g.res runResSize ∗
            callAt A g.call (.send peerV) ∗
            memRegion (fsp + 0x320#64) 32 ∗
            (storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i (.send peerV)) ∗
              coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
              CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ logOff img ∗ runSaved s0 ∗
              memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x208#64) 24 ∗
              memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x4d0#64) 248 ∗
              memRegion (fsp + 0x1750#64) 248 ∗ memRegion (fsp + 0x23b0#64) 32 ∗
              r2_localGaps fsp ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)) (by ac_rfl)) ?_
      exact sepConj_mono (r2_res_open g.res)
        (sepConj_mono (r2_callAt_send_unpack A g.call peerV)
          (sepConj_mono_left (r2_memRegion32_words4 (fsp + 0x320#64))))
    refine sepWPp_weaken_pre hopen_none ?_
    apply r2_peel; intro _r0
    apply r2_peel; intro peerG
    apply r2_peel; intro cw
    apply r2_peel; intro _p0
    apply r2_peel; intro _p1
    apply r2_peel; intro _p2
    apply r2_peel; intro _p3
    apply r2_peel_pure; rintro ⟨_, hw1, hw2, _, _⟩
    simp only [emp_sepConj, sepConj_assoc]
    apply sepWPp_seq_inImage (mid := runPc img ext 2984) hd.base.inv
    rw [← r2_hold_eq (memRegion (g.res + 8#64) (runResSize - 8)),
        ← r2_hold_eq (addrNameHeap A peerG),
        ← r2_hold_eq (storesAt A g.stores StoresGhost.opened ∗ _)]
    dsimp only [fsp] at hsp0 ⊢
    rw [← hsp0]
    (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
    have hfn0 := MainHops.run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 532 8
    code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 1200 108
    code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 2132 12
    clear hfn0
    r2_prep_steps
    wp_steps
    apply SepWP.done (by r2_pc_done) (by r2_run hrun0)
    intro hinv1
    r2_post_steps
    rw [hsp0]
    rw [r2_hold_eq, r2_hold_eq, r2_hold_eq]
    have hin1 : InRun img ext s0 _ 2984 :=
      r2_inRun_mk hd.base (by r2_pc_done)
        (by r2_run hrun0) (by r2_eq)
        (by r2_eq) hinv1 (by r2_eq)
    have hp16 :
        ((fsp + 0x330#64) ↦₆₄ cw.w3) ∗ ((fsp + 0x338#64) ↦₆₄ cw.w4) ⊢
          memRegion (fsp + 0x330#64) 16 := by
      rw [ProofLib.memRegion_split' (b := fsp + 0x330#64) (n := 8) (k := 8)
            (b' := fsp + 0x338#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
    let postNone : SepProp :=
      runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A peerG ∗ runSaved s0 ∗
        ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x330#64) 16 ∗
        memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
        memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
        memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
        memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap
    refine sepWPp_weaken_pre (P' := postNone) ?_ ?_
    · dsimp only [postNone]
      rw [hcall]
      have hres_n := r2_res_write_none A g.res 0xffffffffffffffff#64 rfl
      have hcw_m := r2_callWords_to_memRegion56 g.call cw
      refine Entails.trans (Entails.of_eq (Q :=
          (((g.res ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
            ((g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗
              ((g.call + 16#64) ↦₆₄ cw.w2) ∗ ((g.call + 24#64) ↦₆₄ cw.w3) ∗
              ((g.call + 32#64) ↦₆₄ cw.w4) ∗ ((g.call + 40#64) ↦₆₄ cw.w5) ∗
              ((g.call + 48#64) ↦₆₄ cw.w6)) ∗
            (((fsp + 0x330#64) ↦₆₄ cw.w3) ∗ ((fsp + 0x338#64) ↦₆₄ cw.w4)) ∗
            (coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
              CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ logOff img ∗ anyHeap) ∗
            (storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i (.send peerV)) ∗
              addrNameHeap A peerG ∗ runSaved s0 ∗
              ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
              memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
              memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
              memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
              memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
              stackAt fsp (resStack - runFrame) ∗ A.pool))) ?_) ?_
      · rw [← hw1, ← hw2]
        dsimp only [fsp]
        ac_rfl
      · refine Entails.trans
          (sepConj_mono hres_n
            (sepConj_mono hcw_m
              (sepConj_mono hp16
                (sepConj_mono_left (entails_anyHeap _))))) ?_
        exact Entails.of_eq (by ac_rfl)
    · exact r2_free_peer_reject (peerG := peerG) hh hextNeed hsub64 hin1
        (by (try simp only [arm64_norm]); exact hd.x19)
        (by (try simp only [arm64_norm]); exact hd.trace)
        (r2_histOk_of_trace_files (by r2_eq) (by r2_eq) hhist0)
        hans_none
        hrej
  | some meV meG =>
    obtain ⟨hptLt, hcoinsLt, hfs0, hfilesOk, hencOk, hansLink⟩ :=
      AtDispatch.send_facts he hd hcall
    rcases hd.meRegs with ⟨hx21, hx28, hme_bytes, _, hme_dev⟩
    have hme_val : meG.val = addrValOf meV := by
      unfold AddrGhost.val addrValOf; simp [hme_bytes, hme_dev]
    have halign_b : (img.base &&& 0xfff#64) = 0#64 := r2_loads_base_aligned himg
    let _ := halign_b
    dsimp only [dispatchMem, dispatchMeHeap, dispatchCells]
    rw [hfsp_def, hcall, r2_locals_some_eq fsp]
    have hopen_some :
        (memRegion g.res runResSize ∗ callAt A g.call (.send peerV) ∗
          storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i (.send peerV)) ∗
          coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
          CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ logOff img ∗
          addrNameHeap A meG ∗ runSaved s0 ∗
          (memRegion fsp 16 ∗ addrUpperAt (fsp + 0x1d0#64) meG ∗ memRegion (fsp + 0x208#64) 24 ∗
            memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x320#64) 32 ∗
            memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
            memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool) ∗ anyHeap ⊢
        (∃∗ peerG : AddrGhost, ∃∗ cw : CallW,
          ⌜peerG.val = addrValOf peerV ∧ peerG.name.cap = cw.w1 ∧ peerG.name.ptr = cw.w2 ∧
            cw.w3 = BitVec.ofNat 64 peerG.name.bytes.length ∧ cw.w4.setWidth 8 = peerG.device⌝ ∗
          ((g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
            ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
            ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6)) ∗
          addrNameHeap A peerG) ∗
        (⌜meG.name.cap.toNat < 2 ^ 63⌝ ∗ addrNameHeap A meG) ∗
        (∃∗ n0 : BitVec 64, ∃∗ n1 : BitVec 32,
          (fsp ↦₆₄ n0) ∗ ((fsp + 8#64) ↦₃₂ n1) ∗ memRegion (fsp + 12#64) 4) ∗
        (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64,
          ⌜∀ dst, (dst ↦₆₄ u0) ∗ ((dst + 8#64) ↦₆₄ u1) ⊢ addrUpperAt dst meG⌝ ∗
            ((fsp + 0x1d0#64) ↦₆₄ u0) ∗ (((fsp + 0x1d0#64) + 8#64) ↦₆₄ u1)) ∗
        (∃∗ p0 : BitVec 64, ∃∗ p1 : BitVec 64, ∃∗ p2 : BitVec 64, ∃∗ p3 : BitVec 64,
          ((fsp + 0x320#64) ↦₆₄ p0) ∗ (((fsp + 0x320#64) + 8#64) ↦₆₄ p1) ∗
          (((fsp + 0x320#64) + 16#64) ↦₆₄ p2) ∗ (((fsp + 0x320#64) + 24#64) ↦₆₄ p3)) ∗
        (∃∗ m0 : BitVec 64, ∃∗ m1 : BitVec 64, ∃∗ m2 : BitVec 64, ∃∗ m3 : BitVec 64,
          ((fsp + 0x23b0#64) ↦₆₄ m0) ∗ (((fsp + 0x23b0#64) + 8#64) ↦₆₄ m1) ∗
          (((fsp + 0x23b0#64) + 16#64) ↦₆₄ m2) ∗ (((fsp + 0x23b0#64) + 24#64) ↦₆₄ m3)) ∗
        (memRegion g.res runResSize ∗
          storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ g.i.stdin) ∗
          coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
          CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ logOff img ∗ runSaved s0 ∗
          memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
          memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
          r2_localGaps fsp ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap) := by
      have hinp : inputOf g.i (.send peerV) = g.i.stdin := rfl
      rw [hinp]
      have hgrp_s :
          (memRegion g.res runResSize ∗ callAt A g.call (.send peerV) ∗
            storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ g.i.stdin) ∗
            coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
            CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ logOff img ∗
            addrNameHeap A meG ∗ runSaved s0 ∗
            (memRegion fsp 16 ∗ addrUpperAt (fsp + 0x1d0#64) meG ∗ memRegion (fsp + 0x208#64) 24 ∗
              memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x320#64) 32 ∗
              memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
              memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp) ∗
            stackAt fsp (resStack - runFrame) ∗ A.pool) ∗ anyHeap =
          callAt A g.call (.send peerV) ∗
            addrNameHeap A meG ∗
            memRegion fsp 16 ∗
            addrUpperAt (fsp + 0x1d0#64) meG ∗
            memRegion (fsp + 0x320#64) 32 ∗
            memRegion (fsp + 0x23b0#64) 32 ∗
            (memRegion g.res runResSize ∗
              storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ g.i.stdin) ∗
              coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
              CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ logOff img ∗ runSaved s0 ∗
              memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
              memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
              r2_localGaps fsp ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap) := by
        ac_rfl
      rw [hgrp_s]
      exact sepConj_mono (r2_callAt_send_unpack A g.call peerV)
        (sepConj_mono (r2_addrNameHeap_cap_lt A meG)
          (sepConj_mono (r2_now_open fsp)
            (sepConj_mono (r2_addrUpperAt_reloc (fsp + 0x1d0#64) meG)
              (sepConj_mono (r2_memRegion32_words4 (fsp + 0x320#64))
                (sepConj_mono_left (r2_memRegion32_words4 (fsp + 0x23b0#64)))))))
    refine sepWPp_weaken_pre hopen_some ?_
    apply r2_peel; intro peerG
    apply r2_peel; intro cw
    apply r2_peel; intro _n0
    apply r2_peel; intro _n1
    apply r2_peel; intro u0
    apply r2_peel; intro u1
    apply r2_peel; intro _p0
    apply r2_peel; intro _p1
    apply r2_peel; intro _p2
    apply r2_peel; intro _p3
    apply r2_peel; intro _m0
    apply r2_peel; intro _m1
    apply r2_peel; intro _m2
    apply r2_peel; intro _m3
    apply r2_peel_pure; rintro ⟨hpeer_val, hw1, hw2, hw3, hw4⟩
    apply r2_peel_pure; intro hme_lt
    let _ := hme_lt
    apply r2_peel_pure; intro hu_me
    simp only [emp_sepConj, sepConj_assoc]
    have hcmn_z : (meG.name.cap + 1#64 == 0#64) = false :=
      beq_eq_false_iff_ne.mpr (by bv_omega)
    have hcmn_nz : (meG.name.cap + 1#64 != 0#64) = true :=
      bne_iff_ne.mpr (by bv_omega)
    have hcmn_ne : ConditionHolds .EQ (addsPState64 meG.name.cap 1#64) = false := by
      rw [conditionHolds_eq_addsPState64]; exact hcmn_z
    have hcmn_neq : ConditionHolds .NE (addsPState64 meG.name.cap 1#64) = true := by
      rw [conditionHolds_ne_addsPState64]; exact hcmn_nz
    let _ := hcmn_z; let _ := hcmn_nz; let _ := hcmn_ne; let _ := hcmn_neq
    apply sepWPp_seq_inImage (mid := (mProg img ext).fnAddr wrapEncryptName) hd.base.inv
    rw [← r2_hold_eq (addrNameHeap A peerG),
        ← r2_hold_eq (addrNameHeap A meG),
        ← r2_hold_eq (memRegion (fsp + 12#64) 4),
        ← r2_hold_eq (memRegion g.res runResSize ∗ _)]
    dsimp only [fsp] at hsp0 ⊢
    rw [← hsp0]
    (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
    have hfn0 := MainHops.run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 532 8
    code_fetches_range CryptoVerification.libsignalSessionCode r2_dec img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 1200 108
    clear hfn0
    r2_prep_steps
    wp_steps
    apply SepWP.done (by r2_pc_done) (by r2_run hrun0)
    intro hinv_enc
    r2_post_steps
    rw [hsp0] at hinv_enc ⊢
    rw [r2_hold_eq, r2_hold_eq, r2_hold_eq, r2_hold_eq]
    have hx24_toNat : (s.readReg64 (.gpr 24#5)).toNat = g.i.stdin.length := by
      rw [hd.x24, hcall]
      have hinp : (inputOf g.i (.send peerV)).length = g.i.stdin.length := rfl
      rw [hinp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    let encG : EncGhost :=
      { peer := peerG
        peerA := fsp + 0x320#64
        me := meG
        meA := fsp + 0x23b0#64
        stores := g.stores
        ret := fsp + 0x4d0#64
        coinsP := g.coins
        F := runFiles g.i
        coins := MainHops.coinsOf g.i
        ptA := g.inp
        ptext := g.i.stdin }
    have hspb_enc : resStack - runFrame ≤ (runFsp s0).toNat := by
      dsimp only [runFsp]; dsimp only [runFrame] at hframeLe ⊢; bv_omega
    have hmeA_ne : fsp + 0x23b0#64 ≠ 0#64 := by
      dsimp only [fsp, runFsp]; dsimp only [runFrame] at hframeLe; bv_omega
    refine r2_call_inImage_steps (spec := r2_encInnerSpec A img S (resStack - runFrame)) (s0 := s0) encG
      (hc.encrypt (resStack - runFrame) hencNeed hsub63)
      hinv_enc
      (by r2_pc_done)
      (by r2_run hrun0)
      (by (try simp only [arm64_norm]); exact hsp_al)
      (ret_pc := runPc img ext 1308)
      (by r2_pc_done)
      (F := memRegion g.res runResSize ∗ memRegion g.call 56 ∗ runSaved s0 ∗
        memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x208#64) 24 ∗
        memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x1750#64) 248 ∗
        r2_localGaps fsp ∗ anyHeap)
      ?_
      (hpanic := fun sf R' _ hp => by
        (try dsimp only [r2_encInnerSpec, encG] at hp)
        rw [sepConj_assoc, satisfies_pure_sepConj] at hp
        rcases hp.1 with hnone | halloc
        · rw [hpeer_val, hme_val] at hnone
          have ga0 : g.a = none := by rw [hansLink, hnone]; rfl
          exact hpanic sf _ (Or.inl ga0)
        · exact hpanic sf _ (Or.inr
            (allocFailedIn_of_prefix hd.trace (r2_allocFailedIn_of_trace_eq (by r2_eq) halloc))))
      (hoom := fun _ _ _ ho => by
        (try dsimp only [r2_encInnerSpec, encG] at ho)
        exact (not_satisfies_false_sepConj ho).elim)
      (hnext := fun s_ret _ hinv_ret hpcm_ret hrun_ret hsp_ret hcs_ret => ?_)
    ·
      dsimp only [r2_encInnerSpec, slotFrame, encG]
      rw [sepConj_assoc]
      apply Entails.pure_right
      · exact ⟨by (try simp only [arm64_norm]); exact hd.x23,
               by (try simp only [arm64_norm]); exact hx24_toNat,
               hptLt,
               by (try simp only [arm64_norm]); dsimp only [fsp]; bv_omega,
               by (try simp only [arm64_norm]); dsimp only [fsp]; bv_omega,
               by (try simp only [arm64_norm]); rw [hd.x19],
               by (try simp only [arm64_norm]); rw [r2_sessVt_eq],
               by (try simp only [arm64_norm]); exact hd.x19,
               by (try simp only [arm64_norm]); rw [r2_idVt_eq],
               by (try simp only [arm64_norm]); dsimp only [fsp]; bv_omega,
               by (try simp only [arm64_norm]); exact hfs0,
               by rw [hpeer_val, hme_val]; exact hfilesOk,
               by rw [hpeer_val]; exact hencOk,
               by (try simp only [arm64_norm]); rw [hsp0]; exact hspb_enc,
               hmeA_ne⟩
      · (try simp only [arm64_norm])
        rw [hsp0, ← hw3]
        have hcw_m := r2_callWords_to_memRegion56 g.call cw
        have hpeer_p := r2_peerWords_pack A (fsp + 0x320#64) peerG cw hw1 hw2 hw3 hw4
        have hme_p :
            ((fsp + 0x23b0#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x23b8#64) ↦₆₄ meG.name.ptr) ∗
              ((fsp + 0x23c0#64) ↦₆₄ u0) ∗ ((fsp + 0x23c8#64) ↦₆₄ u1) ∗ addrNameHeap A meG ⊢
            protocolAddressAt A meG (fsp + 0x23b0#64) := by
          rw [protocolAddressAt_eq_parts A meG (fsp + 0x23b0#64)]
          (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
          exact sepConj_mono_right (sepConj_mono_right
            (Entails.trans (Entails.of_eq (sepConj_assoc _ _ _).symm)
              (sepConj_mono_left
                (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hu_me (fsp + 0x23c0#64)))))
        have hu16 :
            ((fsp + 0x1d0#64) ↦₆₄ u0) ∗ ((fsp + 0x1d8#64) ↦₆₄ u1) ⊢
              memRegion (fsp + 0x1d0#64) 16 := by
          rw [ProofLib.memRegion_split' (b := fsp + 0x1d0#64) (n := 8) (k := 8)
                (b' := fsp + 0x1d8#64) rfl (by bv_omega) (by decide)]
          exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
        (try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpeer_p)
        refine Entails.trans (Entails.of_eq (Q :=
            (((g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
                ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
                ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6)) ∗
              (((fsp + 0x320#64) ↦₆₄ cw.w1) ∗ ((fsp + 0x328#64) ↦₆₄ cw.w2) ∗
                ((fsp + 0x330#64) ↦₆₄ cw.w3) ∗ ((fsp + 0x338#64) ↦₆₄ cw.w4) ∗
                addrNameHeap A peerG) ∗
              (((fsp + 0x23b0#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x23b8#64) ↦₆₄ meG.name.ptr) ∗
                ((fsp + 0x23c0#64) ↦₆₄ u0) ∗ ((fsp + 0x23c8#64) ↦₆₄ u1) ∗
                addrNameHeap A meG) ∗
              (((fsp + 0x1d0#64) ↦₆₄ u0) ∗ ((fsp + 0x1d8#64) ↦₆₄ u1)) ∗
              nowCellAt fsp unixEpoch ∗
              (storesAt A g.stores StoresGhost.opened ∗
                coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
                CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ logOff img ∗ A.pool ∗
                (g.inp ↦ₛ g.i.stdin) ∗ memRegion (fsp + 0x4d0#64) 248 ∗
                stackAt fsp (resStack - runFrame) ∗
                memRegion g.res runResSize ∗ runSaved s0 ∗
                memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
                memRegion (fsp + 0x1750#64) 248 ∗ r2_localGaps fsp ∗ anyHeap))) ?_) ?_
        · dsimp only [nowCellAt, unixEpoch, fsp, runFsp]
          (try simp only [arm64_norm])
          ac_rfl
        · refine Entails.trans
            (sepConj_mono hcw_m
              (sepConj_mono hpeer_p
                (sepConj_mono hme_p
                  (sepConj_mono_left hu16)))) ?_
          exact Entails.pure_right hcoinsLt
            (Entails.of_eq (by dsimp only [nowCellAt, unixEpoch, fsp, runFsp]; (try simp only [arm64_norm]); ac_rfl))
    ·
      (try dsimp only [r2_encInnerSpec, encG])
      apply r2_peel; intro g'
      apply r2_peel; intro e
      apply r2_peel_pure; rintro ⟨hst, hout, hpkBound⟩
      simp only [emp_sepConj, sepConj_assoc]
      obtain ⟨htr_ret, hhist_ret⟩ :=
        r2_histOk_of_slotTrace hd.fs hd.stdout hd.trace hst
      have hin_ret : InRun img ext s0 s_ret 1308 :=
        r2_inRun_mk hd.base hpcm_ret hrun_ret (hsp_ret.trans (by r2_eq))
          ((r2_csm_fp hcs_ret).trans (by r2_eq)) hinv_ret
          ((r2_csm_vregs hcs_ret).trans (by r2_eq))
      have hx19_r : s_ret.readReg64 (.gpr 19#5) = g.stores := by
        rw [r2_csm_x19 hcs_ret]; (try simp only [arm64_norm]); exact hd.x19
      have hx20_r : s_ret.readReg64 (.gpr 20#5) = g.res := by
        rw [r2_csm_x20 hcs_ret]; (try simp only [arm64_norm]); exact hd.x20
      have hx21_r : s_ret.readReg64 (.gpr 21#5) = meG.name.cap := by
        rw [r2_csm_x21 hcs_ret]; (try simp only [arm64_norm]); exact hx21
      have hx22_r : s_ret.readReg64 (.gpr 22#5) = fsp + 0x4d0#64 := by
        rw [r2_csm_x22 hcs_ret]; (try simp only [arm64_norm]); dsimp only [fsp]; bv_omega
      have hx26_r : s_ret.readReg64 (.gpr 26#5) = fsp + 0x4d0#64 := by
        rw [r2_csm_x26 hcs_ret]; (try simp only [arm64_norm]); exact hd.x26
      have hx27_r : s_ret.readReg64 (.gpr 27#5) = fsp + 0x1750#64 := by
        rw [r2_csm_x27 hcs_ret]; (try simp only [arm64_norm]); exact hd.x27
      have hx28_r : s_ret.readReg64 (.gpr 28#5) = meG.name.ptr := by
        rw [r2_csm_x28 hcs_ret]; (try simp only [arm64_norm]); exact hx28
      refine sepWPp_weaken_pre (P' :=
          encResAt A (fsp + 0x4d0#64) e ∗
            addrNameHeap A meG ∗
            memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            addrNameHeap A peerG ∗ runSaved s0 ∗
            ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x330#64) 16 ∗
            memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
            memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
            memRegion (fsp + 0x1750#64) 248 ∗
            memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
            stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap) ?_ ?_
      · (try simp only [arm64_norm])
        rw [hsp0, hcall]
        have hinp : inputOf g.i (.send peerV) = g.i.stdin := rfl
        rw [hinp]
        have hpeer_split :
            protocolAddressAt A peerG (fsp + 0x320#64) ⊢
              ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
              memRegion (fsp + 0x330#64) 16 ∗ addrNameHeap A peerG := by
          rw [protocolAddressAt_eq_parts A peerG (fsp + 0x320#64)]
          (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
          exact sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left
              (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
                addrUpperAt_entails_memRegion (fsp + 0x330#64) peerG)))
        refine Entails.trans (Entails.of_eq (Q :=
            protocolAddressAt A peerG (fsp + 0x320#64) ∗
              protocolAddressAt A meG (fsp + 0x23b0#64) ∗
              nowCellAt fsp unixEpoch ∗
              (logOff img ∗ anyHeap ∗ anyHeap) ∗
              (encResAt A (fsp + 0x4d0#64) e ∗
                memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                storesAt A g.stores g' ∗ (g.inp ↦ₛ g.i.stdin) ∗ runSaved s0 ∗
                memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x208#64) 24 ∗
                memRegion (fsp + 0x2a0#64) 8 ∗ memRegion (fsp + 0x1750#64) 248 ∗
                r2_localGaps fsp ∗ stackAt fsp (resStack - runFrame) ∗ A.pool)) ?_) ?_
        · dsimp only [fsp, runFsp]
          (try simp only [arm64_norm])
          ac_rfl
        · refine Entails.trans
            (sepConj_mono hpeer_split
              (sepConj_mono (r2_protocolAddress_to_mem32_heap A meG (fsp + 0x23b0#64))
                (sepConj_mono (r2_now_to_mem16 fsp)
                  (sepConj_mono_left (entails_anyHeap _))))) ?_
          exact Entails.of_eq (by dsimp only [fsp, runFsp]; (try simp only [arm64_norm]); ac_rfl)
      rw [hpeer_val, hme_val] at hout
      cases e with
      | error err =>
        have hneStore : err ≠ .store () := RunProofs.slotOut_err_ne_store hout
        have hans_err : g.a = some none := by
          rw [hansLink, hout.2.2]; rfl
        exact r2_err_arm (peerG := peerG) (meG := meG) hh hdrop hdropNeed hextNeed hsub64 hin_ret
          hx19_r hx20_r hx21_r hx22_r hx28_r htr_ret hhist_ret hneStore hans_err hrej
      | ok msg =>
        rcases hout.2.2 with ⟨hans_ok, hwr⟩
        cases msg with
        | signalMessage m =>
          have hans_sig : g.a = some (some (namedWrites g'.writes, [2#8] ++ m.serialized)) := by
            rw [hansLink, hans_ok]; rfl
          exact r2_sig_arm (peerG := peerG) (meG := meG) hh hcatNeed hextNeed hsub64 hin_ret
            hx19_r hx20_r hx21_r hx22_r hx26_r hx27_r hx28_r
            htr_ret hhist_ret hans_sig hwr hpanic hjoin
        | preKeySignalMessage m =>
          have hans_pk : g.a = some (some (namedWrites g'.writes, [3#8] ++ m.serialized)) := by
            rw [hansLink, hans_ok]; rfl
          exact r2_pk_arm (peerG := peerG) (meG := meG) hh hcatNeed hdpkNeed hextNeed hsub64 hin_ret
            hx19_r hx20_r hx21_r hx22_r hx26_r hx27_r hx28_r
            htr_ret hhist_ret hans_pk hwr (hpkBound m rfl) hpanic hjoin

/-- Corollary of `run_hop_send_ok_ext` widening `PanicK` with `SendConcatOverflow g`. -/
theorem run_hop_send_or_overflow_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {g : RunCall} {peerV : AddrV}
    {me : MeAtDispatch} {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    (hc : RunCallees img A ext B (slotsOf A img S needs))
    (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hres : runNeed B (slotsOf A img S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63)
    (hspb : resStack ≤ s0.sp.toNat)
    (he : AtRunEntry S img ext g s0)
    (hd : AtDispatch img ext g me s0 s)
    (hcall : g.c = .send peerV)
    (hpanic : ∀ sf Pf, (runPanicProp g s0 sf ∨ SendConcatOverflow g) → Qp sf Pf)
    (hrej : RejectK img ext A g s0 resStack Q Qp)
    (hjoin : JoinK img ext A g s0 resStack Q Qp) :
    ProofLib.SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (dispatchMem A img g me s0 resStack) Q Qp (runOom s0) :=
  run_hop_send_ok_ext himg hh hc hdrop hres hres64 hspb he hd hcall
    (fun sf Pf hp => hpanic sf Pf (Or.inl hp)) hrej hjoin

theorem run_hop_send_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {g : RunCall} {peerV : AddrV}
    {me : MeAtDispatch} {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A ext)
    (hc : RunCallees img A ext B (slotsOf A img S needs))
    (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hres : runNeed B (slotsOf A img S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63)
    (hspb : resStack ≤ s0.sp.toNat)
    (he : AtRunEntry S img ext g s0)
    (hd : AtDispatch img ext g me s0 s)
    (hcall : g.c = .send peerV)
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectK img ext A g s0 resStack Q Qp)
    (hjoin : JoinK img ext A g s0 resStack Q Qp) :
    ProofLib.SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (dispatchMem A img g me s0 resStack) Q Qp (runOom s0) :=
  run_hop_send_ok_ext himg hh.toExt hc hdrop hres hres64 hspb he hd hcall hpanic hrej hjoin

theorem run_hop_send_or_overflow_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {g : RunCall} {peerV : AddrV}
    {me : MeAtDispatch} {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A ext)
    (hc : RunCallees img A ext B (slotsOf A img S needs))
    (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hres : runNeed B (slotsOf A img S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63)
    (hspb : resStack ≤ s0.sp.toNat)
    (he : AtRunEntry S img ext g s0)
    (hd : AtDispatch img ext g me s0 s)
    (hcall : g.c = .send peerV)
    (hpanic : ∀ sf Pf, (runPanicProp g s0 sf ∨ SendConcatOverflow g) → Qp sf Pf)
    (hrej : RejectK img ext A g s0 resStack Q Qp)
    (hjoin : JoinK img ext A g s0 resStack Q Qp) :
    ProofLib.SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (dispatchMem A img g me s0 resStack) Q Qp (runOom s0) :=
  run_hop_send_or_overflow_ok_ext himg hh.toExt hc hdrop hres hres64 hspb he hd hcall hpanic hrej
    hjoin

end CryptoVerification.SignalSession.Cli.RunCompose



