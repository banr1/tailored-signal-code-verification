/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSpe2Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Consts
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep

/-!
# Previous-Session Version-Skip Tail Proof (`+0x1fd4 → +0x2cfc`)

Proves `overPrevErr_cli_4k_ok` and `overPrevErr_cli_ok` on `tripleRatchetProgAtExt`: compares
`w8 = 4` against `msgVer ≠ 4`, invokes `pqxdh_log_closure`, appends the second
`UnrecognizedMessageVersion` entry at `errsPtr + 48..96` (`errs.len = 2`), drops the decoded
`SessionStructure` at `sp + 0x930`, and exits the 1-element loop to `+0x2cfc`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")

private gen_decodes libsignalSessionCode_tree verNeLoopErrCliDec [
  (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x1fd4) →
  (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x1fdc),
  (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x2088) →
  (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x20c4),
  (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x20d0) →
  (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x2110)]

local macro "loopErr_fetches_range " b:term:max H:term:max lo:num hi:num : tactic => do
  let s := lo.getNat
  let l := Lean.Syntax.mkNumLit (toString (hi.getNat - s + 4))
  `(tactic| code_fetches_range libsignalSessionCode verNeLoopErrCliDec $b $H
    (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
    (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") $lo $l)

/-! ## Arithmetic and spatial helpers -/

private theorem cond_ne_subs32_4_of_ne {v : BitVec 32} (h : v ≠ 4#32) :
    ConditionHolds CondCode.NE (subsPState32 4#32 v) = true := by
  unfold subsPState32
  rw [conditionHolds_ne_subs32, bne_iff_ne]
  exact Ne.symm h

private theorem spA90_344_ver_split_eq (sp : BitVec 64) :
    memRegion (sp + 0xa90#64) 344 = (∃∗ e5 : BitVec 64, ∃∗ e4 : BitVec 64, ∃∗ e3 : BitVec 64,
      ∃∗ e2 : BitVec 64, ∃∗ ua9c : BitVec 32, ∃∗ ua98 : BitVec 32, ∃∗ ua90 : BitVec 64,
      ((sp + 0xa90#64) ↦₆₄ ua90) ∗ ((sp + 0xa98#64) ↦₃₂ ua98) ∗ ((sp + 0xa9c#64) ↦₃₂ ua9c) ∗
      ((sp + 0xaa0#64) ↦₆₄ e2) ∗ ((sp + 0xaa8#64) ↦₆₄ e3) ∗
      ((sp + 0xab0#64) ↦₆₄ e4) ∗ ((sp + 0xab8#64) ↦₆₄ e5) ∗
      memRegion (sp + 0xac0#64) 296) := by
  rw [ProofLib.memRegion_split' (b := sp + 0xa90#64) (n := 8) (k := 336) (b' := sp + 0xa98#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xa98#64) (n := 4) (k := 332) (b' := sp + 0xa9c#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xa9c#64) (n := 4) (k := 328) (b' := sp + 0xaa0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xaa0#64) (n := 8) (k := 320) (b' := sp + 0xaa8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xaa8#64) (n := 8) (k := 312) (b' := sp + 0xab0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xab0#64) (n := 8) (k := 304) (b' := sp + 0xab8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xab8#64) (n := 8) (k := 296) (b' := sp + 0xac0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 0xa90#64), ProofLib.memRegion_four (sp + 0xa98#64),
      ProofLib.memRegion_four (sp + 0xa9c#64), ProofLib.memRegion_eight (sp + 0xaa0#64),
      ProofLib.memRegion_eight (sp + 0xaa8#64), ProofLib.memRegion_eight (sp + 0xab0#64),
      ProofLib.memRegion_eight (sp + 0xab8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

private theorem pointsTo32_pair_spA98 (sp : BitVec 64) (lo hi : BitVec 32) :
    (((sp + 0xa98#64) ↦₃₂ lo) ∗ ((sp + 0xa9c#64) ↦₃₂ hi)) = ((sp + 0xa98#64) ↦₆₄ (hi ++ lo)) := by
  have h : sp + 0xa9c#64 = (sp + 0xa98#64) + 4#64 := by bv_omega
  rw [h, pointsTo32_pair]

private theorem spA90_344_fold (sp w0 w1 e2 e3 e4 e5 : BitVec 64) :
    ((sp + 0xa90#64) ↦₆₄ w0) ∗ ((sp + 0xa98#64) ↦₆₄ w1) ∗ ((sp + 0xaa0#64) ↦₆₄ e2) ∗
    ((sp + 0xaa8#64) ↦₆₄ e3) ∗ ((sp + 0xab0#64) ↦₆₄ e4) ∗ ((sp + 0xab8#64) ↦₆₄ e5) ∗
    memRegion (sp + 0xac0#64) 296 ⊢
    memRegion (sp + 0xa90#64) 344 := by
  rw [ProofLib.memRegion_split' (b := sp + 0xa90#64) (n := 8) (k := 336) (b' := sp + 0xa98#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xa98#64) (n := 8) (k := 328) (b' := sp + 0xaa0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xaa0#64) (n := 8) (k := 320) (b' := sp + 0xaa8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xaa8#64) (n := 8) (k := 312) (b' := sp + 0xab0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xab0#64) (n := 8) (k := 304) (b' := sp + 0xab8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0xab8#64) (n := 8) (k := 296) (b' := sp + 0xac0#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _))))))

private theorem errs144_split_eq_at48 (errsPtr : BitVec 64) :
    memRegion (errsPtr + 48#64) 144 = (∃∗ u_e5 : BitVec 64, ∃∗ u_e4 : BitVec 64, ∃∗ u_e3 : BitVec 64,
      ∃∗ u_e2 : BitVec 64, ∃∗ u_e1 : BitVec 64, ∃∗ u_e0 : BitVec 64,
      ((errsPtr + 48#64) ↦₆₄ u_e0) ∗ ((errsPtr + 56#64) ↦₆₄ u_e1) ∗
      ((errsPtr + 64#64) ↦₆₄ u_e2) ∗ ((errsPtr + 72#64) ↦₆₄ u_e3) ∗
      ((errsPtr + 80#64) ↦₆₄ u_e4) ∗ ((errsPtr + 88#64) ↦₆₄ u_e5) ∗
      memRegion (errsPtr + 96#64) 96) := by
  rw [ProofLib.memRegion_split' (b := errsPtr + 48#64) (n := 8) (k := 136) (b' := errsPtr + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 56#64) (n := 8) (k := 128) (b' := errsPtr + 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 64#64) (n := 8) (k := 120) (b' := errsPtr + 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 72#64) (n := 8) (k := 112) (b' := errsPtr + 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 80#64) (n := 8) (k := 104) (b' := errsPtr + 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 88#64) (n := 8) (k := 96) (b' := errsPtr + 96#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (errsPtr + 48#64), ProofLib.memRegion_eight (errsPtr + 56#64),
      ProofLib.memRegion_eight (errsPtr + 64#64), ProofLib.memRegion_eight (errsPtr + 72#64),
      ProofLib.memRegion_eight (errsPtr + 80#64), ProofLib.memRegion_eight (errsPtr + 88#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

private theorem errs48_fold_ver_at48 (errsPtr e2 e3 e4 e5 : BitVec 64) (msgVer ua9c : BitVec 32) :
    ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 56#64) ↦₆₄ (ua9c ++ msgVer)) ∗
    ((errsPtr + 64#64) ↦₆₄ e2) ∗ ((errsPtr + 72#64) ↦₆₄ e3) ∗ ((errsPtr + 80#64) ↦₆₄ e4) ∗
    ((errsPtr + 88#64) ↦₆₄ e5) ⊢
    ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 56#64) ↦₃₂ msgVer) ∗
    memRegion (errsPtr + 60#64) 36 := by
  have hpair : ((errsPtr + 56#64) ↦₆₄ (ua9c ++ msgVer)) =
      ((errsPtr + 56#64) ↦₃₂ msgVer) ∗ ((errsPtr + 60#64) ↦₃₂ ua9c) := by
    have h60 : errsPtr + 60#64 = (errsPtr + 56#64) + 4#64 := by bv_omega
    rw [h60, ← pointsTo32_pair]
  rw [hpair, sepConj_assoc,
      ProofLib.memRegion_split' (b := errsPtr + 60#64) (n := 4) (k := 32) (b' := errsPtr + 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 64#64) (n := 8) (k := 24) (b' := errsPtr + 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 72#64) (n := 8) (k := 16) (b' := errsPtr + 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 80#64) (n := 8) (k := 8) (b' := errsPtr + 88#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))))))

private theorem call_frame_inImage_nopanic_loopErr {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro sf; first | rfl | simp only [Spec.inImage]) :
    SepWPp prog ret s P Q Qp := by
  refine P3P4.SepWPp.call_frame_frozen_nopanic hF hsym hcall hpc hrun hsp hlr
    (φ := (img.FrozenLoaded s ∧ s.symtab = img.symtab) ∧ φ)
    (T := T) (F := F) ?_ ⟨⟨hF, hsym⟩, hφ⟩ hP hpan_false hexit_false hnext hoom_false
  dsimp only [Spec.inImage]; rw [hspec, pure_sepConj_pure_assoc]

/-! ## Basic-block segments (`+0x1fd4 → +0x2cfc`) -/

/-- Segment `+0x1fd4 → pqxdh_log_closure` on `tripleRatchetProgAtExt b ext`. -/
theorem over_prev_err_seg1_cli_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (prevPtr ua90 : BitVec 64) (msgVer ua98 : BitVec 32)
    (hver_ne : msgVer ≠ 4#32)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1fd4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = 4#64)
    (hx27 : s.readReg64 .x27 = prevPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      (b + bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}")) s
      (((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
       ((s.sp + 0xa90#64) ↦₆₄ ua90) ∗
       ((s.sp + 0xa98#64) ↦₃₂ ua98))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
          ((s.sp + 0xa90#64) ↦₆₄ 0x8000000000000006#64) ∗
          ((s.sp + 0xa98#64) ↦₃₂ msgVer)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x27 = prevPtr ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x20b4#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond_ver := cond_ne_subs32_4_of_ne hver_ne
  loopErr_fetches_range b (Rust.withPanics ext) 0x1fd4 0x1fdc
  loopErr_fetches_range b (Rust.withPanics ext) 0x2088 0x20b0
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName =
      b + bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have htarget : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName +
      0x20b0#64 + bv% ((2^64 + ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 8368)) % 2^64) =
      b + bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}") := by
    rw [hentry]; bv_omega
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx8_32 : s.readReg32 (Reg.gpr 8#5) = 4#32 := by simp [State.readReg32, hx8]
  have hx27' : s.readReg64 (Reg.gpr 27#5) = prevPtr := hx27
  wp_steps
  refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Segment `+0x20b4 → drop_session_structure3` on `tripleRatchetProgAtExt b ext`. -/
theorem over_prev_err_seg2_cli_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (prevPtr errsPtr errTag e1 e2 e3 e4 e5 u_e0 u_e1 u_e2 u_e3 u_e4 u_e5 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x20b4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx27 : s.readReg64 .x27 = prevPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      (b + bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) s
      (((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
       ((s.sp + 0xa90#64) ↦₆₄ errTag) ∗
       ((s.sp + 0xa98#64) ↦₆₄ e1) ∗
       ((s.sp + 0xaa0#64) ↦₆₄ e2) ∗
       ((s.sp + 0xaa8#64) ↦₆₄ e3) ∗
       ((s.sp + 0xab0#64) ↦₆₄ e4) ∗
       ((s.sp + 0xab8#64) ↦₆₄ e5) ∗
       ((errsPtr + 48#64) ↦₆₄ u_e0) ∗
       ((errsPtr + 56#64) ↦₆₄ u_e1) ∗
       ((errsPtr + 64#64) ↦₆₄ u_e2) ∗
       ((errsPtr + 72#64) ↦₆₄ u_e3) ∗
       ((errsPtr + 80#64) ↦₆₄ u_e4) ∗
       ((errsPtr + 88#64) ↦₆₄ u_e5))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
          ((s.sp + 0xa90#64) ↦₆₄ errTag) ∗
          ((s.sp + 0xa98#64) ↦₆₄ e1) ∗
          ((s.sp + 0xaa0#64) ↦₆₄ e2) ∗
          ((s.sp + 0xaa8#64) ↦₆₄ e3) ∗
          ((s.sp + 0xab0#64) ↦₆₄ e4) ∗
          ((s.sp + 0xab8#64) ↦₆₄ e5) ∗
          ((errsPtr + 48#64) ↦₆₄ errTag) ∗
          ((errsPtr + 56#64) ↦₆₄ e1) ∗
          ((errsPtr + 64#64) ↦₆₄ e2) ∗
          ((errsPtr + 72#64) ↦₆₄ e3) ∗
          ((errsPtr + 80#64) ↦₆₄ e4) ∗
          ((errsPtr + 88#64) ↦₆₄ e5)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x930#64 ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x27 = prevPtr ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x20fc#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  loopErr_fetches_range b (Rust.withPanics ext) 0x20b4 0x20c4
  loopErr_fetches_range b (Rust.withPanics ext) 0x20d0 0x20f8
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName =
      b + bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have htarget : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName +
      0x20f8#64 + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 8440)) % 2^64) =
      b + bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") := by
    rw [hentry]; bv_omega
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx27' : s.readReg64 (Reg.gpr 27#5) = prevPtr := hx27
  have herr1 : 1#64 * 0x30#64 + errsPtr = errsPtr + 48#64 := by bv_arith
  wp_steps
  refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- Segment `+0x20fc → +0x2cfc` on `tripleRatchetProgAtExt b ext`. -/
theorem over_prev_err_seg3_cli_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (prevPtr : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x20fc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx27 : s.readReg64 .x27 = prevPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x2cfc#64) s
      (((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)))
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64))) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  loopErr_fetches_range b (Rust.withPanics ext) 0x20fc 0x2110
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx27' : s.readReg64 (Reg.gpr 27#5) = prevPtr := hx27
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-! ## Composition -/

set_option maxHeartbeats 1000000 in
/-- Proves `OverPrevErrCliStmt4K` (`+0x1fd4 → +0x2cfc`). -/
theorem overPrevErr_cli_4k_ok : OverPrevErrCliStmt4K := by
  intro A img ext himg hA s0 s prevPtr errsPtr msgVer G st
    hver_ne hF hsym hpc hrun hsp_align htr hx8 hx27
  have hlog := pqxdh_log_closure_ok_ext (ext := ext) himg
  have hdrop := drop_session_structure3_ok_of_mem4k (b := img.base) (ext := ext) hA
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (spA90_344_ver_split_eq s.sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun e5 => SepWPp.exists_elim fun e4 =>
    SepWPp.exists_elim fun e3 => SepWPp.exists_elim fun e2 =>
    SepWPp.exists_elim fun ua9c => SepWPp.exists_elim fun ua98 => SepWPp.exists_elim fun ua90 => ?_
  refine P3P4.SepWPp.bind_sepWP_frame hF hsym
    (over_prev_err_seg1_cli_wp img.base ext s prevPtr ua90 msgVer ua98
      hver_ne hpc hrun hsp_align hx8 hx27)
    (by sep_focus)
    fun s1 hpc1 hrun1 hF1 hsym1 ⟨hsp1, htr1, hx19_1, hx20_1, hx27_1, hx29_1, hlr1, hvregs1⟩ => ?_
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  have hpc1_log : s1.pc =
      (tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName := by
    rw [hpc1, fnAddr_pqxdhLogClosure_eq]
  have hstack_log :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack :=
    stackAt_split_bottom s.sp pqxdhClosureStack 4176 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_log) (by sep_focus) ?_
  refine call_frame_inImage_nopanic_loopErr
    (spec := pqxdhLogClosureSpec img) (x := ()) (φ := True)
    (T := logOff img ∗ stackAt s.sp pqxdhClosureStack)
    hF1 hsym1 hlog hpc1_log hrun1 hsp1_al hlr1
    (by dsimp only [pqxdhLogClosureSpec]; rw [hsp1, pure_true, emp_sepConj])
    trivial (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hF2 hsym2 => ?_)
  dsimp only [pqxdhLogClosureSpec]
  rw [hsp1, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  have hstack_restore2 :
      memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_log]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore2 (by sep_focus) ?_
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, hx20_cs2, _, _, _, _, _, _, hx27_cs2, _, hx29_cs2, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = s.readReg64 .x19 := hx19_cs2.trans hx19_1
  have hx20_2 : s2.readReg64 .x20 = s.readReg64 .x20 := hx20_cs2.trans hx20_1
  have hx27_2 : s2.readReg64 .x27 = prevPtr := hx27_cs2.trans hx27_1
  have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 := hx29_cs2.trans hx29_1
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (pointsTo32_pair_spA98 s.sp msgVer ua9c)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (errs144_split_eq_at48 errsPtr)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_e5 => SepWPp.exists_elim fun u_e4 =>
    SepWPp.exists_elim fun u_e3 => SepWPp.exists_elim fun u_e2 =>
    SepWPp.exists_elim fun u_e1 => SepWPp.exists_elim fun u_e0 => ?_
  have hseg2 := over_prev_err_seg2_cli_wp img.base ext s2 prevPtr errsPtr
    0x8000000000000006#64 (ua9c ++ msgVer) e2 e3 e4 e5 u_e0 u_e1 u_e2 u_e3 u_e4 u_e5
    hpc2 hrun2 hsp2_align hx27_2
  rw [hsp2] at hseg2
  refine P3P4.SepWPp.bind_sepWP_frame hF2 hsym2 hseg2 (by sep_focus)
    fun s3 hpc3 hrun3 hF3 hsym3 ⟨hsp3_2, htr3_2, hx0_3, hx19_3, hx20_3, hx27_3, hx29_3, hlr3, hvregs3⟩ => ?_
  refine P3P4.SepWPp.weaken_frame (errs48_fold_ver_at48 errsPtr e2 e3 e4 e5 msgVer ua9c) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (spA90_344_fold s.sp 0x8000000000000006#64 (ua9c ++ msgVer) e2 e3 e4 e5)
    (by sep_focus) ?_
  have hsp3 : s3.sp = s.sp := hsp3_2
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3] using hsp_align
  have hpc3_drop : s3.pc =
      (tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name := by
    rw [hpc3, fnAddr_dropSs3_eq]
  have hstack_drop2 :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
    stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_
  refine P3P4.SepWPp.call_frame_frozen_nopanic
    (x := (⟨s.sp + 0x930#64, G, st⟩ : DropSessionStructureGhost))
    (T := sessionStateAt A (s.sp + 0x930#64) G st ∗ A.pool ∗ stackAt s.sp dropSessionStructure2Stack)
    hF3 hsym3 hdrop hpc3_drop hrun3 hsp3_al hlr3
    (by dsimp only [dropSessionStructure2Spec, dropSessionStructureLocal2Spec]; rw [hsp3])
    hx0_3 (by sep_focus)
    (hnext := fun s4 hpc4 hrun4 hsp4_3 _ hcs4 hF4 hsym4 => ?_)
  dsimp only [dropSessionStructure2Spec, dropSessionStructureLocal2Spec]
  rw [hsp3, sepConj_assoc]
  refine SepWPp.pure_elim fun htr4_3 => ?_
  have hstack_restore4 :
      memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_drop2]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore4 (by sep_focus) ?_
  have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4]; exact hsp_align
  rcases hcs4 with ⟨hx19_cs4, hx20_cs4, _, _, _, _, _, _, hx27_cs4, _, hx29_cs4, hvregs_cs4⟩
  have hx19_4 : s4.readReg64 .x19 = s.readReg64 .x19 := hx19_cs4.trans (hx19_3.trans hx19_2)
  have hx20_4 : s4.readReg64 .x20 = s.readReg64 .x20 := hx20_cs4.trans (hx20_3.trans hx20_2)
  have hx27_4 : s4.readReg64 .x27 = prevPtr := hx27_cs4.trans hx27_3
  have hx29_4 : s4.readReg64 .x29 = s.readReg64 .x29 := hx29_cs4.trans (hx29_3.trans hx29_2)
  have hseg3 := over_prev_err_seg3_cli_wp img.base ext s4 prevPtr hpc4 hrun4 hsp4_align hx27_4
  rw [hsp4] at hseg3
  refine P3P4.SepWPp.bind_sepWP_frame hF4 hsym4 hseg3 (by sep_focus)
    fun sf hpcf hrunf hFf hsymf ⟨hspf_4, htrf_4, hx19_f, hx20_f, hx29_f, hvregsf⟩ => ?_
  have htrf : sf.trace = s0.trace := by rw [htrf_4, htr4_3, htr3_2, htr2_1, htr1, htr]
  have hx19f : sf.readReg64 .x19 = s.readReg64 .x19 := hx19_f.trans hx19_4
  have hx20f : sf.readReg64 .x20 = s.readReg64 .x20 := hx20_f.trans hx20_4
  have hx29f : sf.readReg64 .x29 = s.readReg64 .x29 := hx29_f.trans hx29_4
  have hvregsf_s : calleeSavedVRegs sf = calleeSavedVRegs s := by
    rw [hvregsf, hvregs_cs4, hvregs3, hvregs_cs2, hvregs1]
  refine SepWPp.done hpcf hrunf
    ⟨Entails.of_eq (by ac_rfl), hspf_4, htrf, hx19f, hx20f, hx29f, hvregsf_s, hFf, hsymf⟩

theorem overPrevErr_cli_ok : OverPrevErrCliStmt :=
  fun img ext himg hA => overPrevErr_cli_4k_ok img ext himg (.of_AllocContracts hA)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
