/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.FetchDecrypt
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Record.FetchDecrypt
import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatch
import ProofLib.SepLogic.WPp

/-!
# CLI `SegMismatch` (Version-Mismatch Error Push)

Proves `SegMismatchSpec` (`+0x7e4 → +0x850`) in the CLI image: pushes
`UnrecognizedMessageVersion(x9)` onto `errs` and reaches `FState` (or panics on `grow_one` OOM).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Record

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession

open CryptoVerification.RustHeap

open CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees

open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone


set_option maxRecDepth 200000

set_option maxHeartbeats 400000

namespace SegDecryptFacts

open Lean Elab Tactic in
elab "segDecrypt_wpp_call_frozen_cli " hcall:term:max a:term:max hF:term:max hpan:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  evalTactic (← `(tactic| (
    apply (segDecrypt_call_frozen $hcall (x := $a) $hF)
    { try wp_norm_goal; try wp_norm_lhs; try assumption; try rfl }
    { try wp_norm_lhs; try assumption; try rfl }
    { try wp_norm_lhs; try wp_norm_goal; try assumption; try rfl }
    { simp only [Reg.lr, wp_norm, arm64_norm]; rfl }
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_frozen: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| (
    intro _R' _hmR'
    have _hF_loaded := ($hF).1
    have _hF_sym := ($hF).2
  )))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only [logClosureSpec, growOneSpeSpec, setSessionStateSpec,
      dropSessionStructureLocal2Spec, CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptSpecQF', CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, mkTryDecryptGhost,
      sessionMemcpyRegionSpec, memcpyRegionSpec, memcpySpec, Spec.inImage]
    try simp (config := { decide := true }) only [
      stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR' ⊢
    repeat' (rcases _hmR' with ⟨_, _hmR'⟩)
  )))
  for decl in (← getLCtx) do
    if !decl.isImplementationDetail && decl.userName.toString.startsWith "hsp" then
      let id := mkIdent decl.userName
      evalTactic (← `(tactic| try rw [$id:ident] at _hmR' ⊢))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals [gPanic]
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only [logClosureSpec, growOneSpeSpec, setSessionStateSpec,
      dropSessionStructureLocal2Spec, CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptSpecQF', CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, mkTryDecryptGhost,
      sessionMemcpyRegionSpec, memcpyRegionSpec, memcpySpec, CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec, Spec.inImage]
    intro _
    exact $hpan
  )))
  setGoals [gErr]
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only [logClosureSpec, growOneSpeSpec, setSessionStateSpec,
      dropSessionStructureLocal2Spec, CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptSpecQF', CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, mkTryDecryptGhost,
      sessionMemcpyRegionSpec, memcpyRegionSpec, memcpySpec, Spec.inImage]
    exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  )))
  setGoals (gCont :: rest)
  evalTactic (← `(tactic|
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hFId:ident
  ))
  foldStructEtaTarget
  evalTactic (← `(tactic| try dsimp only [logClosureSpec, growOneSpeSpec, setSessionStateSpec,
    dropSessionStructureLocal2Spec, CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptSpecQF', CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, mkTryDecryptGhost,
    sessionMemcpyRegionSpec, memcpyRegionSpec, memcpySpec, Spec.inImage]))
  let mut oldHspIds : Array Ident := #[]
  for decl in (← getLCtx) do
    if !decl.isImplementationDetail && decl.userName.toString.startsWith "hsp" then
      oldHspIds := oldHspIds.push (mkIdent decl.userName)
  wpNormAndSplitHyp hspId
  for oldId in oldHspIds do
    evalTactic (← `(tactic| try rw [$oldId:ident] at $hspId:ident))
  wpNormAndSplitHyp hcsId
  evalTactic (← `(tactic| try rw [$hspId:ident]))
  for oldId in oldHspIds do
    evalTactic (← `(tactic| try rw [$oldId:ident]))
  let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| (
    conv =>
      arg 4
      simp (config := { decide := true }) only [
        Spec.inImage,
        stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        wp_norm, arm64_norm, $hspId:ident]))))

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.seg_of_sepWPp_F {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    {img : Obj.Image} {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {target : BitVec 64} {P : SepProp}
    (_htarget : target = CryptoVerification.Cli.LibsignalTripleRatchet.Record.recFPC img)
    (hm : s.mem ⊨ P ∗ R)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem)
    (hwp : SepWPp (tripleRatchetProgAtExt img.base ext) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl uuidTryParse S img x R s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R))) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl uuidTryParse S img x R s0 s' ∨
        regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s') := by
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨_, _, P_f, hmf, hF⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩
  · exact ⟨sf, hsteps, Or.inl (hF hmf)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr ⟨hpan, hqp hmf⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

end SegDecryptFacts

open SegDecryptFacts

attribute [local irreducible] Program.fetch Program.externAt?

/-- Pushes `UnrecognizedMessageVersion(x9)` onto `errs` (`sp + 0x5d8`) and reaches `FState` at
`recFPC img` (`+0x850`), or panics on `grow_one` OOM. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.segMismatch_ok_ext_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegMismatchSpecExt_trap img C A ctl uuidTryParse S ext := by
  intro hloads _hhooks hgrow hclosure x G₁ R s0 s hM hL
  rcases hM with ⟨hpc, ⟨hrun, hsp, hsp_align, hx29, htr, hfrozen, hsym, hvregs⟩, hne, hx9, hmem⟩
  have hentry := entryOf_eq_tripleRatchetProgAtExt ext hloads CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Record.recMPC at hpc
  rw [hentry] at hpc
  have hfn := CryptoVerification.Cli.LibsignalTripleRatchet.Record.libsignalSessionCode_fnOff_sym_3a4a8
  have hclosure_rel :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
          bv% (2 ^ 64 + (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_ratchet::Coins>::{closure#0}") - (ls_off% "libsignal_cli_ratchet::decrypt_signal")))
        ((logClosureSpec img).inImage img) := by
    have h1 : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.logClosureName = num% (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_ratchet::Coins>::{closure#0}") :=
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_ratchet::Coins>::{closure#0}")
    have h2 : (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% (2 ^ 64 + (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_ratchet::Coins>::{closure#0}") - (ls_off% "libsignal_cli_ratchet::decrypt_signal")) =
        (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.logClosureName := by
      simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, hfn, h1]
      bv_omega
    rw [h2]
    exact hclosure
  have hgrow_rel :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
          bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one") - (ls_off% "libsignal_cli_ratchet::decrypt_signal")))
        (growOneSpeSpec A) := by
    have h1 : libsignalSessionCode.fnOff growOneSpeName = num% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one") :=
      (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one")
    have h2 : (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one") - (ls_off% "libsignal_cli_ratchet::decrypt_signal")) =
        (tripleRatchetProgAtExt img.base ext).fnAddr growOneSpeName := by
      simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, hfn, h1]
      bv_omega
    rw [h2]
    exact hgrow
  have hFPC : (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 2128#64 =
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.recFPC img := by
    unfold CryptoVerification.Cli.LibsignalTripleRatchet.Record.recFPC
    rw [hentry]
  segDecrypt_rec_fetches_cli img.base (Rust.withPanics ext) hfn 2020 108
  change s.pc = (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 2020#64 at hpc
  clear hentry hfn hgrow hclosure hloads
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry
  examples_hide_fetches
  -- Replace s0.sp with s.sp in hmem so s.sp is uniform across all callee frames
  have hsp0 : s0.sp = s.sp := hsp.symm
  clear hsp
  unfold recFrame at hmem
  rw [hsp0, stackAt_root_split_closure s.sp, memRegion_5f0_split48 s.sp,
    memRegion48_eq_words6At (s.sp + 0x5f0#64), errsAt_nil_unfold A s.sp] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨w0, w1, w2, w3, w4, w5, hmem⟩
  unfold words6At at hmem
  simp only [← sepConj_assoc] at hmem
  have hF0 : FrozenInv img s := ⟨hfrozen, hsym⟩
  apply CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.seg_of_sepWPp_F hFPC hmem hL
  apply segDecrypt_of_sepWP_frozen hF0 (mid := entry + bv% (2 ^ 64 + (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_ratchet::Coins>::{closure#0}") - (ls_off% "libsignal_cli_ratchet::decrypt_signal")))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF1
  segDecrypt_wpp_call_frozen_cli hclosure_rel () hF1 noPanic_onPanic_entails
  apply segDecrypt_of_sepWP_frozen hF_sf (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one") - (ls_off% "libsignal_cli_ratchet::decrypt_signal")))
  segDecrypt_wp_extract_exists
  rename_i htr_sf
  refine segDecrypt_replace_pre (closureStack_to_growStack s.sp) (by sep_focus) ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF2
  segDecrypt_wpp_call_frozen_cli hgrow_rel (s.sp + 0x5d8#64, 0#64, 8#64, []) hF2
    (grow_onPanic_entails (by simp only [wp_norm, arm64_norm, htr_sf, htr]))
  apply segDecrypt_of_sepWP_ret_frozen hF_sf_1
  segDecrypt_wp_extract_exists
  rename_i p' hp'
  rw [memRegion_192_split48 p', memRegion48_eq_words6At p']
  unfold words6At
  segDecrypt_wp_extract_exists
  wp_steps
  rw [hsp_sf]
  refine segDecrypt_replace_pre
    (mismatch_errsAt_entails A s.sp p' w1 w2 w3 w4 w5 x.msg.messageVersion hp'.2) (by sep_focus) ?_
  refine segDecrypt_replace_pre
    (words6_5f0_to_memRegion s.sp 9223372036854775814#64
      (w1 &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 x.msg.messageVersion)
      w2 w3 w4 w5) (by sep_focus) ?_
  refine segDecrypt_replace_pre (growStack_to_rootStack s.sp) (by sep_focus) ?_
  refine segDecrypt_replace_pre (sessionStateAt_exists_intro A (s.sp + 3232#64) G₁ x.st) (by sep_focus) ?_
  refine segDecrypt_replace_pre
    (draws_of_version_ne C x hne ▸ CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.tapeAfter_zero img.base x.cur x.rest) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF3 hmf
  refine ⟨by rw [← hFPC]; wp_norm_lhs, ?_, model_of_version_ne C S x hne, ?_⟩
  · refine ⟨by wp_norm_lhs,
            by simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf, hsp0],
            by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf]; exact hsp_align,
            by simp only [wp_norm, arm64_norm, hcs_sf_1, hcs_sf]; exact hx29,
            by simp only [wp_norm, arm64_norm, hp'.1, htr_sf, htr],
            hF3.1, hF3.2,
            by simp only [wp_norm, arm64_norm, hvregs_2, hvregs_1, hvregs]⟩
  · unfold recFrame
    rw [hsp0]
    exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hmf

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.segMismatch_ok_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegMismatchSpecExt img C A ctl uuidTryParse S ext :=
  fun hloads hhooks => CryptoVerification.Cli.LibsignalTripleRatchet.Record.segMismatch_ok_ext_trap hloads hhooks.to_trap

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.segMismatch_ok_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegMismatchSpec_trap img C A ctl uuidTryParse S abs :=
  fun hloads hhooks hgrow hclosure =>
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.segMismatch_ok_ext_trap hloads (Stage2Contracts_trap.of_tripleRatchetProgAt'_trap hhooks) hgrow hclosure

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.segMismatch_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegMismatchSpec img C A ctl uuidTryParse S abs :=
  fun hloads hhooks hgrow hclosure =>
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.segMismatch_ok_ext hloads (Stage2Contracts.of_tripleRatchetProgAt' hhooks) hgrow hclosure

end CryptoVerification.LibsignalTripleRatchet.Record
