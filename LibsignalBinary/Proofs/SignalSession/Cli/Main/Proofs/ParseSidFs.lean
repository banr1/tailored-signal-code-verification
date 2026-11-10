/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.UuidFs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ParseServiceId
import ProofLib.SepLogic.WPp

/-!
# In-Image `ServiceId::parse_from_service_id_string` Preserving `fs` (`Spec.keepsFs`)

Proves `ServiceId::parse_from_service_id_string` satisfies
`(parseSidCodeStackSpec hookStack).keepsFs.inImage img` for any `hookStack ≥ uuidTryParseStack`,
deriving `hookStack ≤ 2 ^ 64` from stack-frame disjointness, plus call-site offset forms.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.ParseServiceId
open CryptoVerification.SignalSession.Cli.MainHops.UuidFs

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
private theorem fs_writeReg_local (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).fs = s.fs := by
  cases s; cases w <;> cases r <;> rfl

private abbrev ParseSidImgInv (img : Obj.Image) (s : State) : Prop :=
  img.FrozenLoaded s ∧ s.symtab = img.symtab

private theorem ParseSidImgInv.of_steps {img : Obj.Image} {prog : Program} {s s' : State}
    (h : ParseSidImgInv img s) (hs : Steps prog s s') : ParseSidImgInv img s' :=
  ⟨h.1.of_keepsFrozen hs.keepsFrozen, hs.symtab_eq.trans h.2⟩

private theorem sepWP_seq_inImage_local {prog : Program} {img : Obj.Image}
    {mid target_pc : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hinv : ParseSidImgInv img s)
    (h : SepWP prog mid s P (fun sm Pm => ParseSidImgInv img sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post := by
  unfold SepWP
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨hoom, hfalse⟩⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', out⟩ :=
      (hnext (hinv.of_steps hsteps)).elim hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', out⟩
  · exact ⟨sm, hsteps, Or.inr ⟨hoom, hfalse⟩⟩

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem frozenLoaded_setMem_local (img : Obj.Image) (s : State) (m : Memory) :
    img.FrozenLoaded (s.setMem m) = img.FrozenLoaded (State.setMem default m) := by
  simp only [Obj.Image.frozenLoaded_iff]; rfl

private theorem ok_at_rebase_any {α : Type} (b : BitVec 64) (H : String → Option (State → State))
    (target : String) {spec : Spec α}
    (h : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr target) spec)
    (caller : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff caller + k = libsignalSessionCode.fnOff target) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr caller + BitVec.ofNat 64 k) spec := by
  have heq :
      (libsignalSessionCode.rebase b H).fnAddr caller + BitVec.ofNat 64 k =
        (libsignalSessionCode.rebase b H).fnAddr target := by
    simp only [Program.fnAddr_rebase, ← hk, BitVec.ofNat_add, BitVec.add_assoc]
  rwa [heq]

set_option maxHeartbeats 800000 in
/-- Contract-backed `ServiceId::parse_from_service_id_string` with caller-supplied
`((uuidTryParseStackSpec hookStack).keepsFs.inImage img)` on `libsignalSessionCode.rebase img.base H`. -/
theorem parseSid_okFs_of_contract_stack_inImage (img : Obj.Image)
    (H : String → Option (State → State)) (hookStack : Nat := 0)
    (huuid_entry : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr uuidTryParseName)
      ((uuidTryParseStackSpec hookStack).keepsFs.inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr parseSidName)
      ((parseSidCodeStackSpec hookStack).keepsFs.inImage img) := by
  unfold Spec.inImage Spec.keepsFs at huuid_entry ⊢
  simp only [parseSidCodeStackSpec, parseSidSpec, uuidTryParseStackSpec, uuidTryParseSpec]
    at huuid_entry ⊢
  have hfn : libsignalSessionCode.fnOff parseSidName =
      num% (ls_off% "<libsignal_core::address::ServiceId>::parse_from_service_id_string") :=
    (ls_lemma% fnOff "<libsignal_core::address::ServiceId>::parse_from_service_id_string")
  have huuid := ok_at_rebase_any img.base H uuidTryParseName huuid_entry parseSidName
    (num% (ls_off% "<uuid::Uuid>::try_parse" -
      ls_off% "<libsignal_core::address::ServiceId>::parse_from_service_id_string"))
    (by simp only [arm64_norm])
  code_fetches CryptoVerification.libsignalSessionCode libsignalSessionBin
    img.base H
    (ls_lemma% fnOff "<libsignal_core::address::ServiceId>::parse_from_service_id_string")
    (num% (ls_off% "<libsignal_core::address::ServiceId>::parse_from_service_id_string")) 212
  clear hfn huuid_entry
  dsimp only [parseSidName, BitVec.ofNat_eq_ofNat] at huuid ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr
    "<libsignal_core::address::ServiceId>::parse_from_service_id_string" = entry
  wp_init x s0
  examples_hide_fetches
  obtain ⟨p, bs, out⟩ := x
  dsimp only at *
  have hinv0 : ParseSidImgInv img s0 := ⟨by assumption, by assumption⟩
  rw [memRegion_17_none_split out, stackAt_parseSidFrame_split s0.sp]
  wp_pull_exists
  apply sepWP_seq_inImage_local (mid := entry + bv% (16)) hinv0
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  rintro ⟨hF1, hsym1⟩
  simp only [frozenLoaded_setMem_local, arm64_norm] at hF1 hsym1
  wp_steps
  wp_if hlt4
  · rw [serviceIdParse_of_lt_4 bs (toNat_lt_of_ult h_4 hlt4), parseSidResultAt]
    wp_steps
    wp_done
  · obtain ⟨b0, b1, b2, b3, bs', rfl⟩ := exists_cons4_of_le (le_of_not_ult h_4 hlt4)
    rw [pointsToBytes_cons4 p b0 b1 b2 b3 bs']
    wp_steps
    wp_if hpni
    · rw [serviceIdParse_cons4_pni b0 b1 b2 b3 bs' hpni]
      wp_steps
      wp_if hlen40
      · have hne36 := length_ne_36_of_ne_40 h_4 hlen40
        simp only [hne36, ↓reduceIte, parseSidResultAt]
        wp_steps
        wp_done
      · have heq36 := length_eq_36_of_eq_40 h_4 hlen40
        simp only [heq36, ↓reduceIte]
        wp_steps
        wp_call huuid (p + 4#64, bs', s0.sp - 64#64)
        cases hparse : uuidTryParse bs' with
        | none =>
          rw [uuidResultAt_sp64_none s0.sp, memRegion_sp64_none_split s0.sp]
          dsimp only [Option.map, parseSidResultAt]
          wp_steps
          wp_done
        | some u =>
          rw [uuidResultAt_sp64_some s0.sp u, memRegion_sp64_some_split s0.sp,
              memRegion_out1_16_split out]
          dsimp only [Option.map]
          rw [parseSidResultAt_some_eq out true u]
          wp_pull_exists
          wp_steps
          wp_done
    · rw [serviceIdParse_cons4_aci b0 b1 b2 b3 bs' hpni, ← pointsToBytes_cons4 p b0 b1 b2 b3 bs']
      wp_steps
      wp_if hlen36
      · have hne36 := length_ne_36_of_ne_36 h_4 hlen36
        simp only [hne36, ↓reduceIte, parseSidResultAt]
        wp_steps
        wp_done
      · have heq36 := length_eq_36_of_eq_36 h_4 hlen36
        simp only [heq36, ↓reduceIte]
        wp_steps
        wp_call huuid (p, b0 :: b1 :: b2 :: b3 :: bs', s0.sp - 64#64)
        cases hparse : uuidTryParse (b0 :: b1 :: b2 :: b3 :: bs') with
        | none =>
          rw [uuidResultAt_sp64_none s0.sp, memRegion_sp64_none_split s0.sp]
          dsimp only [Option.map, parseSidResultAt]
          wp_steps
          wp_done
        | some u =>
          rw [uuidResultAt_sp64_some s0.sp u, memRegion_sp64_some_split s0.sp,
              memRegion_out1_16_split out]
          dsimp only [Option.map]
          rw [parseSidResultAt_some_eq out false u]
          wp_pull_exists
          wp_steps
          wp_done

private theorem hookStack_le_of_frame_disjoint {m : Memory} {sp : BitVec 64} {hookStack : Nat}
    {R : SepProp}
    (hm : m ⊨ stackAt (sp - 80#64) hookStack ∗ stackAt sp parseSidFrameStack ∗ R) :
    hookStack ≤ 2 ^ 64 := by
  by_cases h0 : hookStack = 0
  · omega
  · have hm' :
        m ⊨ memRegion (sp - 80#64) 80 ∗
          (memRegion ((sp - 80#64) - BitVec.ofNat 64 hookStack) hookStack ∗ R) := by
      dsimp only [stackAt, parseSidFrameStack] at hm
      ac_nf at hm ⊢
    have hd := disjointRegions_of_coversRegion (by decide) (Nat.pos_of_ne_zero h0)
      (IsBlock.memRegion (sp - 80#64) 80).covers
      (IsBlock.memRegion ((sp - 80#64) - BitVec.ofNat 64 hookStack) hookStack).covers
      hm'
    have hlt1 := (((sp - 80#64) - BitVec.ofNat 64 hookStack) - (sp - 80#64)).isLt
    have hlt2 := ((sp - 80#64) - ((sp - 80#64) - BitVec.ofNat 64 hookStack)).isLt
    have h1 := hd.1
    have h2 := hd.2
    omega

/-- In-image `ServiceId::parse_from_service_id_string` with `.keepsFs.inImage img` on any
`libsignalSessionCode.rebase img.base H`, for any `hookStack ≥ uuidTryParseStack`. -/
theorem parseSid_okFs_rebase (img : Obj.Image) (H : String → Option (State → State))
    (hookStack : Nat := extHookStack)
    (hstack : uuidTryParseStack ≤ hookStack := by decide) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr parseSidName)
      ((parseSidCodeStackSpec hookStack).keepsFs.inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hmax : hookStack ≤ 2 ^ 64 := by
    have hm :
        s0.mem ⊨ stackAt (s0.sp - 80#64) hookStack ∗ stackAt s0.sp parseSidFrameStack ∗
          (⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
            (parseSidSpec (serviceIdParse uuidTryParse)).pre x s0 ∗ R) := by
      dsimp only [Spec.inImage, Spec.keepsFs, parseSidCodeStackSpec] at hpre
      ac_nf at hpre ⊢
    exact hookStack_le_of_frame_disjoint hm
  exact (parseSid_okFs_of_contract_stack_inImage img H hookStack
    (uuidTryParse_stack_keepsFs_inImage img H hstack hmax)).to_outcome
    x R s0 hpc hrun hpre hal

/-- Stack-generalized `parseSid_okFs` on `mProg img ext`, requiring only
`uuidTryParseStack ≤ hookStack` (no upper bound hypothesis needed). -/
theorem parseSid_okFs_stack {img : Obj.Image} {ext : String → Option (State → State)}
    (hookStack : Nat := extHookStack)
    (hstack : uuidTryParseStack ≤ hookStack := by decide) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr parseSidName)
      ((parseSidCodeStackSpec hookStack).keepsFs.inImage img) :=
  parseSid_okFs_rebase img (Rust.withPanics ext) hookStack hstack

/-- `ServiceId::parse_from_service_id_string` satisfies
`(parseSidCodeStackSpec extHookStack).keepsFs.inImage img`. -/
theorem parseSid_okFs {img : Obj.Image} {ext : String → Option (State → State)} :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr parseSidName)
      ((parseSidCodeStackSpec extHookStack).keepsFs.inImage img) :=
  parseSid_okFs_stack extHookStack (by decide)

/-- Call-site wrapper at `(mProg img ext).fnAddr caller + off` (signed/wrapped or forward `bl`). -/
theorem parseSid_okFs_rel {img : Obj.Image} {ext : String → Option (State → State)}
    (hookStack : Nat := extHookStack)
    (hstack : uuidTryParseStack ≤ hookStack := by decide)
    {caller : String} {off : BitVec 64}
    (hoff : BitVec.ofNat 64 (libsignalSessionCode.fnOff caller) + off =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff parseSidName)) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr caller + off)
      ((parseSidCodeStackSpec hookStack).keepsFs.inImage img) := by
  have heq : (mProg img ext).fnAddr caller + off = (mProg img ext).fnAddr parseSidName := by
    simp only [mProg, tripleRatchetProgAtExt, Program.fnAddr_rebase, BitVec.add_assoc, hoff]
  rw [heq]
  exact parseSid_okFs_stack hookStack hstack

/-- Call-site wrapper at `(mProg img ext).fnAddr caller - off` (backward `bl` written as `-`). -/
theorem parseSid_okFs_sub {img : Obj.Image} {ext : String → Option (State → State)}
    (hookStack : Nat := extHookStack)
    (hstack : uuidTryParseStack ≤ hookStack := by decide)
    {caller : String} {off : BitVec 64}
    (hoff : BitVec.ofNat 64 (libsignalSessionCode.fnOff caller) - off =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff parseSidName)) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr caller - off)
      ((parseSidCodeStackSpec hookStack).keepsFs.inImage img) := by
  have hadd : BitVec.ofNat 64 (libsignalSessionCode.fnOff caller) + (0#64 - off) =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff parseSidName) := by
    rw [← hoff]; bv_omega
  have hrel := parseSid_okFs_rel (img := img) (ext := ext) hookStack hstack hadd
  have heq : (mProg img ext).fnAddr caller - off =
      (mProg img ext).fnAddr caller + (0#64 - off) := by bv_omega
  rwa [heq]

/-- Ready-to-use backward `bl` call-site wrapper from `signal_session::address` to
`ServiceId::parse_from_service_id_string` (`fnAddr addressName + bv% (2 ^ 64 + ...)`). -/
theorem address_parseSid_okFs {img : Obj.Image} {ext : String → Option (State → State)}
    (hookStack : Nat := extHookStack)
    (hstack : uuidTryParseStack ≤ hookStack := by decide) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr addressName +
        bv% (2 ^ 64 +
          (ls_off% "<libsignal_core::address::ServiceId>::parse_from_service_id_string") -
          (ls_off% "libsignal_cli::address")))
      ((parseSidCodeStackSpec hookStack).keepsFs.inImage img) :=
  parseSid_okFs_rel hookStack hstack (by
    simp only [addressName, parseSidName,
      (ls_lemma% fnOff "libsignal_cli::address"),
      (ls_lemma% fnOff "<libsignal_core::address::ServiceId>::parse_from_service_id_string")]
    bv_arith)

end CryptoVerification.SignalSession.Cli.MainHops
