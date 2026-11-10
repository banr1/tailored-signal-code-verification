/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordClonePV1
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.DefsP
public import LibsignalBinary.Proofs.TripleRatchet.Record.FetchDecrypt
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.FetchDecrypt
import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegDecrypt
import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatch
import LibsignalBinary.Proofs.TripleRatchet.Alloc.FinishGrow
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpe
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244
import LibsignalBinary.Proofs.TripleRatchet.Record.SegDecrypt
import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatch
import ProofLib.SepLogic.WPp

/-!
# 4 KB-Stack `SegDecrypt` (`+1692`) and `finish_grow`

Proves `finish_grow_ok_4k`, `grow_one_spe_ok_4k`, and `rdp_segDecrypt_ok_4k` parameterized over
an arbitrary token `tok : SepProp` and panic postconditions `tryOnPanic` / `recSpec`, using only
4096-byte (`allocHookStack`) allocator and `memcpy` contracts.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalSpqrV1.M4

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts
open CryptoVerification.InImageLift

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## 1. `finish_grow` under 4096-Byte `shim` / `alloc` / `realloc` -/

theorem finish_grow_ok_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hshim_fn : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr shimName) sessionShimSpec)
    (halloc_fn : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr allocName) (rustAllocSpec A))
    (hrealloc_fn : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr reallocName) (rustReallocSpec A)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName)
      (finishGrowSpec A) := by
  open SepProp in
  have hfn := (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")
  refine subroutine_ok_of_optNone
    (finish_grow_ok_of_hooks_opt (by decide) ?_ ?_ ?_)
  · apply subroutine_ok_to_optNone
    have h := subroutine_ok_withStack_of_subroutine_ok
      (sub_ok_at_of_fnAddr hshim_fn finishGrowName
        (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]"))
        (by rw [hfn, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")]))
      allocHookStack
    refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
    have hpre' : s0.mem ⊨ (withStack sessionShimSpec allocHookStack).pre x s0 ∗ R := by
      dsimp only [withStack, sessionShimSpec, shimSpecWithStack] at hpre ⊢
      simpa only [emp_sepConj, sepConj_assoc] using hpre
    exact h.mono_outcome x R s0 hpc hrun hpre' hal fun _ hout => hout
  · exact subroutine_ok_to_optNone
      (sub_ok_at_of_fnAddr halloc_fn finishGrowName
        (num% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]"))
        (by rw [hfn, (ls_stub% "__rustc::__rust_alloc")]))
  · exact subroutine_ok_to_optNone
      (rustReallocExternWithStack_of_rustRealloc
        (sub_ok_at_of_fnAddr hrealloc_fn finishGrowName
          (num% (ls_off% "__rustc::__rust_realloc" -
            ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]"))
          (by rw [hfn, (ls_stub% "__rustc::__rust_realloc")])))

theorem grow_one_spe_ok_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hshim_fn : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr shimName) sessionShimSpec)
    (halloc_fn : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr allocName) (rustAllocSpec A))
    (hrealloc_fn : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr reallocName) (rustReallocSpec A)) :
    FromRecordCallees.GrowOneSpeOkExt b A ext :=
  FromRecordCallees.grow_one_spe_ok_ext (finish_grow_ok_4k hshim_fn halloc_fn hrealloc_fn)

/-! ## 2. Parametric Token/Panic Spec and 4 KB Stack Split Helpers -/

def rdpTrySpecParam (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (img : Obj.Image) (tok : SepProp)
    (tryOnPanic : TryDecryptGhost → State → State → SepProp) : Spec TryDecryptGhost :=
  { CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP C A ctl uuidParse S img with
    pre := fun x s =>
      ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗
        (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP C A ctl uuidParse S img).pre x s ∗
        tok
    post := fun x s0 sf =>
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP C A ctl uuidParse S img).post x s0 sf ∗
        tok
    onPanic := tryOnPanic }

private theorem rdp_seg_of_sepWPp_JF_param {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    {img : Obj.Image} {tok : SepProp} {recSpec : Spec RecordDecryptGhost}
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {target : BitVec 64} {P : SepProp}
    (hm : s.mem ⊨ P ∗ R)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem)
    (hwp : SepWPp (tripleRatchetProgAtExt img.base ext) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl uuidTryParse S img x (tok ∗ R) s0 sf ∨
          CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl uuidTryParse S img x (tok ∗ R) s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ recSpec.onPanic x s0 sf ∗ R))) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl uuidTryParse S img x (tok ∗ R) s0 s' ∨
        CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl uuidTryParse S img x (tok ∗ R) s0 s' ∨
        regionOutcome recSpec
          (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s') := by
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨_, _, P_f, hmf, hJF⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩
  · rcases hJF hmf with hJ | hF
    · exact ⟨sf, hsteps, Or.inl hJ⟩
    · exact ⟨sf, hsteps, Or.inr (Or.inl hF)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hpan, hqp hmf⟩))⟩
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem stackAt_setSessionState_split_alloc_4k (sp : BitVec 64) :
    stackAt sp setSessionStateStack =
      stackAt sp allocHookStack ∗ memRegion (sp - BitVec.ofNat 64 setSessionStateStack) 160 := by
  have heq : setSessionStateStack = 160 + allocHookStack := rfl
  dsimp only [stackAt]
  rw [heq, memRegion_split (sp - BitVec.ofNat 64 (160 + allocHookStack)) 160 allocHookStack (by decide)]
  have hsub : (sp - BitVec.ofNat 64 (160 + allocHookStack)) + BitVec.ofNat 64 160 =
      sp - BitVec.ofNat 64 allocHookStack := by
    dsimp only [allocHookStack]
    bv_omega
  rw [hsub]
  ac_rfl

private theorem stackAt_alloc_join_setSessionState_4k (sp : BitVec 64) :
    stackAt sp allocHookStack ∗ memRegion (sp - BitVec.ofNat 64 setSessionStateStack) 160 ⊢
      stackAt sp setSessionStateStack := by
  rw [stackAt_setSessionState_split_alloc_4k sp]
  exact Entails.refl _

private theorem rdp_memcpy_ok_at_4k {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hmemcpy_fn : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName)
      (withStack sessionMemcpyRegionSpec allocHookStack)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((libsignalSessionCode.rebase b
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% ((2^64 + ls_off% "memcpy" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
      (withStack sessionMemcpyRegionSpec allocHookStack) := by
  have hk :
      (bv% ((2^64 + ls_off% "memcpy" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64) : BitVec 64) =
      BitVec.ofNat 64 (num% (ls_off% "memcpy" - ls_off% "libsignal_cli_ratchet::decrypt_signal")) := rfl
  change subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + _)
    (withStack sessionMemcpyRegionSpec allocHookStack)
  rw [hk]
  exact sub_ok_at_of_fnAddr hmemcpy_fn
    CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName
    (num% (ls_off% "memcpy" - ls_off% "libsignal_cli_ratchet::decrypt_signal"))
    (by
      rw [(ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal"), (ls_stub% "memcpy")])

/-! ## 3. `SegDecrypt` (`+1692`) under 4096-Byte `memcpy` -/

attribute [local arm64_norm ↓, local wp_norm ↓]
  Record.SegDecryptFacts.SegDecryptRegReadSimp.sp_setPC_pre
  Record.SegDecryptFacts.SegDecryptRegReadSimp.sp_setMem_setPC_pre
  Record.SegDecryptFacts.SegDecryptRegReadSimp.readReg64_setPC_pre
  Record.SegDecryptFacts.SegDecryptRegReadSimp.readReg64_setMem_setPC_pre
  Record.SegDecryptFacts.SegDecryptRegReadSimp.readReg32_setPC_pre
  Record.SegDecryptFacts.SegDecryptRegReadSimp.readReg32_setMem_setPC_pre
  Record.SegDecryptFacts.SegDecryptRegReadSimp.readReg_setPC_pre
  Record.SegDecryptFacts.SegDecryptRegReadSimp.readReg_setMem_setPC_pre

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

set_option maxHeartbeats 1200000 in
theorem rdp_segDecrypt_ok_4k {img : Obj.Image} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {ext : String → Option (State → State)}
    {tok : SepProp} {tryOnPanic : TryDecryptGhost → State → State → SepProp}
    {recSpec : Spec RecordDecryptGhost}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hmemcpy_fn : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr memcpyName)
      (withStack sessionMemcpyRegionSpec allocHookStack))
    (htry : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (rdpTrySpecParam C A ctl uuidTryParse S img tok tryOnPanic))
    (hset : FromRecordCallees.SetSessionStateOkExt img.base A ext)
    (hdrop : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt img.base A ext)
    (hgrow : FromRecordCallees.GrowOneSpeOkExt img.base A ext)
    (hclosure : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.LogClosureOkExt img ext)
    (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State)
    (_hQ : x.st.pqRatchetState.length < 2 ^ 32)
    (hpan_try : ∀ (sp : BitVec 64) (s1 sf : State) (F : SepProp),
      x.st.version.toNat = x.msg.messageVersion.toNat →
      s1.trace = s0.trace →
      tryOnPanic (mkTryDecryptGhost sp x G₁) s1 sf ∗ F ⊢ recSpec.onPanic x s0 sf)
    (hpan_grow : ∀ (s1 sf : State) (F : SepProp),
      s1.trace = s0.trace →
      (⌜allocFailedIn s1 sf ∧ s1.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢ recSpec.onPanic x s0 sf)
    (hV : CryptoVerification.Cli.LibsignalTripleRatchet.Record.VStateP A ctl uuidTryParse img x G₁ (tok ∗ R) s0 s)
    (hsp_bound : rootStack ≤ s0.sp.toNat)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl uuidTryParse S img x (tok ∗ R) s0 s' ∨
        CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl uuidTryParse S img x (tok ∗ R) s0 s' ∨
        regionOutcome recSpec
          (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s') := by
  rcases hV with ⟨hpc, ⟨hrun, hsp, hsp_align, hx29, htr, hfrozen, hsym, hvregs⟩,
    ⟨hrem_or_dist, hseeds, hrc_len⟩, hclone, heq, hmem⟩
  have hentry := entryOf_eq_tripleRatchetProgAtExt ext hloads CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Record.recVPC at hpc
  rw [hentry] at hpc
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName =
      num% (ls_off% "libsignal_cli_ratchet::decrypt_signal") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal")
  have htry_rel :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
          bv% (2 ^ 64 + (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") -
            (ls_off% "libsignal_cli_ratchet::decrypt_signal")))
        (rdpTrySpecParam C A ctl uuidTryParse S img tok tryOnPanic) := by
    have h1 : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName =
        num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") :=
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")
    have h2 : (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% (2 ^ 64 + (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") -
          (ls_off% "libsignal_cli_ratchet::decrypt_signal")) =
        (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName := by
      simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, hfn, h1]
      bv_omega
    rw [h2]
    exact htry
  dsimp only [rdpTrySpecParam, CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP] at htry_rel
  have hmemcpy_rel := rdp_memcpy_ok_at_4k hmemcpy_fn
  dsimp only [withStack, sessionMemcpyRegionSpec] at hmemcpy_rel
  have hset_rel :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
          bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state") -
            (ls_off% "libsignal_cli_ratchet::decrypt_signal")))
        (setSessionStateSpec A) := by
    have h1 : libsignalSessionCode.fnOff setSessionStateName =
        num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state") :=
      (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::set_session_state")
    have h2 : (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state") -
          (ls_off% "libsignal_cli_ratchet::decrypt_signal")) =
        (tripleRatchetProgAtExt img.base ext).fnAddr setSessionStateName := by
      simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, hfn, h1]
      bv_omega
    rw [h2]
    exact hset
  have hdrop_rel :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
          bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#3]") -
            (ls_off% "libsignal_cli_ratchet::decrypt_signal")))
        (dropSessionStructureLocal2Spec A) := by
    have h1 : libsignalSessionCode.fnOff
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructureLocal2Name =
        num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#3]") :=
      (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#3]")
    have h2 : (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#3]") -
          (ls_off% "libsignal_cli_ratchet::decrypt_signal")) =
        (tripleRatchetProgAtExt img.base ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructureLocal2Name := by
      simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, hfn, h1]
      bv_omega
    rw [h2]
    exact hdrop
  have hclosure_rel :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
          bv% (2 ^ 64 + (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_ratchet::Coins>::{closure#0}") -
            (ls_off% "libsignal_cli_ratchet::decrypt_signal")))
        ((logClosureSpec img).inImage img) := by
    have h1 : libsignalSessionCode.fnOff
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.logClosureName =
        num% (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_ratchet::Coins>::{closure#0}") :=
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_ratchet::Coins>::{closure#0}")
    have h2 : (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% (2 ^ 64 + (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_ratchet::Coins>::{closure#0}") -
          (ls_off% "libsignal_cli_ratchet::decrypt_signal")) =
        (tripleRatchetProgAtExt img.base ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.logClosureName := by
      simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, hfn, h1]
      bv_omega
    rw [h2]
    exact hclosure
  have hgrow_rel :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
          bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one") -
            (ls_off% "libsignal_cli_ratchet::decrypt_signal")))
        (growOneSpeSpec A) := by
    have h1 : libsignalSessionCode.fnOff growOneSpeName =
        num% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one") :=
      (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one")
    have h2 : (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one") -
          (ls_off% "libsignal_cli_ratchet::decrypt_signal")) =
        (tripleRatchetProgAtExt img.base ext).fnAddr growOneSpeName := by
      simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, hfn, h1]
      bv_omega
    rw [h2]
    exact hgrow
  have hFPC : CryptoVerification.Cli.LibsignalTripleRatchet.Record.recFPC img =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 2128#64 := by
    unfold CryptoVerification.Cli.LibsignalTripleRatchet.Record.recFPC
    rw [hentry]
  have hJPC : CryptoVerification.Cli.LibsignalTripleRatchet.Record.recJPC img =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 7820#64 := by
    unfold CryptoVerification.Cli.LibsignalTripleRatchet.Record.recJPC
    rw [hentry]
  have hlog1732 : logOff img =
      (((((libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 1732#64 &&&
        bv% (2 ^ 64 - 4096)) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) -
          page% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1732))) +
        bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096)) ↦₆₄ 0#64) :=
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.logOff_eq_at_1732
      hloads (by rw [Program.fnAddr_rebase, hfn])
  have hlog1732' :
      (((((libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 1732#64 &&&
        bv% (2 ^ 64 - 4096)) + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256 -
          page% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1732))) ↦₆₄ 0#64) : SepProp) ⊢
        logOff img := by
    rw [hlog1732]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.refl _
  segDecrypt_rec_fetches_cli img.base (Rust.withPanics ext) hfn 1692 64
  segDecrypt_rec_fetches_cli img.base (Rust.withPanics ext) hfn 1984 36
  segDecrypt_rec_fetches_cli img.base (Rust.withPanics ext) hfn 5948 156
  segDecrypt_rec_fetches_cli img.base (Rust.withPanics ext) hfn 7812 8
  change s.pc = (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 1692#64 at hpc
  clear hentry hfn htry hset hdrop hgrow hclosure hloads hmemcpy_fn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry
  examples_hide_fetches
  have hsp0 : s0.sp = s.sp := hsp.symm
  clear hsp
  rw [hsp0] at hsp_bound hmem
  unfold recFrame at hmem
  simp only [← sepConj_assoc] at hmem
  have hF0 : FrozenInv img s := ⟨hfrozen, hsym⟩
  apply rdp_seg_of_sepWPp_JF_param hmem hL
    (target := decryptTarget entry ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).1)
  apply segDecrypt_of_sepWP_frozen hF0
    (mid := entry + bv% (2 ^ 64 + (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") -
      (ls_off% "libsignal_cli_ratchet::decrypt_signal")))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF1
  have hsp_bound1 : rootStack ≤
      ((((((((s.writeReg64 (Reg.gpr 2#5) x.remA).writeReg64
              (Reg.gpr 3#5) x.locA).writeReg64
            (Reg.gpr 4#5) x.msgA).writeReg64
          (Reg.gpr 0#5) (s.sp + 1200#64)).writeReg64
        (Reg.gpr 1#5) (s.sp + 3232#64)).writeReg64
      (Reg.gpr 5#5) 2#64).writeReg64
    (Reg.gpr 6#5) 0#64).writeReg64 (Reg.gpr 30#5) (entry + bv% (1720)) |>.setPC
      (entry + bv% (2 ^ 64 + (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") -
        (ls_off% "libsignal_cli_ratchet::decrypt_signal")))).sp.toNat := hsp_bound
  segDecrypt_wpp_call_frozen_cli htry_rel
    ({ ret := s.sp + 1200#64, ss := s.sp + 3232#64, G := G₁, st := x.st,
       rem := x.rem, remA := x.remA, loc := x.loc, locA := x.locA,
       msgG := x.msgG, msgA := x.msgA, msg := x.msg, msgType := .whisper,
       cur := x.cur, rest := x.rest : TryDecryptGhost }) hF1
    (hpan_try s.sp _ _ _ heq (by simp only [wp_norm, arm64_norm, htr]))
  apply SepWPp.exists_elim
  intro G₂
  apply SepWPp.pure_elim
  rintro ⟨⟨hnpan, htr_sf⟩, hdec⟩
  have hmk :
      ({ ret := s.sp + 1200#64, ss := s.sp + 3232#64, G := G₁, st := x.st,
         rem := x.rem, remA := x.remA, loc := x.loc, locA := x.locA,
         msgG := x.msgG, msgA := x.msgA, msg := x.msg, msgType := .whisper,
         cur := x.cur, rest := x.rest : TryDecryptGhost }) = mkTryDecryptGhost s.sp x G₁ := rfl
  rw [hmk] at hnpan hdec ⊢
  rcases hres : ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).1 with e | pt
  · dsimp only [decryptTarget, vecResultAt]
    have he_npan : e ≠ .panic := fun h => hnpan (h ▸ hres)
    cases hdup : isDupErr e
    · have htag_ne23 : speTag e ≠ speWord 23 := speTag_ne_speWord23_of_not_isDupErr hdup
      have hmodel_err : x.model C S uuidTryParse =
          (.error (.invalidMessage .whisper .decryptionFailed), x.st) := by
        rw [model_err_of_tryDecrypt_err C S s.sp x G₁ heq (Prod.ext hres rfl),
          recordError_of_speTag_ne_speWord23 he_npan htag_ne23]
      have hmodel_err1 : (x.model C S uuidTryParse).1 =
          .error (.invalidMessage .whisper .decryptionFailed) := congrArg Prod.fst hmodel_err
      have htag_add2 : speTag e + 2#64 ≠ 0#64 := speTag_add2_ne_zero he_npan
      have htag_ne23' : speTag e ≠ 9223372036854775831#64 := htag_ne23
      apply segDecrypt_of_sepWP_frozen hF_sf
        (mid := entry + bv% (2 ^ 64 + (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_ratchet::Coins>::{closure#0}") -
          (ls_off% "libsignal_cli_ratchet::decrypt_signal")))
      refine segDecrypt_replace_pre
        (speAt_decomp6 A (utf8 "decrypt") (s.sp + 1200#64) e he_npan) (by sep_focus) ?_
      rw [memRegion_5f0_split_b40 s.sp, memRegion48_eq_words6At (s.sp + 2880#64),
        stackAt_root_split_closure s.sp, errsAt_nil_unfold A s.sp]
      unfold words6At
      segDecrypt_wp_extract_exists
      rename_i u0 u1 u2 u3 u4 u5 w1 w2 w3 w4 w5 H hreassemble
      generalize htag_def : speTag e = tag at htag_add2 htag_ne23' hreassemble ⊢
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF2
      segDecrypt_wpp_call_frozen_cli hclosure_rel () hF2 noPanic_onPanic_entails
      apply segDecrypt_of_sepWP_frozen hF_sf_1
        (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one") -
          (ls_off% "libsignal_cli_ratchet::decrypt_signal")))
      segDecrypt_wp_extract_exists
      rename_i htr_cl
      rw [hsp_sf]
      refine segDecrypt_replace_pre (closureStack_to_growStack s.sp) (by sep_focus) ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF3
      segDecrypt_wpp_call_frozen_cli hgrow_rel (s.sp + 0x5d8#64, 0#64, 8#64, []) hF3
        (hpan_grow _ _ _ (by simp only [wp_norm, arm64_norm, htr_cl, htr_sf, htr]))
      apply segDecrypt_of_sepWP_ret_frozen hF_sf_2
      segDecrypt_wp_extract_exists
      rename_i p' hp'
      rw [memRegion_192_split48 p', memRegion48_eq_words6At p']
      unfold words6At
      segDecrypt_wp_extract_exists
      wp_steps
      rw [hsp_sf_1, hsp_sf]
      refine segDecrypt_replace_pre
        (spe_errsAt_entails A s.sp p' e tag w1 w2 w3 w4 w5 H hp'.2 (hreassemble p'))
        (by sep_focus) ?_
      refine segDecrypt_replace_pre (words6_4b0_to_memRegion s.sp tag w1 w2 w3 w4 w5) (by sep_focus) ?_
      refine segDecrypt_replace_pre (words6_b40_to_memRegion s.sp tag w1 w2 w3 w4 w5) (by sep_focus) ?_
      refine segDecrypt_replace_pre (growStack_to_rootStack s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre
        (sessionStateAt_exists_intro A (s.sp + 3232#64) G₂
          ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2) (by sep_focus) ?_
      refine segDecrypt_replace_pre
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.tapeAfter_tryDecrypt_entails
          C img.base s.sp x G₁ heq) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF4 hmf
      right
      refine ⟨by rw [hFPC]; wp_norm_lhs, ?_, hmodel_err1, ?_⟩
      · refine ⟨by wp_norm_lhs,
                by simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf, hsp0],
                by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf]; exact hsp_align,
                by simp only [wp_norm, arm64_norm, hcs_sf_2, hcs_sf_1, hcs_sf]; exact hx29,
                by simp only [wp_norm, arm64_norm, hp'.1, htr_cl, htr_sf, htr],
                hF4.1, hF4.2,
                by simp only [wp_norm, arm64_norm, hvregs_3, hvregs_2, hvregs_1, hvregs]⟩
      · unfold recFrame
        rw [hsp0]
        exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hmf
    · obtain ⟨i, c, rfl⟩ := eq_duplicatedMessage_of_isDupErr hdup
      have hmodel_dup : x.model C S uuidTryParse = (.error (.duplicatedMessage i c), x.st) :=
        model_err_of_tryDecrypt_err C S s.sp x G₁ heq (Prod.ext hres rfl)
      have hmodel_dup1 : (x.model C S uuidTryParse).1 = .error (.duplicatedMessage i c) :=
        congrArg Prod.fst hmodel_dup
      apply segDecrypt_of_sepWP_frozen hF_sf
        (mid := entry + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#3]") -
          (ls_off% "libsignal_cli_ratchet::decrypt_signal")))
      dsimp only [speAt]
      rw [stackAt_root_split_dropLocal2 s.sp]
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF2
      segDecrypt_wpp_call_frozen_cli hdrop_rel
        ({ ss := s.sp + 3232#64, G := G₂,
           st := ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 : DropSessionStructureGhost })
        hF2 noPanic_onPanic_entails
      apply segDecrypt_of_sepWP_ret_frozen hF_sf_1
      segDecrypt_wp_extract_exists
      rename_i htr_drop
      rw [hsp_sf]
      refine segDecrypt_replace_pre (dropLocal2Stack_to_rootStack s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre (errsAt_nil_exists_intro A s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.tapeAfter_tryDecrypt_entails
          C img.base s.sp x G₁ heq) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF3 hmf
      left
      refine ⟨by rw [hJPC]; wp_norm_lhs, ?_, by rw [hmodel_dup1]; nofun,
        by simp only [wp_norm, arm64_norm, h_17, hsp0],
        by simp only [wp_norm, arm64_norm, h_18],
        by rw [hmodel_dup1]; dsimp only [recordResultTag, speWord]; wp_norm_lhs, ?_⟩
      · refine ⟨by wp_norm_lhs,
                by simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf, hsp0],
                by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf]; exact hsp_align,
                by simp only [wp_norm, arm64_norm, hcs_sf_1, hcs_sf]; exact hx29,
                by simp only [wp_norm, arm64_norm, htr_drop, htr_sf, htr],
                hF3.1, hF3.2,
                by simp only [wp_norm, arm64_norm, hvregs_2, hvregs_1, hvregs]⟩
      · unfold recFrame
        rw [hsp0, hmodel_dup1]
        dsimp only [recordResultAt, vecResultAt, speAt]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hmf
  · dsimp only [decryptTarget, vecResultAt]
    have hmodel_ok : x.model C S uuidTryParse =
        (.ok pt, ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2) :=
      model_ok_of_tryDecrypt_ok C S s.sp x G₁ heq (Prod.ext hres rfl)
    have hmodel_ok1 : (x.model C S uuidTryParse).1 = .ok pt := by rw [hmodel_ok]
    have hmodel_ok2 : (x.model C S uuidTryParse).2 =
        ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 := by rw [hmodel_ok]
    rw [hres] at hdec
    have hrel : x.G.AfterRecordDecrypt G₂ := recordOkRel_of_clone_dec hclone hdec
    apply segDecrypt_of_sepWP_frozen hF_sf
      (mid := entry + bv% ((2^64 + ls_off% "memcpy" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
    rw [sessionStateAt_eq_inline_sep_heap A (s.sp + 3232#64) G₂
      ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2,
      memRegion_5f0_split344 s.sp, stackAt_root_split_set s.sp,
      stackAt_setSessionState_split_alloc_4k s.sp, hlog1732]
    segDecrypt_wp_extract_exists
    rename_i bs hbs
    rw [← hbs.1]
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF2
    segDecrypt_wpp_call_frozen_cli hmemcpy_rel (s.sp + 1520#64, s.sp + 3232#64, bs) hF2
      noPanic_onPanic_entails
    apply segDecrypt_of_sepWP_frozen hF_sf_1
      (mid := entry + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state") -
        (ls_off% "libsignal_cli_ratchet::decrypt_signal")))
    segDecrypt_wp_extract_exists
    rename_i hmc
    rw [hsp_sf]
    refine segDecrypt_replace_pre
      (stackAt_alloc_join_setSessionState_4k s.sp) (by sep_focus) ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF3
    segDecrypt_wpp_call_frozen_cli hset_rel
      ({ record := s.sp + 288#64, src := s.sp + 1520#64,
         cur := some (x.G, x.st), bs := bs : SetSessionStateGhost }) hF3
      noPanic_onPanic_entails
    apply segDecrypt_of_sepWP_ret_frozen hF_sf_2
    segDecrypt_wp_extract_exists
    rename_i htr_set
    wp_steps
    rw [hsp_sf_1, hsp_sf]
    refine segDecrypt_replace_pre
      (sessionStateAt_move_bytes_twice A (s.sp + 3232#64) (s.sp + 1520#64) (s.sp + 312#64)
        G₂ ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 hbs.2) (by sep_focus) ?_
    refine segDecrypt_replace_pre (memRegion_5f0_join344 s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre (setStack_to_rootStack s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre hlog1732' (by sep_focus) ?_
    refine segDecrypt_replace_pre
      (sessionStateAt_ok_exists_intro A (s.sp + 312#64) x.G G₂
        ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 hrel) (by sep_focus) ?_
    refine segDecrypt_replace_pre (errsAt_nil_exists_intro A s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.tapeAfter_tryDecrypt_entails
        C img.base s.sp x G₁ heq) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF4 hmf
    left
    refine ⟨by rw [hJPC]; wp_norm_lhs, ?_, by rw [hmodel_ok1]; nofun,
      by simp only [wp_norm, arm64_norm, h_27, h_17, hsp0],
      by simp only [wp_norm, arm64_norm, h_28, h_18],
      by rw [hmodel_ok1]; dsimp only [recordResultTag, okTagVec]; wp_norm_lhs, ?_⟩
    · refine ⟨by wp_norm_lhs,
              by simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf, hsp0],
              by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf]; exact hsp_align,
              by simp only [wp_norm, arm64_norm, hcs_sf_2, hcs_sf_1, hcs_sf]; exact hx29,
              by simp only [wp_norm, arm64_norm, htr_set, hmc.2, htr_sf, htr],
              hF4.1, hF4.2,
              by simp only [wp_norm, arm64_norm, hvregs_3, hvregs_2, hvregs_1, hvregs]⟩
    · unfold recFrame
      rw [hsp0, hmodel_ok1, hmodel_ok2]
      dsimp only [recordResultAt, vecResultAt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hmf

end CryptoVerification.Cli.LibsignalSpqrV1.M4
