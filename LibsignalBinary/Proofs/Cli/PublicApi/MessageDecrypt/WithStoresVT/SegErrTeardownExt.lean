/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegErrTeardown
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefs
public import LibsignalBinary.Proofs.Cli.PublicApi.StoreSession.StoreCallSite
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegStoreAux
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WP.Apply

/-!
# Ext-Generic `SegErrTeardown` (`+0x2294 / +0x22a8 → +0x24d4`)

Proves ext-generic error-teardown segment `segErrTeardownVX_ok_ext` over
`tripleRatchetProgAtExt img.base ext`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
open CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegStore
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegErrTeardown

namespace ErrTeardownExtBin

gen_decodes libsignalSessionCode_tree libsignalSessionBinCli
  [(ls_off% "libsignal_cli_ratchet::decrypt_signal" + 8852) →
   (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 8996)]

end ErrTeardownExtBin

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem stack_ws_dropLocal2 (sp : BitVec 64) :
    stackAt sp wsCalleeStack =
      memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - FromRecordCallees.dropSessionStructureLocal2Stack) ∗
        stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack := by
  have h := stackAt_split_bottom sp FromRecordCallees.dropSessionStructureLocal2Stack
    (wsCalleeStack - FromRecordCallees.dropSessionStructureLocal2Stack) (by decide)
  rwa [show FromRecordCallees.dropSessionStructureLocal2Stack +
    (wsCalleeStack - FromRecordCallees.dropSessionStructureLocal2Stack) = wsCalleeStack by decide] at h

private theorem stack_ws_alloc (sp : BitVec 64) :
    stackAt sp wsCalleeStack =
      memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - allocHookStack) ∗
        stackAt sp allocHookStack := by
  have h := stackAt_split_bottom sp allocHookStack (wsCalleeStack - allocHookStack) (by decide)
  rwa [show allocHookStack + (wsCalleeStack - allocHookStack) = wsCalleeStack by decide] at h

private theorem cap_add_one_beq_zero_eq_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]; intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change cap.toNat + 1 = 0 at ht; omega

private def vecGhostTailAt (A : RustAlloc) (g : VecGhost) (v : BitVec 64) : SepProp :=
  ((v + 8#64) ↦₆₄ g.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
  (if g.cap = 0 then emp
   else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
     memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))

private theorem vecGhostAt_unfold_cap (A : RustAlloc) (g : VecGhost) (v : BitVec 64) :
    vecGhostAt A g v =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
      (v ↦₆₄ g.cap) ∗ vecGhostTailAt A g v := by
  simp only [vecGhostAt, vecU8At, vecHeader, vecGhostTailAt]; ac_rfl

private def sessionStateAfterLocalIk (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SepProp :=
  ⌜PublicKey.deserialize G.localIk.bytes = Except.ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with
      | none => G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize G.remoteIk.bytes = Except.ok ik.publicKey) ∧
    G.chains.length = st.receiverChains.length ∧ G.pending.isSome = st.pendingPreKey ∧
    G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧ (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
  vecGhostAt A G.remoteIk (ss + 24#64) ∗
  vecU8At A (ss + 48#64) G.root.cap G.root.ptr (CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
  vecAt A 104 8 (chainAt A) (ss + 72#64) G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
  vecGhostAt A G.alice (ss + 96#64) ∗
  vecU8At A (ss + 120#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
  optSenderChainAt A (ss + 144#64) G.sender st.senderChain ∗
  optTailVecAt A 48 (ss + 248#64) G.pending ∗ optTailVecAt A 32 (ss + 296#64) G.kyber ∗
  ((ss + 328#64) ↦₃₂ st.sessionVersion) ∗ ((ss + 332#64) ↦₃₂ st.previousCounter) ∗
  ((ss + 336#64) ↦ₛ G.regIds)

private theorem sessionStateAt_unfold_cap (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st =
      ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
      (ss ↦₆₄ G.localIk.cap) ∗ vecGhostTailAt A G.localIk ss ∗
      sessionStateAfterLocalIk A ss G st := by
  unfold sessionStateAt sessionStateAfterLocalIk; rw [vecGhostAt_unfold_cap]; ac_rfl

private def dropSessionStructureLocal2HeadSpec (A : RustAlloc) : Spec FromRecordCallees.DropSessionStructureGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ x.G.localIk.bytes.length ≤ x.G.localIk.cap.toNat ∧
      x.G.localIk.cap.toNat < 2 ^ 63 ∧ x.G.localIk.ptr ≠ 0⌝ ∗
      (x.ss ↦₆₄ x.G.localIk.cap) ∗ vecGhostTailAt A x.G.localIk x.ss ∗
      sessionStateAfterLocalIk A x.ss x.G x.st ∗ A.pool ∗ stackAt s.sp FromRecordCallees.dropSessionStructureLocal2Stack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion x.ss 344 ∗ A.pool ∗ stackAt s0.sp FromRecordCallees.dropSessionStructureLocal2Stack

private theorem drop_session_structure_local2_head_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdrop2 : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructureLocal2Name)
      (dropSessionStructureLocal2HeadSpec A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
    hdrop2.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
  simp only [FromRecordCallees.dropSessionStructureLocal2Spec, dropSessionStructureLocal2HeadSpec,
    sessionStateAt_unfold_cap, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  exact ⟨hpre.1.1, hpre.1.2, hpre.2⟩

private theorem prevCap_ubfm_eq {cap : BitVec 64} (h : cap.toNat * 24 < 2 ^ 63) :
    ((cap + cap <<< 1) <<< 3).toNat = cap.toNat * 24 := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_shiftLeft]
  omega

private theorem noneCap_fold (a v : BitVec 64) :
    (a ↦₆₄ v) ∗ memRegion (a + 8#64) 336 ⊢ memRegion a 344 := by
  rw [memRegion_split a 8 336 (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion a v)

set_option maxHeartbeats 600000 in
theorem teardown_tail_ok_ext4K {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (hdrop2 : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt b A ext)
    {s : State} {R : SepProp} {prevCap prevPtr : BitVec 64}
    {cs : Option (SessionGhost × SessionState (List (BitVec 8)))}
    {s0_580 s1_588 s2_590 s3_598 : BitVec 64} {s4_5a0 : BitVec 32}
    {t0_300 t1_308 t2_310 t3_318 : BitVec 64} {t4_320 : BitVec 32}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x22a8#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx28 : s.readReg64 .x28 ≠ pendingTag) (hx26 : s.readReg64 .x26 = s.sp + 0xa0#64)
    (hprev_lt : prevCap.toNat * 24 < 2 ^ 63) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x24d4#64) s
      (((s.sp + 0x120#64) ↦₆₄ prevCap) ∗ ((s.sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗
        (if prevCap = 0#64 then emp else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
        curPre A (s.sp + 0x138#64) cs ∗
        ((s.sp + 0x300#64) ↦₆₄ t0_300) ∗ ((s.sp + 0x308#64) ↦₆₄ t1_308) ∗ ((s.sp + 0x310#64) ↦₆₄ t2_310) ∗
        ((s.sp + 0x318#64) ↦₆₄ t3_318) ∗ ((s.sp + 0x320#64) ↦₃₂ t4_320) ∗
        ((s.sp + 0x580#64) ↦₆₄ s0_580) ∗ ((s.sp + 0x588#64) ↦₆₄ s1_588) ∗ ((s.sp + 0x590#64) ↦₆₄ s2_590) ∗
        ((s.sp + 0x598#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x5a0#64) ↦₃₂ s4_5a0) ∗
        A.pool ∗ stackAt s.sp wsCalleeStack)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (((s.sp + 0x120#64) ↦₆₄ prevCap) ∗ ((s.sp + 0x128#64) ↦₆₄ prevPtr) ∗
          ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗ memRegion (s.sp + 0x138#64) 344 ∗
          ((s.sp + 0x300#64) ↦₆₄ s0_580) ∗ ((s.sp + 0x308#64) ↦₆₄ s1_588) ∗ ((s.sp + 0x310#64) ↦₆₄ s2_590) ∗
          ((s.sp + 0x318#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x320#64) ↦₃₂ s4_5a0) ∗
          ((s.sp + 0x580#64) ↦₆₄ s0_580) ∗ ((s.sp + 0x588#64) ↦₆₄ s1_588) ∗ ((s.sp + 0x590#64) ↦₆₄ s2_590) ∗
          ((s.sp + 0x598#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x5a0#64) ↦₃₂ s4_5a0) ∗
          A.pool ∗ stackAt s.sp wsCalleeStack) ∗ R) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName =
      (ls_off% "libsignal_cli_ratchet::decrypt_signal") := by
    simp only [CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName, arm64_norm]
  have hfn2 : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructureLocal2Name =
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#3]") := by
    simp only [CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructureLocal2Name, arm64_norm]
  have hdrop := drop_session_structure_local2_head_ok_ext hdrop2
  have hrel : (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructureLocal2Name =
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName +
        bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#3]" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64) := by
    simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, hfn, hfn2, BitVec.add_assoc]; rfl
  rw [hrel] at hdrop; clear hrel
  have hdealloc := msgDecrypt_dealloc_ok_ext4K hA
  have hx28n : s.readReg64 (Reg.gpr 28#5) ≠ pendingTag := hx28
  have hx28' : (s.readReg64 (Reg.gpr 28#5) + 3#64 == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h; apply hx28n
    simp only [pendingTag]; bv_omega
  have hx28b : (s.readReg64 (Reg.gpr 28#5) + 3#64 != 0#64) = true := by
    rw [bne_iff_ne]; intro h; apply hx28n
    simp only [pendingTag]; bv_omega
  code_fetches_range CryptoVerification.libsignalSessionCode ErrTeardownExtBin.libsignalSessionBinCli b (Rust.withPanics ext) hfn (ls_off% "libsignal_cli_ratchet::decrypt_signal") 0x22a8 0x1c
  code_fetches_range CryptoVerification.libsignalSessionCode ErrTeardownExtBin.libsignalSessionBinCli b (Rust.withPanics ext) hfn (ls_off% "libsignal_cli_ratchet::decrypt_signal") 0x22f0 0x38
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName,
    CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName] at hpc hdrop hdealloc ⊢
  generalize (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "libsignal_cli_ratchet::decrypt_signal" = entry at *
  examples_hide_fetches
  rcases cs with _ | ⟨G, st⟩
  · have hnone : (noneCap + 1#64 == 0#64) = true := by decide
    simp only [curPre]
    wp_simp_pre [sepConj_assoc]
    wp_steps
    have hfold := noneCap_fold (s.sp + 0x138#64) noneCap
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hfold
    apply SepWP.fold hfold (by sep_focus)
    by_cases hcap : prevCap = 0#64
    · subst hcap; simp only [beq_self_eq_true, ↓reduceIte, emp_sepConj]; wp_steps; wp_done
    · have hcap_beq : (prevCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      simp only [hcap_beq, hcap, ↓reduceIte, Bool.false_eq_true]
      apply SepWP.fold (Entails.of_eq (stack_ws_alloc s.sp)) (by sep_focus)
      wp_steps
      have hmul := prevCap_ubfm_eq hprev_lt
      wp_apply
      apply SepWP.fold (Entails.of_eq (stack_ws_alloc s.sp).symm) (by sep_focus)
      wp_steps; wp_done
  · simp only [curPre]
    wp_simp_pre [sessionStateAt_unfold_cap, sepConj_assoc, sepConj_pure_left_comm]
    apply SepWP.pure_elim; rintro ⟨hlik_len, hlik_cap, hlik_ptr⟩
    have hcmn : (G.localIk.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hlik_cap
    apply SepWP.fold (Entails.of_eq (stack_ws_dropLocal2 s.sp)) (by sep_focus)
    wp_steps
    wp_apply
    apply SepWP.fold (Entails.of_eq (stack_ws_dropLocal2 s.sp).symm) (by sep_focus)
    wp_steps
    by_cases hcap : prevCap = 0#64
    · subst hcap; simp only [beq_self_eq_true, ↓reduceIte, emp_sepConj]; wp_steps; wp_done
    · have hcap_beq : (prevCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      simp only [hcap_beq, hcap, ↓reduceIte, Bool.false_eq_true]
      apply SepWP.fold (Entails.of_eq (stack_ws_alloc s.sp)) (by sep_focus)
      wp_steps
      have hmul := prevCap_ubfm_eq hprev_lt
      wp_apply
      simp only [hsp_sf] at hsp_sf_1 ⊢
      apply SepWP.fold (Entails.of_eq (stack_ws_alloc s.sp).symm) (by sep_focus)
      wp_steps; wp_done

theorem teardown_tail_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (hdrop2 : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt b A ext)
    {s : State} {R : SepProp} {prevCap prevPtr : BitVec 64}
    {cs : Option (SessionGhost × SessionState (List (BitVec 8)))}
    {s0_580 s1_588 s2_590 s3_598 : BitVec 64} {s4_5a0 : BitVec 32}
    {t0_300 t1_308 t2_310 t3_318 : BitVec 64} {t4_320 : BitVec 32}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x22a8#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx28 : s.readReg64 .x28 ≠ pendingTag) (hx26 : s.readReg64 .x26 = s.sp + 0xa0#64)
    (hprev_lt : prevCap.toNat * 24 < 2 ^ 63) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x24d4#64) s
      (((s.sp + 0x120#64) ↦₆₄ prevCap) ∗ ((s.sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗
        (if prevCap = 0#64 then emp else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
        curPre A (s.sp + 0x138#64) cs ∗
        ((s.sp + 0x300#64) ↦₆₄ t0_300) ∗ ((s.sp + 0x308#64) ↦₆₄ t1_308) ∗ ((s.sp + 0x310#64) ↦₆₄ t2_310) ∗
        ((s.sp + 0x318#64) ↦₆₄ t3_318) ∗ ((s.sp + 0x320#64) ↦₃₂ t4_320) ∗
        ((s.sp + 0x580#64) ↦₆₄ s0_580) ∗ ((s.sp + 0x588#64) ↦₆₄ s1_588) ∗ ((s.sp + 0x590#64) ↦₆₄ s2_590) ∗
        ((s.sp + 0x598#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x5a0#64) ↦₃₂ s4_5a0) ∗
        A.pool ∗ stackAt s.sp wsCalleeStack)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (((s.sp + 0x120#64) ↦₆₄ prevCap) ∗ ((s.sp + 0x128#64) ↦₆₄ prevPtr) ∗
          ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗ memRegion (s.sp + 0x138#64) 344 ∗
          ((s.sp + 0x300#64) ↦₆₄ s0_580) ∗ ((s.sp + 0x308#64) ↦₆₄ s1_588) ∗ ((s.sp + 0x310#64) ↦₆₄ s2_590) ∗
          ((s.sp + 0x318#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x320#64) ↦₃₂ s4_5a0) ∗
          ((s.sp + 0x580#64) ↦₆₄ s0_580) ∗ ((s.sp + 0x588#64) ↦₆₄ s1_588) ∗ ((s.sp + 0x590#64) ↦₆₄ s2_590) ∗
          ((s.sp + 0x598#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x5a0#64) ↦₃₂ s4_5a0) ∗
          A.pool ∗ stackAt s.sp wsCalleeStack) ∗ R) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) :=
  teardown_tail_ok_ext4K hA.toAllocContracts4K hdrop2 hpc hrun hsp_align hx28 hx26 hprev_lt

set_option linter.unusedVariables false in
def teardownFrameExt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (s0 : State) (sp : BitVec 64)
    (F : SepProp) : SepProp :=
  wsFixedV kit ikit x s0 sp ∗
  (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗ logOff img) ∗
  wsMsgCells x sp ∗ memRegion (sp + 0x290#64) 24 ∗ F ∗
  memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
  memRegion (sp + 0x324#64) 0x25c ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
  memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans)

private theorem ej_false_expose_ext (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (s0 : State) (sp : BitVec 64)
    (cs : Option (SessionGhost × SessionState (List (BitVec 8))))
    (x28 w20 w21 : BitVec 64) (res : Except (ApiError AddrVal Unit) (List (BitVec 8))) (R : SepProp) :
    (wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      droppableRecordAt A (sp + 0x120#64) cs ∗ memRegion (sp + 0x290#64) 24 ∗
      StagedRes A x28 w20 w21 (sp + 0x580#64) res ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) ∗ R) ⊢
    ∃∗ prevCap : BitVec 64, ∃∗ prevPtr : BitVec 64,
    ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 32,
    ∃∗ F : SepProp,
    ∃∗ t0 : BitVec 64, ∃∗ t1 : BitVec 64, ∃∗ t2 : BitVec 64, ∃∗ t3 : BitVec 64, ∃∗ t4 : BitVec 32,
      ⌜prevCap.toNat * 24 < 2 ^ 63⌝ ∗ ⌜resOk A x28 w20 w21 res w0 w1 w2 w3 w4 F⌝ ∗
      (teardownPre A sp prevCap prevPtr cs w0 w1 w2 w3 w4 t0 t1 t2 t3 t4 ∗
        (teardownFrameExt C A ctl img kit ikit x ans s0 sp F ∗ R)) := by
  rw [memRegion_300_280_head_split]
  refine Entails.trans (Entails.of_eq (show _ =
    droppableRecordAt A (sp + 0x120#64) cs ∗ StagedRes A x28 w20 w21 (sp + 0x580#64) res ∗
      memRegion (sp + 0x300#64) 0x24 ∗
      (wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗ memRegion (sp + 0x290#64) 24 ∗
        memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
        memRegion (sp + 0x324#64) 0x25c ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
        memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) ∗ R) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono (droppable_expose A (sp + 0x120#64) cs)
    (sepConj_mono (stagedRes_expose A x28 w20 w21 (sp + 0x580#64) res)
      (sepConj_mono_left (memRegion_36_entails_cells (sp + 0x300#64))))) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro prevCap
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro prevPtr
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w0
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w1
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w2
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w3
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w4
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro F
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro t0
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro t1
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro t2
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro t3
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro t4
  refine Entails.sepExists_right prevCap (Entails.sepExists_right prevPtr (Entails.sepExists_right w0
    (Entails.sepExists_right w1 (Entails.sepExists_right w2 (Entails.sepExists_right w3
      (Entails.sepExists_right w4 (Entails.sepExists_right F (Entails.sepExists_right t0
        (Entails.sepExists_right t1 (Entails.sepExists_right t2 (Entails.sepExists_right t3
          (Entails.sepExists_right t4 ?_))))))))))))
  unfold teardownPre teardownFrameExt wsEnv
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

private theorem teardown_post_entails_ext (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (s0 : State)
    (sp prevCap prevPtr : BitVec 64) (x28 w20 w21 : BitVec 64)
    (res : Except (ApiError AddrVal Unit) (List (BitVec 8)))
    (w0 w1 w2 w3 : BitVec 64) (w4 : BitVec 32) (F R : SepProp)
    (hres : resOk A x28 w20 w21 res w0 w1 w2 w3 w4 F) :
    teardownPost A sp prevCap prevPtr w0 w1 w2 w3 w4 ∗ (teardownFrameExt C A ctl img kit ikit x ans s0 sp F ∗ R) ⊢
      wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      StagedRes A x28 w20 w21 (sp + 0x300#64) res ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x324#64) 0xadc ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) ∗ R := by
  have h120 := rec120_join sp prevCap prevPtr
  have h580 := cells_36_entails_memRegion (sp + 0x580#64) w0 w1 w2 w3 w4
  have hst := stagedRes_repack A x28 w20 w21 (sp + 0x300#64) res w0 w1 w2 w3 w4 F hres
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h580 hst
  refine Entails.trans (Entails.of_eq (show _ =
    (((sp + 0x120#64) ↦₆₄ prevCap) ∗ ((sp + 0x128#64) ↦₆₄ prevPtr) ∗
      ((sp + 0x130#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x138#64) 344 ∗
      memRegion (sp + 0x290#64) 24 ∗ memRegion (sp + 0x2a8#64) 0x20) ∗
    ((((sp + 0x300#64) ↦₆₄ w0) ∗ ((sp + 0x308#64) ↦₆₄ w1) ∗ ((sp + 0x310#64) ↦₆₄ w2) ∗
      ((sp + 0x318#64) ↦₆₄ w3) ∗ ((sp + 0x320#64) ↦₃₂ w4)) ∗ F) ∗
    (((sp + 0x580#64) ↦₆₄ w0) ∗ ((sp + 0x588#64) ↦₆₄ w1) ∗ ((sp + 0x590#64) ↦₆₄ w2) ∗
      ((sp + 0x598#64) ↦₆₄ w3) ∗ ((sp + 0x5a0#64) ↦₃₂ w4)) ∗
    (wsFixedV kit ikit x s0 sp ∗
      (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ logOff img ∗ stackAt sp wsCalleeStack ∗ A.pool) ∗
      wsMsgCells x sp ∗ memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x324#64) 0x25c ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) ∗ R) by
    unfold teardownPost teardownFrameExt; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono h120 (sepConj_mono hst (sepConj_mono_left h580))) ?_
  rw [memRegion_324_adc_split sp]
  unfold wsEnv
  exact Entails.of_eq (by ac_rfl)

attribute [local semireducible] SepWP in
theorem segErrTeardownVX_false_ext4K {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (hyps : DecHypsExt4K img C A uuidTryParse S encRecord ext kit ikit st0 Scope)
    (hdrop2 : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt img.base A ext)
    {x : DecryptGhost} {R : SepProp} {s0 s : State}
    (hst : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x false R s0 s) :
    DecSegVXExt img C A ctl uuidTryParse S encRecord ext kit ikit st0 ist0 Scope Extra x R s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ResultFinalStateV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x R s0 s') := by
  intro hL
  rcases hst with ⟨hpc, hmeta, hx26, hx28, ans, cs, hpan, _hnok, hscope, hcalls, hid_calls, htr, hm⟩
  have hmeta0 := hmeta
  rcases hmeta0 with ⟨hrun, hsp, _hsp0_al, hsp_al, _hx29, _hx27, _hfr, _hsym, _hvregs⟩
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  have hpc' : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x22a8#64 := by
    rw [hpc, ← entryOf_eq_tripleRatchetProgAtExt ext hyps.loads]
    try rfl
  rw [← hsp] at hx26 hm
  simp only [Bool.false_eq_true, ↓reduceIte] at hm
  let R' : SepProp :=
    decStoreExtra kit ikit
      (kit.storeFinal st0 ans (x.model C S uuidTryParse ans).2)
      (ikit.idFinal ist0 ans (x.model C S uuidTryParse ans).2) s0 ∗ R
  have hm_r' : s.mem ⊨ wsFixedV kit ikit x s0 s.sp ∗ wsEnv A img x s.sp ∗ wsMsgCells x s.sp ∗
      droppableRecordAt A (s.sp + 0x120#64) cs ∗ memRegion (s.sp + 0x290#64) 24 ∗
      StagedRes A (s.readReg64 .x28) (s.readReg64 .x20) (s.readReg64 .x21) (s.sp + 0x580#64)
        (x.model C S uuidTryParse ans).1 ∗
      memRegion s.sp 0xa0 ∗ memRegion (s.sp + 0x2a8#64) 0x20 ∗ memRegion (s.sp + 0x2d0#64) 0x10 ∗
      memRegion (s.sp + 0x300#64) 0x280 ∗ memRegion (s.sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) ∗ R' := hm
  have hm_pre := Satisfies.mono (ej_false_expose_ext C A ctl img kit ikit x ans s0 s.sp cs _ _ _ _ R') hm_r'
  simp only [satisfies_sepExists] at hm_pre
  rcases hm_pre with ⟨prevCap, prevPtr, w0, w1, w2, w3, w4, F, t0, t1, t2, t3, t4, hm_pre⟩
  rw [satisfies_pure_sepConj] at hm_pre
  obtain ⟨hprev_lt, hm_pre⟩ := hm_pre
  rw [satisfies_pure_sepConj] at hm_pre
  obtain ⟨hres, hm_pre⟩ := hm_pre
  obtain ⟨sf, hsteps, ⟨hpc2, hrun2, P_f, hmf, hpost⟩ | ⟨_, _hoom⟩⟩ :=
    teardown_tail_ok_ext4K (cs := cs) (prevCap := prevCap) (prevPtr := prevPtr)
      (s0_580 := w0) (s1_588 := w1) (s2_590 := w2) (s3_598 := w3) (s4_5a0 := w4)
      (t0_300 := t0) (t1_308 := t1) (t2_310 := t2) (t3_318 := t3) (t4_320 := t4)
      (R := teardownFrameExt C A ctl img kit ikit x ans s0 s.sp F ∗ R')
      hyps.alloc hdrop2 hpc' hrun hsp_align hx28 hx26 hprev_lt
      (teardownFrameExt C A ctl img kit ikit x ans s0 s.sp F ∗ R') hm_pre hL
  rotate_left
  · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨hmf', hsp2, htr2, hx28_2, hx20_2, hx21_2, hx27_2, hx29_2, hvregs_2⟩ := hpost hmf
  have hmeta2 := wsMeta_of_steps hmeta hsteps hrun2 hsp2 hx29_2 hx27_2 hvregs_2
  have hm_fin := Satisfies.mono (teardown_post_entails_ext C A ctl img kit ikit x ans s0 s.sp prevCap prevPtr
    (s.readReg64 .x28) (s.readReg64 .x20) (s.readReg64 .x21) (x.model C S uuidTryParse ans).1
    w0 w1 w2 w3 w4 F R' hres) hmf'
  refine ⟨sf, hsteps, Or.inl ⟨?_, hmeta2, ans, hpan, hscope, hcalls, hid_calls, ?_, ?_⟩⟩
  · rw [hpc2, ← entryOf_eq_tripleRatchetProgAtExt ext hyps.loads]
  · rw [htr2, htr]
  · rw [hx28_2, hx20_2, hx21_2, ← hsp]; exact hm_fin

theorem segErrTeardownVX_false_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (hyps : DecHypsExt img C A uuidTryParse S encRecord ext kit ikit st0 Scope)
    (hdrop2 : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt img.base A ext)
    {x : DecryptGhost} {R : SepProp} {s0 s : State}
    (hst : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x false R s0 s) :
    DecSegVXExt img C A ctl uuidTryParse S encRecord ext kit ikit st0 ist0 Scope Extra x R s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ResultFinalStateV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x R s0 s') :=
  segErrTeardownVX_false_ext4K hyps.toDecHypsExt4K hdrop2 hst

theorem teardown_pt_ok_ext4K {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) {s : State} {R : SepProp} {cap ptr len : BitVec 64}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x2294#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x22a8#64) s
      (((s.sp + 0x290#64) ↦₆₄ cap) ∗ ((s.sp + 0x298#64) ↦₆₄ ptr) ∗ ((s.sp + 0x2a0#64) ↦₆₄ len) ∗
        (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗
        A.pool ∗ stackAt s.sp wsCalleeStack)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (((s.sp + 0x290#64) ↦₆₄ cap) ∗ ((s.sp + 0x298#64) ↦₆₄ ptr) ∗
          ((s.sp + 0x2a0#64) ↦₆₄ len) ∗ A.pool ∗ stackAt s.sp wsCalleeStack) ∗ R) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName =
      (ls_off% "libsignal_cli_ratchet::decrypt_signal") := by
    simp only [CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName, arm64_norm]
  have hdealloc := msgDecrypt_dealloc_ok_ext4K hA
  code_fetches_range CryptoVerification.libsignalSessionCode ErrTeardownExtBin.libsignalSessionBinCli b (Rust.withPanics ext) hfn (ls_off% "libsignal_cli_ratchet::decrypt_signal") 0x2294 0x14
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName,
    CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName] at hpc hdealloc ⊢
  generalize (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "libsignal_cli_ratchet::decrypt_signal" = entry at *
  examples_hide_fetches
  by_cases hcap : cap = 0
  · subst hcap; simp only [↓reduceIte, emp_sepConj]
    wp_steps; wp_done
  · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    simp only [hcap, ↓reduceIte]
    apply SepWP.fold (Entails.of_eq (stack_ws_alloc s.sp)) (by sep_focus)
    wp_steps
    wp_apply
    apply SepWP.fold (Entails.of_eq (stack_ws_alloc s.sp).symm) (by sep_focus)
    wp_done

theorem teardown_pt_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) {s : State} {R : SepProp} {cap ptr len : BitVec 64}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x2294#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x22a8#64) s
      (((s.sp + 0x290#64) ↦₆₄ cap) ∗ ((s.sp + 0x298#64) ↦₆₄ ptr) ∗ ((s.sp + 0x2a0#64) ↦₆₄ len) ∗
        (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗
        A.pool ∗ stackAt s.sp wsCalleeStack)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (((s.sp + 0x290#64) ↦₆₄ cap) ∗ ((s.sp + 0x298#64) ↦₆₄ ptr) ∗
          ((s.sp + 0x2a0#64) ↦₆₄ len) ∗ A.pool ∗ stackAt s.sp wsCalleeStack) ∗ R) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) :=
  teardown_pt_ok_ext4K hA.toAllocContracts4K hpc hrun hsp_align

set_option linter.unusedVariables false in
def ptFrameExt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (s0 : State) (sp : BitVec 64)
    (cs : Option (SessionGhost × SessionState (List (BitVec 8))))
    (x28 w20 w21 : BitVec 64) (res : Except (ApiError AddrVal Unit) (List (BitVec 8))) : SepProp :=
  wsFixedV kit ikit x s0 sp ∗
  (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗ logOff img) ∗
  wsMsgCells x sp ∗ droppableRecordAt A (sp + 0x120#64) cs ∗
  StagedRes A x28 w20 w21 (sp + 0x580#64) res ∗
  memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
  memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
  memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans)

private theorem ej_true_expose_ext (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (s0 : State) (sp : BitVec 64)
    (cs : Option (SessionGhost × SessionState (List (BitVec 8))))
    (x28 w20 w21 : BitVec 64) (res : Except (ApiError AddrVal Unit) (List (BitVec 8))) (R : SepProp) :
    (wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      droppableRecordAt A (sp + 0x120#64) cs ∗ (∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p) ∗
      StagedRes A x28 w20 w21 (sp + 0x580#64) res ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) ∗ R) ⊢
    ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ len : BitVec 64,
      ptPre A sp cap ptr len ∗ (ptFrameExt C A ctl img kit ikit x ans s0 sp cs x28 w20 w21 res ∗ R) := by
  refine Entails.trans (Entails.of_eq (show _ =
    (∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p) ∗
      (wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
        droppableRecordAt A (sp + 0x120#64) cs ∗ StagedRes A x28 w20 w21 (sp + 0x580#64) res ∗
        memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
        memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
        memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) ∗ R) by ac_rfl)) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro p
  refine Entails.trans (sepConj_mono_left (vecU8_pt_expose A (sp + 0x290#64) p)) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro cap
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro ptr
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro len
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.sepExists_right len ?_))
  unfold ptPre ptFrameExt wsEnv
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

private theorem pt_post_entails_ext (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (s0 : State) (sp : BitVec 64)
    (cs : Option (SessionGhost × SessionState (List (BitVec 8))))
    (x28 w20 w21 : BitVec 64) (res : Except (ApiError AddrVal Unit) (List (BitVec 8))) (R : SepProp)
    (cap ptr len : BitVec 64) :
    ptPost A sp cap ptr len ∗ (ptFrameExt C A ctl img kit ikit x ans s0 sp cs x28 w20 w21 res ∗ R) ⊢
      wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      droppableRecordAt A (sp + 0x120#64) cs ∗ memRegion (sp + 0x290#64) 24 ∗
      StagedRes A x28 w20 w21 (sp + 0x580#64) res ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) ∗ R := by
  have hh := header_fold (sp + 0x290#64) cap ptr len
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hh
  refine Entails.trans (Entails.of_eq (show _ =
    (((sp + 0x290#64) ↦₆₄ cap) ∗ ((sp + 0x298#64) ↦₆₄ ptr) ∗ ((sp + 0x2a0#64) ↦₆₄ len)) ∗
      (A.pool ∗ stackAt sp wsCalleeStack ∗ ptFrameExt C A ctl img kit ikit x ans s0 sp cs x28 w20 w21 res ∗ R) by
    unfold ptPost; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hh) ?_
  unfold ptFrameExt wsEnv
  exact Entails.of_eq (by ac_rfl)

attribute [local semireducible] SepWP in
theorem segErrTeardownVX_ok_ext4K {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (hyps : DecHypsExt4K img C A uuidTryParse S encRecord ext kit ikit st0 Scope)
    (hdrop2 : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt img.base A ext)
    (x : DecryptGhost) (pt : Bool) (R : SepProp) (s0 s : State)
    (hst : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x pt R s0 s) :
    DecSegVXExt img C A ctl uuidTryParse S encRecord ext kit ikit st0 ist0 Scope Extra x R s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ResultFinalStateV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x R s0 s') := by
  cases pt with
  | false => exact segErrTeardownVX_false_ext4K hyps hdrop2 hst
  | true =>
    intro hL
    rcases hst with ⟨hpc, hmeta, hx26, hx28, ans, cs, hpan, hnok, hscope, hcalls, hid_calls, htr, hm⟩
    have hmeta0 := hmeta
    rcases hmeta0 with ⟨hrun, hsp, _hsp0_al, hsp_al, _hx29, _hx27, _hfr, _hsym, _hvregs⟩
    have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
    have hpc' : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x2294#64 := by
      rw [hpc, ← entryOf_eq_tripleRatchetProgAtExt ext hyps.loads]
      try rfl
    rw [← hsp] at hx26 hm
    simp only [↓reduceIte] at hm
    let R' : SepProp :=
      decStoreExtra kit ikit
        (kit.storeFinal st0 ans (x.model C S uuidTryParse ans).2)
        (ikit.idFinal ist0 ans (x.model C S uuidTryParse ans).2) s0 ∗ R
    have hm_r' : s.mem ⊨ wsFixedV kit ikit x s0 s.sp ∗ wsEnv A img x s.sp ∗ wsMsgCells x s.sp ∗
        droppableRecordAt A (s.sp + 0x120#64) cs ∗ (∃∗ p : List (BitVec 8), vecU8 A (s.sp + 0x290#64) p) ∗
        StagedRes A (s.readReg64 .x28) (s.readReg64 .x20) (s.readReg64 .x21) (s.sp + 0x580#64)
          (x.model C S uuidTryParse ans).1 ∗
        memRegion s.sp 0xa0 ∗ memRegion (s.sp + 0x2a8#64) 0x20 ∗ memRegion (s.sp + 0x2d0#64) 0x10 ∗
        memRegion (s.sp + 0x300#64) 0x280 ∗ memRegion (s.sp + 0x5a4#64) 0x85c ∗
        memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) ∗ R' := hm
    have hm_pre := Satisfies.mono (ej_true_expose_ext C A ctl img kit ikit x ans s0 s.sp cs _ _ _ _ R') hm_r'
    simp only [satisfies_sepExists] at hm_pre
    rcases hm_pre with ⟨cap, ptr, len, hm_pre⟩
    obtain ⟨s1, hsteps1, ⟨hpc1, hrun1, P_f, hm1, hpost1⟩ | ⟨_, _hoom⟩⟩ :=
      teardown_pt_ok_ext4K (cap := cap) (ptr := ptr) (len := len)
        (R := ptFrameExt C A ctl img kit ikit x ans s0 s.sp cs (s.readReg64 .x28) (s.readReg64 .x20)
          (s.readReg64 .x21) (x.model C S uuidTryParse ans).1 ∗ R')
        hyps.alloc hpc' hrun hsp_align
        (ptFrameExt C A ctl img kit ikit x ans s0 s.sp cs (s.readReg64 .x28) (s.readReg64 .x20)
          (s.readReg64 .x21) (x.model C S uuidTryParse ans).1 ∗ R') hm_pre hL
    rotate_left
    · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
    obtain ⟨hm1', hsp1, htr1, hx28_1, hx20_1, hx21_1, hx26_1, hx27_1, hx29_1, hvregs_1⟩ := hpost1 hm1
    have hmeta1 := wsMeta_of_steps hmeta hsteps1 hrun1 hsp1 hx29_1 hx27_1 hvregs_1
    have hm1_f := Satisfies.mono
      (pt_post_entails_ext C A ctl img kit ikit x ans s0 s.sp cs _ _ _ _ R' cap ptr len) hm1'
    have hst1 : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x false R s0 s1 := by
      refine ⟨?_, hmeta1, ?_, ?_, ans, cs, hpan, hnok, hscope, hcalls, hid_calls, ?_, ?_⟩
      · rw [hpc1, ← entryOf_eq_tripleRatchetProgAtExt ext hyps.loads]
        try rfl
      · rw [hx26_1, hx26, hsp]
      · rw [hx28_1]; exact hx28
      · rw [htr1, htr]
      · rw [hx28_1, hx20_1, hx21_1, ← hsp]
        simpa only [Bool.false_eq_true, ↓reduceIte] using hm1_f
    obtain ⟨s2, hsteps2, hout⟩ := segErrTeardownVX_false_ext4K hyps hdrop2 hst1 (hsteps1.codeLoaded hL)
    exact ⟨s2, hsteps1.trans hsteps2, hout⟩

theorem segErrTeardownVX_ok_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (hyps : DecHypsExt img C A uuidTryParse S encRecord ext kit ikit st0 Scope)
    (hdrop2 : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt img.base A ext)
    (x : DecryptGhost) (pt : Bool) (R : SepProp) (s0 s : State)
    (hst : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x pt R s0 s) :
    DecSegVXExt img C A ctl uuidTryParse S encRecord ext kit ikit st0 ist0 Scope Extra x R s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ResultFinalStateV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x R s0 s') :=
  segErrTeardownVX_ok_ext4K hyps.toDecHypsExt4K hdrop2 x pt R s0 s hst

end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT
