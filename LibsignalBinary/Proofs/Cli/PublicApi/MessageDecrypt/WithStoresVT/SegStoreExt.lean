/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.StoreSession.StoreCallSite
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAux
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegBatch1
import LibsignalBinary.Proofs.Cli.PublicApi.StoreSession.Decodes
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegStore
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WP.Apply

/-!
# Ext-Generic `SegStore` (`+0x2388 → +0x24d4 / +0x2294`)

Proves ext-generic `store_session` shim/poll and tail dispatch `segStoreVX_ok_ext` over
`tripleRatchetProgAtExt img.base ext`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegStore

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private abbrev saveErrHookRelocOff : BitVec 64 :=
  bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))

private abbrev saveErrXrefOff : BitVec 64 :=
  bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620)
    (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16)

/-! ## Decode lemmas and `segStore_tail_{ok,err}_ext` (`+0x2428 → +0x24d4 / +0x2294`) -/

gen_decodes libsignalSessionCode_tree segStoreTailExtBinCli
  [(ls_off% "libsignal_cli_ratchet::decrypt_signal" + 9172) →
     (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 9176),
   (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 9256) →
     (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 9308),
   (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 9356) →
     (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 9424)]

private theorem stack_seg_alloc (sp : BitVec 64) :
    stackAt sp storeSegStack =
      memRegion (sp - BitVec.ofNat 64 storeSegStack) (storeSegStack - allocHookStack) ∗
        stackAt sp allocHookStack := by
  have h := stackAt_split_bottom sp allocHookStack (storeSegStack - allocHookStack) (by decide)
  rwa [show allocHookStack + (storeSegStack - allocHookStack) = storeSegStack by decide] at h

private theorem stack_seg_dropLocal2 (sp : BitVec 64) :
    stackAt sp storeSegStack =
      memRegion (sp - 16416#64) (storeSegStack - FromRecordCallees.dropSessionStructureLocal2Stack) ∗
        stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack := by
  have h := stackAt_split_bottom sp FromRecordCallees.dropSessionStructureLocal2Stack
    (storeSegStack - FromRecordCallees.dropSessionStructureLocal2Stack) (by decide)
  rwa [show FromRecordCallees.dropSessionStructureLocal2Stack +
    (storeSegStack - FromRecordCallees.dropSessionStructureLocal2Stack) = storeSegStack by decide] at h

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

private def dropSessionStructureLocal2HeadSpec (A : RustAlloc) :
    Spec FromRecordCallees.DropSessionStructureGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ x.G.localIk.bytes.length ≤ x.G.localIk.cap.toNat ∧
      x.G.localIk.cap.toNat < 2 ^ 63 ∧ x.G.localIk.ptr ≠ 0⌝ ∗
      (x.ss ↦₆₄ x.G.localIk.cap) ∗ vecGhostTailAt A x.G.localIk x.ss ∗
      sessionStateAfterLocalIk A x.ss x.G x.st ∗ A.pool ∗
      stackAt s.sp FromRecordCallees.dropSessionStructureLocal2Stack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion x.ss 344 ∗ A.pool ∗
      stackAt s0.sp FromRecordCallees.dropSessionStructureLocal2Stack

private theorem drop_session_structure_local2_head_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdrop2 : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructureLocal2Name)
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

set_option maxHeartbeats 800000 in
theorem segStore_tail_ok_ext4K {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (hdrop2 : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt b A ext)
    {s : State} {R : SepProp} {prevCap prevPtr : BitVec 64} {G : SessionGhost}
    {st : SessionState (List (BitVec 8))} {v1 : BitVec 32} {v2 v3 : BitVec 64} {v4 : BitVec 32}
    {s0_580 s1_588 : BitVec 64} {s2_lo s2_hi : BitVec 32} {s3_598 : BitVec 64} {s4_5a0 : BitVec 32}
    {t0_300 t1_308 t2_310 t3_318 : BitVec 64} {t4_320 : BitVec 32}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x2428#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx28 : s.readReg64 .x28 = pollTag (.ok ())) (hx26 : s.readReg64 .x26 = s.sp + 0xa0#64)
    (hx22 : s.readReg64 .x22 = s.sp + 0x294#64) (hprev_lt : prevCap.toNat * 24 < 2 ^ 63)
    (_hprev_ptr : prevPtr ≠ 0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x24d4#64) s
      (((s.sp + 0x120#64) ↦₆₄ prevCap) ∗ ((s.sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗
        (if prevCap = 0#64 then emp else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
        sessionStateAt A (s.sp + 0x138#64) G st ∗
        ((s.sp + 0x290#64) ↦₃₂ v1) ∗ ((s.sp + 0x294#64) ↦₆₄ v2) ∗ ((s.sp + 0x29c#64) ↦₆₄ v3) ∗ ((s.sp + 0x2a4#64) ↦₃₂ v4) ∗
        ((s.sp + 0x300#64) ↦₆₄ t0_300) ∗ ((s.sp + 0x308#64) ↦₆₄ t1_308) ∗ ((s.sp + 0x310#64) ↦₆₄ t2_310) ∗
        ((s.sp + 0x318#64) ↦₆₄ t3_318) ∗ ((s.sp + 0x320#64) ↦₃₂ t4_320) ∗
        ((s.sp + 0x580#64) ↦₆₄ s0_580) ∗ ((s.sp + 0x588#64) ↦₆₄ s1_588) ∗ ((s.sp + 0x590#64) ↦₃₂ s2_lo) ∗
        ((s.sp + 0x594#64) ↦₃₂ s2_hi) ∗ ((s.sp + 0x598#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x5a0#64) ↦₃₂ s4_5a0) ∗
        A.pool ∗ stackAt s.sp storeSegStack)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (((s.sp + 0x120#64) ↦₆₄ prevCap) ∗ ((s.sp + 0x128#64) ↦₆₄ prevPtr) ∗
          ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗ memRegion (s.sp + 0x138#64) 344 ∗
          ((s.sp + 0x290#64) ↦₃₂ v1) ∗ ((s.sp + 0x294#64) ↦₆₄ v2) ∗ ((s.sp + 0x29c#64) ↦₆₄ v3) ∗ ((s.sp + 0x2a4#64) ↦₃₂ v4) ∗
          ((s.sp + 0x300#64) ↦₆₄ v2) ∗ ((s.sp + 0x308#64) ↦₆₄ v3) ∗ ((s.sp + 0x310#64) ↦₆₄ (s2_hi ++ v4)) ∗
          ((s.sp + 0x318#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x320#64) ↦₃₂ s4_5a0) ∗
          ((s.sp + 0x580#64) ↦₆₄ v2) ∗ ((s.sp + 0x588#64) ↦₆₄ v3) ∗ ((s.sp + 0x590#64) ↦₆₄ (s2_hi ++ v4)) ∗
          ((s.sp + 0x598#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x5a0#64) ↦₃₂ s4_5a0) ∗
          A.pool ∗ stackAt s.sp storeSegStack) ∗ R) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧ sf.readReg64 .x28 = okTagVec ∧
        sf.readReg64 .x20 = (v1 >>> 8#32).zeroExtend 64 ∧ sf.readReg64 .x21 = v1.zeroExtend 64 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName =
      num% (ls_off% "libsignal_cli_ratchet::decrypt_signal") := by
    simp only [CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName, arm64_norm]
  have hfn2 : libsignalSessionCode.fnOff
      CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructureLocal2Name =
      num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#3]") := by
    simp only [CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructureLocal2Name, arm64_norm]
  have hdrop := drop_session_structure_local2_head_ok_ext hdrop2
  have hrel : (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructureLocal2Name =
      (tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName +
        bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#3]") -
          (ls_off% "libsignal_cli_ratchet::decrypt_signal")) := by
    simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, hfn, hfn2, BitVec.add_assoc]; rfl
  rw [hrel] at hdrop; clear hrel
  have hdealloc := msgDecrypt_dealloc_ok_ext4K hA
  code_fetches_range CryptoVerification.libsignalSessionCode segStoreTailExtBinCli b
    (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli_ratchet::decrypt_signal")) 0x2428 0x38
  code_fetches_range CryptoVerification.libsignalSessionCode segStoreTailExtBinCli b
    (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli_ratchet::decrypt_signal")) 0x249c 0x38
  dsimp only [tripleRatchetProgAtExt] at hpc hdrop hdealloc ⊢
  generalize (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName = entry at *
  examples_hide_fetches; simp only [pollTag] at hx28
  wp_simp_pre [sessionStateAt_unfold_cap, sepConj_assoc, sepConj_pure_left_comm]
  apply SepWP.pure_elim; rintro ⟨hlik_len, hlik_cap, hlik_ptr⟩
  have hcmn : (G.localIk.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hlik_cap
  apply SepWP.fold (Entails.of_eq (stack_seg_dropLocal2 s.sp)) (by sep_focus)
  wp_steps
  wp_apply
  apply SepWP.fold (Entails.of_eq (stack_seg_dropLocal2 s.sp).symm) (by sep_focus)
  apply SepWP.fold (Entails.of_eq (pointsTo64_append32 s2_hi v4 (s.sp + 0x590#64)).symm) (by sep_focus)
  wp_steps
  by_cases hcap : prevCap = 0#64
  · subst hcap; simp only [beq_self_eq_true, ↓reduceIte, emp_sepConj]; wp_steps; wp_done
  · have hcap_beq : (prevCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    simp only [hcap_beq, hcap, ↓reduceIte, Bool.false_eq_true]
    apply SepWP.fold (Entails.of_eq (stack_seg_alloc s.sp)) (by sep_focus)
    wp_steps
    have hmul := prevCap_ubfm_eq hprev_lt
    wp_apply
    simp only [hsp_sf] at hsp_sf_1 ⊢
    apply SepWP.fold (Entails.of_eq (stack_seg_alloc s.sp).symm) (by sep_focus)
    wp_steps; wp_done

theorem segStore_tail_ok_ext {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (hdrop2 : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt b A ext)
    {s : State} {R : SepProp} {prevCap prevPtr : BitVec 64} {G : SessionGhost}
    {st : SessionState (List (BitVec 8))} {v1 : BitVec 32} {v2 v3 : BitVec 64} {v4 : BitVec 32}
    {s0_580 s1_588 : BitVec 64} {s2_lo s2_hi : BitVec 32} {s3_598 : BitVec 64} {s4_5a0 : BitVec 32}
    {t0_300 t1_308 t2_310 t3_318 : BitVec 64} {t4_320 : BitVec 32}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x2428#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx28 : s.readReg64 .x28 = pollTag (.ok ())) (hx26 : s.readReg64 .x26 = s.sp + 0xa0#64)
    (hx22 : s.readReg64 .x22 = s.sp + 0x294#64) (hprev_lt : prevCap.toNat * 24 < 2 ^ 63) (_hprev_ptr : prevPtr ≠ 0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x24d4#64) s
      (((s.sp + 0x120#64) ↦₆₄ prevCap) ∗ ((s.sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗
        (if prevCap = 0#64 then emp else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
        sessionStateAt A (s.sp + 0x138#64) G st ∗
        ((s.sp + 0x290#64) ↦₃₂ v1) ∗ ((s.sp + 0x294#64) ↦₆₄ v2) ∗ ((s.sp + 0x29c#64) ↦₆₄ v3) ∗ ((s.sp + 0x2a4#64) ↦₃₂ v4) ∗
        ((s.sp + 0x300#64) ↦₆₄ t0_300) ∗ ((s.sp + 0x308#64) ↦₆₄ t1_308) ∗ ((s.sp + 0x310#64) ↦₆₄ t2_310) ∗
        ((s.sp + 0x318#64) ↦₆₄ t3_318) ∗ ((s.sp + 0x320#64) ↦₃₂ t4_320) ∗
        ((s.sp + 0x580#64) ↦₆₄ s0_580) ∗ ((s.sp + 0x588#64) ↦₆₄ s1_588) ∗ ((s.sp + 0x590#64) ↦₃₂ s2_lo) ∗
        ((s.sp + 0x594#64) ↦₃₂ s2_hi) ∗ ((s.sp + 0x598#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x5a0#64) ↦₃₂ s4_5a0) ∗
        A.pool ∗ stackAt s.sp storeSegStack)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (((s.sp + 0x120#64) ↦₆₄ prevCap) ∗ ((s.sp + 0x128#64) ↦₆₄ prevPtr) ∗
          ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗ memRegion (s.sp + 0x138#64) 344 ∗
          ((s.sp + 0x290#64) ↦₃₂ v1) ∗ ((s.sp + 0x294#64) ↦₆₄ v2) ∗ ((s.sp + 0x29c#64) ↦₆₄ v3) ∗ ((s.sp + 0x2a4#64) ↦₃₂ v4) ∗
          ((s.sp + 0x300#64) ↦₆₄ v2) ∗ ((s.sp + 0x308#64) ↦₆₄ v3) ∗ ((s.sp + 0x310#64) ↦₆₄ (s2_hi ++ v4)) ∗
          ((s.sp + 0x318#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x320#64) ↦₃₂ s4_5a0) ∗
          ((s.sp + 0x580#64) ↦₆₄ v2) ∗ ((s.sp + 0x588#64) ↦₆₄ v3) ∗ ((s.sp + 0x590#64) ↦₆₄ (s2_hi ++ v4)) ∗
          ((s.sp + 0x598#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x5a0#64) ↦₃₂ s4_5a0) ∗
          A.pool ∗ stackAt s.sp storeSegStack) ∗ R) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧ sf.readReg64 .x28 = okTagVec ∧
        sf.readReg64 .x20 = (v1 >>> 8#32).zeroExtend 64 ∧ sf.readReg64 .x21 = v1.zeroExtend 64 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) :=
  segStore_tail_ok_ext4K hA.toAllocContracts4K hdrop2 hpc hrun hsp_align hx28 hx26 hx22 hprev_lt _hprev_ptr

theorem segStore_tail_err_ext {b : BitVec 64}
    {ext : String → Option (State → State)}
    {s : State} {R : SepProp} {o1 : BitVec 32} {o2 o3 o4 o5 : BitVec 64} {o6 : BitVec 32}
    {s0_580 s1_588 s2_590 s3_598 : BitVec 64} {s4_5a0 : BitVec 32}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x2428#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx28 : s.readReg64 .x28 = pollTag (.error ())) (hx21 : s.readReg64 .x21 = o1.zeroExtend 64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x2294#64) s
      (((s.sp + 0x550#64) ↦₆₄ o2) ∗ ((s.sp + 0x558#64) ↦₆₄ o3) ∗ ((s.sp + 0x560#64) ↦₆₄ o4) ∗
        ((s.sp + 0x568#64) ↦₆₄ o5) ∗ ((s.sp + 0x570#64) ↦₃₂ o6) ∗
        ((s.sp + 0x580#64) ↦₆₄ s0_580) ∗ ((s.sp + 0x588#64) ↦₆₄ s1_588) ∗ ((s.sp + 0x590#64) ↦₆₄ s2_590) ∗
        ((s.sp + 0x598#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x5a0#64) ↦₃₂ s4_5a0))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (((s.sp + 0x550#64) ↦₆₄ o2) ∗ ((s.sp + 0x558#64) ↦₆₄ o3) ∗
          ((s.sp + 0x560#64) ↦₆₄ o4) ∗ ((s.sp + 0x568#64) ↦₆₄ o5) ∗ ((s.sp + 0x570#64) ↦₃₂ o6) ∗
          ((s.sp + 0x580#64) ↦₆₄ o2) ∗ ((s.sp + 0x588#64) ↦₆₄ o3) ∗ ((s.sp + 0x590#64) ↦₆₄ o4) ∗
          ((s.sp + 0x598#64) ↦₆₄ o5) ∗ ((s.sp + 0x5a0#64) ↦₃₂ o6)) ∗ R) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧ sf.readReg64 .x28 = 0x800000000000001A#64 ∧
        sf.readReg64 .x20 = (o1 >>> 8#32).zeroExtend 64 ∧ sf.readReg64 .x21 = o1.zeroExtend 64 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName =
      num% (ls_off% "libsignal_cli_ratchet::decrypt_signal") := by
    simp only [CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName, arm64_norm]
  code_fetches_range CryptoVerification.libsignalSessionCode segStoreTailExtBinCli b
    (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli_ratchet::decrypt_signal")) 0x2428 8
  code_fetches_range CryptoVerification.libsignalSessionCode segStoreTailExtBinCli b
    (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli_ratchet::decrypt_signal")) 0x248c 16
  code_fetches_range CryptoVerification.libsignalSessionCode segStoreTailExtBinCli b
    (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli_ratchet::decrypt_signal")) 0x23d4 8
  code_fetches_range CryptoVerification.libsignalSessionCode segSaveBinCli b
    (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli_ratchet::decrypt_signal")) 0x21a0 16
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName = entry at *
  examples_hide_fetches; simp only [pollTag] at hx28; wp_steps; wp_done

/-! ## `segStore_call_wp_ext` (`+0x2388 → +0x2428`) -/

set_option maxHeartbeats 1200000 in
private theorem segStore_call_wp_ext4K {A : RustAlloc}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {img : Obj.Image}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hA : AllocContracts4K img.base A ext)
    (hkit : SessionOnlyKitOkSE kit Scope encRecord ext)
    (hb : img.base &&& 0xfff#64 = 0#64) {s : State} {R : SepProp} {self addrA : BitVec 64}
    {addr : AddrGhost} {g : RecordGhost} {record : SessionRecord (List (BitVec 8))}
    {st : kit.StoreState} {c0 c1 d0 d1 d2 d3 : BitVec 64} {d5 : BitVec 32} {Q : Prop}
    (hinv : ImgCallInv img s)
    (haddr : kit.addrOk addr.val)
    (hrecOk : kit.RecOk record)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr
      CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x2388#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hstack_lt : storeCallStack kit ≤ 2 ^ 64)
    (hfs : FsAt kit.envOk Q (tripleRatchetProgAtExt img.base ext) s) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x2428#64) s
      (((s.sp + 0xe8#64) ↦₆₄ addrA) ∗ ((s.sp + 0xf8#64) ↦₆₄ self) ∗ ((s.sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (img.base + kit.storeShimOff)) ∗
        ((img.base + kit.storeFutVtOff) ↦₆₄ᵣ (img.base + kit.storeFutDropOff)) ∗
        ((img.base + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((img.base + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((img.base + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.storePollOff)) ∗
        ((s.sp + 0x2d0#64) ↦₆₄ c0) ∗ ((s.sp + 0x2d8#64) ↦₆₄ c1) ∗
        ((s.sp + 0x550#64) ↦₆₄ d0) ∗ ((s.sp + 0x558#64) ↦₆₄ d1) ∗ ((s.sp + 0x560#64) ↦₆₄ d2) ∗
        ((s.sp + 0x568#64) ↦₆₄ d3) ∗ ((s.sp + 0x570#64) ↦₃₂ d5) ∗ memRegion (s.sp + 0x5f0#64) 48 ∗
        protocolAddressAt A addr addrA ∗ sessionRecordAt A (s.readReg64 .x26 + 0x80#64) g record ∗
        kit.storeAt self st ∗ A.pool ∗ stackAt s.sp (storeCallStack kit))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (∃∗ ans : Except Unit Unit, ∃∗ box : BitVec 64,
          ∃∗ o1 : BitVec 32, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64,
          ∃∗ o4 : BitVec 64, ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32,
          ⌜kit.storeRel st addr.val record ans ∧
            sf.readReg64 .x28 = pollTag ans ∧
            sf.trace = s.trace ++ kit.storeEvs encRecord addr.val record ans ∧
            sf.readReg64 .x21 = o1.zeroExtend 64 ∧
            storePollOutRel img.base o2 o3 o4 o5 o1 ans⌝ ∗
          ((s.sp + 0xe8#64) ↦₆₄ addrA) ∗ ((s.sp + 0xf8#64) ↦₆₄ self) ∗ ((s.sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗
          ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (img.base + kit.storeShimOff)) ∗
          ((img.base + kit.storeFutVtOff) ↦₆₄ᵣ (img.base + kit.storeFutDropOff)) ∗
          ((img.base + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
          ((img.base + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          ((img.base + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.storePollOff)) ∗
          ((s.sp + 0x2d0#64) ↦₆₄ box) ∗ ((s.sp + 0x2d8#64) ↦₆₄ (img.base + kit.storeFutVtOff)) ∗
          ((s.sp + 0x550#64) ↦₆₄ o2) ∗ ((s.sp + 0x558#64) ↦₆₄ o3) ∗ ((s.sp + 0x560#64) ↦₆₄ o4) ∗
          ((s.sp + 0x568#64) ↦₆₄ o5) ∗ ((s.sp + 0x570#64) ↦₃₂ o6) ∗
          ((s.sp + 0x5f0#64) ↦₆₄ pollTag ans) ∗ ((s.sp + 0x5f8#64) ↦₃₂ o1) ∗
          ((s.sp + 0x5fc#64) ↦₆₄ o2) ∗ ((s.sp + 0x604#64) ↦₆₄ o3) ∗ ((s.sp + 0x60c#64) ↦₆₄ o4) ∗
          ((s.sp + 0x614#64) ↦₆₄ o5) ∗ ((s.sp + 0x61c#64) ↦₃₂ o6) ∗
          protocolAddressAt A addr addrA ∗ sessionRecordAt A (s.readReg64 .x26 + 0x80#64) g record ∗
          kit.storeAt self (kit.storeUpdate st addr.val record ans) ∗
          (if ans.isOk then emp else ((img.base + saveErrHookRelocOff) ↦ᵣ storeHookStr)) ∗
          A.pool ∗ stackAt s.sp (storeCallStack kit)) ∗ R) ∧
        sf.sp = s.sp ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName =
      num% (ls_off% "libsignal_cli_ratchet::decrypt_signal") := by
    simp only [CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName, arm64_norm]
  have hshim := subroutine_ok_withStepsPost_inImage hkit.storeShim
  have hdrop := hkit.storeFutDrop
  have hdealloc := msgDecrypt_dealloc_ok_ext4K hA
  code_fetches_range CryptoVerification.libsignalSessionCode storeSessionBinCli img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli_ratchet::decrypt_signal")) 0x2388 0xa8
  dsimp only [tripleRatchetProgAtExt] at hpc hshim hdrop hdealloc hfs ⊢
  generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName = entry at *
  examples_hide_fetches
  refine SepWPp.congr_pre (by rw [stack_storeCall_to_storeShim kit s.sp hstack_lt]) ?_
  apply SepWPp.of_sepWP_inImage (mid := img.base + kit.storeShimOff) hinv
  clear hinv
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  intro hinv1
  messageDecrypt_call_panic_p_inImage hshim hinv1
    (⟨self, addrA, s.readReg64 .x26 + 0x80#64⟩ : StoreShimCall)
  clear hinv1 hshim
  apply SepWPp.of_sepWP_inImage (mid := img.base + kit.storePollOff) hinv_sf
  clear hinv_sf
  wp_simp_pre [sepConj_assoc]
  first
  | (apply SepWP.pure_elim; rintro ⟨hsteps_sh, hx1_sf, hx0_ne, hx0_al, htr_sf⟩)
  | (apply SepWP.pure_elim; intro hsteps_sh; apply SepWP.pure_elim; rintro ⟨hx1_sf, hx0_ne, hx0_al, htr_sf⟩)
  have henv : kit.envOk sf.fs.files :=
    (hfs.of_call hsteps_sh (by simp only [arm64_norm]) htr_sf).envOk_here
  clear hsteps_sh hfs
  apply SepWP.fold (Entails.of_eq (stack_storeShim_to_storePoll kit s.sp hstack_lt)) (by sep_focus)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  intro hinv2
  have hpoll := hkit.storePoll
  dsimp only [tripleRatchetProgAtExt] at hpoll
  messageDecrypt_call_panic_inImage hpoll hinv2 (⟨sf.readReg64 (Reg.gpr 0#5), s.sp + 0x5f0#64,
    ⟨addrA, addr, s.readReg64 .x26 + 0x80#64, g, record⟩⟩, self, st)
  clear hinv2 hpoll hkit
  generalize hbox : sf.readReg64 (Reg.gpr 0#5) = box at *
  simp only [hsp_sf] at hsp_sf_1 ⊢
  have hdz := kit.storeFutDrop_ne_zero hb
  have hdz' : (img.base + kit.storeFutDropOff == 0#64) = false := beq_eq_false_iff_ne.mpr hdz
  have hbs := kit.storeBoxSize_ne_zero
  have hbs' : (BitVec.ofNat 64 kit.storeBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs
  have hbs_toNat : (BitVec.ofNat 64 kit.storeBoxSize).toNat = kit.storeBoxSize :=
    Nat.mod_eq_of_lt kit.storeBoxSize_lt
  rcases w with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · dsimp only [storePollOutAt]
    wp_simp_pre [ProofLib.memRegion_eight,
      sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    apply SepWP.exists_elim; intro w5
    apply SepWP.fold
      (Entails.of_eq (out_repack_sp s.sp (img.base + saveErrHookRelocOff) 10#64 1#64 (img.base + saveErrXrefOff) w5))
      (by sep_focus)
    wp_steps
    wp_apply
    wp_steps
    apply SepWP.fold (kit.storeBoxAt_memRegion box self addrA (s.readReg64 (Reg.gpr 26#5) + 128#64) 1#8) (by sep_focus)
    apply SepWP.fold (Entails.of_eq (stack_storePoll_to_alloc kit s.sp hstack_lt)) (by sep_focus)
    wp_apply
    simp only [h_22, hsp_sf_1] at hsp_sf_2 ⊢
    apply SepWP.fold (Entails.of_eq (stack_alloc_to_storeCall kit s.sp hstack_lt)) (by sep_focus)
    simp only [show (9223372036854775834#64 : BitVec 64) = pollTag (.error ()) from rfl,
      storePollOutRel] at *
    apply SepWP.done (by simp_all) (by simp_all)
    refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
    refine Entails.sepExists_right (.error ())
      (Entails.sepExists_right box
      (Entails.sepExists_right ((img.base + saveErrHookRelocOff).extractLsb' 0 32)
      (Entails.sepExists_right (10#32 ++ (img.base + saveErrHookRelocOff).extractLsb' 32 32)
      (Entails.sepExists_right 4294967296#64
      (Entails.sepExists_right ((img.base + saveErrXrefOff).extractLsb' 0 32 ++ 0#32)
      (Entails.sepExists_right (w5.extractLsb' 0 32 ++ (img.base + saveErrXrefOff).extractLsb' 32 32)
      (Entails.sepExists_right (w5.extractLsb' 32 32) ?_)))))))
    refine Entails.pure_right (by simp_all [saveErrHookRelocOff, saveErrXrefOff]; exact BitVec.extractLsb'_append_eq_right) ?_
    dsimp only [Except.isOk, Except.toBool, saveErrHookRelocOff, saveErrXrefOff]
    simp only [Bool.false_eq_true, ↓reduceIte, BitVec.add_assoc]
    exact Entails.of_eq (by ac_rfl)
  · dsimp only [storePollOutAt]
    have hm40 : memRegion (s.sp + 1528#64) 40 =
        ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
          ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
          ((s.sp + 1528#64) ↦₆₄ w5) ∗ ((s.sp + 1536#64) ↦₆₄ w4) ∗
            ((s.sp + 1544#64) ↦₆₄ w3) ∗ ((s.sp + 1552#64) ↦₆₄ w2) ∗
            ((s.sp + 1560#64) ↦₆₄ w1) := by
      rw [show (40 : Nat) = 8 + (8 + (8 + (8 + 8))) from rfl,
        memRegion_split (s.sp + 1528#64) 8 32 (by decide),
        memRegion_split (s.sp + 1528#64 + 8#64) 8 24 (by decide),
        memRegion_split (s.sp + 1528#64 + 8#64 + 8#64) 8 16 (by decide),
        memRegion_split (s.sp + 1528#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
        ProofLib.memRegion_eight, ProofLib.memRegion_eight]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    wp_simp_pre [BitVec.add_assoc, BitVec.reduceAdd, hm40, sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w2
    apply SepWP.exists_elim; intro w3; apply SepWP.exists_elim; intro w4
    apply SepWP.exists_elim; intro w5
    apply SepWP.fold
      (Entails.of_eq (out_repack_sp s.sp w5 w4 w3 w2 w1))
      (by sep_focus)
    wp_steps
    wp_apply
    wp_steps
    apply SepWP.fold (kit.storeBoxAt_memRegion box self addrA (s.readReg64 (Reg.gpr 26#5) + 128#64) 1#8) (by sep_focus)
    apply SepWP.fold (Entails.of_eq (stack_storePoll_to_alloc kit s.sp hstack_lt)) (by sep_focus)
    wp_apply
    simp only [h_22, hsp_sf_1] at hsp_sf_2 ⊢
    apply SepWP.fold (Entails.of_eq (stack_alloc_to_storeCall kit s.sp hstack_lt)) (by sep_focus)
    simp only [show (bv% (2 ^ 64 - 2) : BitVec 64) = pollTag (.ok ()) from rfl,
      storePollOutRel] at *
    apply SepWP.done (by simp_all) (by simp_all)
    refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
    refine Entails.sepExists_right (.ok ())
      (Entails.sepExists_right box
      (Entails.sepExists_right (w5.extractLsb' 0 32)
      (Entails.sepExists_right (w4.extractLsb' 0 32 ++ w5.extractLsb' 32 32)
      (Entails.sepExists_right (w3.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
      (Entails.sepExists_right (w2.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
      (Entails.sepExists_right (w1.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
      (Entails.sepExists_right (w1.extractLsb' 32 32) ?_)))))))
    refine Entails.pure_right (by simp_all) ?_
    dsimp only [Except.isOk, Except.toBool]
    simp only [↓reduceIte, emp_sepConj, BitVec.add_assoc]
    exact Entails.of_eq (by ac_rfl)

private theorem segStore_call_wp_ext {A : RustAlloc}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {img : Obj.Image}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hA : AllocContracts img.base A ext) (hkit : SessionOnlyKitOkSE kit Scope encRecord ext)
    (hb : img.base &&& 0xfff#64 = 0#64) {s : State} {R : SepProp} {self addrA : BitVec 64}
    {addr : AddrGhost} {g : RecordGhost} {record : SessionRecord (List (BitVec 8))}
    {st : kit.StoreState} {c0 c1 d0 d1 d2 d3 : BitVec 64} {d5 : BitVec 32} {Q : Prop}
    (hinv : ImgCallInv img s) (haddr : kit.addrOk addr.val) (hrecOk : kit.RecOk record)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x2388#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hstack_lt : storeCallStack kit ≤ 2 ^ 64)
    (hfs : FsAt kit.envOk Q (tripleRatchetProgAtExt img.base ext) s) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x2428#64) s
      (((s.sp + 0xe8#64) ↦₆₄ addrA) ∗ ((s.sp + 0xf8#64) ↦₆₄ self) ∗ ((s.sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (img.base + kit.storeShimOff)) ∗
        ((img.base + kit.storeFutVtOff) ↦₆₄ᵣ (img.base + kit.storeFutDropOff)) ∗
        ((img.base + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((img.base + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((img.base + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.storePollOff)) ∗
        ((s.sp + 0x2d0#64) ↦₆₄ c0) ∗ ((s.sp + 0x2d8#64) ↦₆₄ c1) ∗
        ((s.sp + 0x550#64) ↦₆₄ d0) ∗ ((s.sp + 0x558#64) ↦₆₄ d1) ∗ ((s.sp + 0x560#64) ↦₆₄ d2) ∗
        ((s.sp + 0x568#64) ↦₆₄ d3) ∗ ((s.sp + 0x570#64) ↦₃₂ d5) ∗ memRegion (s.sp + 0x5f0#64) 48 ∗
        protocolAddressAt A addr addrA ∗ sessionRecordAt A (s.readReg64 .x26 + 0x80#64) g record ∗
        kit.storeAt self st ∗ A.pool ∗ stackAt s.sp (storeCallStack kit))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (∃∗ ans : Except Unit Unit, ∃∗ box : BitVec 64,
          ∃∗ o1 : BitVec 32, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64,
          ∃∗ o4 : BitVec 64, ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32,
          ⌜kit.storeRel st addr.val record ans ∧ sf.readReg64 .x28 = pollTag ans ∧
            sf.trace = s.trace ++ kit.storeEvs encRecord addr.val record ans ∧
            sf.readReg64 .x21 = o1.zeroExtend 64 ∧ storePollOutRel img.base o2 o3 o4 o5 o1 ans⌝ ∗
          ((s.sp + 0xe8#64) ↦₆₄ addrA) ∗ ((s.sp + 0xf8#64) ↦₆₄ self) ∗ ((s.sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗
          ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (img.base + kit.storeShimOff)) ∗
          ((img.base + kit.storeFutVtOff) ↦₆₄ᵣ (img.base + kit.storeFutDropOff)) ∗
          ((img.base + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
          ((img.base + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          ((img.base + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.storePollOff)) ∗
          ((s.sp + 0x2d0#64) ↦₆₄ box) ∗ ((s.sp + 0x2d8#64) ↦₆₄ (img.base + kit.storeFutVtOff)) ∗
          ((s.sp + 0x550#64) ↦₆₄ o2) ∗ ((s.sp + 0x558#64) ↦₆₄ o3) ∗ ((s.sp + 0x560#64) ↦₆₄ o4) ∗
          ((s.sp + 0x568#64) ↦₆₄ o5) ∗ ((s.sp + 0x570#64) ↦₃₂ o6) ∗
          ((s.sp + 0x5f0#64) ↦₆₄ pollTag ans) ∗ ((s.sp + 0x5f8#64) ↦₃₂ o1) ∗
          ((s.sp + 0x5fc#64) ↦₆₄ o2) ∗ ((s.sp + 0x604#64) ↦₆₄ o3) ∗ ((s.sp + 0x60c#64) ↦₆₄ o4) ∗
          ((s.sp + 0x614#64) ↦₆₄ o5) ∗ ((s.sp + 0x61c#64) ↦₃₂ o6) ∗
          protocolAddressAt A addr addrA ∗ sessionRecordAt A (s.readReg64 .x26 + 0x80#64) g record ∗
          kit.storeAt self (kit.storeUpdate st addr.val record ans) ∗
          (if ans.isOk then emp else ((img.base + saveErrHookRelocOff) ↦ᵣ storeHookStr)) ∗
          A.pool ∗ stackAt s.sp (storeCallStack kit)) ∗ R) ∧
        sf.sp = s.sp ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) :=
  segStore_call_wp_ext4K hA.toAllocContracts4K hkit hb hinv haddr hrecOk hpc hrun hsp_align hstack_lt hfs

/-! ## Framing and entailment helpers -/

private def wsStoreFrameExt (C : Crypto) (A : RustAlloc)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (ist : ikit.IdState) (pt : List (BitVec 8)) : SepProp :=
  wsStoreFixedRest A img kit ikit x s0 sp ist ∗ wsMsgCells x sp ∗
  vecU8 A (sp + 0x290#64) pt ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion sp 0xa0 ∗
  (memRegion (sp + 0x300#64) 0x250 ∗ memRegion (sp + 0x574#64) 0xc) ∗
  memRegion (sp + 0x580#64) 0x24 ∗
  (memRegion (sp + 0x5a4#64) 0x4c ∗ memRegion (sp + 0x620#64) 0x7e0) ∗
  memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans)

private theorem storeCall_entails_storeCallPre_ext (C : Crypto) (A : RustAlloc)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp r26 : BitVec 64) (st : kit.StoreState) (ist : ikit.IdState)
    (rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (hsp : sp = s0.sp - 0xee0#64) (hr26 : r26 = sp + 0xa0#64) :
    (wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ memRegion (sp + 0x2a8#64) 0x20 ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x300#64) 0xb00 ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) ∗
      decStoreExtra kit ikit st ist s0) ⊢
    ∃∗ g : RecordGhost, ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64,
    ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64, ∃∗ d5 : BitVec 32,
      ⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
      wsStoreCallPre A img kit x s0 sp r26 g rec' st c0 c1 d0 d1 d2 d3 d5 ∗
      wsStoreFrameExt C A img kit ikit x ans s0 sp ist pt := by
  subst hr26
  refine Entails.trans (Entails.of_eq (show _ =
    (wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ decStoreExtra kit ikit st ist s0) ∗
    (wsMsgCells x sp ∗ (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ memRegion (sp + 0x2a8#64) 0x20 ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x300#64) 0xb00 ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans)) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left
    (wsFixed_wsEnv_store_split A img kit ikit x s0 sp st ist hsp)) ?_
  rw [sepConj_assoc (⌜_⌝)]
  apply Entails.pure_left; intro hbound
  rw [memRegion_300_b00_split, memRegion_300_280_store_split, memRegion_5a4_85c_split]
  refine Entails.trans (Entails.of_eq (show _ =
    (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      (memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x550#64) 0x24) ∗
      (wsStoreFixedEnv A img kit x s0 sp st ∗ memRegion (sp + 0x5f0#64) 48 ∗
        wsStoreFrameExt C A img kit ikit x ans s0 sp ist pt) by
    unfold wsStoreFrameExt; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left (sepConj_mono
    (memRegion_16_entails_cells (sp + 0x2d0#64))
    (memRegion_36_entails_cells (sp + 0x550#64))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro d0; apply Entails.sepExists_elim; intro d1
  apply Entails.sepExists_elim; intro d2; apply Entails.sepExists_elim; intro d3
  apply Entails.sepExists_elim; intro d5; apply Entails.sepExists_elim; intro c0
  apply Entails.sepExists_elim; intro c1; apply Entails.sepExists_elim; intro g
  refine Entails.sepExists_right g (Entails.sepExists_right c0 (Entails.sepExists_right c1
    (Entails.sepExists_right d0 (Entails.sepExists_right d1
      (Entails.sepExists_right d2 (Entails.sepExists_right d3
        (Entails.sepExists_right d5 (Entails.pure_right hbound ?_))))))))
  unfold wsStoreCallPre wsStoreFixedEnv
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

private def wsStorePostCommonRestExt (C : Crypto) (A : RustAlloc)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (st : kit.StoreState) (ist : ikit.IdState)
    (pt : List (BitVec 8)) : SepProp :=
  wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
  vecU8 A (sp + 0x290#64) pt ∗ memRegion sp 0xa0 ∗
  memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
  (memRegion (sp + 0x300#64) 0x250 ∗ memRegion (sp + 0x574#64) 0xc) ∗
  memRegion (sp + 0x5a4#64) 0x85c ∗
  memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) ∗
  decStoreExtra kit ikit st ist s0

private theorem storeCallPost_entails_common_ext (C : Crypto) (A : RustAlloc)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp r26 : BitVec 64) (g : RecordGhost) (rec' : SessionRecord (List (BitVec 8)))
    (st : kit.StoreState) (ist : ikit.IdState) (pt : List (BitVec 8))
    (ans_store : Except Unit Unit)
    (box o2 o3 o4 o5 : BitVec 64) (o1 o6 : BitVec 32)
    (hsp : sp = s0.sp - 0xee0#64) (hr26 : r26 = sp + 0xa0#64)
    (hbound : wsStackV kit ikit ≤ s0.sp.toNat) :
    wsStoreCallPostSpatial A img kit x s0 sp r26 g rec' st ans_store box o2 o3 o4 o5 o1 o6 ∗
      wsStoreFrameExt C A img kit ikit x ans s0 sp ist pt ⊢
    (((sp + 0x550#64) ↦₆₄ o2) ∗ ((sp + 0x558#64) ↦₆₄ o3) ∗
      ((sp + 0x560#64) ↦₆₄ o4) ∗ ((sp + 0x568#64) ↦₆₄ o5) ∗
      ((sp + 0x570#64) ↦₃₂ o6)) ∗
    memRegion (sp + 0x580#64) 0x24 ∗
    (if ans_store.isOk then emp else ((img.base + saveErrHookRelocOff) ↦ᵣ storeHookStr)) ∗
    sessionRecordAt A (sp + 0x120#64) g rec' ∗
    wsStorePostCommonRestExt C A img kit ikit x ans s0 sp st ist pt := by
  subst hr26
  refine Entails.trans (Entails.of_eq (show _ =
    ((((sp + 0x2d0#64) ↦₆₄ box) ∗ ((sp + 0x2d8#64) ↦₆₄ (img.base + kit.storeFutVtOff))) ∗
      (((sp + 0x5f0#64) ↦₆₄ pollTag ans_store) ∗ ((sp + 0x5f8#64) ↦₃₂ o1) ∗
        ((sp + 0x5fc#64) ↦₆₄ o2) ∗ ((sp + 0x604#64) ↦₆₄ o3) ∗
        ((sp + 0x60c#64) ↦₆₄ o4) ∗ ((sp + 0x614#64) ↦₆₄ o5) ∗
        ((sp + 0x61c#64) ↦₃₂ o6))) ∗
    (wsStoreFixedEnv A img kit x s0 sp st ∗ wsStoreFixedRest A img kit ikit x s0 sp ist) ∗
    ((((sp + 0x550#64) ↦₆₄ o2) ∗ ((sp + 0x558#64) ↦₆₄ o3) ∗
      ((sp + 0x560#64) ↦₆₄ o4) ∗ ((sp + 0x568#64) ↦₆₄ o5) ∗
      ((sp + 0x570#64) ↦₃₂ o6)) ∗
      memRegion (sp + 0x580#64) 0x24 ∗
      (if ans_store.isOk then emp else ((img.base + saveErrHookRelocOff) ↦ᵣ storeHookStr)) ∗
      sessionRecordAt A (sp + 0x120#64) g rec' ∗
      wsMsgCells x sp ∗ vecU8 A (sp + 0x290#64) pt ∗ memRegion sp 0xa0 ∗
      memRegion (sp + 0x2a8#64) 0x20 ∗
      (memRegion (sp + 0x300#64) 0x250 ∗ memRegion (sp + 0x574#64) 0xc) ∗
      (memRegion (sp + 0x5a4#64) 0x4c ∗ memRegion (sp + 0x620#64) 0x7e0) ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans)) by
    unfold wsStoreCallPostSpatial wsStoreFrameExt wsStoreFixedEnv saveErrHookRelocOff
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl)) ?_
  have h16 := cells_16_entails_memRegion (sp + 0x2d0#64) box (img.base + kit.storeFutVtOff)
  have h48 := cells_48_poll_entails_memRegion (sp + 0x5f0#64) (pollTag ans_store)
    o2 o3 o4 o5 o1 o6
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h16 h48
  refine Entails.trans (sepConj_mono (sepConj_mono h16 h48)
    (sepConj_mono_left (wsFixed_wsEnv_store_join A img kit ikit x s0 sp st ist hsp hbound))) ?_
  unfold wsStorePostCommonRestExt
  rw [memRegion_5a4_85c_split]
  exact Entails.of_eq (by ac_rfl)

private theorem storePostCommon_err_entails_ext (C : Crypto) (A : RustAlloc)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (g : RecordGhost) (rec' : SessionRecord (List (BitVec 8)))
    (ses : Session (List (BitVec 8))) (hcur : rec'.currentSession = some ses)
    (st : kit.StoreState) (ist : ikit.IdState) (pt : List (BitVec 8))
    (x28 w20 w21 o2 o3 o4 o5 : BitVec 64) (o1 o6 : BitVec 32)
    (hx28 : x28 = 0x800000000000001A#64) (hw1 : resWord1 w20 w21 = o1)
    (hrel : storePollOutRel img.base o2 o3 o4 o5 o1 (.error ())) :
    ((img.base + saveErrHookRelocOff) ↦ᵣ storeHookStr) ∗
    ((((sp + 0x550#64) ↦₆₄ o2) ∗ ((sp + 0x558#64) ↦₆₄ o3) ∗
      ((sp + 0x560#64) ↦₆₄ o4) ∗ ((sp + 0x568#64) ↦₆₄ o5) ∗ ((sp + 0x570#64) ↦₃₂ o6) ∗
      ((sp + 0x580#64) ↦₆₄ o2) ∗ ((sp + 0x588#64) ↦₆₄ o3) ∗
      ((sp + 0x590#64) ↦₆₄ o4) ∗ ((sp + 0x598#64) ↦₆₄ o5) ∗ ((sp + 0x5a0#64) ↦₃₂ o6)) ∗
    sessionRecordAt A (sp + 0x120#64) g rec' ∗
    wsStorePostCommonRestExt C A img kit ikit x ans s0 sp st ist pt) ⊢
    ∃∗ G : SessionGhost,
      wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      droppableRecordAt A (sp + 0x120#64) (some (G, ses.state)) ∗
      (∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p) ∗
      StagedRes A x28 w20 w21 (sp + 0x580#64) (.error (.store ())) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) ∗
      decStoreExtra kit ikit st ist s0 := by
  have hrel' : savePollOutRel img.base o2 o3 o4 o5 o1 (.error ()) := hrel
  have hrec0 : sessionRecordAt A (sp + 0x120#64) g rec' ⊢
      ∃∗ G : SessionGhost, droppableRecordAt A (sp + 0x120#64) (some (G, ses.state)) :=
    Entails.trans (Entails.sepExists_right g (Entails.refl _))
      (sessionRecordAt_some_entails_droppable A (sp + 0x120#64) rec' ses hcur)
  refine Entails.trans (Entails.of_eq (show _ =
    sessionRecordAt A (sp + 0x120#64) g rec' ∗
    ((((sp + 0x550#64) ↦₆₄ o2) ∗ ((sp + 0x558#64) ↦₆₄ o3) ∗
      ((sp + 0x560#64) ↦₆₄ o4) ∗ ((sp + 0x568#64) ↦₆₄ o5) ∗ ((sp + 0x570#64) ↦₃₂ o6)) ∗
    ((((sp + 0x580#64) ↦₆₄ o2) ∗ ((sp + 0x588#64) ↦₆₄ o3) ∗
      ((sp + 0x590#64) ↦₆₄ o4) ∗ ((sp + 0x598#64) ↦₆₄ o5) ∗
      ((sp + 0x5a0#64) ↦₃₂ o6)) ∗ ((img.base + saveErrHookRelocOff) ↦ᵣ storeHookStr)) ∗
    vecU8 A (sp + 0x290#64) pt ∗
    (wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      (memRegion (sp + 0x300#64) 0x250 ∗ memRegion (sp + 0x574#64) 0xc) ∗
      memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) ∗
      decStoreExtra kit ikit st ist s0)) by
    unfold wsStorePostCommonRestExt; ac_rfl)) ?_
  have h36 := cells_36_entails_memRegion (sp + 0x550#64) o2 o3 o4 o5 o6
  have hst := stagedRes_storeErr_of_savePollOutRel A img.base x28 w20 w21 (sp + 0x580#64)
    o2 o3 o4 o5 o1 o6 hx28 hw1 hrel'
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h36 hst
  have hpt : vecU8 A (sp + 0x290#64) pt ⊢ ∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p :=
    Entails.sepExists_right pt (Entails.refl _)
  refine Entails.trans (sepConj_mono hrec0 (sepConj_mono h36
    (sepConj_mono hst (sepConj_mono_left hpt)))) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro G
  refine Entails.sepExists_right G ?_
  rw [memRegion_300_280_store_split]
  exact Entails.of_eq (by ac_rfl)

private def wsStoreTailOkFrameExt (C : Crypto) (A : RustAlloc)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp cap ptr : BitVec 64) (st : kit.StoreState) (ist : ikit.IdState)
    (pt : List (BitVec 8)) : SepProp :=
  wsFixedV kit ikit x s0 sp ∗
  (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗ logOff img ∗
    kit.storeAt (s0.readReg64 .x3) st ∗ ikit.identityAt (s0.readReg64 .x5) ist ∗
    memRegion (sp - BitVec.ofNat 64 (wsCalleeStackV kit ikit)) (wsCalleeStackV kit ikit - storeSegStack)) ∗
  wsMsgCells x sp ∗ vecU8BufPure A cap ptr pt ∗
  memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
  memRegion (sp + 0x324#64) 0x25c ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
  memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans)

private theorem storePostCommon_ok_pre_tail_ext (C : Crypto) (A : RustAlloc)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (g : RecordGhost) (rec' : SessionRecord (List (BitVec 8)))
    (ses : Session (List (BitVec 8))) (hcur : rec'.currentSession = some ses)
    (st : kit.StoreState) (ist : ikit.IdState)
    (pt : List (BitVec 8)) (o2 o3 o4 o5 : BitVec 64) (o6 : BitVec 32)
    (hsp : sp = s0.sp - 0xee0#64) :
    (((sp + 0x550#64) ↦₆₄ o2) ∗ ((sp + 0x558#64) ↦₆₄ o3) ∗
      ((sp + 0x560#64) ↦₆₄ o4) ∗ ((sp + 0x568#64) ↦₆₄ o5) ∗ ((sp + 0x570#64) ↦₃₂ o6)) ∗
    memRegion (sp + 0x580#64) 0x24 ∗ sessionRecordAt A (sp + 0x120#64) g rec' ∗
    wsStorePostCommonRestExt C A img kit ikit x ans s0 sp st ist pt ⊢
    ∃∗ G : SessionGhost, ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
    ∃∗ s0_580 : BitVec 64, ∃∗ s1_588 : BitVec 64, ∃∗ s2_lo : BitVec 32, ∃∗ s2_hi : BitVec 32,
    ∃∗ s3_598 : BitVec 64, ∃∗ s4_5a0 : BitVec 32,
    ∃∗ t0_300 : BitVec 64, ∃∗ t1_308 : BitVec 64, ∃∗ t2_310 : BitVec 64,
    ∃∗ t3_318 : BitVec 64, ∃∗ t4_320 : BitVec 32,
      ⌜wsStackV kit ikit ≤ s0.sp.toNat ∧ g.prevCap.toNat * 24 < 2 ^ 63 ∧ g.prevPtr ≠ 0⌝ ∗
      wsStoreTailOkPre A sp g.prevCap g.prevPtr G ses.state
        (cap.extractLsb' 0 32) (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
        ((BitVec.ofNat 64 pt.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
        ((BitVec.ofNat 64 pt.length).extractLsb' 32 32)
        s0_580 s1_588 s2_lo s2_hi s3_598 s4_5a0 t0_300 t1_308 t2_310 t3_318 t4_320 ∗
      wsStoreTailOkFrameExt C A img kit ikit x ans s0 sp cap ptr st ist pt := by
  have h550 := cells_36_entails_memRegion (sp + 0x550#64) o2 o3 o4 o5 o6
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h550
  refine Entails.trans (sepConj_mono_left h550) ?_
  unfold wsStorePostCommonRestExt
  have hrejoin :
      (memRegion (sp + 0x550#64) 0x24 ∗ memRegion (sp + 0x580#64) 0x24 ∗
        sessionRecordAt A (sp + 0x120#64) g rec' ∗
        (wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
          vecU8 A (sp + 0x290#64) pt ∗ memRegion sp 0xa0 ∗
          memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
          (memRegion (sp + 0x300#64) 0x250 ∗ memRegion (sp + 0x574#64) 0xc) ∗
          memRegion (sp + 0x5a4#64) 0x85c ∗
          memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) ∗
          decStoreExtra kit ikit st ist s0)) =
      ((stackAt sp wsCalleeStack ∗ decStoreExtra kit ikit st ist s0) ∗
        sessionRecordAt A (sp + 0x120#64) g rec' ∗ vecU8 A (sp + 0x290#64) pt ∗
        memRegion (sp + 0x300#64) 0x24 ∗ memRegion (sp + 0x580#64) 0x24 ∗
        (wsFixedV kit ikit x s0 sp ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
          protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
          logOff img ∗ A.pool ∗ wsMsgCells x sp ∗
          memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗
          memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x324#64) 0x25c ∗
          memRegion (sp + 0x5a4#64) 0x85c ∗
          memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans))) := by
    unfold wsEnv
    rw [memRegion_split (sp + 0x300#64) 0x24 0x22c (by decide),
      memRegion_split (sp + 0x324#64) 0x22c 0x30 (by decide),
      memRegion_split (sp + 0x324#64 + 0x22c#64) 0x24 0xc (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl
  rw [hrejoin]
  have hj := wsCalleeStack_join_extra kit ikit st ist s0
  rw [← hsp] at hj
  refine Entails.trans (sepConj_mono hj
    (sepConj_mono (sessionRecordAt_some_expose A (sp + 0x120#64) g rec' ses hcur)
      (sepConj_mono (vecU8_290_expose A sp pt)
        (sepConj_mono (memRegion_36_entails_cells (sp + 0x300#64))
          (sepConj_mono_left (memRegion_36_entails_cells_split16 (sp + 0x580#64))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro s0_580; apply Entails.sepExists_elim; intro s1_588
  apply Entails.sepExists_elim; intro s2_lo; apply Entails.sepExists_elim; intro s2_hi
  apply Entails.sepExists_elim; intro s3_598; apply Entails.sepExists_elim; intro s4_5a0
  apply Entails.sepExists_elim; intro t0_300; apply Entails.sepExists_elim; intro t1_308
  apply Entails.sepExists_elim; intro t2_310; apply Entails.sepExists_elim; intro t3_318
  apply Entails.sepExists_elim; intro t4_320; apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr; apply Entails.sepExists_elim; intro G
  rw [sepConj_assoc (⌜_⌝)]; apply Entails.pure_left; intro hbound
  have hn : wsCalleeStackV kit ikit ≤ 2 ^ 64 := by
    have := s0.sp.isLt; unfold wsStackV at hbound; omega
  rw [sepConj_assoc (⌜_⌝), sepConj_pure_left_comm]
  apply Entails.pure_left; intro hpure
  refine Entails.sepExists_right G (Entails.sepExists_right cap (Entails.sepExists_right ptr
    (Entails.sepExists_right s0_580 (Entails.sepExists_right s1_588 (Entails.sepExists_right s2_lo
      (Entails.sepExists_right s2_hi (Entails.sepExists_right s3_598 (Entails.sepExists_right s4_5a0
        (Entails.sepExists_right t0_300 (Entails.sepExists_right t1_308 (Entails.sepExists_right t2_310
           (Entails.sepExists_right t3_318 (Entails.sepExists_right t4_320
             (Entails.pure_right ⟨hbound, hpure⟩ ?_))))))))))))))
  unfold wsStoreTailOkPre wsStoreTailOkFrameExt
  rw [stack_wsCalleeV_storeSeg kit ikit sp hn]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by ac_rfl)

private theorem storePost_ok_entails_ext (C : Crypto) (A : RustAlloc)
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp prevCap prevPtr cap ptr : BitVec 64)
    (st : kit.StoreState) (ist : ikit.IdState) (pt : List (BitVec 8))
    (v1 : BitVec 32) (v2 v3 : BitVec 64) (v4 : BitVec 32)
    (s2_hi : BitVec 32) (s3_598 : BitVec 64) (s4_5a0 : BitVec 32)
    (x28 w20 w21 : BitVec 64) (hx28 : x28 = okTagVec)
    (hw20 : w20 = (v1 >>> 8#32).zeroExtend 64) (hw21 : w21 = v1.zeroExtend 64)
    (hv1 : v1 = cap.extractLsb' 0 32) (hv2 : v2 = ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
    (hv3 : v3 = (BitVec.ofNat 64 pt.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
    (hv4 : v4 = (BitVec.ofNat 64 pt.length).extractLsb' 32 32)
    (hsp : sp = s0.sp - 0xee0#64) (hbound : wsStackV kit ikit ≤ s0.sp.toNat) :
    wsStoreTailOkPost A sp prevCap prevPtr v1 v2 v3 v4 s2_hi s3_598 s4_5a0 ∗
      wsStoreTailOkFrameExt C A img kit ikit x ans s0 sp cap ptr st ist pt ⊢
    wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      StagedRes A x28 w20 w21 (sp + 0x300#64) (.ok pt) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x324#64) 0xadc ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) ∗
      decStoreExtra kit ikit st ist s0 := by
  subst hx28 hw20 hw21 hsp
  have h120 := memRegion_120_1a8_join (s0.sp - 0xee0#64) prevCap prevPtr v1 v2 v3 v4
  have h580 := cells_36_entails_memRegion (s0.sp - 0xee0#64 + 0x580#64) v2 v3 (s2_hi ++ v4) s3_598 s4_5a0
  have hst := stagedRes_ok_pt A (s0.sp - 0xee0#64 + 0x300#64) cap ptr pt s2_hi s3_598 s4_5a0
    v1 v2 v3 v4 hv1 hv2 hv3 hv4
  have hsplit := wsCalleeStack_split_extra kit ikit st ist s0 hbound
  have hn : wsCalleeStackV kit ikit ≤ 2 ^ 64 := by
    have := s0.sp.isLt; unfold wsStackV at hbound; omega
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h120 h580 hst
  refine Entails.trans (Entails.of_eq (show _ =
    (((s0.sp - 0xee0#64 + 0x120#64) ↦₆₄ prevCap) ∗ ((s0.sp - 0xee0#64 + 0x128#64) ↦₆₄ prevPtr) ∗
      ((s0.sp - 0xee0#64 + 0x130#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xee0#64 + 0x138#64) 344 ∗
      ((s0.sp - 0xee0#64 + 0x290#64) ↦₃₂ v1) ∗ ((s0.sp - 0xee0#64 + 0x294#64) ↦₆₄ v2) ∗ ((s0.sp - 0xee0#64 + 0x29c#64) ↦₆₄ v3) ∗
      ((s0.sp - 0xee0#64 + 0x2a4#64) ↦₃₂ v4) ∗ memRegion (s0.sp - 0xee0#64 + 0x2a8#64) 0x20) ∗
    ((((s0.sp - 0xee0#64 + 0x300#64) ↦₆₄ v2) ∗ ((s0.sp - 0xee0#64 + 0x308#64) ↦₆₄ v3) ∗
      ((s0.sp - 0xee0#64 + 0x310#64) ↦₆₄ (s2_hi ++ v4)) ∗ ((s0.sp - 0xee0#64 + 0x318#64) ↦₆₄ s3_598) ∗
      ((s0.sp - 0xee0#64 + 0x320#64) ↦₃₂ s4_5a0)) ∗ vecU8BufPure A cap ptr pt) ∗
    (((s0.sp - 0xee0#64 + 0x580#64) ↦₆₄ v2) ∗ ((s0.sp - 0xee0#64 + 0x588#64) ↦₆₄ v3) ∗
      ((s0.sp - 0xee0#64 + 0x590#64) ↦₆₄ (s2_hi ++ v4)) ∗ ((s0.sp - 0xee0#64 + 0x598#64) ↦₆₄ s3_598) ∗
      ((s0.sp - 0xee0#64 + 0x5a0#64) ↦₃₂ s4_5a0)) ∗
    (kit.storeAt (s0.readReg64 .x3) st ∗ ikit.identityAt (s0.readReg64 .x5) ist ∗
      (memRegion ((s0.sp - 0xee0#64) - BitVec.ofNat 64 (wsCalleeStackV kit ikit))
        (wsCalleeStackV kit ikit - storeSegStack) ∗
        stackAt (s0.sp - 0xee0#64) storeSegStack)) ∗
    (wsFixedV kit ikit x s0 (s0.sp - 0xee0#64) ∗
      (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ logOff img ∗ A.pool) ∗
      wsMsgCells x (s0.sp - 0xee0#64) ∗ memRegion (s0.sp - 0xee0#64) 0xa0 ∗ memRegion (s0.sp - 0xee0#64 + 0x2d0#64) 0x10 ∗
      memRegion (s0.sp - 0xee0#64 + 0x324#64) 0x25c ∗ memRegion (s0.sp - 0xee0#64 + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans)) by
    unfold wsStoreTailOkPost wsStoreTailOkFrameExt
    ac_rfl)) ?_
  rw [← stack_wsCalleeV_storeSeg kit ikit (s0.sp - 0xee0#64) hn]
  refine Entails.trans (sepConj_mono h120 (sepConj_mono hst
    (sepConj_mono h580 (sepConj_mono_left hsplit)))) ?_
  unfold wsEnv; rw [memRegion_324_adc_split (s0.sp - 0xee0#64)]
  exact Entails.of_eq (by ac_rfl)

/-! ## `segStoreVX_ok_ext` -/

attribute [local semireducible] SepWP in
set_option maxHeartbeats 1200000 in
theorem segStoreVX_ok_ext4K {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (hyps : DecHypsExt4K img C A uuidTryParse S encRecord ext kit ikit st0 Scope)
    (hdrop2 : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt img.base A ext)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State)
    (haddr : kit.addrOk x.rem.val)
    (hfs : DecFsCtxExt kit ikit ext s0 s)
    (hst : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.StoreCallStateV
      C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s) :
    DecSegVXExt img C A ctl uuidTryParse S encRecord ext kit ikit st0 ist0 Scope Extra x R s0 s
      (fun s' =>
        CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ResultFinalStateV
          C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x R s0 s' ∨
        CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV
          C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x true R s0 s') := by
  intro hL
  rcases hst with ⟨hpc, hmeta, hx26, hx22,
    rec, rec', pt, ses, k, c, hload, hscope, hdec, hcur, hrem, htrust, hsave, htrustRel, hsaveRel, htr, hm⟩
  have hfsAt : FsAt kit.envOk (kit.Quiet ∧ ikit.Quiet) (tripleRatchetProgAtExt img.base ext) s :=
    (hfs.fsAt htr fun hq => by
      obtain ⟨⟨hl, -⟩, ht, hs⟩ := hq
      simp only [NoFsEv.append_iff, hl, ht, hs, and_self]).mono (fun _ h => h.1) id
  have hmeta0 := hmeta
  rcases hmeta0 with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx27, hfr, hsym, _hvregs⟩
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads hyps.loads
  have hentry := entryOf_eq_tripleRatchetProgAtExt ext hyps.loads
    CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName
  have hpc' : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr
      CryptoVerification.Cli.LibsignalPublicApi.StoreSession.decWithStoresName + 0x2388#64 := by
    rw [← hentry, hpc]
  have hrecOk : kit.RecOk rec' := hyps.recOk x rec pt rec' haddr hscope hdec
  rw [← hsp] at hx26 hx22 hm
  let ist2 := ikit.saveUpdate (ikit.trustUpdate ist0 x.rem.val k .receiving ans.isTrustedIdentity)
    x.rem.val k ans.saveIdentity
  have hm_pre : s.mem ⊨
      (∃∗ g : RecordGhost, ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64,
        ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64, ∃∗ d5 : BitVec 32,
          ⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
          wsStoreCallPre A img kit x s0 s.sp (s.readReg64 .x26) g rec' st0 c0 c1 d0 d1 d2 d3 d5 ∗
          wsStoreFrameExt C A img kit ikit x ans s0 s.sp ist2 pt) ∗ R := by
    refine Satisfies.mono (sepConj_mono_left
      (storeCall_entails_storeCallPre_ext C A img kit ikit x ans s0 s.sp (s.readReg64 .x26)
        st0 ist2 rec' pt hsp hx26)) ?_
    simpa only [sepConj_assoc] using hm
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm_pre
  rcases hm_pre with ⟨g, c0, c1, d0, d1, d2, d3, d5, hm_pre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_pre
  rcases hm_pre with ⟨hbound, hm_pre⟩
  rw [sepConj_assoc] at hm_pre
  have hstack_lt : storeCallStack kit ≤ 2 ^ 64 := by
    have h1 := storeCallStack_le kit ikit
    have := s0.sp.isLt; unfold wsStackV at hbound; omega
  obtain ⟨sf, hsteps1, hout1⟩ :=
    segStore_call_wp_ext4K hyps.alloc hyps.kit hb
      (self := s0.readReg64 .x3) (addrA := x.remA) (addr := x.rem)
      (g := g) (record := rec') (st := st0)
      (c0 := c0) (c1 := c1) (d0 := d0) (d1 := d1) (d2 := d2) (d3 := d3) (d5 := d5)
      (R := wsStoreFrameExt C A img kit ikit x ans s0 s.sp ist2 pt ∗ R)
      ⟨hfr, hsym⟩ haddr hrecOk hpc' hrun hsp_align hstack_lt hfsAt
      (wsStoreFrameExt C A img kit ikit x ans s0 s.sp ist2 pt ∗ R) hm_pre hL
  rcases hout1 with ⟨hpc1, hrun1, P_f, hm1, hpost1⟩ | ⟨hpan1, P_f, hm1, hpan_post1⟩ | ⟨_, _hoom⟩
  · obtain ⟨hm1', hsp1, hx26_1, hx22_1, hx27_1, hx29_1, hvregs_1⟩ := hpost1 hm1
    rw [← sepConj_assoc] at hm1'
    have hm1_common : sf.mem ⊨
        (∃∗ ans_store : Except Unit Unit,
          ∃∗ o1 : BitVec 32, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64, ∃∗ o4 : BitVec 64,
          ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32,
          ⌜kit.storeRel st0 x.rem.val rec' ans_store ∧
            sf.readReg64 .x28 = pollTag ans_store ∧
            sf.trace = s.trace ++ kit.storeEvs encRecord x.rem.val rec' ans_store ∧
            sf.readReg64 .x21 = o1.zeroExtend 64 ∧
            storePollOutRel img.base o2 o3 o4 o5 o1 ans_store⌝ ∗
          (((s.sp + 0x550#64) ↦₆₄ o2) ∗ ((s.sp + 0x558#64) ↦₆₄ o3) ∗
            ((s.sp + 0x560#64) ↦₆₄ o4) ∗ ((s.sp + 0x568#64) ↦₆₄ o5) ∗ ((s.sp + 0x570#64) ↦₃₂ o6)) ∗
          memRegion (s.sp + 0x580#64) 0x24 ∗
          (if ans_store.isOk then emp else ((img.base + saveErrHookRelocOff) ↦ᵣ storeHookStr)) ∗
          sessionRecordAt A (s.sp + 0x120#64) g rec' ∗
          wsStorePostCommonRestExt C A img kit ikit x ans s0 s.sp
            (kit.storeUpdate st0 x.rem.val rec' ans_store) ist2 pt) ∗ R := by
      refine Satisfies.mono (sepConj_mono_left ?_) hm1'
      simp only [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro ans_store; apply Entails.sepExists_elim; intro box
      apply Entails.sepExists_elim; intro o1; apply Entails.sepExists_elim; intro o2
      apply Entails.sepExists_elim; intro o3; apply Entails.sepExists_elim; intro o4
      apply Entails.sepExists_elim; intro o5; apply Entails.sepExists_elim; intro o6
      rw [sepConj_assoc]; apply Entails.pure_left; intro hpure
      refine Entails.sepExists_right ans_store (Entails.sepExists_right o1
        (Entails.sepExists_right o2 (Entails.sepExists_right o3
          (Entails.sepExists_right o4 (Entails.sepExists_right o5
            (Entails.sepExists_right o6 (Entails.pure_right hpure ?_)))))))
      exact storeCallPost_entails_common_ext C A img kit ikit x ans s0 s.sp (s.readReg64 .x26) g rec'
        (kit.storeUpdate st0 x.rem.val rec' ans_store) ist2 pt
        ans_store box o2 o3 o4 o5 o1 o6 hsp hx26 hbound
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1_common
    rcases hm1_common with ⟨ans_store, o1, o2, o3, o4, o5, o6, hm1_common⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1_common
    rcases hm1_common with ⟨⟨hstoreRel, hx28_1, htr1, hx21_1, hrel1⟩, hm1_common⟩
    have hL1 := hsteps1.codeLoaded hL
    rcases ans_store with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
    · let st1 := kit.storeUpdate st0 x.rem.val rec' (.error ())
      simp only [Except.isOk, Except.toBool, Bool.false_eq_true, ↓reduceIte] at hm1_common
      have hm1_err : sf.mem ⊨
          (∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64, ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 32,
            (((sf.sp + 0x550#64) ↦₆₄ o2) ∗ ((sf.sp + 0x558#64) ↦₆₄ o3) ∗
              ((sf.sp + 0x560#64) ↦₆₄ o4) ∗ ((sf.sp + 0x568#64) ↦₆₄ o5) ∗ ((sf.sp + 0x570#64) ↦₃₂ o6) ∗
              ((sf.sp + 0x580#64) ↦₆₄ e0) ∗ ((sf.sp + 0x588#64) ↦₆₄ e1) ∗ ((sf.sp + 0x590#64) ↦₆₄ e2) ∗
              ((sf.sp + 0x598#64) ↦₆₄ e3) ∗ ((sf.sp + 0x5a0#64) ↦₃₂ e4)) ∗
            (((img.base + saveErrHookRelocOff) ↦ᵣ storeHookStr) ∗
              sessionRecordAt A (s.sp + 0x120#64) g rec' ∗
              wsStorePostCommonRestExt C A img kit ikit x ans s0 s.sp st1 ist2 pt)) ∗ R := by
        rw [hsp1]; refine Satisfies.mono (sepConj_mono_left ?_) hm1_common
        refine Entails.trans (sepConj_mono_right
          (sepConj_mono_left (memRegion_36_entails_cells (s.sp + 0x580#64)))) ?_
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        apply Entails.sepExists_elim; intro e0; apply Entails.sepExists_elim; intro e1
        apply Entails.sepExists_elim; intro e2; apply Entails.sepExists_elim; intro e3
        apply Entails.sepExists_elim; intro e4
        refine Entails.sepExists_right e0 (Entails.sepExists_right e1
          (Entails.sepExists_right e2 (Entails.sepExists_right e3
            (Entails.sepExists_right e4 ?_))))
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; exact Entails.refl _
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1_err
      rcases hm1_err with ⟨e0, e1, e2, e3, e4, hm1_err⟩
      rw [sepConj_assoc] at hm1_err
      obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hpost2⟩ | ⟨_, _hoom⟩⟩ :=
        segStore_tail_err_ext
          (R := (((img.base + saveErrHookRelocOff) ↦ᵣ storeHookStr) ∗
            sessionRecordAt A (s.sp + 0x120#64) g rec' ∗
            wsStorePostCommonRestExt C A img kit ikit x ans s0 s.sp st1 ist2 pt) ∗ R)
          hpc1 hrun1 (hsp1 ▸ hsp_align) hx28_1 hx21_1
          ((((img.base + saveErrHookRelocOff) ↦ᵣ storeHookStr) ∗
            sessionRecordAt A (s.sp + 0x120#64) g rec' ∗
            wsStorePostCommonRestExt C A img kit ikit x ans s0 s.sp st1 ist2 pt) ∗ R) hm1_err hL1
      rotate_left
      · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
      obtain ⟨hm2', hsp2, htr2, hx28_2, hx20_2, hx21_2, hx26_2, hx27_2, hx29_2, hvregs_2⟩ := hpost2 hm2
      have hsteps12 := hsteps1.trans hsteps2
      have hmeta2 := wsMeta_of_steps hmeta hsteps12 hrun2 (hsp2.trans hsp1)
        (hx29_2.trans hx29_1) (hx27_2.trans hx27_1) (hvregs_2.trans hvregs_1)
      rw [hsp1] at hm2'
      have hm2_ro : sf2.mem ⊨
          (((img.base + saveErrHookRelocOff) ↦ᵣ storeHookStr) ∗
            ((((s.sp + 0x550#64) ↦₆₄ o2) ∗ ((s.sp + 0x558#64) ↦₆₄ o3) ∗
              ((s.sp + 0x560#64) ↦₆₄ o4) ∗ ((s.sp + 0x568#64) ↦₆₄ o5) ∗ ((s.sp + 0x570#64) ↦₃₂ o6) ∗
              ((s.sp + 0x580#64) ↦₆₄ o2) ∗ ((s.sp + 0x588#64) ↦₆₄ o3) ∗
              ((s.sp + 0x590#64) ↦₆₄ o4) ∗ ((s.sp + 0x598#64) ↦₆₄ o5) ∗ ((s.sp + 0x5a0#64) ↦₃₂ o6)) ∗
            sessionRecordAt A (s.sp + 0x120#64) g rec' ∗
            wsStorePostCommonRestExt C A img kit ikit x ans s0 s.sp st1 ist2 pt)) ∗ R :=
        Eq.mp (congrArg (sf2.mem ⊨ ·) (by ac_rfl)) hm2'
      have hw1 : resWord1 (sf2.readReg64 .x20) (sf2.readReg64 .x21) = o1 := by
        rw [hx20_2, hx21_2, resWord1_lsr8]
      have hm2_err := Satisfies.mono (sepConj_mono_left
        (storePostCommon_err_entails_ext C A img kit ikit x ans s0 s.sp g rec' ses hcur
          st1 ist2 pt (sf2.readReg64 .x28) (sf2.readReg64 .x20) (sf2.readReg64 .x21)
          o2 o3 o4 o5 o1 o6 hx28_2 hw1 hrel1)) hm2_ro
      rw [sepExists_sepConj_left, satisfies_sepExists] at hm2_err
      rcases hm2_err with ⟨G, hm2_err⟩
      refine ⟨sf2, hsteps12, Or.inl (Or.inr ?_)⟩
      have hmod := model_of_store_err C S x
        { ans with storeSession := .error () } rec rec' pt ses k c
        hload hscope.1 hdec hcur hrem htrust hsave rfl
      have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
        (ans' := { ans with storeSession := .error () }) (ans := ans) rfl
      refine ⟨?_, hmeta2, ?_, ?_, { ans with storeSession := .error () }, some (G, ses.state),
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hpc2, ← hentry]; rfl
      · rw [hx26_2, hx26_1, hx26, hsp]
      · rw [hx28_2]; decide
      · rw [hmod.1]; decide
      · intro p; rw [hmod.1]; exact nofun
      · intro r hr; dsimp only at hr; rw [hload] at hr; cases hr; exact hscope
      · rw [hmod.2]; exact ⟨hload ▸ hscope.2, hstoreRel, trivial⟩
      · rw [hmod.2]; exact ⟨htrustRel, hsaveRel, trivial⟩
      · rw [htr2, htr1, htr, hmod.2, Identity.IdentityStoreSpec.traceOfWith_all4]
        simp only [List.append_assoc]
      · rw [hmod.1, hmod.2, hdraws]
        dsimp only [SessionStoreSpec.storeFinal, Identity.IdentityStoreSpec.idFinal]
        simpa only [ite_true, hsp, sepConj_assoc] using hm2_err
    · let st1 := kit.storeUpdate st0 x.rem.val rec' (.ok ())
      simp only [Except.isOk, Except.toBool, ↓reduceIte, emp_sepConj] at hm1_common
      have hm1_ok := Satisfies.mono (sepConj_mono_left
        (storePostCommon_ok_pre_tail_ext C A img kit ikit x ans s0 s.sp g rec' ses hcur
          st1 ist2 pt o2 o3 o4 o5 o6 hsp)) hm1_common
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1_ok
      rcases hm1_ok with ⟨G, cap, ptr, s0_580, s1_588, s2_lo, s2_hi, s3_598, s4_5a0,
        t0_300, t1_308, t2_310, t3_318, t4_320, hm1_ok⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hm1_ok
      rcases hm1_ok with ⟨⟨_, hprev_lt, hprev_ptr⟩, hm1_ok⟩
      rw [sepConj_assoc, ← hsp1] at hm1_ok
      have hx26_sf : sf.readReg64 .x26 = sf.sp + 0xa0#64 := by rw [hx26_1, hx26, hsp1]
      have hx22_sf : sf.readReg64 .x22 = sf.sp + 0x294#64 := by rw [hx22_1, hx22, hsp1]
      obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hpost2⟩ | ⟨_, _hoom⟩⟩ :=
        segStore_tail_ok_ext4K hyps.alloc hdrop2
          (R := wsStoreTailOkFrameExt C A img kit ikit x ans s0 sf.sp cap ptr st1 ist2 pt ∗ R)
          hpc1 hrun1 (hsp1 ▸ hsp_align) hx28_1 hx26_sf hx22_sf hprev_lt hprev_ptr
          (wsStoreTailOkFrameExt C A img kit ikit x ans s0 sf.sp cap ptr st1 ist2 pt ∗ R) hm1_ok hL1
      rotate_left
      · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
      obtain ⟨hm2', hsp2, htr2, hx28_2, hx20_2, hx21_2, hx27_2, hx29_2, hvregs_2⟩ := hpost2 hm2
      have hsteps12 := hsteps1.trans hsteps2
      have hmeta2 := wsMeta_of_steps hmeta hsteps12 hrun2 (hsp2.trans hsp1)
        (hx29_2.trans hx29_1) (hx27_2.trans hx27_1) (hvregs_2.trans hvregs_1)
      rw [hsp1, ← sepConj_assoc] at hm2'
      have hm2_ok := Satisfies.mono (sepConj_mono_left
        (storePost_ok_entails_ext C A img kit ikit x ans s0 s.sp g.prevCap g.prevPtr cap ptr
          st1 ist2 pt
          (cap.extractLsb' 0 32)
          (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
          ((BitVec.ofNat 64 pt.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
          ((BitVec.ofNat 64 pt.length).extractLsb' 32 32)
          s2_hi s3_598 s4_5a0 (sf2.readReg64 .x28) (sf2.readReg64 .x20) (sf2.readReg64 .x21)
          hx28_2 hx20_2 hx21_2 rfl rfl rfl rfl hsp hbound)) hm2'
      refine ⟨sf2, hsteps12, Or.inl (Or.inl ?_)⟩
      have hmod := model_of_store_ok C S x
        { ans with storeSession := .ok () } rec rec' pt ses k c
        hload hscope.1 hdec hcur hrem htrust hsave rfl
      have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
        (ans' := { ans with storeSession := .ok () }) (ans := ans) rfl
      refine ⟨?_, hmeta2, { ans with storeSession := .ok () }, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hpc2, ← hentry]
      · rw [hmod.1]; exact nofun
      · intro r hr; dsimp only at hr; rw [hload] at hr; cases hr; exact hscope
      · rw [hmod.2]; exact ⟨hload ▸ hscope.2, hstoreRel, trivial⟩
      · rw [hmod.2]; exact ⟨htrustRel, hsaveRel, trivial⟩
      · rw [htr2, htr1, htr, hmod.2, Identity.IdentityStoreSpec.traceOfWith_all4]
        simp only [List.append_assoc]
      · rw [hmod.1, hmod.2, hdraws]
        dsimp only [SessionStoreSpec.storeFinal, Identity.IdentityStoreSpec.idFinal]
        simpa only [hsp, sepConj_assoc] using hm2_ok
  · have hpan_m := hpan_post1 hm1; rw [← sepConj_assoc] at hpan_m
    have hpan_m' : sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R :=
      Satisfies.mono (sepConj_mono_left (shim_onPanic_entails rfl)) hpan_m
    exact ⟨sf, hsteps1, Or.inr (panic_outcome_of_allocFailedInVX_ext ⟨_, htr.symm⟩ hpan1 hpan_m')⟩
  · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim

theorem segStoreVX_ok_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (hyps : DecHypsExt img C A uuidTryParse S encRecord ext kit ikit st0 Scope)
    (hdrop2 : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt img.base A ext)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State)
    (haddr : kit.addrOk x.rem.val) (hfs : DecFsCtxExt kit ikit ext s0 s)
    (hst : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.StoreCallStateV
      C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s) :
    DecSegVXExt img C A ctl uuidTryParse S encRecord ext kit ikit st0 ist0 Scope Extra x R s0 s
      (fun s' =>
        CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ResultFinalStateV
          C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x R s0 s' ∨
        CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV
          C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x true R s0 s') :=
  segStoreVX_ok_ext4K hyps.toDecHypsExt4K hdrop2 x ans R s0 s haddr hfs hst

end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT
