/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegSaveAux
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Push
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts
import ProofLib.SepLogic.WP.Apply

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegStore

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
open CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Decode lemmas for D9 (`+0x2428..+0x24d4` = `0x3c8d0..0x3c97c`) -/

gen_decodes libsignalSessionCode_tree segStoreTailBin [(ls_off% "session_message_decrypt_signal" + 9172) → (ls_off% "session_message_decrypt_signal" + 9176), (ls_off% "session_message_decrypt_signal" + 9256) → (ls_off% "session_message_decrypt_signal" + 9308),
    (ls_off% "session_message_decrypt_signal" + 9356) → (ls_off% "session_message_decrypt_signal" + 9424)]

/-! ## 2. Stack Splits & Repack Helpers -/

def storeCallStack {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b) : Nat :=
  max kit.storeShimStack (max kit.storePollStack allocHookStack)

theorem storeShimStack_le_storeCall {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b) :
    kit.storeShimStack ≤ storeCallStack kit := Nat.le_max_left _ _

theorem storePollStack_le_storeCall {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b) :
    kit.storePollStack ≤ storeCallStack kit :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem allocHookStack_le_storeCall {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b) :
    allocHookStack ≤ storeCallStack kit :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

theorem storeCallStack_le {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    storeCallStack kit ≤ wsCalleeStackV kit ikit :=
  Nat.max_le.mpr ⟨storeShimStack_le_V kit ikit,
    Nat.max_le.mpr ⟨storePollStack_le_V kit ikit, allocHookStack_le_V kit ikit⟩⟩

theorem stack_storeCall_to_storeShim {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (sp : BitVec 64)
    (hn : storeCallStack kit ≤ 2 ^ 64) :
    stackAt sp (storeCallStack kit) =
      memRegion (sp - BitVec.ofNat 64 (storeCallStack kit))
        (storeCallStack kit - kit.storeShimStack) ∗
      stackAt sp kit.storeShimStack :=
  stack_wsCalleeV_sub sp (storeShimStack_le_storeCall kit) hn

theorem stack_storeShim_to_storePoll {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (sp : BitVec 64)
    (hn : storeCallStack kit ≤ 2 ^ 64) :
    memRegion (sp - BitVec.ofNat 64 (storeCallStack kit))
        (storeCallStack kit - kit.storeShimStack) ∗
      stackAt sp kit.storeShimStack =
    memRegion (sp - BitVec.ofNat 64 (storeCallStack kit))
        (storeCallStack kit - kit.storePollStack) ∗
      stackAt sp kit.storePollStack := by
  rw [← stack_storeCall_to_storeShim kit sp hn]
  exact stack_wsCalleeV_sub sp (storePollStack_le_storeCall kit) hn

theorem stack_storePoll_to_alloc {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (sp : BitVec 64)
    (hn : storeCallStack kit ≤ 2 ^ 64) :
    memRegion (sp - BitVec.ofNat 64 (storeCallStack kit))
        (storeCallStack kit - kit.storePollStack) ∗
      stackAt sp kit.storePollStack =
    memRegion (sp - BitVec.ofNat 64 (storeCallStack kit))
        (storeCallStack kit - allocHookStack) ∗
      stackAt sp allocHookStack := by
  rw [← stack_wsCalleeV_sub sp (storePollStack_le_storeCall kit) hn]
  exact stack_wsCalleeV_sub sp (allocHookStack_le_storeCall kit) hn

theorem stack_alloc_to_storeCall {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (sp : BitVec 64)
    (hn : storeCallStack kit ≤ 2 ^ 64) :
    memRegion (sp - BitVec.ofNat 64 (storeCallStack kit))
        (storeCallStack kit - allocHookStack) ∗
      stackAt sp allocHookStack =
    stackAt sp (storeCallStack kit) :=
  (stack_wsCalleeV_sub sp (allocHookStack_le_storeCall kit) hn).symm

theorem stack_wsCalleeV_storeCall {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (sp : BitVec 64) (hn : wsCalleeStackV kit ikit ≤ 2 ^ 64) :
    stackAt sp (wsCalleeStackV kit ikit) =
      memRegion (sp - BitVec.ofNat 64 (wsCalleeStackV kit ikit))
        (wsCalleeStackV kit ikit - storeCallStack kit) ∗
      stackAt sp (storeCallStack kit) :=
  stack_wsCalleeV_sub sp (storeCallStack_le kit ikit) hn

theorem stack_wsCalleeV_storeSeg {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (sp : BitVec 64) (hn : wsCalleeStackV kit ikit ≤ 2 ^ 64) :
    stackAt sp (wsCalleeStackV kit ikit) =
      memRegion (sp - BitVec.ofNat 64 (wsCalleeStackV kit ikit))
        (wsCalleeStackV kit ikit - storeSegStack) ∗
      stackAt sp storeSegStack := by
  have hle : storeSegStack ≤ wsCalleeStackV kit ikit := by
    have : storeSegStack ≤ wsCalleeStack := by decide
    unfold wsCalleeStackV; omega
  exact stack_wsCalleeV_sub sp hle hn

def storePollOutRel (b o2 o3 o4 o5 : BitVec 64) (o1 : BitVec 32) :
    Except Unit Unit → Prop
  | .ok () => True
  | .error () =>
    o1 = (b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))).extractLsb' 0 32 ∧
    o2 = 10#32 ++ (b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))).extractLsb' 32 32 ∧
    o3 = 0x100000000#64 ∧
    o4 = (b + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16)).extractLsb' 0 32 ++ 0#32 ∧
    o5.extractLsb' 0 32 = (b + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16)).extractLsb' 32 32

private theorem stack_seg_shim (sp : BitVec 64) :
    stackAt sp storeSegStack =
      memRegion (sp - BitVec.ofNat 64 storeSegStack) (storeSegStack - storeSessionShimStack) ∗
        stackAt sp storeSessionShimStack := by
  have h := stackAt_split_bottom sp storeSessionShimStack (storeSegStack - storeSessionShimStack) (by decide)
  rwa [show storeSessionShimStack + (storeSegStack - storeSessionShimStack) = storeSegStack by decide] at h

private theorem stack_seg_shim' (sp : BitVec 64) :
    memRegion (sp - 16416#64) (storeSegStack - storeSessionShimStack) ∗
        stackAt sp storeSessionShimStack = stackAt sp storeSegStack := (stack_seg_shim sp).symm

private theorem stack_seg_alloc (sp : BitVec 64) :
    stackAt sp storeSegStack =
      memRegion (sp - BitVec.ofNat 64 storeSegStack) (storeSegStack - allocHookStack) ∗
        stackAt sp allocHookStack := by
  have h := stackAt_split_bottom sp allocHookStack (storeSegStack - allocHookStack) (by decide)
  rwa [show allocHookStack + (storeSegStack - allocHookStack) = storeSegStack by decide] at h

private theorem stack_seg_alloc' (sp : BitVec 64) :
    stackAt sp storeSessionPollStack =
      memRegion (sp - 16416#64) (storeSegStack - allocHookStack) ∗ stackAt sp allocHookStack :=
  stack_seg_alloc sp

private theorem stack_seg_dropLocal2 (sp : BitVec 64) :
    stackAt sp storeSegStack =
      memRegion (sp - 16416#64) (storeSegStack - FromRecordCallees.dropSessionStructureLocal2Stack) ∗
        stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack := by
  have h := stackAt_split_bottom sp FromRecordCallees.dropSessionStructureLocal2Stack
    (storeSegStack - FromRecordCallees.dropSessionStructureLocal2Stack) (by decide)
  rwa [show FromRecordCallees.dropSessionStructureLocal2Stack +
    (storeSegStack - FromRecordCallees.dropSessionStructureLocal2Stack) = storeSegStack by decide] at h

theorem store_box_fold (p u0 u1 u2 : BitVec 64) (b0 : BitVec 8) :
    (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1) ∗ ((p + 16#64) ↦₆₄ u2) ∗ ((p + 24#64) ↦₈ b0) ∗
        memRegion (p + 25#64) 7 ⊢ memRegion p 32 := by
  rw [memRegion_split p 8 24 (by decide), memRegion_split (p + 8#64) 8 16 (by decide),
    memRegion_split (p + 8#64 + 8#64) 8 8 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64) 1 7 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono
    (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo8_entails_memRegion _ _) (Entails.refl _))))

theorem header3_repack (o w1 w2 w3 : BitVec 64) :
    (o ↦₆₄ w1) ∗ ((o + 8#64) ↦₆₄ w2) ∗ ((o + 16#64) ↦₆₄ w3) =
      (o ↦₃₂ w1.extractLsb' 0 32) ∗ ((o + 4#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
        ((o + 12#64) ↦₆₄ (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)) ∗
        ((o + 20#64) ↦₃₂ w3.extractLsb' 32 32) := by
  rw [pointsTo64_split32 o w1, pointsTo64_split32 (o + 8#64) w2,
    pointsTo64_split32 (o + 16#64) w3, pointsTo64_append32, pointsTo64_append32]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl

theorem header3_repack_290 (sp w1 w2 w3 : BitVec 64) :
    ((sp + 0x290#64) ↦₆₄ w1) ∗ ((sp + 0x298#64) ↦₆₄ w2) ∗ ((sp + 0x2a0#64) ↦₆₄ w3) =
      ((sp + 0x290#64) ↦₃₂ w1.extractLsb' 0 32) ∗
        ((sp + 0x294#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
        ((sp + 0x29c#64) ↦₆₄ (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)) ∗
        ((sp + 0x2a4#64) ↦₃₂ w3.extractLsb' 32 32) := by
  have h := header3_repack (sp + 0x290#64) w1 w2 w3
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h; exact h

def vecU8BufPure (A : RustAlloc) (cap ptr : BitVec 64) (pt : List (BitVec 8)) : SepProp :=
  ⌜pt.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ pt) ∗
       memRegion (ptr + BitVec.ofNat 64 pt.length) (cap.toNat - pt.length))

theorem vecU8At_eq_header_buf (A : RustAlloc) (a cap ptr : BitVec 64) (pt : List (BitVec 8)) :
    vecU8At A a cap ptr pt =
      (((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pt.length)) ∗
        vecU8BufPure A cap ptr pt) := by
  simp only [vecU8At, vecHeader, vecU8BufPure]

/-! ## 3. Helpers & D9 tail on `Ok ()` (`+0x2428 → +0x24d4`) -/

theorem cap_add_one_beq_zero_eq_false_shared_lb {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]; intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change cap.toNat + 1 = 0 at ht; omega

def vecGhostTailAt_shared_lb (A : RustAlloc) (g : VecGhost) (v : BitVec 64) : SepProp :=
  ((v + 8#64) ↦₆₄ g.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
  (if g.cap = 0 then emp
   else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
     memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))

theorem vecGhostAt_unfold_cap_shared_lb (A : RustAlloc) (g : VecGhost) (v : BitVec 64) :
    vecGhostAt A g v =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
      (v ↦₆₄ g.cap) ∗ vecGhostTailAt_shared_lb A g v := by
  simp only [vecGhostAt, vecU8At, vecHeader, vecGhostTailAt_shared_lb]; ac_rfl

def sessionStateAfterLocalIk_shared_lb (A : RustAlloc) (ss : BitVec 64)
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

theorem sessionStateAt_unfold_cap_shared_lb (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st =
      ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
      (ss ↦₆₄ G.localIk.cap) ∗ vecGhostTailAt_shared_lb A G.localIk ss ∗
      sessionStateAfterLocalIk_shared_lb A ss G st := by
  unfold sessionStateAt sessionStateAfterLocalIk_shared_lb; rw [vecGhostAt_unfold_cap_shared_lb]; ac_rfl

def dropSessionStructureLocal2HeadSpec_shared_lb (A : RustAlloc) : Spec FromRecordCallees.DropSessionStructureGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ x.G.localIk.bytes.length ≤ x.G.localIk.cap.toNat ∧
      x.G.localIk.cap.toNat < 2 ^ 63 ∧ x.G.localIk.ptr ≠ 0⌝ ∗
      (x.ss ↦₆₄ x.G.localIk.cap) ∗ vecGhostTailAt_shared_lb A x.G.localIk x.ss ∗
      sessionStateAfterLocalIk_shared_lb A x.ss x.G x.st ∗ A.pool ∗ stackAt s.sp FromRecordCallees.dropSessionStructureLocal2Stack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion x.ss 344 ∗ A.pool ∗ stackAt s0.sp FromRecordCallees.dropSessionStructureLocal2Stack

private theorem drop_session_structure_local2_head_ok {A : RustAlloc} {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hdrop2 : FromRecordCallees.DropSessionStructureLocal2Ok b C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr FromRecordCallees.dropSessionStructureLocal2Name)
      (dropSessionStructureLocal2HeadSpec_shared_lb A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
    hdrop2.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
  simp only [FromRecordCallees.dropSessionStructureLocal2Spec, dropSessionStructureLocal2HeadSpec_shared_lb,
    sessionStateAt_unfold_cap_shared_lb, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  exact ⟨hpre.1.1, hpre.1.2, hpre.2⟩

theorem prevCap_ubfm_eq_shared_lb {cap : BitVec 64} (h : cap.toNat * 24 < 2 ^ 63) :
    ((cap + cap <<< 1) <<< 3).toNat = cap.toNat * 24 := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_shiftLeft]
  omega

theorem tail16_entails_memRegion (a : BitVec 64) (w0 : BitVec 32) (w1 : BitVec 64) (w2 : BitVec 32) :
    (a ↦₃₂ w0) ∗ ((a + 4#64) ↦₆₄ w1) ∗ ((a + 12#64) ↦₃₂ w2) ⊢ memRegion a 16 := by
  rw [memRegion_split a 4 12 (by decide), memRegion_split (a + 4#64) 8 4 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo32_entails_memRegion _ _))

theorem stagedRes_ok_pt (A : RustAlloc) (src cap ptr : BitVec 64) (pt : List (BitVec 8))
    (s2_hi : BitVec 32) (s3_598 : BitVec 64) (s4_5a0 : BitVec 32)
    (v1 : BitVec 32) (v2 v3 : BitVec 64) (v4 : BitVec 32)
    (hv1 : v1 = cap.extractLsb' 0 32) (hv2 : v2 = ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
    (hv3 : v3 = (BitVec.ofNat 64 pt.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
    (hv4 : v4 = (BitVec.ofNat 64 pt.length).extractLsb' 32 32) :
    (((src ↦₆₄ v2) ∗ ((src + 8#64) ↦₆₄ v3) ∗ ((src + 16#64) ↦₆₄ (s2_hi ++ v4)) ∗
      ((src + 24#64) ↦₆₄ s3_598) ∗ ((src + 32#64) ↦₃₂ s4_5a0)) ∗
      vecU8BufPure A cap ptr pt) ⊢
      StagedRes A okTagVec ((v1 >>> 8#32).zeroExtend 64) (v1.zeroExtend 64) src (.ok pt) := by
  rw [words36At_eq_pointsToBytes]; unfold StagedRes
  refine Entails.sepExists_right (bytes36 v2 v3 (s2_hi ++ v4) s3_598 s4_5a0) ?_
  refine Entails.sepExists_right (vecU8BufPure A cap ptr pt) ?_
  refine Entails.pure_right ⟨bytes36_length v2 v3 (s2_hi ++ v4) s3_598 s4_5a0, fun r => ?_⟩ (Entails.refl _)
  rw [resWord1_lsr8 v1, ← words36At_eq_pointsToBytes]
  have hsplit : ((r + 12#64 + 16#64) ↦₆₄ (s2_hi ++ v4)) =
      ((r + 28#64) ↦₃₂ v4) ∗ ((r + 32#64) ↦₃₂ s2_hi) := by
    have h := pointsTo64_append32 s2_hi v4 (r + 28#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h ⊢; exact h
  rw [hsplit]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hrep := (header3_repack (r + 8#64) cap ptr (BitVec.ofNat 64 pt.length)).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrep
  have hgrp :
      ((r ↦₆₄ okTagVec) ∗ ((r + 8#64) ↦₃₂ v1) ∗
        (((r + 12#64) ↦₆₄ v2) ∗ ((r + 20#64) ↦₆₄ v3) ∗
          (((r + 28#64) ↦₃₂ v4) ∗ ((r + 32#64) ↦₃₂ s2_hi)) ∗
          ((r + 36#64) ↦₆₄ s3_598) ∗ ((r + 44#64) ↦₃₂ s4_5a0)) ∗
        vecU8BufPure A cap ptr pt) =
      ((r ↦₆₄ okTagVec) ∗
        ((((r + 8#64) ↦₃₂ v1) ∗ ((r + 12#64) ↦₆₄ v2) ∗ ((r + 20#64) ↦₆₄ v3) ∗ ((r + 28#64) ↦₃₂ v4)) ∗
          vecU8BufPure A cap ptr pt) ∗
        (((r + 32#64) ↦₃₂ s2_hi) ∗ ((r + 36#64) ↦₆₄ s3_598) ∗ ((r + 44#64) ↦₃₂ s4_5a0))) := by ac_rfl
  rw [hgrp, hv1, hv2, hv3, hv4, hrep]
  have hvec :
      ((((r + 8#64) ↦₆₄ cap) ∗ ((r + 16#64) ↦₆₄ ptr) ∗ ((r + 24#64) ↦₆₄ BitVec.ofNat 64 pt.length)) ∗
        vecU8BufPure A cap ptr pt) ⊢ vecU8 A (r + 8#64) pt := by
    refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
    have hv := (vecU8At_eq_header_buf A (r + 8#64) cap ptr pt).symm
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hv ⊢; exact Entails.of_eq hv
  have htail := tail16_entails_memRegion (r + 32#64) s2_hi s3_598 s4_5a0
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at htail
  unfold apiDecResultAt vecResultAt; exact sepConj_mono_right (sepConj_mono hvec htail)

theorem model_of_store_ok {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (C : Crypto) (S : SpqrModel) (x : DecryptGhost)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (rec rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (ses : Session (List (BitVec 8))) (k : IdentityKey) (c : IdentityChange)
    (hload : ans.loadSession = .ok (some rec)) (_hscope : Scope rec)
    (hdec : decryptRecord C S uuidTryParse x rec = .ok (pt, rec')) (hcur : rec'.currentSession = some ses)
    (hik : ses.state.remoteIdentity = some k) (htrust : ans.isTrustedIdentity = .ok true)
    (hsave : ans.saveIdentity = .ok c) (hstore : ans.storeSession = .ok ()) :
    (x.model C S uuidTryParse ans).1 = .ok pt ∧
      (x.model C S uuidTryParse ans).2 =
        [.loadSession x.rem.val, .isTrustedIdentity x.rem.val k .receiving,
          .saveIdentity x.rem.val k, .storeSession x.rem.val rec'] := by
  have h : x.model C S uuidTryParse ans =
      (.ok pt, [.loadSession x.rem.val, .isTrustedIdentity x.rem.val k .receiving,
        .saveIdentity x.rem.val k, .storeSession x.rem.val rec']) := by
    unfold DecryptGhost.model; unfold decryptRecord at hdec; rw [messageDecryptSignal_eq_flat]
    simp [decryptFlat, hload, hdec, hcur, hik, htrust, hsave, hstore]
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

theorem model_of_store_err {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (C : Crypto) (S : SpqrModel) (x : DecryptGhost)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (rec rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (ses : Session (List (BitVec 8))) (k : IdentityKey) (c : IdentityChange)
    (hload : ans.loadSession = .ok (some rec)) (_hscope : Scope rec)
    (hdec : decryptRecord C S uuidTryParse x rec = .ok (pt, rec')) (hcur : rec'.currentSession = some ses)
    (hik : ses.state.remoteIdentity = some k) (htrust : ans.isTrustedIdentity = .ok true)
    (hsave : ans.saveIdentity = .ok c) (hstore : ans.storeSession = .error ()) :
    (x.model C S uuidTryParse ans).1 = .error (.store ()) ∧
      (x.model C S uuidTryParse ans).2 =
        [.loadSession x.rem.val, .isTrustedIdentity x.rem.val k .receiving,
          .saveIdentity x.rem.val k, .storeSession x.rem.val rec'] := by
  have h : x.model C S uuidTryParse ans =
      (.error (.store ()), [.loadSession x.rem.val, .isTrustedIdentity x.rem.val k .receiving,
        .saveIdentity x.rem.val k, .storeSession x.rem.val rec']) := by
    unfold DecryptGhost.model; unfold decryptRecord at hdec; rw [messageDecryptSignal_eq_flat]
    simp [decryptFlat, hload, hdec, hcur, hik, htrust, hsave, hstore]
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-! ## 3a. Region Split Helpers -/

theorem memRegion_300_280_store_split (sp : BitVec 64) :
    memRegion (sp + 0x300#64) 0x280 =
      memRegion (sp + 0x550#64) 0x24 ∗
        (memRegion (sp + 0x300#64) 0x250 ∗ memRegion (sp + 0x574#64) 0xc) := by
  rw [memRegion_split (sp + 0x300#64) 0x250 0x30 (by decide),
    memRegion_split (sp + 0x300#64 + 0x250#64) 0x24 0xc (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl

theorem memRegion_300_280_head_split (sp : BitVec 64) :
    memRegion (sp + 0x300#64) 0x280 =
      memRegion (sp + 0x300#64) 0x24 ∗ memRegion (sp + 0x324#64) 0x25c := by
  rw [memRegion_split (sp + 0x300#64) 0x24 0x25c (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_324_adc_split (sp : BitVec 64) :
    memRegion (sp + 0x324#64) 0xadc =
      memRegion (sp + 0x324#64) 0x25c ∗ memRegion (sp + 0x580#64) 0x24 ∗
        memRegion (sp + 0x5a4#64) 0x85c := by
  rw [memRegion_split (sp + 0x324#64) 0x25c 0x880 (by decide),
    memRegion_split (sp + 0x324#64 + 0x25c#64) 0x24 0x85c (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_120_1a8_join (sp prevCap prevPtr : BitVec 64)
    (v1 : BitVec 32) (v2 v3 : BitVec 64) (v4 : BitVec 32) :
    (((sp + 0x120#64) ↦₆₄ prevCap) ∗ ((sp + 0x128#64) ↦₆₄ prevPtr) ∗
      ((sp + 0x130#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x138#64) 344 ∗
      ((sp + 0x290#64) ↦₃₂ v1) ∗ ((sp + 0x294#64) ↦₆₄ v2) ∗
      ((sp + 0x29c#64) ↦₆₄ v3) ∗ ((sp + 0x2a4#64) ↦₃₂ v4) ∗
      memRegion (sp + 0x2a8#64) 0x20) ⊢ memRegion (sp + 0x120#64) 0x1a8 := by
  rw [memRegion_split (sp + 0x120#64) 8 416 (by decide),
    memRegion_split (sp + 0x120#64 + 8#64) 8 408 (by decide),
    memRegion_split (sp + 0x120#64 + 8#64 + 8#64) 8 400 (by decide),
    memRegion_split (sp + 0x120#64 + 8#64 + 8#64 + 8#64) 344 56 (by decide),
    memRegion_split (sp + 0x120#64 + 8#64 + 8#64 + 8#64 + 344#64) 4 52 (by decide),
    memRegion_split (sp + 0x120#64 + 8#64 + 8#64 + 8#64 + 344#64 + 4#64) 8 44 (by decide),
    memRegion_split (sp + 0x120#64 + 8#64 + 8#64 + 8#64 + 344#64 + 4#64 + 8#64) 8 36 (by decide),
    memRegion_split (sp + 0x120#64 + 8#64 + 8#64 + 8#64 + 344#64 + 4#64 + 8#64 + 8#64) 4 32 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (Entails.refl _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo32_entails_memRegion _ _) (Entails.refl _))))))))

theorem sessionRecordAt_some_expose (A : RustAlloc) (r : BitVec 64) (g : RecordGhost)
    (rec' : SessionRecord (List (BitVec 8))) (ses : Session (List (BitVec 8)))
    (hcur : rec'.currentSession = some ses) :
    sessionRecordAt A r g rec' ⊢
      ∃∗ G : SessionGhost,
        ⌜g.prevCap.toNat * 24 < 2 ^ 63 ∧ g.prevPtr ≠ 0⌝ ∗
        (r ↦₆₄ g.prevCap) ∗ ((r + 8#64) ↦₆₄ g.prevPtr) ∗ ((r + 16#64) ↦₆₄ 0#64) ∗
        (if g.prevCap = 0#64 then emp
         else A.live g.prevPtr (g.prevCap.toNat * 24) 8 ∗
           memRegion g.prevPtr (g.prevCap.toNat * 24)) ∗
        sessionStateAt A (r + 0x18#64) G ses.state := by
  rcases g with ⟨prevCap, prevPtr, gcur⟩
  cases gcur with
  | none =>
    unfold sessionRecordAt; simp only [hcur]; rw [sepConj_comm]; exact Entails.pure_left False.elim
  | some G =>
    refine Entails.sepExists_right G ?_
    unfold sessionRecordAt vecAt vecHeader vecBuf arrayAt
    simp only [hcur, sessionAt_eq, List.length_nil, Nat.zero_mul, Nat.sub_zero,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, emp_sepConj]
    rw [sepConj_assoc, sepConj_pure_left_comm, sepConj_pure_left_comm]
    apply Entails.pure_left; intro _
    simp only [sepConj_assoc]
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨_, hcap_lt, hptr_ne⟩
    exact Entails.pure_right ⟨hcap_lt, hptr_ne⟩ (Entails.of_eq (by ac_rfl))

theorem memRegion_36_entails_cells_split16 (a : BitVec 64) :
    memRegion a 0x24 ⊢
      ∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2_lo : BitVec 32, ∃∗ s2_hi : BitVec 32,
      ∃∗ s3 : BitVec 64, ∃∗ s4 : BitVec 32,
        (a ↦₆₄ s0) ∗ ((a + 8#64) ↦₆₄ s1) ∗ ((a + 16#64) ↦₃₂ s2_lo) ∗
        ((a + 20#64) ↦₃₂ s2_hi) ∗ ((a + 24#64) ↦₆₄ s3) ∗ ((a + 32#64) ↦₃₂ s4) := by
  refine Entails.trans (memRegion_36_entails_cells a) ?_
  apply Entails.sepExists_elim; intro s0; apply Entails.sepExists_elim; intro s1
  apply Entails.sepExists_elim; intro s2; apply Entails.sepExists_elim; intro s3
  apply Entails.sepExists_elim; intro s4
  refine Entails.sepExists_right s0 (Entails.sepExists_right s1
    (Entails.sepExists_right (s2.extractLsb' 0 32) (Entails.sepExists_right (s2.extractLsb' 32 32)
      (Entails.sepExists_right s3 (Entails.sepExists_right s4 ?_)))))
  rw [pointsTo64_split32 (a + 16#64) s2]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; exact Entails.refl _

theorem vecU8_290_expose (A : RustAlloc) (sp : BitVec 64) (pt : List (BitVec 8)) :
    vecU8 A (sp + 0x290#64) pt ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (((sp + 0x290#64) ↦₃₂ cap.extractLsb' 0 32) ∗
          ((sp + 0x294#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
          ((sp + 0x29c#64) ↦₆₄ ((BitVec.ofNat 64 pt.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
          ((sp + 0x2a4#64) ↦₃₂ (BitVec.ofNat 64 pt.length).extractLsb' 32 32)) ∗
        vecU8BufPure A cap ptr pt := by
  unfold vecU8; apply Entails.sepExists_elim; intro cap; apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [vecU8At_eq_header_buf]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [header3_repack_290]
  exact Entails.refl _

/-! ## 3b. D9 tails (`segStore_tail_ok`, `segStore_tail_err`) and `E₀` `storeCallSeg_ok_prime_pf` -/

theorem segStore_tail_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) (hdrop2 : FromRecordCallees.DropSessionStructureLocal2Ok b C A ctl abs)
    {s : State} {R : SepProp} {prevCap prevPtr : BitVec 64} {G : SessionGhost}
    {st : SessionState (List (BitVec 8))} {v1 : BitVec 32} {v2 v3 : BitVec 64} {v4 : BitVec 32}
    {s0_580 s1_588 : BitVec 64} {s2_lo s2_hi : BitVec 32} {s3_598 : BitVec 64} {s4_5a0 : BitVec 32}
    {t0_300 t1_308 t2_310 t3_318 : BitVec 64} {t4_320 : BitVec 32}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr decWithStoresName + 0x2428#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx28 : s.readReg64 .x28 = pollTag (.ok ())) (hx26 : s.readReg64 .x26 = s.sp + 0xa0#64)
    (hx22 : s.readReg64 .x22 = s.sp + 0x294#64) (hprev_lt : prevCap.toNat * 24 < 2 ^ 63)
    (_hprev_ptr : prevPtr ≠ 0) :
    SepWP (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr decWithStoresName + 0x24d4#64) s
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
  have hfn : libsignalSessionCode.fnOff decWithStoresName = num% (ls_off% "session_message_decrypt_signal") := by simp only [decWithStoresName, arm64_norm]
  have hfn2 : libsignalSessionCode.fnOff FromRecordCallees.dropSessionStructureLocal2Name = num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#2]") := by
    simp only [FromRecordCallees.dropSessionStructureLocal2Name, arm64_norm]
  have hdrop := drop_session_structure_local2_head_ok hdrop2
  have hrel : (tripleRatchetProgAt b C ctl abs).fnAddr FromRecordCallees.dropSessionStructureLocal2Name =
      (tripleRatchetProgAt b C ctl abs).fnAddr decWithStoresName + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#2]") - (ls_off% "session_message_decrypt_signal")) := by
    simp only [tripleRatchetProgAt, Program.fnAddr_rebase, hfn, hfn2, BitVec.add_assoc]; rfl
  rw [hrel] at hdrop; clear hrel
  have hdealloc := dealloc_ok_at_norm (b := b) (C := C) (ctl := ctl)
    (name := decWithStoresName) (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "session_message_decrypt_signal")) hA
  code_fetches_range CryptoVerification.libsignalSessionCode segStoreTailBin b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (num% (ls_off% "session_message_decrypt_signal")) 0x2428 0x38
  code_fetches_range CryptoVerification.libsignalSessionCode segStoreTailBin b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (num% (ls_off% "session_message_decrypt_signal")) 0x249c 0x38
  dsimp only [tripleRatchetProgAt] at hpc hdrop hdealloc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr decWithStoresName = entry at *
  examples_hide_fetches; simp only [pollTag] at hx28
  wp_simp_pre [sessionStateAt_unfold_cap_shared_lb, sepConj_assoc, sepConj_pure_left_comm]
  apply SepWP.pure_elim; rintro ⟨hlik_len, hlik_cap, hlik_ptr⟩
  have hcmn : (G.localIk.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false_shared_lb hlik_cap
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
    have hmul := prevCap_ubfm_eq_shared_lb hprev_lt
    wp_apply
    simp only [hsp_sf] at hsp_sf_1 ⊢
    apply SepWP.fold (Entails.of_eq (stack_seg_alloc s.sp).symm) (by sep_focus)
    wp_steps; wp_done

theorem segStore_tail_err {b : BitVec 64} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    {s : State} {R : SepProp} {o1 : BitVec 32} {o2 o3 o4 o5 : BitVec 64} {o6 : BitVec 32}
    {s0_580 s1_588 s2_590 s3_598 : BitVec 64} {s4_5a0 : BitVec 32}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr decWithStoresName + 0x2428#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx28 : s.readReg64 .x28 = pollTag (.error ())) (hx21 : s.readReg64 .x21 = o1.zeroExtend 64) :
    SepWP (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr decWithStoresName + 0x2294#64) s
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
  have hfn : libsignalSessionCode.fnOff decWithStoresName = num% (ls_off% "session_message_decrypt_signal") := by simp only [decWithStoresName, arm64_norm]
  code_fetches_range CryptoVerification.libsignalSessionCode segStoreTailBin b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (num% (ls_off% "session_message_decrypt_signal")) 0x2428 8
  code_fetches_range CryptoVerification.libsignalSessionCode segStoreTailBin b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (num% (ls_off% "session_message_decrypt_signal")) 0x248c 16
  code_fetches_range CryptoVerification.libsignalSessionCode segStoreTailBin b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (num% (ls_off% "session_message_decrypt_signal")) 0x23d4 8
  code_fetches_range CryptoVerification.libsignalSessionCode segSaveBin b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (num% (ls_off% "session_message_decrypt_signal")) 0x21a0 16
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr decWithStoresName = entry at *
  examples_hide_fetches; simp only [pollTag] at hx28; wp_steps; wp_done

/-! ## Relocatable `[LibsignalPlacement]` Proofs -/

section Placed

open CryptoVerification.LibsignalPublicApi.Placed

theorem drop_session_structure_local2_head_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hdrop2 : DropSessionStructureLocal2PlacedOk A H) :
    subroutine_ok (lsProg_197 H) (lsmpl.base 139)
      (StoreKit.withLsRoCl lsmpl (dropSessionStructureLocal2HeadSpec_shared_lb A)) := by
  refine subroutine_ok_mono_entails hdrop2 (fun x s0 => ?_) (fun _ _ _ => Entails.refl _)
  dsimp only [StoreKit.withLsRoCl, FromRecordCallees.dropSessionStructureLocal2Spec,
    dropSessionStructureLocal2HeadSpec_shared_lb]
  rw [sessionStateAt_unfold_cap_shared_lb]
  simp only [sepConj_assoc]
  apply Entails.pure_left; rintro ⟨hx0, hlen, hcap, hptr⟩
  exact Entails.pure_right hx0 (Entails.pure_right ⟨hlen, hcap, hptr⟩ (Entails.refl _))

theorem segStore_tail_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hdealloc_sat : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hdrop2 : DropSessionStructureLocal2PlacedOk A H)
    {s : State} {R : SepProp} {prevCap prevPtr : BitVec 64} {G : SessionGhost}
    {st : SessionState (List (BitVec 8))} {v1 : BitVec 32} {v2 v3 : BitVec 64} {v4 : BitVec 32}
    {s0_580 s1_588 : BitVec 64} {s2_lo s2_hi : BitVec 32} {s3_598 : BitVec 64} {s4_5a0 : BitVec 32}
    {t0_300 t1_308 t2_310 t3_318 : BitVec 64} {t4_320 : BitVec 32}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_197).base + 9256#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx28 : s.readReg64 .x28 = pollTag (.ok ())) (hx26 : s.readReg64 .x26 = s.sp + 0xa0#64)
    (hx22 : s.readReg64 .x22 = s.sp + 0x294#64) (hprev_lt : prevCap.toNat * 24 < 2 ^ 63)
    (_hprev_ptr : prevPtr ≠ 0) :
    SepWP (lsProg_197 H) resultFinalPCPlaced s
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
  have hdrop := drop_session_structure_local2_head_placed_ok hdrop2
  have hdealloc : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsρ lsRustDeallocSym)
      (rustDeallocSpec A) := ls_hook_ok_of_mem hdealloc_sat
  unfold resultFinalPCPlaced
  dsimp only [lsProg_197] at hdrop ⊢
  simp only [pollTag] at hx28
  wp_simp_pre [sessionStateAt_unfold_cap_shared_lb, sepConj_assoc, sepConj_pure_left_comm]
  apply SepWP.pure_elim; rintro ⟨hlik_len, hlik_cap, hlik_ptr⟩
  have hcmn : (G.localIk.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false_shared_lb hlik_cap
  apply SepWP.fold (Entails.of_eq (stack_seg_dropLocal2 s.sp)) (by sep_focus)
  apply StoreKit.sepWP_seq_lscro (mid := lsmpl.base 139) hcrl
  clear hcrl
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  rintro ⟨hcl1, hro1⟩
  wp_apply
  clear hcl1 hro1
  apply SepWP.fold (Entails.of_eq (stack_seg_dropLocal2 s.sp).symm) (by sep_focus)
  apply SepWP.fold (Entails.of_eq (pointsTo64_append32 s2_hi v4 (s.sp + 0x590#64)).symm) (by sep_focus)
  wp_steps
  by_cases hcap : prevCap = 0#64
  · subst hcap; simp only [beq_self_eq_true, ↓reduceIte, emp_sepConj]; wp_steps; wp_done
  · have hcap_beq : (prevCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    simp only [hcap_beq, hcap, ↓reduceIte, Bool.false_eq_true]
    apply SepWP.fold (Entails.of_eq (stack_seg_alloc s.sp)) (by sep_focus)
    wp_steps
    have hmul := prevCap_ubfm_eq_shared_lb hprev_lt
    wp_apply
    simp only [hsp_sf] at hsp_sf_1 ⊢
    apply SepWP.fold (Entails.of_eq (stack_seg_alloc s.sp).symm) (by sep_focus)
    wp_steps; wp_done

theorem segStore_tail_placed_err [LibsignalPlacement] {H : LibsignalHooks}
    {s : State} {R : SepProp} {o1 : BitVec 32} {o2 o3 o4 o5 : BitVec 64} {o6 : BitVec 32}
    {s0_580 s1_588 s2_590 s3_598 : BitVec 64} {s4_5a0 : BitVec 32}
    (hpc : s.pc = (blkPl_197).base + 9256#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx28 : s.readReg64 .x28 = pollTag (.error ())) (hx21 : s.readReg64 .x21 = o1.zeroExtend 64) :
    SepWP (lsProg_197 H) (errJoinPCPlaced true) s
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
  simp only [errJoinPCPlaced, ↓reduceIte]
  dsimp only [lsProg_197]
  simp only [pollTag] at hx28
  wp_steps
  wp_done

def wsStoreFixedEnvPlaced [LibsignalPlacement] (A : RustAlloc)
    (kit : SessionStoreSpec A 0#64) (x : DecryptGhost) (s0 : State)
    (sp : BitVec 64) (st : kit.StoreState) : SepProp :=
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗ ((sp + 0xf8#64) ↦₆₄ s0.readReg64 .x3) ∗
  ((sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗
  ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ kit.storeShimOff) ∗
  (kit.storeFutVtOff ↦₆₄ᵣ kit.storeFutDropOff) ∗
  ((kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
  ((kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ kit.storePollOff) ∗
  protocolAddressAt A x.rem x.remA ∗ kit.storeAt (s0.readReg64 .x3) st ∗
  A.pool ∗ stackAt sp (storeCallStack kit)

def wsStoreFixedRestPlaced [LibsignalPlacement] (A : RustAlloc)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) (ist : ikit.IdState) : SepProp :=
  wsSavedRegs s0.sp s0 ∗ ((sp + 0x108#64) ↦₆₄ s0.readReg64 .x5) ∗
  ((sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗ ((sp + 0x118#64) ↦₆₄ (s0.sp - 0x71#64)) ∗
  decLoadVtableAtV kit ∗ decSaveVtableAtV ikit ∗ decTrustVtableAtV ikit ∗
  memRegion (sp + 0xa0#64) 0x40 ∗ memRegion (sp + 0x2c8#64) 8 ∗
  memRegion (sp + 0x2e0#64) 0x20 ∗ memRegion (sp + 0xe00#64) 0x80 ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.loc x.locA ∗
  FromRecordCallees.lsLogOff ∗
  ikit.identityAt (s0.readReg64 .x5) ist ∗
  memRegion (sp - BitVec.ofNat 64 (wsCalleeStackV kit ikit))
    (wsCalleeStackV kit ikit - storeCallStack kit)

theorem wsFixed_wsEnv_store_split_placed [LibsignalPlacement] (A : RustAlloc)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64)
    (st : kit.StoreState) (ist : ikit.IdState)
    (hsp : sp = s0.sp - 0xee0#64) :
    wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ decStoreExtraPlaced kit ikit st ist s0 ⊢
      ⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
      wsStoreFixedEnvPlaced A kit x s0 sp st ∗ wsStoreFixedRestPlaced A kit ikit x s0 sp ist := by
  subst hsp
  have hj := wsCalleeStack_join_extra_placed kit ikit st ist s0
  refine Entails.trans (Entails.of_eq (show
    wsFixedVPlaced kit ikit x s0 (s0.sp - 0xee0#64) ∗ wsEnvPlaced A x (s0.sp - 0xee0#64) ∗
      decStoreExtraPlaced kit ikit st ist s0 =
    (stackAt (s0.sp - 0xee0#64) wsCalleeStack ∗ decStoreExtraPlaced kit ikit st ist s0) ∗
    (wsFixedVPlaced kit ikit x s0 (s0.sp - 0xee0#64) ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
      protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      FromRecordCallees.lsLogOff ∗ A.pool) by
    unfold wsEnvPlaced; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hj) ?_
  rw [sepConj_assoc (⌜_⌝)]
  apply Entails.pure_left; intro hbound
  have hn : wsCalleeStackV kit ikit ≤ 2 ^ 64 := by
    have := s0.sp.isLt; unfold wsStackV at hbound; omega
  refine Entails.pure_right hbound ?_
  unfold wsFixedVPlaced wsArgCellsV decVtablesAtV decStoreVtableAtV
    wsStoreFixedEnvPlaced wsStoreFixedRestPlaced
  simp only [BitVec.zero_add]
  rw [stack_wsCalleeV_storeCall kit ikit (s0.sp - 0xee0#64) hn]
  exact Entails.of_eq (by ac_rfl)

theorem wsFixed_wsEnv_store_join_placed [LibsignalPlacement] (A : RustAlloc)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64)
    (st : kit.StoreState) (ist : ikit.IdState)
    (hsp : sp = s0.sp - 0xee0#64) (hbound : wsStackV kit ikit ≤ s0.sp.toNat) :
    wsStoreFixedEnvPlaced A kit x s0 sp st ∗ wsStoreFixedRestPlaced A kit ikit x s0 sp ist ⊢
      wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ decStoreExtraPlaced kit ikit st ist s0 := by
  subst hsp
  have hsplit := wsCalleeStack_split_extra_placed kit ikit st ist s0 hbound
  have hn : wsCalleeStackV kit ikit ≤ 2 ^ 64 := by
    have := s0.sp.isLt; unfold wsStackV at hbound; omega
  refine Entails.trans (Entails.of_eq (show
    wsStoreFixedEnvPlaced A kit x s0 (s0.sp - 0xee0#64) st ∗
      wsStoreFixedRestPlaced A kit ikit x s0 (s0.sp - 0xee0#64) ist =
    (kit.storeAt (s0.readReg64 .x3) st ∗ ikit.identityAt (s0.readReg64 .x5) ist ∗
      (memRegion ((s0.sp - 0xee0#64) - BitVec.ofNat 64 (wsCalleeStackV kit ikit))
        (wsCalleeStackV kit ikit - storeCallStack kit) ∗
        stackAt (s0.sp - 0xee0#64) (storeCallStack kit))) ∗
    (wsFixedVPlaced kit ikit x s0 (s0.sp - 0xee0#64) ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
      protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      FromRecordCallees.lsLogOff ∗ A.pool) by
    unfold wsFixedVPlaced wsArgCellsV decVtablesAtV decStoreVtableAtV
      wsStoreFixedEnvPlaced wsStoreFixedRestPlaced
    simp only [BitVec.zero_add]; ac_rfl)) ?_
  rw [← stack_wsCalleeV_storeCall kit ikit (s0.sp - 0xee0#64) hn]
  refine Entails.trans (sepConj_mono_left hsplit) ?_
  unfold wsEnvPlaced
  exact Entails.of_eq (by ac_rfl)

def wsStoreCallPrePlaced [LibsignalPlacement] (A : RustAlloc)
    (kit : SessionStoreSpec A 0#64) (x : DecryptGhost) (s0 : State)
    (sp r26 : BitVec 64) (g : RecordGhost) (rec' : SessionRecord (List (BitVec 8)))
    (st : kit.StoreState) (c0 c1 d0 d1 d2 d3 : BitVec 64) (d5 : BitVec 32) : SepProp :=
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗ ((sp + 0xf8#64) ↦₆₄ s0.readReg64 .x3) ∗
  ((sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗
  ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ kit.storeShimOff) ∗
  (kit.storeFutVtOff ↦₆₄ᵣ kit.storeFutDropOff) ∗
  ((kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
  ((kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ kit.storePollOff) ∗
  ((sp + 0x2d0#64) ↦₆₄ c0) ∗ ((sp + 0x2d8#64) ↦₆₄ c1) ∗
  ((sp + 0x550#64) ↦₆₄ d0) ∗ ((sp + 0x558#64) ↦₆₄ d1) ∗ ((sp + 0x560#64) ↦₆₄ d2) ∗
  ((sp + 0x568#64) ↦₆₄ d3) ∗ ((sp + 0x570#64) ↦₃₂ d5) ∗
  memRegion (sp + 0x5f0#64) 48 ∗ protocolAddressAt A x.rem x.remA ∗
  sessionRecordAt A (r26 + 0x80#64) g rec' ∗ kit.storeAt (s0.readReg64 .x3) st ∗
  A.pool ∗ stackAt sp (storeCallStack kit)

def wsStoreFramePlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (ist : ikit.IdState) (pt : List (BitVec 8)) : SepProp :=
  wsStoreFixedRestPlaced A kit ikit x s0 sp ist ∗ wsMsgCells x sp ∗
  vecU8 A (sp + 0x290#64) pt ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion sp 0xa0 ∗
  (memRegion (sp + 0x300#64) 0x250 ∗ memRegion (sp + 0x574#64) 0xc) ∗
  memRegion (sp + 0x580#64) 0x24 ∗
  (memRegion (sp + 0x5a4#64) 0x4c ∗ memRegion (sp + 0x620#64) 0x7e0) ∗
  memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans)

theorem storeCall_entails_storeCallPre_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp r26 : BitVec 64) (st : kit.StoreState) (ist : ikit.IdState)
    (rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (hsp : sp = s0.sp - 0xee0#64) (hr26 : r26 = sp + 0xa0#64) :
    (wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ memRegion (sp + 0x2a8#64) 0x20 ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x300#64) 0xb00 ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtraPlaced kit ikit st ist s0) ⊢
    ∃∗ g : RecordGhost, ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64,
    ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64, ∃∗ d5 : BitVec 32,
      ⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
      wsStoreCallPrePlaced A kit x s0 sp r26 g rec' st c0 c1 d0 d1 d2 d3 d5 ∗
      wsStoreFramePlaced C A ctl kit ikit x ans s0 sp ist pt := by
  subst hr26
  refine Entails.trans (Entails.of_eq (show _ =
    (wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ decStoreExtraPlaced kit ikit st ist s0) ∗
    (wsMsgCells x sp ∗ (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ memRegion (sp + 0x2a8#64) 0x20 ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x300#64) 0xb00 ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans)) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left
    (wsFixed_wsEnv_store_split_placed A kit ikit x s0 sp st ist hsp)) ?_
  rw [sepConj_assoc (⌜_⌝)]
  apply Entails.pure_left; intro hbound
  rw [memRegion_300_b00_split, memRegion_300_280_store_split, memRegion_5a4_85c_split]
  refine Entails.trans (Entails.of_eq (show _ =
    (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      (memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x550#64) 0x24) ∗
      (wsStoreFixedEnvPlaced A kit x s0 sp st ∗ memRegion (sp + 0x5f0#64) 48 ∗
        wsStoreFramePlaced C A ctl kit ikit x ans s0 sp ist pt) by
    unfold wsStoreFramePlaced; ac_rfl)) ?_
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
  unfold wsStoreCallPrePlaced wsStoreFixedEnvPlaced
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

def wsStoreCallPostSpatialPlaced [LibsignalPlacement] (A : RustAlloc)
    (kit : SessionStoreSpec A 0#64) (x : DecryptGhost) (s0 : State)
    (sp r26 : BitVec 64) (g : RecordGhost) (rec' : SessionRecord (List (BitVec 8)))
    (st : kit.StoreState) (ans_store : Except Unit Unit)
    (box strPtr o2 o3 o4 o5 : BitVec 64) (o1 o6 : BitVec 32) : SepProp :=
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗ ((sp + 0xf8#64) ↦₆₄ s0.readReg64 .x3) ∗
  ((sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗
  ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ kit.storeShimOff) ∗
  (kit.storeFutVtOff ↦₆₄ᵣ kit.storeFutDropOff) ∗
  ((kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
  ((kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ kit.storePollOff) ∗
  ((sp + 0x2d0#64) ↦₆₄ box) ∗ ((sp + 0x2d8#64) ↦₆₄ kit.storeFutVtOff) ∗
  ((sp + 0x550#64) ↦₆₄ o2) ∗ ((sp + 0x558#64) ↦₆₄ o3) ∗
  ((sp + 0x560#64) ↦₆₄ o4) ∗ ((sp + 0x568#64) ↦₆₄ o5) ∗ ((sp + 0x570#64) ↦₃₂ o6) ∗
  ((sp + 0x5f0#64) ↦₆₄ pollTag ans_store) ∗ ((sp + 0x5f8#64) ↦₃₂ o1) ∗
  ((sp + 0x5fc#64) ↦₆₄ o2) ∗ ((sp + 0x604#64) ↦₆₄ o3) ∗
  ((sp + 0x60c#64) ↦₆₄ o4) ∗ ((sp + 0x614#64) ↦₆₄ o5) ∗ ((sp + 0x61c#64) ↦₃₂ o6) ∗
  protocolAddressAt A x.rem x.remA ∗
  sessionRecordAt A (r26 + 0x80#64) g rec' ∗ kit.storeAt (s0.readReg64 .x3) st ∗
  (if ans_store.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
  A.pool ∗ stackAt sp (storeCallStack kit)

def wsStorePostCommonRestPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (st : kit.StoreState) (ist : ikit.IdState)
    (pt : List (BitVec 8)) : SepProp :=
  wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
  vecU8 A (sp + 0x290#64) pt ∗ memRegion sp 0xa0 ∗
  memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
  (memRegion (sp + 0x300#64) 0x250 ∗ memRegion (sp + 0x574#64) 0xc) ∗
  memRegion (sp + 0x5a4#64) 0x85c ∗
  memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
  decStoreExtraPlaced kit ikit st ist s0

theorem storeCallPost_entails_common_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp r26 : BitVec 64) (g : RecordGhost) (rec' : SessionRecord (List (BitVec 8)))
    (st : kit.StoreState) (ist : ikit.IdState) (pt : List (BitVec 8))
    (ans_store : Except Unit Unit)
    (box strPtr o2 o3 o4 o5 : BitVec 64) (o1 o6 : BitVec 32)
    (hsp : sp = s0.sp - 0xee0#64) (hr26 : r26 = sp + 0xa0#64)
    (hbound : wsStackV kit ikit ≤ s0.sp.toNat) :
    wsStoreCallPostSpatialPlaced A kit x s0 sp r26 g rec' st ans_store box strPtr o2 o3 o4 o5 o1 o6 ∗
      wsStoreFramePlaced C A ctl kit ikit x ans s0 sp ist pt ⊢
    (((sp + 0x550#64) ↦₆₄ o2) ∗ ((sp + 0x558#64) ↦₆₄ o3) ∗
      ((sp + 0x560#64) ↦₆₄ o4) ∗ ((sp + 0x568#64) ↦₆₄ o5) ∗
      ((sp + 0x570#64) ↦₃₂ o6)) ∗
    memRegion (sp + 0x580#64) 0x24 ∗
    (if ans_store.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
    sessionRecordAt A (sp + 0x120#64) g rec' ∗
    wsStorePostCommonRestPlaced C A ctl kit ikit x ans s0 sp st ist pt := by
  subst hr26
  refine Entails.trans (Entails.of_eq (show _ =
    ((((sp + 0x2d0#64) ↦₆₄ box) ∗ ((sp + 0x2d8#64) ↦₆₄ kit.storeFutVtOff)) ∗
      (((sp + 0x5f0#64) ↦₆₄ pollTag ans_store) ∗ ((sp + 0x5f8#64) ↦₃₂ o1) ∗
        ((sp + 0x5fc#64) ↦₆₄ o2) ∗ ((sp + 0x604#64) ↦₆₄ o3) ∗
        ((sp + 0x60c#64) ↦₆₄ o4) ∗ ((sp + 0x614#64) ↦₆₄ o5) ∗
        ((sp + 0x61c#64) ↦₃₂ o6))) ∗
    (wsStoreFixedEnvPlaced A kit x s0 sp st ∗ wsStoreFixedRestPlaced A kit ikit x s0 sp ist) ∗
    ((((sp + 0x550#64) ↦₆₄ o2) ∗ ((sp + 0x558#64) ↦₆₄ o3) ∗
      ((sp + 0x560#64) ↦₆₄ o4) ∗ ((sp + 0x568#64) ↦₆₄ o5) ∗
      ((sp + 0x570#64) ↦₃₂ o6)) ∗
      memRegion (sp + 0x580#64) 0x24 ∗
      (if ans_store.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
      sessionRecordAt A (sp + 0x120#64) g rec' ∗
      wsMsgCells x sp ∗ vecU8 A (sp + 0x290#64) pt ∗ memRegion sp 0xa0 ∗
      memRegion (sp + 0x2a8#64) 0x20 ∗
      (memRegion (sp + 0x300#64) 0x250 ∗ memRegion (sp + 0x574#64) 0xc) ∗
      (memRegion (sp + 0x5a4#64) 0x4c ∗ memRegion (sp + 0x620#64) 0x7e0) ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans)) by
    unfold wsStoreCallPostSpatialPlaced wsStoreFramePlaced wsStoreFixedEnvPlaced
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl)) ?_
  have h16 := cells_16_entails_memRegion (sp + 0x2d0#64) box kit.storeFutVtOff
  have h48 := cells_48_poll_entails_memRegion (sp + 0x5f0#64) (pollTag ans_store)
    o2 o3 o4 o5 o1 o6
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h16 h48
  refine Entails.trans (sepConj_mono (sepConj_mono h16 h48)
    (sepConj_mono_left (wsFixed_wsEnv_store_join_placed A kit ikit x s0 sp st ist hsp hbound))) ?_
  unfold wsStorePostCommonRestPlaced
  rw [memRegion_5a4_85c_split]
  exact Entails.of_eq (by ac_rfl)

theorem storePostCommon_err_entails_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (g : RecordGhost) (rec' : SessionRecord (List (BitVec 8)))
    (ses : Session (List (BitVec 8))) (hcur : rec'.currentSession = some ses)
    (st : kit.StoreState) (ist : ikit.IdState) (pt : List (BitVec 8))
    (strPtr vt x28 w20 w21 o2 o3 o4 o5 : BitVec 64) (o1 o6 : BitVec 32)
    (hx28 : x28 = 0x800000000000001A#64) (hw1 : resWord1 w20 w21 = o1)
    (hrel : pollOutPlacedRel (α := Unit) strPtr vt o2 o3 o4 o5 o1 (.error ())) :
    (strPtr ↦ᵣ storeHookStr) ∗
    ((((sp + 0x550#64) ↦₆₄ o2) ∗ ((sp + 0x558#64) ↦₆₄ o3) ∗
      ((sp + 0x560#64) ↦₆₄ o4) ∗ ((sp + 0x568#64) ↦₆₄ o5) ∗ ((sp + 0x570#64) ↦₃₂ o6) ∗
      ((sp + 0x580#64) ↦₆₄ o2) ∗ ((sp + 0x588#64) ↦₆₄ o3) ∗
      ((sp + 0x590#64) ↦₆₄ o4) ∗ ((sp + 0x598#64) ↦₆₄ o5) ∗ ((sp + 0x5a0#64) ↦₃₂ o6)) ∗
    sessionRecordAt A (sp + 0x120#64) g rec' ∗
    wsStorePostCommonRestPlaced C A ctl kit ikit x ans s0 sp st ist pt) ⊢
    ∃∗ G : SessionGhost,
      wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      droppableRecordAt A (sp + 0x120#64) (some (G, ses.state)) ∗
      (∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p) ∗
      StagedRes A x28 w20 w21 (sp + 0x580#64) (.error (.store ())) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtraPlaced kit ikit st ist s0 := by
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
      ((sp + 0x5a0#64) ↦₃₂ o6)) ∗ (strPtr ↦ᵣ storeHookStr)) ∗
    vecU8 A (sp + 0x290#64) pt ∗
    (wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      (memRegion (sp + 0x300#64) 0x250 ∗ memRegion (sp + 0x574#64) 0xc) ∗
      memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtraPlaced kit ikit st ist s0)) by
    unfold wsStorePostCommonRestPlaced; ac_rfl)) ?_
  have h36 := cells_36_entails_memRegion (sp + 0x550#64) o2 o3 o4 o5 o6
  have hst := stagedRes_storeErr_of_pollOutPlacedRel (α := Unit) A strPtr vt x28 w20 w21
    (sp + 0x580#64) o2 o3 o4 o5 o1 o6 hx28 hw1 hrel
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

def wsStoreTailOkPre_placed (A : RustAlloc) (sp prevCap prevPtr : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (v1 : BitVec 32) (v2 v3 : BitVec 64) (v4 : BitVec 32)
    (s0_580 s1_588 : BitVec 64) (s2_lo s2_hi : BitVec 32) (s3_598 : BitVec 64) (s4_5a0 : BitVec 32)
    (t0_300 t1_308 t2_310 t3_318 : BitVec 64) (t4_320 : BitVec 32) : SepProp :=
  ((sp + 0x120#64) ↦₆₄ prevCap) ∗ ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
  (if prevCap = 0#64 then emp
   else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
  sessionStateAt A (sp + 0x138#64) G st ∗
  ((sp + 0x290#64) ↦₃₂ v1) ∗ ((sp + 0x294#64) ↦₆₄ v2) ∗ ((sp + 0x29c#64) ↦₆₄ v3) ∗
  ((sp + 0x2a4#64) ↦₃₂ v4) ∗ ((sp + 0x300#64) ↦₆₄ t0_300) ∗ ((sp + 0x308#64) ↦₆₄ t1_308) ∗
  ((sp + 0x310#64) ↦₆₄ t2_310) ∗ ((sp + 0x318#64) ↦₆₄ t3_318) ∗ ((sp + 0x320#64) ↦₃₂ t4_320) ∗
  ((sp + 0x580#64) ↦₆₄ s0_580) ∗ ((sp + 0x588#64) ↦₆₄ s1_588) ∗ ((sp + 0x590#64) ↦₃₂ s2_lo) ∗
  ((sp + 0x594#64) ↦₃₂ s2_hi) ∗ ((sp + 0x598#64) ↦₆₄ s3_598) ∗ ((sp + 0x5a0#64) ↦₃₂ s4_5a0) ∗
  A.pool ∗ stackAt sp storeSegStack

def wsStoreTailOkPost_placed (A : RustAlloc) (sp prevCap prevPtr : BitVec 64)
    (v1 : BitVec 32) (v2 v3 : BitVec 64) (v4 : BitVec 32)
    (s2_hi : BitVec 32) (s3_598 : BitVec 64) (s4_5a0 : BitVec 32) : SepProp :=
  ((sp + 0x120#64) ↦₆₄ prevCap) ∗ ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
  memRegion (sp + 0x138#64) 344 ∗
  ((sp + 0x290#64) ↦₃₂ v1) ∗ ((sp + 0x294#64) ↦₆₄ v2) ∗ ((sp + 0x29c#64) ↦₆₄ v3) ∗
  ((sp + 0x2a4#64) ↦₃₂ v4) ∗ ((sp + 0x300#64) ↦₆₄ v2) ∗ ((sp + 0x308#64) ↦₆₄ v3) ∗
  ((sp + 0x310#64) ↦₆₄ (s2_hi ++ v4)) ∗ ((sp + 0x318#64) ↦₆₄ s3_598) ∗ ((sp + 0x320#64) ↦₃₂ s4_5a0) ∗
  ((sp + 0x580#64) ↦₆₄ v2) ∗ ((sp + 0x588#64) ↦₆₄ v3) ∗ ((sp + 0x590#64) ↦₆₄ (s2_hi ++ v4)) ∗
  ((sp + 0x598#64) ↦₆₄ s3_598) ∗ ((sp + 0x5a0#64) ↦₃₂ s4_5a0) ∗ A.pool ∗ stackAt sp storeSegStack

def wsStoreTailOkFramePlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp cap ptr : BitVec 64) (st : kit.StoreState) (ist : ikit.IdState)
    (pt : List (BitVec 8)) : SepProp :=
  wsFixedVPlaced kit ikit x s0 sp ∗
  (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗ FromRecordCallees.lsLogOff ∗
    kit.storeAt (s0.readReg64 .x3) st ∗ ikit.identityAt (s0.readReg64 .x5) ist ∗
    memRegion (sp - BitVec.ofNat 64 (wsCalleeStackV kit ikit)) (wsCalleeStackV kit ikit - storeSegStack)) ∗
  wsMsgCells x sp ∗ vecU8BufPure A cap ptr pt ∗
  memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
  memRegion (sp + 0x324#64) 0x25c ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
  memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans)

theorem storePostCommon_ok_pre_tail_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (g : RecordGhost) (rec' : SessionRecord (List (BitVec 8)))
    (ses : Session (List (BitVec 8))) (hcur : rec'.currentSession = some ses)
    (st : kit.StoreState) (ist : ikit.IdState)
    (pt : List (BitVec 8)) (o2 o3 o4 o5 : BitVec 64) (o6 : BitVec 32)
    (hsp : sp = s0.sp - 0xee0#64) :
    (((sp + 0x550#64) ↦₆₄ o2) ∗ ((sp + 0x558#64) ↦₆₄ o3) ∗
      ((sp + 0x560#64) ↦₆₄ o4) ∗ ((sp + 0x568#64) ↦₆₄ o5) ∗ ((sp + 0x570#64) ↦₃₂ o6)) ∗
    memRegion (sp + 0x580#64) 0x24 ∗ sessionRecordAt A (sp + 0x120#64) g rec' ∗
    wsStorePostCommonRestPlaced C A ctl kit ikit x ans s0 sp st ist pt ⊢
    ∃∗ G : SessionGhost, ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
    ∃∗ s0_580 : BitVec 64, ∃∗ s1_588 : BitVec 64, ∃∗ s2_lo : BitVec 32, ∃∗ s2_hi : BitVec 32,
    ∃∗ s3_598 : BitVec 64, ∃∗ s4_5a0 : BitVec 32,
    ∃∗ t0_300 : BitVec 64, ∃∗ t1_308 : BitVec 64, ∃∗ t2_310 : BitVec 64,
    ∃∗ t3_318 : BitVec 64, ∃∗ t4_320 : BitVec 32,
      ⌜wsStackV kit ikit ≤ s0.sp.toNat ∧ g.prevCap.toNat * 24 < 2 ^ 63 ∧ g.prevPtr ≠ 0⌝ ∗
      wsStoreTailOkPre_placed A sp g.prevCap g.prevPtr G ses.state
        (cap.extractLsb' 0 32) (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
        ((BitVec.ofNat 64 pt.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
        ((BitVec.ofNat 64 pt.length).extractLsb' 32 32)
        s0_580 s1_588 s2_lo s2_hi s3_598 s4_5a0 t0_300 t1_308 t2_310 t3_318 t4_320 ∗
      wsStoreTailOkFramePlaced C A ctl kit ikit x ans s0 sp cap ptr st ist pt := by
  have h550 := cells_36_entails_memRegion (sp + 0x550#64) o2 o3 o4 o5 o6
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h550
  refine Entails.trans (sepConj_mono_left h550) ?_
  unfold wsStorePostCommonRestPlaced
  have hrejoin :
      (memRegion (sp + 0x550#64) 0x24 ∗ memRegion (sp + 0x580#64) 0x24 ∗
        sessionRecordAt A (sp + 0x120#64) g rec' ∗
        (wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
          vecU8 A (sp + 0x290#64) pt ∗ memRegion sp 0xa0 ∗
          memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
          (memRegion (sp + 0x300#64) 0x250 ∗ memRegion (sp + 0x574#64) 0xc) ∗
          memRegion (sp + 0x5a4#64) 0x85c ∗
          memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
          decStoreExtraPlaced kit ikit st ist s0)) =
      ((stackAt sp wsCalleeStack ∗ decStoreExtraPlaced kit ikit st ist s0) ∗
        sessionRecordAt A (sp + 0x120#64) g rec' ∗ vecU8 A (sp + 0x290#64) pt ∗
        memRegion (sp + 0x300#64) 0x24 ∗ memRegion (sp + 0x580#64) 0x24 ∗
        (wsFixedVPlaced kit ikit x s0 sp ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
          protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
          FromRecordCallees.lsLogOff ∗ A.pool ∗ wsMsgCells x sp ∗
          memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗
          memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x324#64) 0x25c ∗
          memRegion (sp + 0x5a4#64) 0x85c ∗
          memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans))) := by
    unfold wsEnvPlaced
    rw [memRegion_split (sp + 0x300#64) 0x24 0x22c (by decide),
      memRegion_split (sp + 0x324#64) 0x22c 0x30 (by decide),
      memRegion_split (sp + 0x324#64 + 0x22c#64) 0x24 0xc (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl
  rw [hrejoin]
  have hj := wsCalleeStack_join_extra_placed kit ikit st ist s0
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
  unfold wsStoreTailOkPre_placed wsStoreTailOkFramePlaced
  rw [stack_wsCalleeV_storeSeg kit ikit sp hn]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by ac_rfl)

theorem storePost_ok_entails_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
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
    wsStoreTailOkPost_placed A sp prevCap prevPtr v1 v2 v3 v4 s2_hi s3_598 s4_5a0 ∗
      wsStoreTailOkFramePlaced C A ctl kit ikit x ans s0 sp cap ptr st ist pt ⊢
    wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      StagedRes A x28 w20 w21 (sp + 0x300#64) (.ok pt) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x324#64) 0xadc ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtraPlaced kit ikit st ist s0 := by
  subst hx28 hw20 hw21 hsp
  have h120 := memRegion_120_1a8_join (s0.sp - 0xee0#64) prevCap prevPtr v1 v2 v3 v4
  have h580 := cells_36_entails_memRegion (s0.sp - 0xee0#64 + 0x580#64) v2 v3 (s2_hi ++ v4) s3_598 s4_5a0
  have hst := stagedRes_ok_pt A (s0.sp - 0xee0#64 + 0x300#64) cap ptr pt s2_hi s3_598 s4_5a0
    v1 v2 v3 v4 hv1 hv2 hv3 hv4
  have hsplit := wsCalleeStack_split_extra_placed kit ikit st ist s0 hbound
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
    (wsFixedVPlaced kit ikit x s0 (s0.sp - 0xee0#64) ∗
      (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ FromRecordCallees.lsLogOff ∗ A.pool) ∗
      wsMsgCells x (s0.sp - 0xee0#64) ∗ memRegion (s0.sp - 0xee0#64) 0xa0 ∗ memRegion (s0.sp - 0xee0#64 + 0x2d0#64) 0x10 ∗
      memRegion (s0.sp - 0xee0#64 + 0x324#64) 0x25c ∗ memRegion (s0.sp - 0xee0#64 + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans)) by
    unfold wsStoreTailOkPost_placed wsStoreTailOkFramePlaced
    ac_rfl)) ?_
  rw [← stack_wsCalleeV_storeSeg kit ikit (s0.sp - 0xee0#64) hn]
  refine Entails.trans (sepConj_mono h120 (sepConj_mono hst
    (sepConj_mono h580 (sepConj_mono_left hsplit)))) ?_
  unfold wsEnvPlaced; rw [memRegion_324_adc_split (s0.sp - 0xee0#64)]
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 1600000 in
theorem segStore_call_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hdealloc_sat : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hkit : SessionOnlyKitPlacedOkSE kit Scope encRecord H)
    (hstack_lt : storeCallStack kit ≤ 2 ^ 64)
    {s : State} {R : SepProp} {self addrA : BitVec 64}
    {addr : AddrGhost} {g : RecordGhost} {record : SessionRecord (List (BitVec 8))}
    {st : kit.StoreState} {c0 c1 d0 d1 d2 d3 : BitVec 64} {d5 : BitVec 32} {Q : Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (haddr : kit.addrOk addr.val)
    (hrecOk : kit.RecOk record)
    (hpc : s.pc = storeCallPCPlaced)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hfs : FsAt kit.envOk Q (lsProg_197 H) s) :
    SepWPp (lsProg_197 H) ((blkPl_197).base + 9256#64) s
      (((s.sp + 0xe8#64) ↦₆₄ addrA) ∗ ((s.sp + 0xf8#64) ↦₆₄ self) ∗ ((s.sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ kit.storeShimOff) ∗
        (kit.storeFutVtOff ↦₆₄ᵣ kit.storeFutDropOff) ∗
        ((kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ kit.storePollOff) ∗
        ((s.sp + 0x2d0#64) ↦₆₄ c0) ∗ ((s.sp + 0x2d8#64) ↦₆₄ c1) ∗
        ((s.sp + 0x550#64) ↦₆₄ d0) ∗ ((s.sp + 0x558#64) ↦₆₄ d1) ∗ ((s.sp + 0x560#64) ↦₆₄ d2) ∗
        ((s.sp + 0x568#64) ↦₆₄ d3) ∗ ((s.sp + 0x570#64) ↦₃₂ d5) ∗ memRegion (s.sp + 0x5f0#64) 48 ∗
        protocolAddressAt A addr addrA ∗ sessionRecordAt A (s.readReg64 .x26 + 0x80#64) g record ∗
        kit.storeAt self st ∗ A.pool ∗ stackAt s.sp (storeCallStack kit))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (∃∗ ans : Except Unit Unit, ∃∗ box : BitVec 64,
          ∃∗ strPtr : BitVec 64, ∃∗ vt : BitVec 64,
          ∃∗ o1 : BitVec 32, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64,
          ∃∗ o4 : BitVec 64, ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32,
          ⌜kit.storeRel st addr.val record ans ∧
            sf.readReg64 .x28 = pollTag ans ∧
            sf.trace = s.trace ++ kit.storeEvs encRecord addr.val record ans ∧
            sf.readReg64 .x21 = o1.zeroExtend 64 ∧
            pollOutPlacedRel (α := Unit) strPtr vt o2 o3 o4 o5 o1 ans⌝ ∗
          ((s.sp + 0xe8#64) ↦₆₄ addrA) ∗ ((s.sp + 0xf8#64) ↦₆₄ self) ∗ ((s.sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗
          ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ kit.storeShimOff) ∗
          (kit.storeFutVtOff ↦₆₄ᵣ kit.storeFutDropOff) ∗
          ((kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
          ((kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          ((kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ kit.storePollOff) ∗
          ((s.sp + 0x2d0#64) ↦₆₄ box) ∗ ((s.sp + 0x2d8#64) ↦₆₄ kit.storeFutVtOff) ∗
          ((s.sp + 0x550#64) ↦₆₄ o2) ∗ ((s.sp + 0x558#64) ↦₆₄ o3) ∗ ((s.sp + 0x560#64) ↦₆₄ o4) ∗
          ((s.sp + 0x568#64) ↦₆₄ o5) ∗ ((s.sp + 0x570#64) ↦₃₂ o6) ∗
          ((s.sp + 0x5f0#64) ↦₆₄ pollTag ans) ∗ ((s.sp + 0x5f8#64) ↦₃₂ o1) ∗
          ((s.sp + 0x5fc#64) ↦₆₄ o2) ∗ ((s.sp + 0x604#64) ↦₆₄ o3) ∗ ((s.sp + 0x60c#64) ↦₆₄ o4) ∗
          ((s.sp + 0x614#64) ↦₆₄ o5) ∗ ((s.sp + 0x61c#64) ↦₃₂ o6) ∗
          protocolAddressAt A addr addrA ∗ sessionRecordAt A (s.readReg64 .x26 + 0x80#64) g record ∗
          kit.storeAt self (kit.storeUpdate st addr.val record ans) ∗
          (if ans.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
          A.pool ∗ stackAt s.sp (storeCallStack kit)) ∗ R) ∧
        sf.sp = s.sp ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have hshim := shim_197 (hkit.storeShim (callerProg := lsProg_197 H) (callerBlk := 197) (by decide))
  have hdrop := futDrop_197 (hkit.storeFutDrop (callerProg := lsProg_197 H) (callerBlk := 197) (by decide))
  unfold storeCallPCPlaced at hpc
  dsimp only [lsProg_197] at hfs ⊢
  have hdealloc : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsρ lsRustDeallocSym)
      (rustDeallocSpec A) := ls_hook_ok_of_mem hdealloc_sat
  refine SepWPp.congr_pre (by rw [stack_storeCall_to_storeShim kit s.sp hstack_lt]) ?_
  apply StoreKit.sepWPp_seq_lscro (mid := kit.storeShimOff) hcrl
  clear hcrl
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  intro hcrl1
  messageDecrypt_call_panic_p_lscro hshim hcrl1
    (⟨self, addrA, s.readReg64 .x26 + 0x80#64⟩ : StoreShimCall)
  clear hcrl1 hshim
  apply StoreKit.sepWPp_seq_lscro (mid := kit.storePollOff) hcrl_sf
  clear hcrl_sf
  wp_simp_pre [sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hsteps_sh, hx1_sf, hx0_ne, hx0_al, htr_sf⟩
  have henv : kit.envOk sf.fs.files :=
    (hfs.of_call hsteps_sh (by simp only [arm64_norm]) htr_sf).envOk_here
  clear hsteps_sh hfs
  apply SepWP.fold (Entails.of_eq (stack_storeShim_to_storePoll kit s.sp hstack_lt)) (by sep_focus)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  intro hcrl2
  have hpoll := box_lscro_197 (hkit.storePoll (callerProg := lsProg_197 H) (callerBlk := 197) (by decide))
  messageDecrypt_call_panic_lscro hpoll hcrl2 (⟨sf.readReg64 (Reg.gpr 0#5), s.sp + 0x5f0#64,
    ⟨addrA, addr, s.readReg64 .x26 + 0x80#64, g, record⟩⟩, self, st)
  clear hcrl2 hpoll hkit
  generalize hbox : sf.readReg64 (Reg.gpr 0#5) = box at *
  simp only [hsp_sf] at hsp_sf_1 ⊢
  have hdz : kit.storeFutDropOff ≠ 0#64 := by
    simpa only [BitVec.zero_add] using kit.storeFutDrop_ne_zero (by decide)
  have hdz' : (kit.storeFutDropOff == 0#64) = false := beq_eq_false_iff_ne.mpr hdz
  have hbs := kit.storeBoxSize_ne_zero
  have hbs' : (BitVec.ofNat 64 kit.storeBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs
  have hbs_toNat : (BitVec.ofNat 64 kit.storeBoxSize).toNat = kit.storeBoxSize :=
    Nat.mod_eq_of_lt kit.storeBoxSize_lt
  rcases w with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · dsimp only [StoreKit.storePollPlacedOutAt]
    wp_simp_pre [StoreKit.errTailPlacedAt, ProofLib.memRegion_eight,
      sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    apply SepWP.exists_elim; intro (strPtr : BitVec 64)
    apply SepWP.exists_elim; intro (vt : BitVec 64)
    apply SepWP.exists_elim; intro (w5 : BitVec 64)
    apply SepWP.fold
      (Entails.of_eq (out_repack_sp s.sp strPtr 10#64 1#64 vt w5))
      (by sep_focus)
    apply StoreKit.sepWP_seq_lscro hcrl_poll (mid := kit.storeFutDropOff)
    wp_steps
    refine SepWP.done (by simp_all) (by simp_all) fun ⟨hcl_d, hro_d⟩ => ?_
    wp_call hdrop ()
    wp_steps
    apply SepWP.fold (kit.storeBoxAt_memRegion box self addrA (s.readReg64 (Reg.gpr 26#5) + 128#64) 1#8) (by sep_focus)
    apply SepWP.fold (Entails.of_eq (stack_storePoll_to_alloc kit s.sp hstack_lt)) (by sep_focus)
    wp_call hdealloc (box, kit.storeBoxSize, 8)
    simp only [h_22, hsp_sf_1] at hsp_sf_2 ⊢
    apply SepWP.fold (Entails.of_eq (stack_alloc_to_storeCall kit s.sp hstack_lt)) (by sep_focus)
    simp only [show (9223372036854775834#64 : BitVec 64) = pollTag (.error ()) from rfl] at *
    apply SepWP.done (by simp_all) (by simp_all)
    refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
    refine Entails.sepExists_right (.error ())
      (Entails.sepExists_right box
      (Entails.sepExists_right strPtr
      (Entails.sepExists_right vt
      (Entails.sepExists_right (strPtr.extractLsb' 0 32)
      (Entails.sepExists_right (10#32 ++ strPtr.extractLsb' 32 32)
      (Entails.sepExists_right 4294967296#64
      (Entails.sepExists_right (vt.extractLsb' 0 32 ++ 0#32)
      (Entails.sepExists_right (w5.extractLsb' 0 32 ++ vt.extractLsb' 32 32)
      (Entails.sepExists_right (w5.extractLsb' 32 32) ?_)))))))))
    refine Entails.pure_right (by simp_all) ?_
    dsimp only [Except.isOk, Except.toBool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)
  · dsimp only [StoreKit.storePollPlacedOutAt]
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
    apply SepWP.exists_elim; intro (w1 : BitVec 64)
    apply SepWP.exists_elim; intro (w2 : BitVec 64)
    apply SepWP.exists_elim; intro (w3 : BitVec 64)
    apply SepWP.exists_elim; intro (w4 : BitVec 64)
    apply SepWP.exists_elim; intro (w5 : BitVec 64)
    apply SepWP.fold
      (Entails.of_eq (out_repack_sp s.sp w5 w4 w3 w2 w1))
      (by sep_focus)
    apply StoreKit.sepWP_seq_lscro hcrl_poll (mid := kit.storeFutDropOff)
    wp_steps
    refine SepWP.done (by simp_all) (by simp_all) fun ⟨hcl_d, hro_d⟩ => ?_
    wp_call hdrop ()
    wp_steps
    apply SepWP.fold (kit.storeBoxAt_memRegion box self addrA (s.readReg64 (Reg.gpr 26#5) + 128#64) 1#8) (by sep_focus)
    apply SepWP.fold (Entails.of_eq (stack_storePoll_to_alloc kit s.sp hstack_lt)) (by sep_focus)
    wp_call hdealloc (box, kit.storeBoxSize, 8)
    simp only [h_22, hsp_sf_1] at hsp_sf_2 ⊢
    apply SepWP.fold (Entails.of_eq (stack_alloc_to_storeCall kit s.sp hstack_lt)) (by sep_focus)
    simp only [show (bv% (2 ^ 64 - 2) : BitVec 64) = pollTag (.ok ()) from rfl] at *
    apply SepWP.done (by simp_all) (by simp_all)
    refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
    refine Entails.sepExists_right (.ok ())
      (Entails.sepExists_right box
      (Entails.sepExists_right 0#64
      (Entails.sepExists_right 0#64
      (Entails.sepExists_right (w5.extractLsb' 0 32)
      (Entails.sepExists_right (w4.extractLsb' 0 32 ++ w5.extractLsb' 32 32)
      (Entails.sepExists_right (w3.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
      (Entails.sepExists_right (w2.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
      (Entails.sepExists_right (w1.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
      (Entails.sepExists_right (w1.extractLsb' 32 32) ?_)))))))))
    refine Entails.pure_right (by simp_all) ?_
    dsimp only [Except.isOk, Except.toBool]
    simp only [↓reduceIte, emp_sepConj]
    exact Entails.of_eq (by ac_rfl)

end Placed

end CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegStore
