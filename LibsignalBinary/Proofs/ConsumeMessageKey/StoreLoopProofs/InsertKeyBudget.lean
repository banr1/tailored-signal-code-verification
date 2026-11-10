/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DefsBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.InsertKey
import LibsignalBinary.Proofs.Common.HookTrace
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `InsertKey` Sub-Segment (Block 24)

Proves `InsertKeyPlacedSpec` under `RustCliAllocBudget M` and `SeamBudget`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.InsertKeyBudget

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (ShaState keyToBytes32)
open CryptoGames.LibsignalSession (
  ChainKey MessageKeyGenerator PublicKey RatchetState ReceiverChain maxMessageKeys
)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement blkPC_24 blkPl_24 lsmpl lsρ withLsCodeLoaded
)
open CryptoVerification.RustHeap (
  RustAlloc arrayAt memRegion_24_eq_exists_vecHeader vecAt vecBuf vecHeader vecU8Buf
)
open CryptoVerification.LibsignalSessionRepr (
  ChainGhost MessageKeyArrayBytes MessageKeyGhost RatchetGhost
  chainAt chainAt_of_update_messageKeys chainKeyBytes grow_one_newCap_props
  memRegion_104_entails_messageKey_slots messageKeyAt messageKeyAt_eq_headers_sep_heap
  messageKeyHeap messageKeyHeaps optChainKeyAt optSenderChainBytes
  pointsToBytes_listMove_insert0 ratchetAt ratchetAt_set_chain ratchetAt_split_chain
  vecBuf_messageKeyAt_expose_for_insert0 vecBuf_messageKeyAt_full_entails_grow_one
  vecBuf_messageKeyAt_of_grow_one vecBuf_messageKeyAt_of_insert0 vecGhostAt
)
open CryptoVerification.LibsignalSession (
  ConsumeMessageKeyGhost GrowGhost cmkDummyImg cmkLoopFrame cmkLoopHeap
  cmkLoopHeap_placed cmkLoopHeap_placed_eq cmkSavedRegs cmk_hook_ok_of_mem
  logFilterAddr logFilterAddr_cmkDummyImg
)
open CryptoVerification.LibsignalSession.StoreLoop (
  AdvanceChainKeyRegs EvictOldestKeyRegs add_one_ofNat_64 evictOldestKeyHeap
  evictOldestKeyHeapAt evictOldestKeyHeap_placed insertKeyActiveMid insertKeyActivePost
  insertKeyActivePre introduce_withLsCodeLoaded madd_104_toNat madd_chainPtr_eq
  messageKeys_seed_length mkLen_beq_mkCap_false mkLen_eq_mkCap_of_eq
  mkLen_ule_1999_eq_true newMsgKeyGhost pointsToBytes_insert0_zero
  ratchetContextAt sepWP_elim_inv_placed sepWPp_seq_lscl
  steps_of_sepWPp_placed updatedRatchetState updatedReceiverChain
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (hookSat_withVmPreserved withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (
  vmPreserved_refl_iff vmPreserved_setMem_writeBytes vmPreserved_setPC
)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (CmkEnv)
open LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget (
  GrowOneEnv GrowOnePlacedOk growOneSpec
)
open LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DefsBudget (
  CmkGrowOptEvs ConcatEnv InsertKeyPlacedSpec cmkNextCap
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SeamBudget)

attribute [local irreducible] Program.fetch Program.externAt? cmkDummyImg
attribute [-simp, -arm64_norm, -wp_norm] logFilterAddr_cmkDummyImg
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Spatial and Stack Helpers -/

private theorem vecU8Buf_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf (A.atState lim st s) cap ptr bs = vecU8Buf A.repAlloc cap ptr bs := rfl

private theorem messageKeyHeap_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State)
    (gk : MessageKeyGhost × MessageKeyGenerator) :
    messageKeyHeap (A.atState lim st s) gk = messageKeyHeap A.repAlloc gk := rfl

private theorem messageKeyHeaps_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    ∀ gks : List (MessageKeyGhost × MessageKeyGenerator),
      messageKeyHeaps (A.atState lim st s) gks = messageKeyHeaps A.repAlloc gks
  | [] => rfl
  | gk :: gks => by
    simp only [messageKeyHeaps, messageKeyHeap_atState, messageKeyHeaps_atState A lim st s gks]

private theorem messageKeyAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    messageKeyAt (A.atState lim st s) = messageKeyAt A.repAlloc := by
  funext gk a; rfl

private theorem vecBuf_messageKeyAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (cap ptr : BitVec 64)
    (gks : List (MessageKeyGhost × MessageKeyGenerator)) :
    vecBuf (A.atState lim st s) 104 8 (messageKeyAt (A.atState lim st s)) cap ptr gks =
      vecBuf A.repAlloc 104 8 (messageKeyAt A.repAlloc) cap ptr gks := by
  unfold vecBuf
  rw [messageKeyAt_atState]
  rfl

private theorem stackAt_7712_eq_grow (sp : BitVec 64) :
    stackAt sp 7712 = memRegion (sp - 7712#64) 3104 ∗ stackAt sp 4608 := by
  simp only [stackAt]
  rw [show (7712 : Nat) = 3104 + 4608 from rfl, memRegion_split _ 3104 4608 (by decide)]
  have h : sp - 7712#64 + BitVec.ofNat 64 3104 = sp - 4608#64 := by bv_arith
  rw [h]

private theorem stackAt_7712_eq_4096 (sp : BitVec 64) :
    stackAt sp 7712 = memRegion (sp - 7712#64) 3616 ∗ stackAt sp 4096 := by
  simp only [stackAt]
  rw [show (7712 : Nat) = 3616 + 4096 from rfl, memRegion_split _ 3616 4096 (by decide)]
  have h : sp - 7712#64 + BitVec.ofNat 64 3616 = sp - 4096#64 := by bv_arith
  rw [h]

private theorem memRegion_104_entails_messageKey_words (a : BitVec 64) :
    memRegion a 104 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
      ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64,
      ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
      ∃∗ w12 : BitVec 32,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
        ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
        ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₆₄ w8) ∗
        ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗
        ((a + 96#64) ↦₃₂ w12) ∗ memRegion (a + 100#64) 4 := by
  refine Entails.trans (memRegion_104_entails_messageKey_slots a) ?_
  rw [memRegion_24_eq_exists_vecHeader a,
      memRegion_24_eq_exists_vecHeader (a + 24#64),
      memRegion_24_eq_exists_vecHeader (a + 48#64),
      memRegion_24_eq_exists_vecHeader (a + 72#64),
      memRegion_four (a + 96#64)]
  simp only [vecHeader, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w0
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w4
  apply Entails.sepExists_elim; intro w5
  apply Entails.sepExists_elim; intro w6
  apply Entails.sepExists_elim; intro w7
  apply Entails.sepExists_elim; intro w8
  apply Entails.sepExists_elim; intro w9
  apply Entails.sepExists_elim; intro w10
  apply Entails.sepExists_elim; intro w11
  apply Entails.sepExists_elim; intro w12
  apply Entails.sepExists_right w10
  apply Entails.sepExists_right w11
  apply Entails.sepExists_right w12
  apply Entails.sepExists_right w7
  apply Entails.sepExists_right w8
  apply Entails.sepExists_right w9
  apply Entails.sepExists_right w4
  apply Entails.sepExists_right w5
  apply Entails.sepExists_right w6
  apply Entails.sepExists_right w1
  apply Entails.sepExists_right w2
  apply Entails.sepExists_right w3
  apply Entails.sepExists_right w0
  have h32 : a + 24#64 + 8#64 = a + 32#64 := by bv_arith
  have h40 : a + 24#64 + 16#64 = a + 40#64 := by bv_arith
  have h56 : a + 48#64 + 8#64 = a + 56#64 := by bv_arith
  have h64 : a + 48#64 + 16#64 = a + 64#64 := by bv_arith
  have h80 : a + 72#64 + 8#64 = a + 80#64 := by bv_arith
  have h88 : a + 72#64 + 16#64 = a + 88#64 := by bv_arith
  rw [h32, h40, h56, h64, h80, h88]
  exact Entails.refl _

private theorem messageKeyAt_newMsgKeyGhost_intro (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustAlloc) (ckc : ChainKey) (seedPtr a : BitVec 64) :
    ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
     ((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ∗
     ((a + 48#64) ↦₆₄ 0#64) ∗ ((a + 56#64) ↦₆₄ 1#64) ∗ ((a + 64#64) ↦₆₄ 0#64) ∗
     ((a + 72#64) ↦₆₄ 32#64) ∗ ((a + 80#64) ↦₆₄ seedPtr) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗
     ((a + 96#64) ↦₃₂ ckc.index) ∗ memRegion (a + 100#64) 4 ∗
     vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed) ⊢
    messageKeyAt A (newMsgKeyGhost seedPtr, ckc.messageKeys F) a := by
  have hseed_len : (ckc.messageKeys F).seed.length = 32 := messageKeys_seed_length F ckc
  have hseed_ne : (ckc.messageKeys F).seed ≠ [] := by
    intro hnil; rw [hnil] at hseed_len; contradiction
  have hctr : (ckc.messageKeys F).counter = ckc.index := rfl
  rw [messageKeyAt_eq_headers_sep_heap]
  unfold messageKeyHeap newMsgKeyGhost vecHeader
  dsimp only
  rw [hseed_len, hctr]
  have h32 : a + 24#64 + 8#64 = a + 32#64 := by bv_arith
  have h40 : a + 24#64 + 16#64 = a + 40#64 := by bv_arith
  have h56 : a + 48#64 + 8#64 = a + 56#64 := by bv_arith
  have h64 : a + 48#64 + 16#64 = a + 64#64 := by bv_arith
  have h80 : a + 72#64 + 8#64 = a + 80#64 := by bv_arith
  have h88 : a + 72#64 + 16#64 = a + 88#64 := by bv_arith
  rw [h32, h40, h56, h64, h80, h88]
  have hpure0 : emp ⊢ vecU8Buf A 0#64 1#64 [] := by
    unfold vecU8Buf
    simp only [BitVec.ofNat_eq_ofNat, ↓reduceIte]
    exact Entails.pure_right ⟨by decide, by decide, by decide⟩ (Entails.refl _)
  have hassoc :
      ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
       ((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ∗
       ((a + 48#64) ↦₆₄ 0#64) ∗ ((a + 56#64) ↦₆₄ 1#64) ∗ ((a + 64#64) ↦₆₄ 0#64) ∗
       ((a + 72#64) ↦₆₄ 32#64) ∗ ((a + 80#64) ↦₆₄ seedPtr) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗
       ((a + 96#64) ↦₃₂ ckc.index) ∗ memRegion (a + 100#64) 4 ∗
       vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed) =
      (((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64)) ∗
       (((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64)) ∗
       (((a + 48#64) ↦₆₄ 0#64) ∗ ((a + 56#64) ↦₆₄ 1#64) ∗ ((a + 64#64) ↦₆₄ 0#64)) ∗
       (((a + 72#64) ↦₆₄ 32#64) ∗ ((a + 80#64) ↦₆₄ seedPtr) ∗ ((a + 88#64) ↦₆₄ 32#64)) ∗
       ((a + 96#64) ↦₃₂ ckc.index) ∗ memRegion (a + 100#64) 4) ∗
      (emp ∗ emp ∗ emp ∗ vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed) := by
    sep_ac_rfl
  rw [hassoc]
  apply sepConj_mono_right
  apply Entails.pure_right hseed_ne
  exact sepConj_mono hpure0 (sepConj_mono hpure0 (sepConj_mono_left hpure0))

private theorem vecBuf_messageKeyAt_bounds (A : RustAlloc) (cap ptr : BitVec 64)
    (gks : List (MessageKeyGhost × MessageKeyGenerator)) :
    vecBuf A 104 8 (messageKeyAt A) cap ptr gks ⊢
      ⌜gks.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        vecBuf A 104 8 (messageKeyAt A) cap ptr gks := by
  by_cases hcap : cap = 0
  · subst hcap
    rw [CryptoVerification.RustHeap.vecBuf_zero, ← sepConj_emp ⌜gks = [] ∧ ptr ≠ 0⌝]
    apply Entails.pure_left
    rintro ⟨hnil, hptr⟩
    apply Entails.pure_right ⟨by simp [hnil], by decide, hptr⟩
    exact Entails.pure_right ⟨hnil, hptr⟩ (Entails.refl _)
  · rw [CryptoVerification.RustHeap.vecBuf_of_ne_zero A 104 8 (messageKeyAt A) cap ptr gks hcap]
    apply Entails.pure_left
    rintro ⟨hlen, hcap_lt, hptr⟩
    apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩
    exact Entails.pure_right ⟨hlen, hcap_lt, hptr⟩ (Entails.refl _)

private def insertKeyFrame (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost)
    (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost) (s0 : State) : SepProp :=
  let chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
  ⌜cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
  vecGhostAt A cg.srk chainPtr ∗
  vecGhostAt A cg.priv (chainPtr + 24#64) ∗
  optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
  ratchetContextAt A x.self Gc stc ci ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ chainKeyBytes ckc) ∗
  memRegion x.ret 88 ∗
  (logFilterAddr img ↦₆₄ 0#64) ∗
  cmkLoopFrame s0.sp x.ret x.counter ∗
  cmkSavedRegs s0.sp s0

private theorem insertKeyState_chains_len (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (img : Obj.Image) (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState)
    (ckc : ChainKey) (seedPtr : BitVec 64) (s0 : State) :
    (cmkLoopHeap A img x Gc stc ckc s0 ∗ vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed) ⊢
      ⌜Gc.chains.length = stc.receiverChains.length⌝ ∗
        (cmkLoopHeap A img x Gc stc ckc s0 ∗ vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed) := by
  unfold cmkLoopHeap ratchetAt
  simp only [sepConj_assoc]
  apply Entails.pure_left
  rintro ⟨h1, h2, h3⟩
  exact Entails.pure_right h1 (Entails.pure_right ⟨h1, h2, h3⟩ (Entails.refl _))

private theorem insertKeyState_split_active (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (img : Obj.Image) (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState)
    (ckc : ChainKey) (ci : Nat) (chc : ReceiverChain)
    (seedPtr : BitVec 64) (s0 : State)
    (hchc : stc.receiverChains[ci]? = some chc)
    (hci_g : ci < Gc.chains.length) :
    let cg := Gc.chains[ci]
    (cmkLoopHeap A img x Gc stc ckc s0 ∗ vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed) ⊢
      ⌜PublicKey.deserialize cg.srk.bytes = .ok chc.senderRatchetKey ∧
        chc.messageKeys.length ≤ maxMessageKeys ∧
        cg.keys.length = chc.messageKeys.length⌝ ∗
        insertKeyActivePre F A (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)) cg chc ckc seedPtr (s0.sp - 480#64) ∗
        insertKeyFrame A img x Gc stc ckc ci chc cg s0 := by
  intro cg
  have ⟨hci_st, hchc_get⟩ := List.getElem?_eq_some_iff.mp hchc
  unfold cmkLoopHeap
  refine Entails.trans
    (sepConj_mono_left (sepConj_mono_left (ratchetAt_split_chain A x.self Gc stc hci_st hci_g))) ?_
  rw [hchc_get]
  set chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
  simp only [sepConj_assoc]
  apply Entails.pure_left; rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have hchain_eq : chainAt A (Gc.chains[ci], chc) chainPtr =
      (⌜PublicKey.deserialize cg.srk.bytes = .ok chc.senderRatchetKey ∧
        chc.messageKeys.length ≤ maxMessageKeys ∧
        cg.keys.length = chc.messageKeys.length ∧
        cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
       vecGhostAt A cg.srk chainPtr ∗
       vecGhostAt A cg.priv (chainPtr + 24#64) ∗
       (vecHeader (chainPtr + 48#64) cg.mkCap cg.mkPtr (BitVec.ofNat 64 (cg.keys.zip chc.messageKeys).length) ∗
        vecBuf A 104 8 (messageKeyAt A) cg.mkCap cg.mkPtr (cg.keys.zip chc.messageKeys)) ∗
       optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64)) := rfl
  rw [hchain_eq]
  have hpull0 :
      (vecHeader x.self Gc.chainsCap Gc.chainsPtr (BitVec.ofNat 64 stc.receiverChains.length) ∗
        A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
        (⌜PublicKey.deserialize cg.srk.bytes = .ok chc.senderRatchetKey ∧
          chc.messageKeys.length ≤ maxMessageKeys ∧
          cg.keys.length = chc.messageKeys.length ∧
          cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
         vecGhostAt A cg.srk chainPtr ∗
         vecGhostAt A cg.priv (chainPtr + 24#64) ∗
         (vecHeader (chainPtr + 48#64) cg.mkCap cg.mkPtr (BitVec.ofNat 64 (cg.keys.zip chc.messageKeys).length) ∗
          vecBuf A 104 8 (messageKeyAt A) cg.mkCap cg.mkPtr (cg.keys.zip chc.messageKeys)) ∗
         optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64)) ∗
        arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
        arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
          ((Gc.chains.zip stc.receiverChains).drop (ci + 1)) ∗
        memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
          ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
        ((x.self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((x.self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((x.self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (x.self + 172#64) 4 ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (x.ckA ↦ₛ chainKeyBytes ckc) ∗
        memRegion x.ret 88 ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗
        stackAt (s0.sp - 480#64) 7712 ∗
        cmkLoopFrame s0.sp x.ret x.counter ∗
        cmkSavedRegs s0.sp s0 ∗
        A.pool ∗
        vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed) =
      (⌜PublicKey.deserialize cg.srk.bytes = .ok chc.senderRatchetKey ∧
        chc.messageKeys.length ≤ maxMessageKeys ∧
        cg.keys.length = chc.messageKeys.length ∧
        cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
       (vecHeader x.self Gc.chainsCap Gc.chainsPtr (BitVec.ofNat 64 stc.receiverChains.length) ∗
        A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
        vecGhostAt A cg.srk chainPtr ∗
        vecGhostAt A cg.priv (chainPtr + 24#64) ∗
        vecHeader (chainPtr + 48#64) cg.mkCap cg.mkPtr (BitVec.ofNat 64 (cg.keys.zip chc.messageKeys).length) ∗
        vecBuf A 104 8 (messageKeyAt A) cg.mkCap cg.mkPtr (cg.keys.zip chc.messageKeys) ∗
        optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
        arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
        arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
          ((Gc.chains.zip stc.receiverChains).drop (ci + 1)) ∗
        memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
          ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
        ((x.self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((x.self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((x.self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (x.self + 172#64) 4 ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (x.ckA ↦ₛ chainKeyBytes ckc) ∗
        memRegion x.ret 88 ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗
        stackAt (s0.sp - 480#64) 7712 ∗
        cmkLoopFrame s0.sp x.ret x.counter ∗
        cmkSavedRegs s0.sp s0 ∗
        A.pool ∗
        vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed)) := by
    sep_ac_rfl
  rw [hpull0]
  apply Entails.pure_left; rintro ⟨hsrk, hmax, hklen, hsrk_len, hpriv⟩
  have hzip_len : (cg.keys.zip chc.messageKeys).length = chc.messageKeys.length := by
    simp [hklen]
  rw [hzip_len]
  apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
  unfold insertKeyActivePre insertKeyFrame ratchetContextAt
  dsimp only
  have hpull :
      (vecHeader x.self Gc.chainsCap Gc.chainsPtr (BitVec.ofNat 64 stc.receiverChains.length) ∗
        A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
        vecGhostAt A cg.srk chainPtr ∗
        vecGhostAt A cg.priv (chainPtr + 24#64) ∗
        vecHeader (chainPtr + 48#64) cg.mkCap cg.mkPtr (BitVec.ofNat 64 chc.messageKeys.length) ∗
        vecBuf A 104 8 (messageKeyAt A) cg.mkCap cg.mkPtr (cg.keys.zip chc.messageKeys) ∗
        optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
        arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
        arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
          ((Gc.chains.zip stc.receiverChains).drop (ci + 1)) ∗
        memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
          ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
        ((x.self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((x.self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((x.self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (x.self + 172#64) 4 ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (x.ckA ↦ₛ chainKeyBytes ckc) ∗
        memRegion x.ret 88 ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗
        stackAt (s0.sp - 480#64) 7712 ∗
        cmkLoopFrame s0.sp x.ret x.counter ∗
        cmkSavedRegs s0.sp s0 ∗
        A.pool ∗
        vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed) =
      ((vecHeader (chainPtr + 48#64) cg.mkCap cg.mkPtr (BitVec.ofNat 64 chc.messageKeys.length) ∗
        vecBuf A 104 8 (messageKeyAt A) cg.mkCap cg.mkPtr (cg.keys.zip chc.messageKeys) ∗
        vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed ∗
        stackAt (s0.sp - 480#64) 7712 ∗
        A.pool) ∗
       emp ∗
       vecGhostAt A cg.srk chainPtr ∗
       vecGhostAt A cg.priv (chainPtr + 24#64) ∗
       optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
       (emp ∗
        vecHeader x.self Gc.chainsCap Gc.chainsPtr (BitVec.ofNat 64 stc.receiverChains.length) ∗
        A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
        arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
        arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
          ((Gc.chains.zip stc.receiverChains).drop (ci + 1)) ∗
        memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
          ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
        ((x.self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((x.self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((x.self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (x.self + 172#64) 4) ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (x.ckA ↦ₛ chainKeyBytes ckc) ∗
       memRegion x.ret 88 ∗
       (logFilterAddr img ↦₆₄ 0#64) ∗
       cmkLoopFrame s0.sp x.ret x.counter ∗
       cmkSavedRegs s0.sp s0) := by
    sep_ac_rfl
  rw [hpull]
  apply sepConj_mono_right
  rw [emp_sepConj]
  refine Entails.pure_right ⟨hsrk_len, hpriv⟩ ?_
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_left
  exact Entails.pure_right ⟨h1, h2, h3, h4, h5, h6, h7⟩ (by rw [emp_sepConj]; exact Entails.refl _)

private theorem insertKeyPost_entails_evictOldestKeyHeap (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost)
    (stc : RatchetState) (ckc : ChainKey) (ci : Nat) (chc : ReceiverChain)
    (cg : ChainGhost) (mkCap1 mkPtr1 seedPtr : BitVec 64) (s0 : State)
    (hlen2000 : chc.messageKeys.length = 2000) :
    (insertKeyActivePost F A (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)) mkCap1 mkPtr1 cg chc ckc seedPtr (s0.sp - 480#64) ∗
      insertKeyFrame A img x Gc stc ckc ci chc cg s0) ⊢
      evictOldestKeyHeap F A img x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr s0 := by
  unfold insertKeyActivePost insertKeyFrame evictOldestKeyHeap
  dsimp only
  rw [hlen2000]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem insertKeyPost_entails_cmkLoopHeap_D (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost)
    (stc : RatchetState) (ckc : ChainKey) (ci : Nat) (chc : ReceiverChain)
    (cg : ChainGhost) (mkCap1 mkPtr1 seedPtr : BitVec 64) (s0 : State)
    (hci_st : ci < stc.receiverChains.length)
    (hsrk : PublicKey.deserialize cg.srk.bytes = .ok chc.senderRatchetKey)
    (hklen : cg.keys.length = chc.messageKeys.length)
    (hlt2000 : chc.messageKeys.length < 2000) :
    let cg' : ChainGhost :=
      { cg with
        mkCap := mkCap1
        mkPtr := mkPtr1
        keys := newMsgKeyGhost seedPtr :: cg.keys }
    (insertKeyActivePost F A (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)) mkCap1 mkPtr1 cg chc ckc seedPtr (s0.sp - 480#64) ∗
      insertKeyFrame A img x Gc stc ckc ci chc cg s0) ⊢
      cmkLoopHeap A img x (Gc.setChain ci cg') (updatedRatchetState F stc ci chc ckc) ckc s0 := by
  intro cg'
  have htake : (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys =
      ckc.messageKeys F :: chc.messageKeys := by
    apply List.take_of_length_le
    simp only [List.length_cons, maxMessageKeys]
    omega
  have hupd_ch : updatedReceiverChain F chc ckc =
      { chc with messageKeys := ckc.messageKeys F :: chc.messageKeys } := by
    unfold updatedReceiverChain
    rw [htake]
  have hupd_st : updatedRatchetState F stc ci chc ckc =
      stc.setChain ci { chc with messageKeys := ckc.messageKeys F :: chc.messageKeys } := by
    unfold updatedRatchetState RatchetState.setChain
    rw [hupd_ch]
  rw [hupd_st]
  have hmax' : (ckc.messageKeys F :: chc.messageKeys).length ≤ maxMessageKeys := by
    simp only [List.length_cons, maxMessageKeys]; omega
  have hklen' : (newMsgKeyGhost seedPtr :: cg.keys).length =
      (ckc.messageKeys F :: chc.messageKeys).length := by
    simp [hklen]
  have hzip_cons :
      (newMsgKeyGhost seedPtr :: cg.keys).zip (ckc.messageKeys F :: chc.messageKeys) =
        (newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys := rfl
  have hzip_len' :
      ((newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys).length =
        chc.messageKeys.length + 1 := by
    simp [hklen]
  set chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
  unfold insertKeyActivePost insertKeyFrame cmkLoopHeap ratchetContextAt
  dsimp only
  have hpull0 :
      ((vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 (BitVec.ofNat 64 (chc.messageKeys.length + 1)) ∗
        vecBuf A 104 8 (messageKeyAt A) mkCap1 mkPtr1
          ((newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys) ∗
        stackAt (s0.sp - 480#64) 7712 ∗
        A.pool) ∗
       ⌜cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
       vecGhostAt A cg.srk chainPtr ∗
       vecGhostAt A cg.priv (chainPtr + 24#64) ∗
       optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
       (⌜Gc.chains.length = stc.receiverChains.length ∧ Gc.senderPad.length = 100 ∧
          stc.maxForwardJumps < 2 ^ 64 ∧
          stc.receiverChains.length ≤ Gc.chainsCap.toNat ∧
          Gc.chainsCap.toNat * 104 < 2 ^ 63 ∧ Gc.chainsPtr ≠ 0 ∧ Gc.chainsCap ≠ 0⌝ ∗
        vecHeader x.self Gc.chainsCap Gc.chainsPtr (BitVec.ofNat 64 stc.receiverChains.length) ∗
        A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
        arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
        arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
          ((Gc.chains.zip stc.receiverChains).drop (ci + 1)) ∗
        memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
          ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
        ((x.self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((x.self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((x.self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (x.self + 172#64) 4) ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (x.ckA ↦ₛ chainKeyBytes ckc) ∗
       memRegion x.ret 88 ∗
       (logFilterAddr img ↦₆₄ 0#64) ∗
       cmkLoopFrame s0.sp x.ret x.counter ∗
       cmkSavedRegs s0.sp s0) =
      (⌜cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
       ⌜Gc.chains.length = stc.receiverChains.length ∧ Gc.senderPad.length = 100 ∧
        stc.maxForwardJumps < 2 ^ 64 ∧
        stc.receiverChains.length ≤ Gc.chainsCap.toNat ∧
        Gc.chainsCap.toNat * 104 < 2 ^ 63 ∧ Gc.chainsPtr ≠ 0 ∧ Gc.chainsCap ≠ 0⌝ ∗
       (vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 (BitVec.ofNat 64 (chc.messageKeys.length + 1)) ∗
        vecBuf A 104 8 (messageKeyAt A) mkCap1 mkPtr1
          ((newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys) ∗
        stackAt (s0.sp - 480#64) 7712 ∗
        A.pool ∗
        vecGhostAt A cg.srk chainPtr ∗
        vecGhostAt A cg.priv (chainPtr + 24#64) ∗
        optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
        vecHeader x.self Gc.chainsCap Gc.chainsPtr (BitVec.ofNat 64 stc.receiverChains.length) ∗
        A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
        arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
        arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
          ((Gc.chains.zip stc.receiverChains).drop (ci + 1)) ∗
        memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
          ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
        ((x.self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((x.self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((x.self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (x.self + 172#64) 4 ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (x.ckA ↦ₛ chainKeyBytes ckc) ∗
        memRegion x.ret 88 ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗
        cmkLoopFrame s0.sp x.ret x.counter ∗
        cmkSavedRegs s0.sp s0)) := by sep_ac_rfl
  rw [hpull0]
  apply Entails.pure_left; rintro ⟨hsrk_len, hpriv⟩
  apply Entails.pure_left; rintro ⟨hchains_len, hpad_len, hmax_jumps, hcap_le, hcap_lt, hptr_ne, _⟩
  have hchain :
      (vecGhostAt A cg.srk chainPtr ∗
        vecGhostAt A cg.priv (chainPtr + 24#64) ∗
        vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 (BitVec.ofNat 64 (chc.messageKeys.length + 1)) ∗
        vecBuf A 104 8 (messageKeyAt A) mkCap1 mkPtr1
          ((newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys) ∗
        optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64)) ⊢
      chainAt A (cg', { chc with messageKeys := ckc.messageKeys F :: chc.messageKeys }) chainPtr := by
    have h := chainAt_of_update_messageKeys A cg chc chainPtr mkCap1 mkPtr1
      (newMsgKeyGhost seedPtr :: cg.keys) (ckc.messageKeys F :: chc.messageKeys)
      hsrk hmax' hklen' hsrk_len hpriv
    unfold vecAt at h
    rw [hzip_cons, hzip_len'] at h
    have heq :
        (vecGhostAt A cg.srk chainPtr ∗
          vecGhostAt A cg.priv (chainPtr + 24#64) ∗
          vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 (BitVec.ofNat 64 (chc.messageKeys.length + 1)) ∗
          vecBuf A 104 8 (messageKeyAt A) mkCap1 mkPtr1
            ((newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys) ∗
          optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64)) =
        (vecGhostAt A cg.srk chainPtr ∗
          vecGhostAt A cg.priv (chainPtr + 24#64) ∗
          (vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 (BitVec.ofNat 64 (chc.messageKeys.length + 1)) ∗
           vecBuf A 104 8 (messageKeyAt A) mkCap1 mkPtr1
             ((newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys)) ∗
          optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64)) := by sep_ac_rfl
    rw [heq]
    exact h
  have hpull1 :
      (vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 (BitVec.ofNat 64 (chc.messageKeys.length + 1)) ∗
        vecBuf A 104 8 (messageKeyAt A) mkCap1 mkPtr1
          ((newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys) ∗
        stackAt (s0.sp - 480#64) 7712 ∗
        A.pool ∗
        vecGhostAt A cg.srk chainPtr ∗
        vecGhostAt A cg.priv (chainPtr + 24#64) ∗
        optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
        vecHeader x.self Gc.chainsCap Gc.chainsPtr (BitVec.ofNat 64 stc.receiverChains.length) ∗
        A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
        arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
        arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
          ((Gc.chains.zip stc.receiverChains).drop (ci + 1)) ∗
        memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
          ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
        ((x.self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((x.self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((x.self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (x.self + 172#64) 4 ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (x.ckA ↦ₛ chainKeyBytes ckc) ∗
        memRegion x.ret 88 ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗
        cmkLoopFrame s0.sp x.ret x.counter ∗
        cmkSavedRegs s0.sp s0) =
      ((vecHeader x.self Gc.chainsCap Gc.chainsPtr (BitVec.ofNat 64 stc.receiverChains.length) ∗
        A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
        (vecGhostAt A cg.srk chainPtr ∗
          vecGhostAt A cg.priv (chainPtr + 24#64) ∗
          vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 (BitVec.ofNat 64 (chc.messageKeys.length + 1)) ∗
          vecBuf A 104 8 (messageKeyAt A) mkCap1 mkPtr1
            ((newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys) ∗
          optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64)) ∗
        arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
        arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
          ((Gc.chains.zip stc.receiverChains).drop (ci + 1)) ∗
        memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
          ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
        ((x.self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((x.self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((x.self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (x.self + 172#64) 4) ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (x.ckA ↦ₛ chainKeyBytes ckc) ∗
       memRegion x.ret 88 ∗
       (logFilterAddr img ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64) 7712 ∗
       cmkLoopFrame s0.sp x.ret x.counter ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool) := by sep_ac_rfl
  rw [hpull1]
  apply sepConj_mono_left
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hchain))) ?_
  exact ratchetAt_set_chain A x.self Gc stc hci_st cg'
    { chc with messageKeys := ckc.messageKeys F :: chc.messageKeys }
    hchains_len hpad_len hmax_jumps hcap_le hcap_lt hptr_ne

/-! ## Budget-Threaded Callee Wrappers (`grow_one` and `memmove`) -/

private theorem SepWPp.call_growOne_placed_budget [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry ret : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hsub : subroutine_ok prog entry (withLsCodeLoaded lsmpl (growOneSpec M A lim)))
    (x : GrowGhost × M.σ) {s : State} {P F_frame : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hpre : P ⊢ (growOneSpec M A lim).pre x s ∗ F_frame)
    (hcont : ∀ sf, sf.pc = s.readReg64 .lr → sf.sp = s.sp → sf.status = .Running →
      sf.spAligned = true → CalleeSavedPreserved s sf →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWPp prog ret sf ((growOneSpec M A lim).post x s sf ∗ F_frame) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm1 : s.mem ⊨ ((growOneSpec M A lim).pre x s ∗ F_frame) ∗ R :=
    Satisfies.mono (sepConj_mono_left hpre) hm
  have hm2 : s.mem ⊨ (withLsCodeLoaded lsmpl (growOneSpec M A lim)).pre x s ∗ (F_frame ∗ R) :=
    introduce_withLsCodeLoaded hcl (by simpa only [sepConj_assoc] using hm1)
  obtain ⟨sm, hsteps1, hout, -⟩ := hsub.no_fault_before_outcome x (F_frame ∗ R) s hpc hrun hm2 hsp hL
  rcases hout with ⟨⟨hpcm, hspm, hrunm⟩, ⟨_, hcsm⟩, hpostm⟩ | ⟨_, hpan_mem⟩ | ⟨_, _, hundef_mem⟩ | ⟨_, hoom⟩
  · have hsp_alignm : sm.spAligned = true := by
      simpa [State.spAligned, hspm] using hsp
    have hclm : LibsignalCodeLoaded lsmpl sm.mem := hcl.of_keepsFrozen hsteps1.keepsFrozen
    have hpostm' : sm.mem ⊨ ((growOneSpec M A lim).post x s sm ∗ F_frame) ∗ R := by
      simpa only [withLsCodeLoaded, sepConj_assoc] using hpostm
    obtain ⟨sf, hsteps2, hout2⟩ :=
      hcont sm hpcm hspm hrunm hsp_alignm hcsm hclm R hpostm' (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exfalso
    unfold withLsCodeLoaded growOneSpec at hpan_mem
    dsimp only at hpan_mem
    rw [satisfies_pure_sepConj] at hpan_mem
    exact hpan_mem.1
  · exfalso
    unfold withLsCodeLoaded growOneSpec at hundef_mem
    dsimp only at hundef_mem
    rw [satisfies_pure_sepConj] at hundef_mem
    exact hundef_mem.1
  · exfalso
    unfold withLsCodeLoaded growOneSpec at hoom
    dsimp only at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact hoom.1

private def sessionMemmoveSpec (hookStack : Nat := 4096) :
    Spec (BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) where
  pre := (libcMemmoveSpec hookStack).pre
  post := fun (base, buf, dst, src, len) s0 sf =>
    ⌜sf.readReg64 .x0 = base + BitVec.ofNat 64 dst ∧ sf.trace = s0.trace⌝ ∗
    (base ↦ₛ listMove buf dst src len) ∗
    stackAt s0.sp hookStack

private theorem hookSessionMemmove_ok (hookStack : Nat := 4096) :
    HookOk hookMemmove (sessionMemmoveSpec hookStack) := by
  refine CryptoVerification.HookTrace.HookOk.of_trace (hookMemmove_ok hookStack)
    fun _ _ _ ht hpost => ?_
  simp only [libcMemmoveSpec, sessionMemmoveSpec, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.1, ht⟩, hpost.2⟩

private theorem vmPreserved_hookMemmove (s : State) : VmPreserved s (hookMemmove s) := by
  dsimp only [hookMemmove, hookMemcpy, retHook]
  simp only [vmPreserved_setPC, vmPreserved_setMem_writeBytes, vmPreserved_refl_iff]

private theorem session_memmove_placed_ok_at [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hmm : H "memmove" = some hookMemmove) (stackSize : Nat := 4096) :
    subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ "memmove")
      (withVmPreserved (sessionMemmoveSpec stackSize)) :=
  cmk_hook_ok_of_mem (hookSat_withVmPreserved
    ⟨hookMemmove, hmm, hookSessionMemmove_ok (hookStack := stackSize)⟩
    fun f hf s => by cases hmm.symm.trans hf; exact vmPreserved_hookMemmove s)

/-! ## Relocatable Budget-Threaded Sub-Segment Proofs -/

theorem insertKey_from_964_placed [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (x : ConsumeMessageKeyGhost) (stB : M.σ) (Gc : RatchetGhost) (ckc : ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost)
    (mkCap1 mkPtr1 seedPtr : BitVec 64)
    (bs : List (BitVec 8))
    (hklen : cg.keys.length = chc.messageKeys.length)
    (hbs : MessageKeyArrayBytes (cg.keys.zip chc.messageKeys) bs)
    (hlen_lt : chc.messageKeys.length < mkCap1.toNat)
    (hcap1_lt : mkCap1.toNat * 104 < 2 ^ 63)
    (hptr1_ne : mkPtr1 ≠ 0#64)
    (s0 sM : State)
    (hpcM : sM.pc = (blkPl_24).base + 972#64)
    (hrunM : sM.status = .Running)
    (hspM : sM.sp = s0.sp - 480#64)
    (hsp_alignM : sM.spAligned = true)
    (hx29M : sM.readReg64 .x29 = s0.sp - 96#64)
    (htraceM : sM.trace = s0.trace ∧ calleeSavedVRegs sM = calleeSavedVRegs s0)
    (hx19M : sM.readReg64 .x19 = 1#64)
    (hx20M : sM.readReg64 .x20 = seedPtr)
    (hx21M : sM.readReg64 .x21 = x.ckA)
    (hx22M : sM.readReg64 .x22 = x.theirA)
    (hx23M : sM.readReg64 .x23 = x.self)
    (hx24M : sM.readReg64 .x24 = mkPtr1)
    (hx25M : sM.readReg64 .x25 = Gc.chainsPtr + BitVec.ofNat 64 (ci * 104))
    (hx26M : sM.readReg64 .x26 = BitVec.ofNat 64 chc.messageKeys.length)
    (hx27M : sM.readReg64 .x27 = s0.sp - 224#64)
    (hx28M : sM.readReg64 .x28 = ckc.index.zeroExtend 64) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H)
      (if chc.messageKeys.length < 2000 then
        (blkPl_24).base + 1140#64
      else
        (blkPl_24).base + 1020#64)
      sM
      (insertKeyActiveMid F (A.atState lim stB sM)
        (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)) mkCap1 mkPtr1 cg chc ckc seedPtr sM.sp bs)
      (fun sB P_f =>
        sB.sp = s0.sp - 480#64 ∧ sB.spAligned = true ∧
        sB.readReg64 .x29 = s0.sp - 96#64 ∧
        (sB.trace = s0.trace ∧ calleeSavedVRegs sB = calleeSavedVRegs s0) ∧
        AdvanceChainKeyRegs x s0 sB ∧
        sB.readReg64 .x24 = mkPtr1 ∧
        sB.readReg64 .x25 = Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) ∧
        sB.readReg64 .x26 = BitVec.ofNat 64 chc.messageKeys.length ∧
        sB.readReg64 .x28 = ckc.index.zeroExtend 64 ∧
        (P_f ⊢ insertKeyActivePost F (A.atState lim stB sB)
          (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)) mkCap1 mkPtr1 cg chc ckc seedPtr
          (s0.sp - 480#64))) := by
  rcases htraceM with ⟨htraceM, hvregsM⟩
  set chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
  have hzip_len : (cg.keys.zip chc.messageKeys).length = chc.messageKeys.length := by
    simp [hklen]
  have hlen_lt_zip : (cg.keys.zip chc.messageKeys).length < mkCap1.toNat := by
    rw [hzip_len]; exact hlen_lt
  unfold insertKeyActiveMid vecHeader
  apply SepWP.fold (memRegion_104_entails_messageKey_words mkPtr1) (by sep_focus)
  simp only [sepExists_sepConj_left]
  apply SepWP.exists_elim; intro w0
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro w4
  apply SepWP.exists_elim; intro w5
  apply SepWP.exists_elim; intro w6
  apply SepWP.exists_elim; intro w7
  apply SepWP.exists_elim; intro w8
  apply SepWP.exists_elim; intro w9
  apply SepWP.exists_elim; intro w10
  apply SepWP.exists_elim; intro w11
  apply SepWP.exists_elim; intro w12
  have hhdr56 : chainPtr + 48#64 + 8#64 = chainPtr + 56#64 := by bv_arith
  have hhdr64 : chainPtr + 48#64 + 16#64 = chainPtr + 64#64 := by bv_arith
  by_cases hlt2000 : chc.messageKeys.length < 2000
  · simp only [hlt2000, ↓reduceIte]
    have hls : (BitVec.ofNat 64 chc.messageKeys.length).ule 1999#64 = true :=
      mkLen_ule_1999_eq_true hlt2000
    wp_steps_sync_pool ((blkPl_24).base + 1140#64)
    rw [add_one_ofNat_64 chc.messageKeys.length, hspM]
    have hmk_intro := messageKeyAt_newMsgKeyGhost_intro F A.repAlloc ckc seedPtr mkPtr1
    have hins0 := vecBuf_messageKeyAt_of_insert0 A.repAlloc mkCap1 mkPtr1
      (newMsgKeyGhost seedPtr, ckc.messageKeys F) hbs hlen_lt_zip hcap1_lt hptr1_ne
    simp only [RustCliAllocBudget.repAlloc_live] at hmk_intro hins0
    simp only [RustCliAllocBudget.atState_live, vecU8Buf_atState, messageKeyHeaps_atState]
    apply SepWP.fold hmk_intro (by sep_focus)
    rw [← hzip_len]
    apply SepWP.fold hins0 (by sep_focus)
    rw [hzip_len]
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], by simpa [State.spAligned] using hsp_alignM,
       by simp only [wp_norm, arm64_norm, *],
       ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩, ?_,
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *], ?_⟩
    · unfold AdvanceChainKeyRegs
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, arm64_norm, *]
    · unfold insertKeyActivePost vecHeader
      simp only [RustCliAllocBudget.atState_pool, vecBuf_messageKeyAt_atState]
      rw [hhdr56, hhdr64]
      exact Entails.of_eq (by sep_ac_rfl)
  · simp only [hlt2000, ↓reduceIte]
    have hnot_lt : ¬ chc.messageKeys.length < 2000 := hlt2000
    have hls : (BitVec.ofNat 64 chc.messageKeys.length).ule 1999#64 = false := by
      rw [BitVec.ule_eq_decide, decide_eq_false_iff_not, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega)]
      change ¬ chc.messageKeys.length ≤ 1999
      omega
    wp_steps_sync_pool ((blkPl_24).base + 1020#64)
    rw [add_one_ofNat_64 chc.messageKeys.length, hspM]
    have hmk_intro := messageKeyAt_newMsgKeyGhost_intro F A.repAlloc ckc seedPtr mkPtr1
    have hins0 := vecBuf_messageKeyAt_of_insert0 A.repAlloc mkCap1 mkPtr1
      (newMsgKeyGhost seedPtr, ckc.messageKeys F) hbs hlen_lt_zip hcap1_lt hptr1_ne
    simp only [RustCliAllocBudget.repAlloc_live] at hmk_intro hins0
    simp only [RustCliAllocBudget.atState_live, vecU8Buf_atState, messageKeyHeaps_atState]
    apply SepWP.fold hmk_intro (by sep_focus)
    rw [← hzip_len]
    apply SepWP.fold hins0 (by sep_focus)
    rw [hzip_len]
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], by simpa [State.spAligned] using hsp_alignM,
       by simp only [wp_norm, arm64_norm, *],
       ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩, ?_,
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *], ?_⟩
    · unfold AdvanceChainKeyRegs
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, arm64_norm, *]
    · unfold insertKeyActivePost vecHeader
      simp only [RustCliAllocBudget.atState_pool, vecBuf_messageKeyAt_atState]
      rw [hhdr56, hhdr64]
      exact Entails.of_eq (by sep_ac_rfl)

theorem insertKey_memmove_952_placed [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hmm : H "memmove" = some hookMemmove)
    (x : ConsumeMessageKeyGhost) (st : M.σ) (Gc : RatchetGhost) (ckc : ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost)
    (mkCap1 mkPtr1 seedPtr : BitVec 64)
    (bs slotBs : List (BitVec 8))
    (hmax : chc.messageKeys.length ≤ 2000)
    (hbs_len : bs.length = chc.messageKeys.length * 104)
    (hslot_len : slotBs.length = 104)
    (s0 sK : State)
    (hpcK : sK.pc = (blkPl_24).base + 952#64)
    (hrunK : sK.status = .Running)
    (hspK : sK.sp = s0.sp - 480#64)
    (hsp_alignK : sK.spAligned = true)
    (hx29K : sK.readReg64 .x29 = s0.sp - 96#64)
    (htraceK : sK.trace = s0.trace ∧ calleeSavedVRegs sK = calleeSavedVRegs s0)
    (hx19K : sK.readReg64 .x19 = 1#64)
    (hx20K : sK.readReg64 .x20 = seedPtr)
    (hx21K : sK.readReg64 .x21 = x.ckA)
    (hx22K : sK.readReg64 .x22 = x.theirA)
    (hx23K : sK.readReg64 .x23 = x.self)
    (hx24K : sK.readReg64 .x24 = mkPtr1)
    (hx25K : sK.readReg64 .x25 = Gc.chainsPtr + BitVec.ofNat 64 (ci * 104))
    (hx26K : sK.readReg64 .x26 = BitVec.ofNat 64 chc.messageKeys.length)
    (hx27K : sK.readReg64 .x27 = s0.sp - 224#64)
    (hx28K : sK.readReg64 .x28 = ckc.index.zeroExtend 64) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 972#64) sK
      (vecHeader (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) + 48#64) mkCap1 mkPtr1
          (BitVec.ofNat 64 chc.messageKeys.length) ∗
        A.live mkPtr1 (mkCap1.toNat * 104) 8 ∗
        (mkPtr1 ↦ₛ (bs ++ slotBs)) ∗
        memRegion (mkPtr1 + BitVec.ofNat 64 ((chc.messageKeys.length + 1) * 104))
          ((mkCap1.toNat - (chc.messageKeys.length + 1)) * 104) ∗
        messageKeyHeaps A.repAlloc (cg.keys.zip chc.messageKeys) ∗
        vecU8Buf A.repAlloc 32#64 seedPtr (ckc.messageKeys F).seed ∗
        stackAt sK.sp 7712 ∗
        A.pool lim st sK)
      (fun sM P_f =>
        sM.pc = (blkPl_24).base + 972#64 ∧
        sM.status = .Running ∧
        sM.sp = s0.sp - 480#64 ∧ sM.spAligned = true ∧
        sM.readReg64 .x29 = s0.sp - 96#64 ∧
        (sM.trace = s0.trace ∧ calleeSavedVRegs sM = calleeSavedVRegs s0) ∧
        sM.readReg64 .x19 = 1#64 ∧
        sM.readReg64 .x20 = seedPtr ∧
        sM.readReg64 .x21 = x.ckA ∧
        sM.readReg64 .x22 = x.theirA ∧
        sM.readReg64 .x23 = x.self ∧
        sM.readReg64 .x24 = mkPtr1 ∧
        sM.readReg64 .x25 = Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) ∧
        sM.readReg64 .x26 = BitVec.ofNat 64 chc.messageKeys.length ∧
        sM.readReg64 .x27 = s0.sp - 224#64 ∧
        sM.readReg64 .x28 = ckc.index.zeroExtend 64 ∧
        (P_f ⊢ insertKeyActiveMid F (A.atState lim st sM)
          (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)) mkCap1 mkPtr1 cg chc ckc seedPtr sM.sp bs)) := by
  rcases htraceK with ⟨htraceK, hvregsK⟩
  have hmemmove := session_memmove_placed_ok_at hmm
  dsimp only [withVmPreserved] at hmemmove
  have hsp_and : ((s0.sp - 480#64) &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned, hspK] using hsp_alignK
  have hsp0_and : (s0.sp &&& 15#64 == 0#64) = true := by
    simpa using hsp_and
  have hmadd : (BitVec.ofNat 64 chc.messageKeys.length * 104#64).toNat =
      chc.messageKeys.length * 104 := madd_104_toNat hmax
  have hbound1 : 104 + chc.messageKeys.length * 104 ≤ (bs ++ slotBs).length := by
    rw [List.length_append, hbs_len, hslot_len]; omega
  have hbound2 : 0 + chc.messageKeys.length * 104 ≤ (bs ++ slotBs).length := by
    rw [List.length_append, hbs_len, hslot_len]; omega
  rw [hspK, stackAt_7712_eq_4096 (s0.sp - 480#64)]
  wp_steps_sync_pool (lsρ "memmove")
  wp_call hmemmove (mkPtr1, bs ++ slotBs, 104, 0, chc.messageKeys.length * 104)
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  apply SepWP.fold (pointsToBytes_listMove_insert0 mkPtr1 hbs_len hslot_len) (by sep_focus)
  have hsp_sf' : sf.sp = s0.sp - 480#64 := by simp only [wp_norm, arm64_norm, *]
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *], by simpa [State.spAligned, hsp_sf', hspK] using hsp_alignK,
     by simp only [wp_norm, arm64_norm, *],
     ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩,
     by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *], ?_⟩
  rw [hsp_sf', hspK]
  unfold insertKeyActiveMid
  simp only [RustCliAllocBudget.atState_pool, RustCliAllocBudget.atState_live,
    vecU8Buf_atState, messageKeyHeaps_atState]
  rw [stackAt_7712_eq_4096 (s0.sp - 480#64)]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem insertKey_after_grow_1232_placed [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hmm : H "memmove" = some hookMemmove)
    (x : ConsumeMessageKeyGhost) (st_init stB : M.σ)
    (remAfterGrow : List AllocEvent → Prop)
    (Gc : RatchetGhost) (ckc : ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost)
    (mkCap1 mkPtr1 seedPtr : BitVec 64)
    (bs slotBs : List (BitVec 8))
    (s0 sf_g : State)
    (hsbB : SeamBudget M lim (CmkEnv x) st_init stB remAfterGrow)
    (hcap1_eq : mkCap1 = cmkNextCap cg.mkCap chc.messageKeys.length)
    (hbs : MessageKeyArrayBytes (cg.keys.zip chc.messageKeys) bs)
    (hbs_len : bs.length = chc.messageKeys.length * 104)
    (hslot_len : slotBs.length = 104)
    (hmax : chc.messageKeys.length ≤ maxMessageKeys)
    (hlen_lt1 : chc.messageKeys.length < mkCap1.toNat)
    (hcap1_lt : mkCap1.toNat * 104 < 2 ^ 63)
    (hptr1_ne : mkPtr1 ≠ 0#64)
    (hpc_g' : sf_g.pc = (blkPl_24).base + 1232#64)
    (hrun_g : sf_g.status = .Running)
    (hsp_g0 : sf_g.sp = s0.sp - 480#64)
    (hsp_align_g : sf_g.spAligned = true)
    (hx29_g : sf_g.readReg64 .x29 = s0.sp - 96#64)
    (htrace_g : sf_g.trace = s0.trace)
    (hvregs_g : calleeSavedVRegs sf_g = calleeSavedVRegs s0)
    (hx19_g : sf_g.readReg64 .x19 = 1#64)
    (hx20_g : sf_g.readReg64 .x20 = seedPtr)
    (hx21_g : sf_g.readReg64 .x21 = x.ckA)
    (hx22_g : sf_g.readReg64 .x22 = x.theirA)
    (hx23_g : sf_g.readReg64 .x23 = x.self)
    (hx25_g : sf_g.readReg64 .x25 = Gc.chainsPtr + BitVec.ofNat 64 (ci * 104))
    (hx26_g : sf_g.readReg64 .x26 = BitVec.ofNat 64 chc.messageKeys.length)
    (hx27_g : sf_g.readReg64 .x27 = s0.sp - 224#64)
    (hx28_g : sf_g.readReg64 .x28 = ckc.index.zeroExtend 64) :
    let chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 972#64) sf_g
      (((chainPtr + 48#64) ↦₆₄ mkCap1) ∗
        ((chainPtr + 56#64) ↦₆₄ mkPtr1) ∗
        ((chainPtr + 64#64) ↦₆₄ BitVec.ofNat 64 chc.messageKeys.length) ∗
        A.live mkPtr1 (mkCap1.toNat * 104) 8 ∗
        (mkPtr1 ↦ₛ (bs ++ slotBs)) ∗
        memRegion (mkPtr1 + BitVec.ofNat 64 ((chc.messageKeys.length + 1) * 104))
          ((mkCap1.toNat - (chc.messageKeys.length + 1)) * 104) ∗
        messageKeyHeaps A.repAlloc (cg.keys.zip chc.messageKeys) ∗
        vecU8Buf A.repAlloc 32#64 seedPtr (ckc.messageKeys F).seed ∗
        stackAt sf_g.sp 7712 ∗
        A.pool lim stB sf_g)
      (fun sM P_f =>
        sM.sp = s0.sp - 480#64 ∧ sM.spAligned = true ∧
        sM.readReg64 .x29 = s0.sp - 96#64 ∧
        (sM.trace = s0.trace ∧ calleeSavedVRegs sM = calleeSavedVRegs s0) ∧
        sM.readReg64 .x19 = 1#64 ∧
        sM.readReg64 .x20 = seedPtr ∧
        sM.readReg64 .x21 = x.ckA ∧
        sM.readReg64 .x22 = x.theirA ∧
        sM.readReg64 .x23 = x.self ∧
        sM.readReg64 .x25 = chainPtr ∧
        sM.readReg64 .x26 = BitVec.ofNat 64 chc.messageKeys.length ∧
        sM.readReg64 .x27 = s0.sp - 224#64 ∧
        sM.readReg64 .x28 = ckc.index.zeroExtend 64 ∧
        ∃ stB' mkCap1' mkPtr1' bs',
          SeamBudget M lim (CmkEnv x) st_init stB' remAfterGrow ∧
          mkCap1' = cmkNextCap cg.mkCap chc.messageKeys.length ∧
          sM.readReg64 .x24 = mkPtr1' ∧
          MessageKeyArrayBytes (cg.keys.zip chc.messageKeys) bs' ∧
          chc.messageKeys.length < mkCap1'.toNat ∧
          mkCap1'.toNat * 104 < 2 ^ 63 ∧
          mkPtr1' ≠ 0#64 ∧
          (P_f ⊢ insertKeyActiveMid F (A.atState lim stB' sM) chainPtr mkCap1' mkPtr1' cg chc ckc seedPtr sM.sp bs')) := by
  intro chainPtr
  change sf_g.readReg64 .x25 = chainPtr at hx25_g
  have hhdr56 : chainPtr + 48#64 + 8#64 = chainPtr + 56#64 := by bv_arith
  have hhdr64 : chainPtr + 48#64 + 16#64 = chainPtr + 64#64 := by bv_arith
  have hhdr_fold :
      (((chainPtr + 48#64) ↦₆₄ mkCap1) ∗
        ((chainPtr + 56#64) ↦₆₄ mkPtr1) ∗
        ((chainPtr + 64#64) ↦₆₄ BitVec.ofNat 64 chc.messageKeys.length)) =
      vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 (BitVec.ofNat 64 chc.messageKeys.length) := by
    unfold vecHeader; rw [hhdr56, hhdr64]
  by_cases hlen0 : chc.messageKeys.length = 0
  · have hx26_zero : sf_g.readReg64 .x26 = 0#64 := by simp [hx26_g, hlen0]
    wp_steps_sync_pool ((blkPl_24).base + 972#64)
    apply SepWP.fold (Entails.of_eq hhdr_fold) (by sep_focus)
    apply SepWP.fold (pointsToBytes_insert0_zero mkPtr1 (bs := bs) (by omega) hslot_len) (by sep_focus)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *],
       by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_align_g,
       by simp only [wp_norm, arm64_norm, *],
       ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩,
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       stB, mkCap1, mkPtr1, bs, hsbB, hcap1_eq,
       by simp only [wp_norm, arm64_norm, *], hbs, hlen_lt1, hcap1_lt, hptr1_ne, ?_⟩
    unfold insertKeyActiveMid
    simp only [RustCliAllocBudget.atState_pool, RustCliAllocBudget.atState_live,
      vecU8Buf_atState, messageKeyHeaps_atState]
    (conv => rhs; rw [show stackAt _ 7712 = stackAt sf_g.sp 7712 from
      congrArg (stackAt · 7712) (by simp only [wp_norm, arm64_norm])])
    exact Entails.of_eq (by sep_ac_rfl)
  · have hcbnz : (BitVec.ofNat 64 chc.messageKeys.length == 0#64) = false := by
      rw [beq_eq_false_iff_ne]
      intro h0
      have ht := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
      exact hlen0 ht
    have hmm_fn := insertKey_memmove_952_placed F A lim H hmm x stB Gc ckc ci chc cg
    apply SepWP.cut (mid := (blkPl_24).base + bv% (952))
    wp_steps_sync_pool ((blkPl_24).base + bv% (952))
    apply SepWP.fold (Entails.of_eq hhdr_fold) (by sep_focus)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWP.congr_pre ?_
      (SepWP.mono (hmm_fn mkCap1 mkPtr1 seedPtr bs slotBs hmax hbs_len hslot_len s0 _
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_)
    · dsimp only [chainPtr]
      (conv => lhs; rw [show stackAt _ 7712 = stackAt sf_g.sp 7712 from
        congrArg (stackAt · 7712) (by simp only [wp_norm, arm64_norm])])
      sep_ac_rfl
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simpa [State.spAligned, wp_norm, arm64_norm] using hsp_align_g
    · simp only [wp_norm, arm64_norm, *]
    · exact ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]; rfl
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · intro sM P_f _ _ ⟨_, _, hspM, halignM, hx29M, htrM, hx19M, hx20M, hx21M, hx22M, hx23M,
        hx24M, hx25M, hx26M, hx27M, hx28M, himp⟩
      exact ⟨hspM, halignM, hx29M, htrM, hx19M, hx20M, hx21M, hx22M, hx23M, hx25M, hx26M,
        hx27M, hx28M, stB, mkCap1, mkPtr1, bs, hsbB, hcap1_eq, hx24M, hbs, hlen_lt1, hcap1_lt, hptr1_ne, himp⟩

private theorem insertKey_to_972_grow_placed [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hmm : H "memmove" = some hookMemmove)
    (hgrow_ok : GrowOnePlacedOk H A lim)
    (x : ConsumeMessageKeyGhost) (st_init stA : M.σ)
    (remAfterGrow : List AllocEvent → Prop)
    (Gc : RatchetGhost) (ckc : ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost) (seedPtr : BitVec 64)
    (s0 sA : State)
    (hne : ∃ evs, remAfterGrow evs)
    (hsb : SeamBudget M lim (CmkEnv x) st_init stA
      (ConcatEnv (CmkGrowOptEvs cg.mkCap chc.messageKeys.length) remAfterGrow))
    (hmax : chc.messageKeys.length ≤ maxMessageKeys)
    (hklen : cg.keys.length = chc.messageKeys.length)
    (hfull : chc.messageKeys.length = cg.mkCap.toNat)
    (hpc : sA.pc = (blkPl_24).base + 916#64)
    (hrun : sA.status = .Running)
    (hsp : sA.sp = s0.sp - 480#64)
    (hsp_align : sA.spAligned = true)
    (hx29 : sA.readReg64 .x29 = s0.sp - 96#64)
    (htrace : sA.trace = s0.trace ∧ calleeSavedVRegs sA = calleeSavedVRegs s0)
    (hcl : LibsignalCodeLoaded lsmpl sA.mem)
    (hx1 : sA.readReg64 .x1 = BitVec.ofNat 64 ci)
    (hx19 : sA.readReg64 .x19 = 1#64)
    (hx20 : sA.readReg64 .x20 = seedPtr)
    (hx21 : sA.readReg64 .x21 = x.ckA)
    (hx23 : sA.readReg64 .x23 = x.self)
    (hx25 : sA.readReg64 .x25 = Gc.chainsPtr)
    (hx26 : sA.readReg64 .x26 = x.theirA)
    (hx27 : sA.readReg64 .x27 = s0.sp - 224#64)
    (hx28 : sA.readReg64 .x28 = ckc.index.zeroExtend 64) :
    let chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
    SepWPp ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 972#64) sA
      (insertKeyActivePre F (A.atState lim stA sA) chainPtr cg chc ckc seedPtr sA.sp)
      (fun sM P_f =>
        sM.sp = s0.sp - 480#64 ∧ sM.spAligned = true ∧
        sM.readReg64 .x29 = s0.sp - 96#64 ∧
        (sM.trace = s0.trace ∧ calleeSavedVRegs sM = calleeSavedVRegs s0) ∧
        sM.readReg64 .x19 = 1#64 ∧
        sM.readReg64 .x20 = seedPtr ∧
        sM.readReg64 .x21 = x.ckA ∧
        sM.readReg64 .x22 = x.theirA ∧
        sM.readReg64 .x23 = x.self ∧
        sM.readReg64 .x25 = chainPtr ∧
        sM.readReg64 .x26 = BitVec.ofNat 64 chc.messageKeys.length ∧
        sM.readReg64 .x27 = s0.sp - 224#64 ∧
        sM.readReg64 .x28 = ckc.index.zeroExtend 64 ∧
        ∃ stB mkCap1 mkPtr1 bs,
          SeamBudget M lim (CmkEnv x) st_init stB remAfterGrow ∧
          mkCap1 = cmkNextCap cg.mkCap chc.messageKeys.length ∧
          sM.readReg64 .x24 = mkPtr1 ∧
          MessageKeyArrayBytes (cg.keys.zip chc.messageKeys) bs ∧
          chc.messageKeys.length < mkCap1.toNat ∧
          mkCap1.toNat * 104 < 2 ^ 63 ∧
          mkPtr1 ≠ 0#64 ∧
          (P_f ⊢ insertKeyActiveMid F (A.atState lim stB sM) chainPtr mkCap1 mkPtr1 cg chc ckc seedPtr sM.sp bs))
      (fun _ _ => False) := by
  intro chainPtr
  rcases htrace with ⟨htrace, hvregs⟩
  have hfit_grow : FitsEnv M lim stA (GrowOneEnv cg.mkCap) := by
    refine hsb.fitsSeg (fun e1 e2 h1 h2 => ⟨e1, e2, rfl, ?_, h2⟩) hne
    simpa [CmkGrowOptEvs, hfull] using h1
  have hzip_len : (cg.keys.zip chc.messageKeys).length = chc.messageKeys.length := by
    simp [hklen]
  have hmadd_ci : Gc.chainsPtr + BitVec.ofNat 64 ci * 104#64 = chainPtr :=
    madd_chainPtr_eq Gc.chainsPtr ci
  have hhdr56 : chainPtr + 48#64 + 8#64 = chainPtr + 56#64 := by bv_arith
  have hhdr64 : chainPtr + 48#64 + 16#64 = chainPtr + 64#64 := by bv_arith
  unfold insertKeyActivePre
  have hbounds := vecBuf_messageKeyAt_bounds (A.atState lim stA sA) cg.mkCap cg.mkPtr
    (cg.keys.zip chc.messageKeys)
  apply SepWPp.fold hbounds (by sep_focus)
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨_, _, hptr_ne⟩ => ?_
  have hbeq_cap : (BitVec.ofNat 64 chc.messageKeys.length == cg.mkCap) = true := by
    rw [mkLen_eq_mkCap_of_eq hfull, beq_self_eq_true]
  have hfull_zip : (cg.keys.zip chc.messageKeys).length = cg.mkCap.toNat := by
    rw [hzip_len]; exact hfull
  apply SepWPp.fold
    (vecBuf_messageKeyAt_full_entails_grow_one (A.atState lim stA sA) cg.mkCap cg.mkPtr
      (cg.keys.zip chc.messageKeys) hfull_zip)
    (by sep_focus)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro bs_grow
  refine SepWPp.pure_elim fun ⟨hbs_grow, hbs_grow_len⟩ => ?_
  refine SepWPp.pure_elim fun ⟨_, _⟩ => ?_
  unfold vecHeader
  rw [hhdr56, hhdr64, stackAt_7712_eq_grow sA.sp]
  simp only [RustCliAllocBudget.atState_pool, RustCliAllocBudget.atState_live,
    vecU8Buf_atState, messageKeyHeaps_atState, sepConj_assoc]
  apply sepWPp_seq_lscl (mid := lsmpl.base 43) hcl
  wp_steps_sync_pool (lsmpl.base 43)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hcl1
  have hnew_lt : max (2 * cg.mkCap.toNat) 4 * 104 < 2 ^ 63 := by
    change chc.messageKeys.length ≤ 2000 at hmax
    omega
  have hnew_bound : max (2 * cg.mkCap.toNat) 4 * 104 + 8 ≤ 2 ^ 63 := by omega
  refine SepWPp.call_growOne_placed_budget hgrow_ok ((chainPtr + 48#64, cg.mkCap, cg.mkPtr, bs_grow), stA)
    hcl1 (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_align)
    (F_frame := ((chainPtr + 64#64) ↦₆₄ BitVec.ofNat 64 chc.messageKeys.length) ∗
      messageKeyHeaps A.repAlloc (cg.keys.zip chc.messageKeys) ∗
      vecU8Buf A.repAlloc 32#64 seedPtr (ckc.messageKeys F).seed ∗
      memRegion (sA.sp - 7712#64) 3104)
    ?_ ?_
  · unfold growOneSpec
    dsimp only
    rw [hhdr56, sepConj_assoc]
    apply Entails.pure_right
      ⟨by simp only [wp_norm, arm64_norm], hbs_grow_len, hptr_ne, hnew_bound, hfit_grow⟩
    rw [hbs_grow_len]
    (conv => rhs; rw [show stackAt _ 4608 = stackAt sA.sp 4608 from
      congrArg (stackAt · 4608) (by simp only [wp_norm, arm64_norm])])
    by_cases hcap0 : cg.mkCap = 0
    · simp only [hcap0, ↓reduceIte]
      exact Entails.of_eq (by sep_ac_rfl)
    · simp only [hcap0, ↓reduceIte, sepConj_pure_left_comm, sepConj_assoc]
      apply Entails.pure_left; intro _
      exact Entails.of_eq (by sep_ac_rfl)
  intro sf_g hpc_g hsp_g hrun_g hsp_align_g hcs_g _hcl_g
  have hpc_g' : sf_g.pc = (blkPl_24).base + bv% (1232) := by
    rw [hpc_g]; simp only [wp_norm, arm64_norm]
  have hsp_g' : sf_g.sp = sA.sp := by
    rw [hsp_g]; simp only [wp_norm, arm64_norm]
  have hx19_g : sf_g.readReg64 .x19 = 1#64 :=
    (hcs_g.1).trans (by simp only [wp_norm, arm64_norm, *])
  have hx20_g : sf_g.readReg64 .x20 = seedPtr :=
    (hcs_g.2.1).trans (by simp only [wp_norm, arm64_norm, *])
  have hx21_g : sf_g.readReg64 .x21 = x.ckA :=
    (hcs_g.2.2.1).trans (by simp only [wp_norm, arm64_norm, *])
  have hx22_g : sf_g.readReg64 .x22 = x.theirA :=
    (hcs_g.2.2.2.1).trans (by simp only [wp_norm, arm64_norm, *])
  have hx23_g : sf_g.readReg64 .x23 = x.self :=
    (hcs_g.2.2.2.2.1).trans (by simp only [wp_norm, arm64_norm, *])
  have hx25_g : sf_g.readReg64 .x25 = chainPtr :=
    (hcs_g.2.2.2.2.2.2.1).trans (by simp only [wp_norm, arm64_norm, *])
  have hx26_g : sf_g.readReg64 .x26 = BitVec.ofNat 64 chc.messageKeys.length :=
    (hcs_g.2.2.2.2.2.2.2.1).trans
      ((by simp only [wp_norm, arm64_norm] : _ = cg.mkCap).trans
        (mkLen_eq_mkCap_of_eq hfull).symm)
  have hx27_g : sf_g.readReg64 .x27 = s0.sp - 224#64 :=
    (hcs_g.2.2.2.2.2.2.2.2.1).trans (by simp only [wp_norm, arm64_norm, *])
  have hx28_g : sf_g.readReg64 .x28 = ckc.index.zeroExtend 64 :=
    (hcs_g.2.2.2.2.2.2.2.2.2.1).trans (by simp only [wp_norm, arm64_norm, *])
  have hx29_g : sf_g.readReg64 .x29 = s0.sp - 96#64 :=
    (hcs_g.2.2.2.2.2.2.2.2.2.2.1).trans (by simp only [wp_norm, arm64_norm, *])
  have hvregs_g : calleeSavedVRegs sf_g = calleeSavedVRegs s0 :=
    (hcs_g.2.2.2.2.2.2.2.2.2.2.2).trans (by simp only [wp_norm, arm64_norm, *])
  unfold growOneSpec
  dsimp only
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro evs_g
  refine SepWPp.pure_elim fun ⟨htr_g, henv_g⟩ => ?_
  have htrace_g : sf_g.trace = s0.trace :=
    htr_g.trans (by simp only [wp_norm, arm64_norm, *])
  set stB := M.stepEvents evs_g stA
  have hsbB : SeamBudget M lim (CmkEnv x) st_init stB remAfterGrow :=
    hsb.step (fun e1 e2 h1 h2 => ⟨e1, e2, rfl, h1, h2⟩) (by simpa [CmkGrowOptEvs, hfull] using henv_g)
  apply SepWPp.exists_elim; intro mkPtr1
  refine SepWPp.pure_elim fun ⟨hptr1_ne, _⟩ => ?_
  set mkCap1 := BitVec.ofNat 64 (max (2 * cg.mkCap.toNat) 4)
  have hcap1_eq : mkCap1 = cmkNextCap cg.mkCap chc.messageKeys.length := by
    simp [mkCap1, cmkNextCap, hfull]
  obtain ⟨_, _, hlen_lt1_zip, hcap1_lt⟩ := grow_one_newCap_props hfull_zip hnew_lt
  have hlen_lt1 : chc.messageKeys.length < mkCap1.toNat := by
    rwa [hzip_len] at hlen_lt1_zip
  rw [hhdr56, hbs_grow_len, ← hsp_g, hsp_g']
  apply SepWPp.fold (Entails.of_eq (stackAt_7712_eq_grow sA.sp).symm) (by sep_focus)
  have hof_grow := vecBuf_messageKeyAt_of_grow_one A.repAlloc cg.mkCap mkPtr1
    hfull_zip hbs_grow hptr1_ne hnew_lt
  simp only [RustCliAllocBudget.repAlloc_live] at hof_grow
  apply SepWPp.fold hof_grow (by sep_focus)
  clear hfull hfull_zip hbeq_cap hbs_grow hbs_grow_len hcs_g hcl1 htr_g
  have hexpose := vecBuf_messageKeyAt_expose_for_insert0 A.repAlloc mkCap1 mkPtr1
    (cg.keys.zip chc.messageKeys) hlen_lt1_zip
  simp only [RustCliAllocBudget.repAlloc_live] at hexpose
  apply SepWPp.fold hexpose (by sep_focus)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro bs
  apply SepWPp.exists_elim; intro slotBs
  refine SepWPp.pure_elim fun ⟨hbs, hbs_len, hslot_len, _, _⟩ => ?_
  rw [hzip_len] at hbs_len ⊢
  apply SepWPp.of_sepWP_ret
  refine SepWP.congr_pre ?_
    (insertKey_after_grow_1232_placed F A lim H hmm x st_init stB remAfterGrow Gc ckc ci chc cg
      mkCap1 mkPtr1 seedPtr bs slotBs s0 sf_g
      hsbB hcap1_eq hbs hbs_len hslot_len hmax hlen_lt1 hcap1_lt hptr1_ne
      hpc_g' hrun_g (hsp_g'.trans hsp) hsp_align_g hx29_g htrace_g hvregs_g
      hx19_g hx20_g hx21_g hx22_g hx23_g hx25_g hx26_g hx27_g hx28_g)
  dsimp only [chainPtr, stB, mkCap1]
  rw [hsp_g']
  sep_ac_rfl

private theorem insertKey_nogrow_step_zero_placed [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (x : ConsumeMessageKeyGhost) (st_init stA : M.σ)
    (remAfterGrow : List AllocEvent → Prop)
    (Gc : RatchetGhost) (ckc : ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost) (seedPtr : BitVec 64)
    (bs slotBs : List (BitVec 8))
    (s0 sA : State)
    (hsbB : SeamBudget M lim (CmkEnv x) st_init stA remAfterGrow)
    (hnotfull : chc.messageKeys.length ≠ cg.mkCap.toNat)
    (hbs : MessageKeyArrayBytes (cg.keys.zip chc.messageKeys) bs)
    (hbs_len : bs.length = chc.messageKeys.length * 104)
    (hslot_len : slotBs.length = 104)
    (hlen0 : chc.messageKeys.length = 0)
    (hlen_lt : chc.messageKeys.length < cg.mkCap.toNat)
    (hcap_lt : cg.mkCap.toNat * 104 < 2 ^ 63)
    (hptr_ne : cg.mkPtr ≠ 0#64)
    (hpc : sA.pc = (blkPl_24).base + 916#64)
    (hrun : sA.status = .Running)
    (hsp : sA.sp = s0.sp - 480#64)
    (hsp_align : sA.spAligned = true)
    (hx29 : sA.readReg64 .x29 = s0.sp - 96#64)
    (htrace : sA.trace = s0.trace)
    (hvregs : calleeSavedVRegs sA = calleeSavedVRegs s0)
    (hx1 : sA.readReg64 .x1 = BitVec.ofNat 64 ci)
    (hx19 : sA.readReg64 .x19 = 1#64)
    (hx20 : sA.readReg64 .x20 = seedPtr)
    (hx21 : sA.readReg64 .x21 = x.ckA)
    (hx23 : sA.readReg64 .x23 = x.self)
    (hx25 : sA.readReg64 .x25 = Gc.chainsPtr)
    (hx26 : sA.readReg64 .x26 = x.theirA)
    (hx27 : sA.readReg64 .x27 = s0.sp - 224#64)
    (hx28 : sA.readReg64 .x28 = ckc.index.zeroExtend 64) :
    let chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 972#64) sA
      (((chainPtr + 48#64) ↦₆₄ cg.mkCap) ∗
        ((chainPtr + 56#64) ↦₆₄ cg.mkPtr) ∗
        ((chainPtr + 64#64) ↦₆₄ BitVec.ofNat 64 chc.messageKeys.length) ∗
        A.live cg.mkPtr (cg.mkCap.toNat * 104) 8 ∗
        (cg.mkPtr ↦ₛ (bs ++ slotBs)) ∗
        memRegion (cg.mkPtr + BitVec.ofNat 64 ((chc.messageKeys.length + 1) * 104))
          ((cg.mkCap.toNat - (chc.messageKeys.length + 1)) * 104) ∗
        messageKeyHeaps A.repAlloc (cg.keys.zip chc.messageKeys) ∗
        vecU8Buf A.repAlloc 32#64 seedPtr (ckc.messageKeys F).seed ∗
        stackAt sA.sp 7712 ∗
        A.pool lim stA sA)
      (fun sM P_f =>
        sM.sp = s0.sp - 480#64 ∧ sM.spAligned = true ∧
        sM.readReg64 .x29 = s0.sp - 96#64 ∧
        (sM.trace = s0.trace ∧ calleeSavedVRegs sM = calleeSavedVRegs s0) ∧
        sM.readReg64 .x19 = 1#64 ∧
        sM.readReg64 .x20 = seedPtr ∧
        sM.readReg64 .x21 = x.ckA ∧
        sM.readReg64 .x22 = x.theirA ∧
        sM.readReg64 .x23 = x.self ∧
        sM.readReg64 .x25 = chainPtr ∧
        sM.readReg64 .x26 = BitVec.ofNat 64 chc.messageKeys.length ∧
        sM.readReg64 .x27 = s0.sp - 224#64 ∧
        sM.readReg64 .x28 = ckc.index.zeroExtend 64 ∧
        ∃ stB mkCap1 mkPtr1 bs',
          SeamBudget M lim (CmkEnv x) st_init stB remAfterGrow ∧
          mkCap1 = cmkNextCap cg.mkCap chc.messageKeys.length ∧
          sM.readReg64 .x24 = mkPtr1 ∧
          MessageKeyArrayBytes (cg.keys.zip chc.messageKeys) bs' ∧
          chc.messageKeys.length < mkCap1.toNat ∧
          mkCap1.toNat * 104 < 2 ^ 63 ∧
          mkPtr1 ≠ 0#64 ∧
          (P_f ⊢ insertKeyActiveMid F (A.atState lim stB sM) chainPtr mkCap1 mkPtr1 cg chc ckc seedPtr sM.sp bs')) := by
  intro chainPtr
  have hmadd_ci : Gc.chainsPtr + BitVec.ofNat 64 ci * 104#64 = chainPtr :=
    madd_chainPtr_eq Gc.chainsPtr ci
  have hhdr56 : chainPtr + 48#64 + 8#64 = chainPtr + 56#64 := by bv_arith
  have hhdr64 : chainPtr + 48#64 + 16#64 = chainPtr + 64#64 := by bv_arith
  have hhdr_fold :
      (((chainPtr + 48#64) ↦₆₄ cg.mkCap) ∗
        ((chainPtr + 56#64) ↦₆₄ cg.mkPtr) ∗
        ((chainPtr + 64#64) ↦₆₄ BitVec.ofNat 64 chc.messageKeys.length)) =
      vecHeader (chainPtr + 48#64) cg.mkCap cg.mkPtr (BitVec.ofNat 64 chc.messageKeys.length) := by
    unfold vecHeader; rw [hhdr56, hhdr64]
  have hbeq_cap : (0#64 == cg.mkCap) = false := by
    have h := mkLen_beq_mkCap_false hlen_lt
    simpa only [hlen0] using h
  have hx26_zero : (BitVec.ofNat 64 chc.messageKeys.length == 0#64) = true := by simp [hlen0]
  wp_steps_sync_pool ((blkPl_24).base + 972#64)
  apply SepWP.fold (Entails.of_eq hhdr_fold) (by sep_focus)
  apply SepWP.fold (pointsToBytes_insert0_zero cg.mkPtr (bs := bs) (by omega) hslot_len) (by sep_focus)
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm, *],
     by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_align,
     by simp only [wp_norm, arm64_norm, *],
     ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩,
     by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *],
     stA, cg.mkCap, cg.mkPtr, bs, hsbB, by simp [cmkNextCap, hnotfull],
     by simp only [wp_norm, arm64_norm, *], hbs, hlen_lt, hcap_lt, hptr_ne, ?_⟩
  unfold insertKeyActiveMid
  simp only [RustCliAllocBudget.atState_pool, RustCliAllocBudget.atState_live,
    vecU8Buf_atState, messageKeyHeaps_atState]
  (conv => rhs; rw [show stackAt _ 7712 = stackAt sA.sp 7712 from
    congrArg (stackAt · 7712) (by simp only [wp_norm, arm64_norm])])
  exact Entails.of_eq (by sep_ac_rfl)

private theorem insertKey_nogrow_step_nonzero_placed [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hmm : H "memmove" = some hookMemmove)
    (x : ConsumeMessageKeyGhost) (st_init stA : M.σ)
    (remAfterGrow : List AllocEvent → Prop)
    (Gc : RatchetGhost) (ckc : ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost) (seedPtr : BitVec 64)
    (bs slotBs : List (BitVec 8))
    (s0 sA : State)
    (hsbB : SeamBudget M lim (CmkEnv x) st_init stA remAfterGrow)
    (hnotfull : chc.messageKeys.length ≠ cg.mkCap.toNat)
    (hbs : MessageKeyArrayBytes (cg.keys.zip chc.messageKeys) bs)
    (hbs_len : bs.length = chc.messageKeys.length * 104)
    (hslot_len : slotBs.length = 104)
    (hmax : chc.messageKeys.length ≤ maxMessageKeys)
    (hlen0 : ¬ chc.messageKeys.length = 0)
    (hlen_lt : chc.messageKeys.length < cg.mkCap.toNat)
    (hcap_lt : cg.mkCap.toNat * 104 < 2 ^ 63)
    (hptr_ne : cg.mkPtr ≠ 0#64)
    (hpc : sA.pc = (blkPl_24).base + 916#64)
    (hrun : sA.status = .Running)
    (hsp : sA.sp = s0.sp - 480#64)
    (hsp_align : sA.spAligned = true)
    (hx29 : sA.readReg64 .x29 = s0.sp - 96#64)
    (htrace : sA.trace = s0.trace)
    (hvregs : calleeSavedVRegs sA = calleeSavedVRegs s0)
    (hx1 : sA.readReg64 .x1 = BitVec.ofNat 64 ci)
    (hx19 : sA.readReg64 .x19 = 1#64)
    (hx20 : sA.readReg64 .x20 = seedPtr)
    (hx21 : sA.readReg64 .x21 = x.ckA)
    (hx23 : sA.readReg64 .x23 = x.self)
    (hx25 : sA.readReg64 .x25 = Gc.chainsPtr)
    (hx26 : sA.readReg64 .x26 = x.theirA)
    (hx27 : sA.readReg64 .x27 = s0.sp - 224#64)
    (hx28 : sA.readReg64 .x28 = ckc.index.zeroExtend 64) :
    let chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 972#64) sA
      (((chainPtr + 48#64) ↦₆₄ cg.mkCap) ∗
        ((chainPtr + 56#64) ↦₆₄ cg.mkPtr) ∗
        ((chainPtr + 64#64) ↦₆₄ BitVec.ofNat 64 chc.messageKeys.length) ∗
        A.live cg.mkPtr (cg.mkCap.toNat * 104) 8 ∗
        (cg.mkPtr ↦ₛ (bs ++ slotBs)) ∗
        memRegion (cg.mkPtr + BitVec.ofNat 64 ((chc.messageKeys.length + 1) * 104))
          ((cg.mkCap.toNat - (chc.messageKeys.length + 1)) * 104) ∗
        messageKeyHeaps A.repAlloc (cg.keys.zip chc.messageKeys) ∗
        vecU8Buf A.repAlloc 32#64 seedPtr (ckc.messageKeys F).seed ∗
        stackAt sA.sp 7712 ∗
        A.pool lim stA sA)
      (fun sM P_f =>
        sM.sp = s0.sp - 480#64 ∧ sM.spAligned = true ∧
        sM.readReg64 .x29 = s0.sp - 96#64 ∧
        (sM.trace = s0.trace ∧ calleeSavedVRegs sM = calleeSavedVRegs s0) ∧
        sM.readReg64 .x19 = 1#64 ∧
        sM.readReg64 .x20 = seedPtr ∧
        sM.readReg64 .x21 = x.ckA ∧
        sM.readReg64 .x22 = x.theirA ∧
        sM.readReg64 .x23 = x.self ∧
        sM.readReg64 .x25 = chainPtr ∧
        sM.readReg64 .x26 = BitVec.ofNat 64 chc.messageKeys.length ∧
        sM.readReg64 .x27 = s0.sp - 224#64 ∧
        sM.readReg64 .x28 = ckc.index.zeroExtend 64 ∧
        ∃ stB mkCap1 mkPtr1 bs',
          SeamBudget M lim (CmkEnv x) st_init stB remAfterGrow ∧
          mkCap1 = cmkNextCap cg.mkCap chc.messageKeys.length ∧
          sM.readReg64 .x24 = mkPtr1 ∧
          MessageKeyArrayBytes (cg.keys.zip chc.messageKeys) bs' ∧
          chc.messageKeys.length < mkCap1.toNat ∧
          mkCap1.toNat * 104 < 2 ^ 63 ∧
          mkPtr1 ≠ 0#64 ∧
          (P_f ⊢ insertKeyActiveMid F (A.atState lim stB sM) chainPtr mkCap1 mkPtr1 cg chc ckc seedPtr sM.sp bs')) := by
  intro chainPtr
  have hmadd_ci : Gc.chainsPtr + BitVec.ofNat 64 ci * 104#64 = chainPtr :=
    madd_chainPtr_eq Gc.chainsPtr ci
  have hhdr56 : chainPtr + 48#64 + 8#64 = chainPtr + 56#64 := by bv_arith
  have hhdr64 : chainPtr + 48#64 + 16#64 = chainPtr + 64#64 := by bv_arith
  have hhdr_fold :
      (((chainPtr + 48#64) ↦₆₄ cg.mkCap) ∗
        ((chainPtr + 56#64) ↦₆₄ cg.mkPtr) ∗
        ((chainPtr + 64#64) ↦₆₄ BitVec.ofNat 64 chc.messageKeys.length)) =
      vecHeader (chainPtr + 48#64) cg.mkCap cg.mkPtr (BitVec.ofNat 64 chc.messageKeys.length) := by
    unfold vecHeader; rw [hhdr56, hhdr64]
  have hbeq_cap : (BitVec.ofNat 64 chc.messageKeys.length == cg.mkCap) = false :=
    mkLen_beq_mkCap_false hlen_lt
  have hcbz : (BitVec.ofNat 64 chc.messageKeys.length == 0#64) = false := by
    rw [beq_eq_false_iff_ne]
    intro h0
    have ht := congrArg BitVec.toNat h0
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
    exact hlen0 ht
  have hmm_fn := insertKey_memmove_952_placed F A lim H hmm x stA Gc ckc ci chc cg
  apply SepWP.cut (mid := (blkPl_24).base + bv% (952))
  wp_steps_sync_pool ((blkPl_24).base + bv% (952))
  apply SepWP.fold (Entails.of_eq hhdr_fold) (by sep_focus)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine SepWP.congr_pre ?_
    (SepWP.mono (hmm_fn cg.mkCap cg.mkPtr seedPtr bs slotBs hmax hbs_len hslot_len s0 _
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_)
  · dsimp only [chainPtr]
    (conv => lhs; rw [show stackAt _ 7712 = stackAt sA.sp 7712 from
      congrArg (stackAt · 7712) (by simp only [wp_norm, arm64_norm])])
    sep_ac_rfl
  · simp only [wp_norm, arm64_norm, *]
  · simp only [wp_norm, arm64_norm, *]
  · simp only [wp_norm, arm64_norm, *]
  · simpa [State.spAligned, wp_norm, arm64_norm] using hsp_align
  · simp only [wp_norm, arm64_norm, *]
  · exact ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
  · simp only [wp_norm, arm64_norm, *]
  · simp only [wp_norm, arm64_norm, *]
  · simp only [wp_norm, arm64_norm, *]
  · simp only [wp_norm, arm64_norm, *]
  · simp only [wp_norm, arm64_norm, *]
  · simp only [wp_norm, arm64_norm, *]
  · simp only [wp_norm, arm64_norm, *]; rfl
  · simp only [wp_norm, arm64_norm, *]
  · simp only [wp_norm, arm64_norm, *]
  · simp only [wp_norm, arm64_norm, *]
  · intro sM P_f _ _ ⟨_, _, hspM, halignM, hx29M, htrM, hx19M, hx20M, hx21M, hx22M, hx23M,
      hx24M, hx25M, hx26M, hx27M, hx28M, himp⟩
    exact ⟨hspM, halignM, hx29M, htrM, hx19M, hx20M, hx21M, hx22M, hx23M, hx25M, hx26M,
      hx27M, hx28M, stA, cg.mkCap, cg.mkPtr, bs, hsbB, by simp [cmkNextCap, hnotfull],
      hx24M, hbs, hlen_lt, hcap_lt, hptr_ne, himp⟩

private theorem insertKey_to_972_nogrow_placed [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hmm : H "memmove" = some hookMemmove)
    (x : ConsumeMessageKeyGhost) (st_init stA : M.σ)
    (remAfterGrow : List AllocEvent → Prop)
    (Gc : RatchetGhost) (ckc : ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost) (seedPtr : BitVec 64)
    (s0 sA : State)
    (hsb : SeamBudget M lim (CmkEnv x) st_init stA
      (ConcatEnv (CmkGrowOptEvs cg.mkCap chc.messageKeys.length) remAfterGrow))
    (hmax : chc.messageKeys.length ≤ maxMessageKeys)
    (hklen : cg.keys.length = chc.messageKeys.length)
    (hnotfull : chc.messageKeys.length ≠ cg.mkCap.toNat)
    (hpc : sA.pc = (blkPl_24).base + 916#64)
    (hrun : sA.status = .Running)
    (hsp : sA.sp = s0.sp - 480#64)
    (hsp_align : sA.spAligned = true)
    (hx29 : sA.readReg64 .x29 = s0.sp - 96#64)
    (htrace : sA.trace = s0.trace ∧ calleeSavedVRegs sA = calleeSavedVRegs s0)
    (hx1 : sA.readReg64 .x1 = BitVec.ofNat 64 ci)
    (hx19 : sA.readReg64 .x19 = 1#64)
    (hx20 : sA.readReg64 .x20 = seedPtr)
    (hx21 : sA.readReg64 .x21 = x.ckA)
    (hx23 : sA.readReg64 .x23 = x.self)
    (hx25 : sA.readReg64 .x25 = Gc.chainsPtr)
    (hx26 : sA.readReg64 .x26 = x.theirA)
    (hx27 : sA.readReg64 .x27 = s0.sp - 224#64)
    (hx28 : sA.readReg64 .x28 = ckc.index.zeroExtend 64) :
    let chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
    SepWPp ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 972#64) sA
      (insertKeyActivePre F (A.atState lim stA sA) chainPtr cg chc ckc seedPtr sA.sp)
      (fun sM P_f =>
        sM.sp = s0.sp - 480#64 ∧ sM.spAligned = true ∧
        sM.readReg64 .x29 = s0.sp - 96#64 ∧
        (sM.trace = s0.trace ∧ calleeSavedVRegs sM = calleeSavedVRegs s0) ∧
        sM.readReg64 .x19 = 1#64 ∧
        sM.readReg64 .x20 = seedPtr ∧
        sM.readReg64 .x21 = x.ckA ∧
        sM.readReg64 .x22 = x.theirA ∧
        sM.readReg64 .x23 = x.self ∧
        sM.readReg64 .x25 = chainPtr ∧
        sM.readReg64 .x26 = BitVec.ofNat 64 chc.messageKeys.length ∧
        sM.readReg64 .x27 = s0.sp - 224#64 ∧
        sM.readReg64 .x28 = ckc.index.zeroExtend 64 ∧
        ∃ stB mkCap1 mkPtr1 bs,
          SeamBudget M lim (CmkEnv x) st_init stB remAfterGrow ∧
          mkCap1 = cmkNextCap cg.mkCap chc.messageKeys.length ∧
          sM.readReg64 .x24 = mkPtr1 ∧
          MessageKeyArrayBytes (cg.keys.zip chc.messageKeys) bs ∧
          chc.messageKeys.length < mkCap1.toNat ∧
          mkCap1.toNat * 104 < 2 ^ 63 ∧
          mkPtr1 ≠ 0#64 ∧
          (P_f ⊢ insertKeyActiveMid F (A.atState lim stB sM) chainPtr mkCap1 mkPtr1 cg chc ckc seedPtr sM.sp bs))
      (fun _ _ => False) := by
  intro chainPtr
  rcases htrace with ⟨htrace, hvregs⟩
  have hsbB : SeamBudget M lim (CmkEnv x) st_init stA remAfterGrow := by
    simpa only [M.stepEvents_nil] using
      hsb.step (evs_seg := []) (fun e1 e2 h1 h2 => ⟨e1, e2, rfl, h1, h2⟩)
        (by simp [CmkGrowOptEvs, hnotfull])
  have hzip_len : (cg.keys.zip chc.messageKeys).length = chc.messageKeys.length := by
    simp [hklen]
  have hhdr56 : chainPtr + 48#64 + 8#64 = chainPtr + 56#64 := by bv_arith
  have hhdr64 : chainPtr + 48#64 + 16#64 = chainPtr + 64#64 := by bv_arith
  unfold insertKeyActivePre
  apply SepWPp.fold
    (vecBuf_messageKeyAt_bounds (A.atState lim stA sA) cg.mkCap cg.mkPtr (cg.keys.zip chc.messageKeys))
    (by sep_focus)
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hlen_le_cap, hcap_lt, hptr_ne⟩ => ?_
  rw [hzip_len] at hlen_le_cap
  have hlen_lt : chc.messageKeys.length < cg.mkCap.toNat := by omega
  have hlen_lt_zip : (cg.keys.zip chc.messageKeys).length < cg.mkCap.toNat := by
    rw [hzip_len]; exact hlen_lt
  apply SepWPp.fold
    (vecBuf_messageKeyAt_expose_for_insert0 (A.atState lim stA sA) cg.mkCap cg.mkPtr
      (cg.keys.zip chc.messageKeys) hlen_lt_zip)
    (by sep_focus)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro bs
  apply SepWPp.exists_elim; intro slotBs
  refine SepWPp.pure_elim fun ⟨hbs, hbs_len, hslot_len, _, _⟩ => ?_
  rw [hzip_len] at hbs_len ⊢
  unfold vecHeader
  rw [hhdr56, hhdr64]
  simp only [RustCliAllocBudget.atState_pool, RustCliAllocBudget.atState_live,
    vecU8Buf_atState, messageKeyHeaps_atState, sepConj_assoc]
  apply SepWPp.of_sepWP_ret
  by_cases hlen0 : chc.messageKeys.length = 0
  · refine SepWP.congr_pre ?_
      (insertKey_nogrow_step_zero_placed F A lim H x st_init stA remAfterGrow Gc ckc ci chc cg
        seedPtr bs slotBs s0 sA hsbB hnotfull hbs hbs_len hslot_len hlen0 hlen_lt hcap_lt hptr_ne
        hpc hrun hsp hsp_align hx29 htrace hvregs
        hx1 hx19 hx20 hx21 hx23 hx25 hx26 hx27 hx28)
    dsimp only [chainPtr]
    sep_ac_rfl
  · refine SepWP.congr_pre ?_
      (insertKey_nogrow_step_nonzero_placed F A lim H hmm x st_init stA remAfterGrow Gc ckc ci chc cg
        seedPtr bs slotBs s0 sA hsbB hnotfull hbs hbs_len hslot_len hmax hlen0 hlen_lt hcap_lt hptr_ne
        hpc hrun hsp hsp_align hx29 htrace hvregs
        hx1 hx19 hx20 hx21 hx23 hx25 hx26 hx27 hx28)
    dsimp only [chainPtr]
    sep_ac_rfl

theorem insertKey_to_972_placed [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hmm : H "memmove" = some hookMemmove)
    (hgrow_ok : GrowOnePlacedOk H A lim)
    (x : ConsumeMessageKeyGhost) (st_init stA : M.σ)
    (remAfterGrow : List AllocEvent → Prop)
    (Gc : RatchetGhost) (ckc : ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost) (seedPtr : BitVec 64)
    (s0 sA : State)
    (hne : ∃ evs, remAfterGrow evs)
    (hsb : SeamBudget M lim (CmkEnv x) st_init stA
      (ConcatEnv (CmkGrowOptEvs cg.mkCap chc.messageKeys.length) remAfterGrow))
    (hmax : chc.messageKeys.length ≤ maxMessageKeys)
    (hklen : cg.keys.length = chc.messageKeys.length)
    (hpc : sA.pc = (blkPl_24).base + 916#64)
    (hrun : sA.status = .Running)
    (hsp : sA.sp = s0.sp - 480#64)
    (hsp_align : sA.spAligned = true)
    (hx29 : sA.readReg64 .x29 = s0.sp - 96#64)
    (htrace : sA.trace = s0.trace ∧ calleeSavedVRegs sA = calleeSavedVRegs s0)
    (hcl : LibsignalCodeLoaded lsmpl sA.mem)
    (hx1 : sA.readReg64 .x1 = BitVec.ofNat 64 ci)
    (hx19 : sA.readReg64 .x19 = 1#64)
    (hx20 : sA.readReg64 .x20 = seedPtr)
    (hx21 : sA.readReg64 .x21 = x.ckA)
    (hx23 : sA.readReg64 .x23 = x.self)
    (hx25 : sA.readReg64 .x25 = Gc.chainsPtr)
    (hx26 : sA.readReg64 .x26 = x.theirA)
    (hx27 : sA.readReg64 .x27 = s0.sp - 224#64)
    (hx28 : sA.readReg64 .x28 = ckc.index.zeroExtend 64) :
    let chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
    SepWPp ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 972#64) sA
      (insertKeyActivePre F (A.atState lim stA sA) chainPtr cg chc ckc seedPtr sA.sp)
      (fun sM P_f =>
        sM.sp = s0.sp - 480#64 ∧ sM.spAligned = true ∧
        sM.readReg64 .x29 = s0.sp - 96#64 ∧
        (sM.trace = s0.trace ∧ calleeSavedVRegs sM = calleeSavedVRegs s0) ∧
        sM.readReg64 .x19 = 1#64 ∧
        sM.readReg64 .x20 = seedPtr ∧
        sM.readReg64 .x21 = x.ckA ∧
        sM.readReg64 .x22 = x.theirA ∧
        sM.readReg64 .x23 = x.self ∧
        sM.readReg64 .x25 = chainPtr ∧
        sM.readReg64 .x26 = BitVec.ofNat 64 chc.messageKeys.length ∧
        sM.readReg64 .x27 = s0.sp - 224#64 ∧
        sM.readReg64 .x28 = ckc.index.zeroExtend 64 ∧
        ∃ stB mkCap1 mkPtr1 bs,
          SeamBudget M lim (CmkEnv x) st_init stB remAfterGrow ∧
          mkCap1 = cmkNextCap cg.mkCap chc.messageKeys.length ∧
          sM.readReg64 .x24 = mkPtr1 ∧
          MessageKeyArrayBytes (cg.keys.zip chc.messageKeys) bs ∧
          chc.messageKeys.length < mkCap1.toNat ∧
          mkCap1.toNat * 104 < 2 ^ 63 ∧
          mkPtr1 ≠ 0#64 ∧
          (P_f ⊢ insertKeyActiveMid F (A.atState lim stB sM) chainPtr mkCap1 mkPtr1 cg chc ckc seedPtr sM.sp bs))
      (fun _ _ => False) := by
  by_cases hfull : chc.messageKeys.length = cg.mkCap.toNat
  · exact insertKey_to_972_grow_placed F A lim H hmm hgrow_ok x st_init stA remAfterGrow
      Gc ckc ci chc cg seedPtr s0 sA hne hsb hmax hklen hfull
      hpc hrun hsp hsp_align hx29 htrace hcl
      hx1 hx19 hx20 hx21 hx23 hx25 hx26 hx27 hx28
  · exact insertKey_to_972_nogrow_placed F A lim H hmm x st_init stA remAfterGrow
      Gc ckc ci chc cg seedPtr s0 sA hsb hmax hklen hfull
      hpc hrun hsp hsp_align hx29 htrace
      hx1 hx19 hx20 hx21 hx23 hx25 hx26 hx27 hx28

private theorem evictOldestKeyHeap_placed_eq [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState)
    (ckc : ChainKey) (ci : Nat) (chc : ReceiverChain)
    (cg : ChainGhost) (mkCap1 mkPtr1 seedPtr : BitVec 64) (s0 : State) :
    evictOldestKeyHeap_placed F A x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr s0 =
      evictOldestKeyHeap F A cmkDummyImg x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr s0 := by
  unfold evictOldestKeyHeap_placed evictOldestKeyHeap evictOldestKeyHeapAt
  rw [logFilterAddr_cmkDummyImg]

theorem insertKey_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) :
    InsertKeyPlacedSpec F A lim H := by
  intro hmm hgrow_ok x st_init stA remAfterGrow Gc stc ckc ci chc seedPtr R s0 sA
    hchc hne hstate_full hL
  rcases hstate_full with ⟨hsb, hpc, ⟨hrun, hsp, hsp0_align, hsp_align, hx29, htrace, hcl, hvregs⟩,
    ⟨hx1, hx19, hx20, hx21, hx23, hx25, hx26, hx27, hx28⟩, _hseed_ne, hmem⟩
  rw [cmkLoopHeap_placed_eq] at hmem
  have hci_st : ci < stc.receiverChains.length := (List.getElem?_eq_some_iff.mp hchc).1
  have hlen_mem := Satisfies.mono (sepConj_mono_left
    (insertKeyState_chains_len F (A.atState lim stA sA) cmkDummyImg x Gc stc ckc seedPtr s0)) hmem
  rw [sepConj_assoc, satisfies_pure_sepConj] at hlen_mem
  have hchains_len : Gc.chains.length = stc.receiverChains.length := hlen_mem.1
  have hci_g : ci < Gc.chains.length := by omega
  have hsplit := Satisfies.mono (sepConj_mono_left
    (insertKeyState_split_active F (A.atState lim stA sA) cmkDummyImg x Gc stc ckc ci chc seedPtr s0
      hchc hci_g)) hmem
  rw [sepConj_assoc, satisfies_pure_sepConj] at hsplit
  rcases hsplit with ⟨⟨hsrk, hmax, hklen⟩, hmem_act⟩
  rw [← hsp] at hmem_act
  generalize hcg_eq' : Gc.chains[ci] = cg at hsrk hklen hmem_act
  have hcg_eq : cg = Gc.chains[ci] := hcg_eq'.symm
  have hcap0_eq : (Gc.chains[ci]?.map (·.mkCap)).getD 0#64 = cg.mkCap := by
    rw [List.getElem?_eq_getElem hci_g, ← hcg_eq]; rfl
  rw [hcap0_eq] at hsb
  set chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
  set F_rest := insertKeyFrame (A.atState lim stA sA) cmkDummyImg x Gc stc ckc ci chc cg s0
  have hmem_framed :
      sA.mem ⊨ insertKeyActivePre F (A.atState lim stA sA) chainPtr cg chc ckc seedPtr sA.sp ∗
        (F_rest ∗ R) := by
    simpa only [sepConj_assoc] using hmem_act
  clear hmem hlen_mem hmem_act
  have hpc' : sA.pc = (blkPl_24).base + 916#64 := hpc
  have hwp_to_972 := insertKey_to_972_placed F A lim H hmm hgrow_ok x st_init stA remAfterGrow
    Gc ckc ci chc cg seedPtr s0 sA hne hsb hmax hklen hpc' hrun hsp hsp_align hx29 ⟨htrace, hvregs⟩
    hcl hx1 hx19 hx20 hx21 hx23 hx25 hx26 hx27 hx28
  obtain ⟨sM, hsteps1, ⟨hpcM, hrunM, hclM, P_m, hmm_sat,
      hspM, halignM, hx29M, htrM, hx19M, hx20M, hx21M, hx22M, hx23M, hx25M, hx26M, hx27M, hx28M,
      stB, mkCap1, mkPtr1, bs, hsbB, hcap1_eq, hx24M, hbs, hlen_lt1, hcap1_lt, hptr1_ne, himpM⟩ |
      ⟨_, _, _, hqp⟩⟩ :=
    steps_of_sepWPp_placed hcl hmem_framed hL hwp_to_972
  · have hmm_mid :
        sM.mem ⊨ insertKeyActiveMid F (A.atState lim stB sM) chainPtr mkCap1 mkPtr1 cg chc ckc
          seedPtr sM.sp bs ∗ (F_rest ∗ R) :=
      Satisfies.mono (sepConj_mono_left himpM) hmm_sat
    have hLM := hsteps1.codeLoaded hL
    have hwp2 := insertKey_from_964_placed F A lim H x stB Gc ckc ci chc cg
      mkCap1 mkPtr1 seedPtr bs hklen hbs hlen_lt1 hcap1_lt hptr1_ne s0 sM
      hpcM hrunM hspM halignM hx29M htrM hx19M hx20M hx21M hx22M hx23M hx24M hx25M hx26M hx27M hx28M
    obtain ⟨sB, hsteps2, hpcB, hrunB, hclB, _, Pf, hmfB,
        hspB, halignB, hx29B, htrB, hregsD, hx24B, hx25B, hx26B, hx28B, himpB⟩ :=
      sepWP_elim_inv_placed hclM hmm_mid hLM hwp2
    have hframe_eq :
        F_rest = insertKeyFrame (A.atState lim stB sB) cmkDummyImg x Gc stc ckc ci chc cg s0 := rfl
    have hmf_post :
        sB.mem ⊨ (insertKeyActivePost F (A.atState lim stB sB) chainPtr mkCap1 mkPtr1 cg chc ckc
          seedPtr (s0.sp - 480#64) ∗
          insertKeyFrame (A.atState lim stB sB) cmkDummyImg x Gc stc ckc ci chc cg s0) ∗ R := by
      rw [← hframe_eq, sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left himpB) hmfB
    have hcap1_target : mkCap1 = cmkNextCap ((Gc.chains[ci]?.map (·.mkCap)).getD 0#64) chc.messageKeys.length := by
      rw [hcap0_eq]; exact hcap1_eq
    by_cases hlt2000 : chc.messageKeys.length < 2000
    · simp only [hlt2000, ↓reduceIte] at hpcB
      let cg' : ChainGhost :=
        { cg with
          mkCap := mkCap1
          mkPtr := mkPtr1
          keys := newMsgKeyGhost seedPtr :: cg.keys }
      have hG_agree : Gc.AgreeExcept (Gc.setChain ci cg') (some ci) :=
        RatchetGhost.AgreeExcept.setChain Gc hci_g cg'
          (by simp [cg', hcg_eq]) (by simp [cg', hcg_eq])
      have hG'_cap : ((Gc.setChain ci cg').chains[ci]?.map (·.mkCap)).getD 0#64 =
          cmkNextCap ((Gc.chains[ci]?.map (·.mkCap)).getD 0#64) chc.messageKeys.length := by
        rw [show (Gc.setChain ci cg').chains = Gc.chains.set ci cg' from rfl,
          List.getElem?_set_self hci_g]
        exact hcap1_target
      have hmemD : sB.mem ⊨ cmkLoopHeap_placed (A.atState lim stB sB) x (Gc.setChain ci cg')
          (updatedRatchetState F stc ci chc ckc) ckc s0 ∗ R := by
        rw [cmkLoopHeap_placed_eq]
        exact Satisfies.mono (sepConj_mono_left
          (insertKeyPost_entails_cmkLoopHeap_D F (A.atState lim stB sB) cmkDummyImg x Gc stc ckc ci
            chc cg mkCap1 mkPtr1 seedPtr s0 hci_st hsrk hklen hlt2000)) hmf_post
      have hlt_max : chc.messageKeys.length < maxMessageKeys := hlt2000
      refine ⟨sB, hsteps1.trans hsteps2, Or.inl ⟨hlt_max, stB, Gc.setChain ci cg', hG_agree, hG'_cap, ?_⟩⟩
      exact ⟨hsbB, hpcB, ⟨hrunB, hspB, hsp0_align, halignB, hx29B, htrB.1, hclB, htrB.2⟩,
        hregsD, hmemD⟩
    · simp only [hlt2000, ↓reduceIte] at hpcB
      have hlen2000 : chc.messageKeys.length = 2000 := by
        change chc.messageKeys.length ≤ 2000 at hmax
        omega
      have hklen2000 : cg.keys.length = 2000 := by omega
      have hcap2001 : 2001 ≤ mkCap1.toNat := by omega
      have hmemC : sB.mem ⊨ evictOldestKeyHeap_placed F (A.atState lim stB sB) x Gc stc ckc ci chc
          cg mkCap1 mkPtr1 seedPtr s0 ∗ R := by
        rw [evictOldestKeyHeap_placed_eq]
        exact Satisfies.mono (sepConj_mono_left
          (insertKeyPost_entails_evictOldestKeyHeap F (A.atState lim stB sB) cmkDummyImg x Gc stc
            ckc ci chc cg mkCap1 mkPtr1 seedPtr s0 hlen2000)) hmf_post
      have hregsC : EvictOldestKeyRegs x Gc ckc ci mkPtr1 sB := by
        rcases hregsD with ⟨hx19B, hx21B, hx22B, hx23B, _⟩
        rw [hlen2000] at hx26B
        exact ⟨hx19B, hx21B, hx22B, hx23B, hx25B, hx26B, hx28B⟩
      rw [← hx24B] at hptr1_ne hregsC hmemC
      rw [hcap1_target] at hcap2001 hcap1_lt hmemC
      refine ⟨sB, hsteps1.trans hsteps2, Or.inr (Or.inl ⟨stB, cg, ?_⟩)⟩
      exact ⟨hsbB, hpcB, ⟨hrunB, hspB, hsp0_align, halignB, hx29B, htrB.1, hclB, htrB.2⟩,
        hregsC, ⟨hci_g, hcg_eq⟩, hsrk, hlen2000, hklen2000, hcap2001, hcap1_lt, hptr1_ne, hmemC⟩
  · exact hqp.elim

end LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.InsertKeyBudget
