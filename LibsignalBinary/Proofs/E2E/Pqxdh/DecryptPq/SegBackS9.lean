/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.Defs
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegBackDefs

/-!
# Segment 9 Helpers for `try_decrypt_with_state::<HookRng>`

Session-state writeback and return-epilogue helpers for `S9Spec` (`+0x6a4 → +0x4b8 → +0x394 → +0x3b0`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.DecryptPq
open CryptoVerification.LibsignalSession
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] BitVec.toNat_zero

/-! ## Segment 9 (`+0x6a4 → +0x4b8 → +0x394 → +0x3b0`) -/

theorem length_optSenderChainBytes (o : Option SenderChain) {pad : List (BitVec 8)}
    (hpad : pad.length = 100) : (optSenderChainBytes o pad).length = 104 := by
  cases o with
  | none => simp [optSenderChainBytes, leBytes, hpad]
  | some sc =>
    have hpub : sc.ratchetKey.publicKey.bytes.toList.length = 32 := sc.ratchetKey.publicKey.bytes.2
    have hpriv : sc.ratchetKey.privateKey.bytes.toList.length = 32 :=
      sc.ratchetKey.privateKey.bytes.2
    simp [optSenderChainBytes, senderChainBytes, chainKeyBytes, keyToBytes32, leBytes, hpub, hpriv]

def trStackBytes (G : TrGhost) (tr : TripleRatchet (List (BitVec 8))) (pad : BitVec 32) :
    List (BitVec 8) :=
  unpack64 G.ratchet.chainsCap ++
  (unpack64 G.ratchet.chainsPtr ++
  (unpack64 (BitVec.ofNat 64 (G.ratchet.chains.zip tr.ratchet.receiverChains).length) ++
  (optSenderChainBytes tr.ratchet.senderChain G.ratchet.senderPad ++
  (keyToBytes32 tr.ratchet.rootKey ++
  (unpack64 (BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ++
  (unpack32 tr.ratchet.previousCounter ++
  (unpack32 pad ++
  (unpack64 G.pq.cap ++
  (unpack64 G.pq.ptr ++
  (unpack64 (BitVec.ofNat 64 tr.pqrState.length) ++
  (tr.localIdentityKey.publicKey.bytes.toList ++
   tr.remoteIdentityKey.publicKey.bytes.toList)))))))))))

theorem length_trStackBytes (G : TrGhost) (tr : TripleRatchet (List (BitVec 8))) (pad : BitVec 32)
    (hpad : G.ratchet.senderPad.length = 100) :
    (trStackBytes G tr pad).length = 264 := by
  have hloc : tr.localIdentityKey.publicKey.bytes.toList.length = 32 :=
    tr.localIdentityKey.publicKey.bytes.2
  have hrem : tr.remoteIdentityKey.publicKey.bytes.toList.length = 32 :=
    tr.remoteIdentityKey.publicKey.bytes.2
  simp [trStackBytes, length_optSenderChainBytes _ hpad, length_keyToBytes32, hloc, hrem]

def trHeapPart (A : RustAlloc) (G : TrGhost) (tr : TripleRatchet (List (BitVec 8))) : SepProp :=
  ⌜∀ sc, tr.ratchet.senderChain = some sc →
    Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes⌝ ∗
  ⌜G.ratchet.chains.length = tr.ratchet.receiverChains.length ∧
    G.ratchet.senderPad.length = 100 ∧
    tr.ratchet.maxForwardJumps < 2 ^ 64⌝ ∗
  vecBuf A 104 8 (chainAt A) G.ratchet.chainsCap G.ratchet.chainsPtr
    (G.ratchet.chains.zip tr.ratchet.receiverChains) ∗
  ⌜tr.pqrState.length ≤ G.pq.cap.toNat ∧ G.pq.cap.toNat < 2 ^ 63 ∧ G.pq.ptr ≠ 0⌝ ∗
  (if G.pq.cap = 0 then emp
   else (A.live G.pq.ptr G.pq.cap.toNat 1 ∗
     (G.pq.ptr ↦ₛ tr.pqrState)) ∗
     memRegion (G.pq.ptr + BitVec.ofNat 64 tr.pqrState.length) (G.pq.cap.toNat -
       tr.pqrState.length))

theorem pointsToBytes_trStackBytes (t : BitVec 64) (G : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (pad : BitVec 32)
    (hpad : G.ratchet.senderPad.length = 100) :
    (t ↦ₛ trStackBytes G tr pad) =
      ((t ↦₆₄ G.ratchet.chainsCap) ∗
       ((t + 8#64) ↦₆₄ G.ratchet.chainsPtr) ∗
       ((t + 16#64) ↦₆₄ BitVec.ofNat 64 (G.ratchet.chains.zip tr.ratchet.receiverChains).length) ∗
       ((t + 24#64) ↦ₛ optSenderChainBytes tr.ratchet.senderChain G.ratchet.senderPad) ∗
       ((t + 128#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) ∗
       ((t + 160#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
       ((t + 168#64) ↦₃₂ tr.ratchet.previousCounter) ∗
       ((t + 172#64) ↦₃₂ pad) ∗
       ((t + 0xb0#64) ↦₆₄ G.pq.cap) ∗
       ((t + 0xb8#64) ↦₆₄ G.pq.ptr) ∗
       ((t + 0xc0#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
       ((t + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
       ((t + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)) := by
  have hloc : tr.localIdentityKey.publicKey.bytes.toList.length = 32 :=
    tr.localIdentityKey.publicKey.bytes.2
  unfold trStackBytes
  repeat rw [pointsToBytes_append]
  simp only [unpack64_length, unpack32_length, length_optSenderChainBytes _ hpad,
    length_keyToBytes32, hloc,
    ← pointsTo64_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem trAt_eq_stack_heap (A : RustAlloc) (t : BitVec 64) (G : TrGhost)
    (tr : TripleRatchet (List (BitVec 8)))
    (hpad : G.ratchet.senderPad.length = 100) :
    trAt A t G tr =
      ∃∗ pad : BitVec 32, (t ↦ₛ trStackBytes G tr pad) ∗ trHeapPart A G tr := by
  unfold trAt ratchetAt vecAt vecU8At vecHeader trHeapPart
  rw [memRegion_four (t + 172#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  congr 1; funext pad
  rw [pointsToBytes_trStackBytes t G tr pad hpad,
      show t + 0xb0#64 + 8#64 = t + 0xb8#64 by bv_omega,
      show t + 0xb0#64 + 16#64 = t + 0xc0#64 by bv_omega]
  ac_rfl

theorem trAt_of_stack_heap (A : RustAlloc) (t : BitVec 64) (G : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (pad : BitVec 32)
    (hpad : G.ratchet.senderPad.length = 100) :
    (t ↦ₛ trStackBytes G tr pad) ∗ trHeapPart A G tr ⊢ trAt A t G tr := by
  rw [trAt_eq_stack_heap A t G tr hpad]
  exact Entails.sepExists_intro (P := fun p => (t ↦ₛ trStackBytes G tr p) ∗ trHeapPart A G tr) pad

def trWithoutPqAt (A : RustAlloc) (t : BitVec 64) (G : RatchetGhost)
    (tr : TripleRatchet (List (BitVec 8))) : SepProp :=
  ⌜∀ sc, tr.ratchet.senderChain = some sc →
    Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes⌝ ∗
  ratchetAt A t G tr.ratchet ∗
  ((t + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
  ((t + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)

theorem trAt_senderPad_len {A : RustAlloc} {t : BitVec 64} {G : TrGhost}
    {tr : TripleRatchet (List (BitVec 8))} {R : SepProp} {m : Memory}
    (h : m ⊨ trAt A t G tr ∗ R) : G.ratchet.senderPad.length = 100 := by
  unfold trAt ratchetAt at h
  simp only [sepConj_assoc, satisfies_pure_sepConj] at h
  exact h.2.1.2.1

theorem trAt_eq_withoutPq (A : RustAlloc) (sp : BitVec 64) (G : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) :
    trAt A (sp - 1504#64 + 0x38#64) G tr =
      (trWithoutPqAt A (sp - 1448#64) G.ratchet tr ∗
       ⌜tr.pqrState.length ≤ G.pq.cap.toNat ∧ G.pq.cap.toNat < 2 ^ 63 ∧ G.pq.ptr ≠ 0⌝ ∗
       ((sp - 1272#64) ↦₆₄ G.pq.cap) ∗
       ((sp - 1264#64) ↦₆₄ G.pq.ptr) ∗
       ((sp - 1256#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
       (if G.pq.cap = 0 then emp else (A.live G.pq.ptr G.pq.cap.toNat 1 ∗
         (G.pq.ptr ↦ₛ tr.pqrState)) ∗
         memRegion (G.pq.ptr + BitVec.ofNat 64 tr.pqrState.length) (G.pq.cap.toNat -
           tr.pqrState.length))) := by
  unfold trAt trWithoutPqAt vecU8At vecHeader
  rw [show sp - 1504#64 + 0x38#64 = sp - 1448#64 by bv_omega,
      show sp - 1448#64 + 0xb0#64 = sp - 1272#64 by bv_omega,
      show sp - 1272#64 + 8#64 = sp - 1264#64 by bv_omega,
      show sp - 1272#64 + 16#64 = sp - 1256#64 by bv_omega]
  ac_rfl

theorem trAt_of_withoutPq (A : RustAlloc) (sp : BitVec 64) (G : TrGhost)
    (tr : TripleRatchet (List (BitVec 8)))
    (newPqrCap newPqrPtr : BitVec 64) (newPqrState : List (BitVec 8))
    (hle : newPqrState.length ≤ newPqrCap.toNat)
    (hlt : newPqrCap.toNat < 2 ^ 63)
    (hnz : newPqrPtr ≠ 0) :
    trWithoutPqAt A (sp - 1448#64) G.ratchet tr ∗
    ((sp - 1272#64) ↦₆₄ newPqrCap) ∗
    ((sp - 1264#64) ↦₆₄ newPqrPtr) ∗
    ((sp - 1256#64) ↦₆₄ BitVec.ofNat 64 newPqrState.length) ∗
    (if newPqrCap = 0 then emp else (A.live newPqrPtr newPqrCap.toNat 1 ∗
      (newPqrPtr ↦ₛ newPqrState)) ∗
      memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat -
        newPqrState.length)) ⊢
    trAt A (sp - 1448#64) { G with pq := ⟨newPqrCap,
      newPqrPtr⟩ } { tr with pqrState := newPqrState } := by
  have heq := trAt_eq_withoutPq A sp { G with pq := ⟨newPqrCap,
    newPqrPtr⟩ } { tr with pqrState := newPqrState }
  rw [show sp - 1504#64 + 0x38#64 = sp - 1448#64 by bv_omega] at heq
  rw [heq]
  dsimp only [trWithoutPqAt]
  simp only [sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (Entails.pure_right ⟨hle, hlt, hnz⟩ (Entails.refl _)))))

theorem s9_scr_split (sp : BitVec 64) :
    memRegion (sp - 1504#64 + 0x140#64) 0x290 =
      (memRegion (sp - 1184#64) 8 ∗
       memRegion (sp - 1176#64) 8 ∗
       memRegion (sp - 1168#64) 8 ∗
       memRegion (sp - 1160#64) 16 ∗
       memRegion (sp - 1144#64) 8 ∗
       memRegion (sp - 1136#64) 8 ∗
       memRegion (sp - 1128#64) 8 ∗
       memRegion (sp - 1120#64) 16 ∗
       memRegion (sp - 1104#64) 264 ∗
       memRegion (sp - 840#64) 120 ∗
       memRegion (sp - 720#64) 8 ∗
       memRegion (sp - 712#64) 8 ∗
       memRegion (sp - 704#64) 8 ∗
       memRegion (sp - 696#64) 168) := by
  rw [show sp - 1504#64 + 0x140#64 = sp - 1184#64 by bv_omega,
      show (0x290 : Nat)
        = 8 + (8 + (8 + (16 + (8 + (8 + (8 + (16 + (264 + (120 + (8 + (8 + (8 + 168)))))))))))) by
          decide,
      memRegion_split (sp - 1184#64) 8 _ (by decide),
      show sp - 1184#64 + BitVec.ofNat 64 8 = sp - 1176#64 by bv_omega,
      memRegion_split (sp - 1176#64) 8 _ (by decide),
      show sp - 1176#64 + BitVec.ofNat 64 8 = sp - 1168#64 by bv_omega,
      memRegion_split (sp - 1168#64) 8 _ (by decide),
      show sp - 1168#64 + BitVec.ofNat 64 8 = sp - 1160#64 by bv_omega,
      memRegion_split (sp - 1160#64) 16 _ (by decide),
      show sp - 1160#64 + BitVec.ofNat 64 16 = sp - 1144#64 by bv_omega,
      memRegion_split (sp - 1144#64) 8 _ (by decide),
      show sp - 1144#64 + BitVec.ofNat 64 8 = sp - 1136#64 by bv_omega,
      memRegion_split (sp - 1136#64) 8 _ (by decide),
      show sp - 1136#64 + BitVec.ofNat 64 8 = sp - 1128#64 by bv_omega,
      memRegion_split (sp - 1128#64) 8 _ (by decide),
      show sp - 1128#64 + BitVec.ofNat 64 8 = sp - 1120#64 by bv_omega,
      memRegion_split (sp - 1120#64) 16 _ (by decide),
      show sp - 1120#64 + BitVec.ofNat 64 16 = sp - 1104#64 by bv_omega,
      memRegion_split (sp - 1104#64) 264 _ (by decide),
      show sp - 1104#64 + BitVec.ofNat 64 264 = sp - 840#64 by bv_omega,
      memRegion_split (sp - 840#64) 120 _ (by decide),
      show sp - 840#64 + BitVec.ofNat 64 120 = sp - 720#64 by bv_omega,
      memRegion_split (sp - 720#64) 8 _ (by decide),
      show sp - 720#64 + BitVec.ofNat 64 8 = sp - 712#64 by bv_omega,
      memRegion_split (sp - 712#64) 8 _ (by decide),
      show sp - 712#64 + BitVec.ofNat 64 8 = sp - 704#64 by bv_omega,
      memRegion_split (sp - 704#64) 8 168 (by decide),
      show sp - 704#64 + BitVec.ofNat 64 8 = sp - 696#64 by bv_omega]

theorem s9_ret_split (ret : BitVec 64) :
    memRegion ret 48 =
      (memRegion ret 8 ∗ memRegion (ret + 8#64) 8 ∗ memRegion (ret + 16#64) 8 ∗
       memRegion (ret + 24#64) 8 ∗ memRegion (ret + 32#64) 16) := by
  rw [show (48 : Nat) = 8 + (8 + (8 + (8 + 16))) by decide,
      memRegion_split ret 8 _ (by decide),
      show ret + BitVec.ofNat 64 8 = ret + 8#64 by bv_omega,
      memRegion_split (ret + 8#64) 8 _ (by decide),
      show ret + 8#64 + BitVec.ofNat 64 8 = ret + 16#64 by bv_omega,
      memRegion_split (ret + 16#64) 8 _ (by decide),
      show ret + 16#64 + BitVec.ofNat 64 8 = ret + 24#64 by bv_omega,
      memRegion_split (ret + 24#64) 8 16 (by decide),
      show ret + 24#64 + BitVec.ofNat 64 8 = ret + 32#64 by bv_omega]

theorem decResultAt_ok_of_parts (A : RustAlloc) (ret : BitVec 64) (pt : List (BitVec 8))
    (ptCap ptPtr : BitVec 64)
    (hle : pt.length ≤ ptCap.toNat) (hlt : ptCap.toNat < 2 ^ 63) (hnz : ptPtr ≠ 0) :
    (ret ↦₆₄ okTagVec) ∗
    (((ret + 8#64) ↦₆₄ ptCap) ∗
     ((ret + 16#64) ↦₆₄ ptPtr) ∗
     ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
     (if ptCap = 0 then emp else (A.live ptPtr ptCap.toNat 1 ∗ (ptPtr ↦ₛ pt)) ∗
       memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length))) ∗
    memRegion (ret + 32#64) 16 ⊢
    vecResultAt A ret (.ok pt) := by
  unfold vecResultAt
  refine sepConj_mono_right (sepConj_mono_left ?_)
  have hv := vecU8At_parts_entails_vecU8' A (ret + 8#64) ptCap ptPtr pt hle hlt hnz
  rwa [show ret + 8#64 + 8#64 = ret + 16#64 by bv_omega,
       show ret + 8#64 + 16#64 = ret + 24#64 by bv_omega] at hv

theorem decRel_of_trApplyRel {G G1 : SessionGhost} {trG : TrGhost}
    (h : G.afterTrFrom.TrApplyRel trG G1) :
    G.AfterTryDecrypt true { G1 with pending := none, kyber := none } := by
  rcases h with ⟨⟨h1, h2, h3, h4⟩, -⟩
  exact ⟨⟨h1, h2, h3, h4⟩, rfl, rfl⟩

theorem tryDecryptSavedRegs_entails_memRegion (sp0 : BitVec 64) (s0 : State) :
    tryDecryptSavedRegs sp0 s0 ⊢ memRegion (sp0 - 96#64) 96 := by
  unfold tryDecryptSavedRegs
  refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo64_entails_memRegion _ _)))))))))))) ?_
  rw [show (96 : Nat) = 8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + 8)))))))))) by decide,
      memRegion_split (sp0 - 96#64) 8 _ (by decide),
      show sp0 - 96#64 + BitVec.ofNat 64 8 = sp0 - 88#64 by bv_omega,
      memRegion_split (sp0 - 88#64) 8 _ (by decide),
      show sp0 - 88#64 + BitVec.ofNat 64 8 = sp0 - 80#64 by bv_omega,
      memRegion_split (sp0 - 80#64) 8 _ (by decide),
      show sp0 - 80#64 + BitVec.ofNat 64 8 = sp0 - 72#64 by bv_omega,
      memRegion_split (sp0 - 72#64) 8 _ (by decide),
      show sp0 - 72#64 + BitVec.ofNat 64 8 = sp0 - 64#64 by bv_omega,
      memRegion_split (sp0 - 64#64) 8 _ (by decide),
      show sp0 - 64#64 + BitVec.ofNat 64 8 = sp0 - 56#64 by bv_omega,
      memRegion_split (sp0 - 56#64) 8 _ (by decide),
      show sp0 - 56#64 + BitVec.ofNat 64 8 = sp0 - 48#64 by bv_omega,
      memRegion_split (sp0 - 48#64) 8 _ (by decide),
      show sp0 - 48#64 + BitVec.ofNat 64 8 = sp0 - 40#64 by bv_omega,
      memRegion_split (sp0 - 40#64) 8 _ (by decide),
      show sp0 - 40#64 + BitVec.ofNat 64 8 = sp0 - 32#64 by bv_omega,
      memRegion_split (sp0 - 32#64) 8 _ (by decide),
      show sp0 - 32#64 + BitVec.ofNat 64 8 = sp0 - 24#64 by bv_omega,
      memRegion_split (sp0 - 24#64) 8 _ (by decide),
      show sp0 - 24#64 + BitVec.ofNat 64 8 = sp0 - 16#64 by bv_omega,
      memRegion_split (sp0 - 16#64) 8 8 (by decide),
      show sp0 - 16#64 + BitVec.ofNat 64 8 = sp0 - 8#64 by bv_omega]
  exact Entails.refl _

theorem s9_local_frame_entails_memRegion (sp : BitVec 64)
    (v1496 v1464 v1184 v1176 v1168 v1144 v1136 v1128
     v720 v712 v704 v528 v520 v512 : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 264) :
    memRegion (sp - 1504#64) 8 ∗
    ((sp - 1496#64) ↦₆₄ v1496) ∗
    memRegion (sp - 1488#64) 24 ∗
    ((sp - 1464#64) ↦₆₄ v1464) ∗
    memRegion (sp - 1456#64) 8 ∗
    ((sp - 1448#64) ↦ₛ bs) ∗
    ((sp - 1184#64) ↦₆₄ v1184) ∗
    ((sp - 1176#64) ↦₆₄ v1176) ∗
    ((sp - 1168#64) ↦₆₄ v1168) ∗
    memRegion (sp - 1160#64) 16 ∗
    ((sp - 1144#64) ↦₆₄ v1144) ∗
    ((sp - 1136#64) ↦₆₄ v1136) ∗
    ((sp - 1128#64) ↦₆₄ v1128) ∗
    memRegion (sp - 1120#64) 16 ∗
    memRegion (sp - 1104#64) 264 ∗
    memRegion (sp - 840#64) 120 ∗
    ((sp - 720#64) ↦₆₄ v720) ∗
    ((sp - 712#64) ↦₆₄ v712) ∗
    ((sp - 704#64) ↦₆₄ v704) ∗
    memRegion (sp - 696#64) 168 ∗
    ((sp - 528#64) ↦₆₄ v528) ∗
    ((sp - 520#64) ↦₆₄ v520) ∗
    ((sp - 512#64) ↦₆₄ v512) ∗
    memRegion (sp - 504#64) 0x198 ⊢
    memRegion (sp - 1504#64) 1408 := by
  have htr : ((sp - 1448#64) ↦ₛ bs) ⊢ memRegion (sp - 1448#64) 264 := by
    rw [← hbs]; exact pointsToBytes_entails_memRegion (sp - 1448#64) bs
  refine Entails.trans (sepConj_mono_right
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_right
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_right
    (sepConj_mono htr
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_right
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_right
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))))))))))))))))))))))) ?_
  rw [show (1408 : Nat)
    = 8 + (8 + (24 + (8 + (8 + (264 + (8 + (8 + (8 + (16 + (8 + (8 + (8 + (16 + (264 + (120 + (8 +
      (8 + (8 + (168 + (8 + (8 + (8 + 0x198)))))))))))))))))))))) by decide,
      memRegion_split (sp - 1504#64) 8 _ (by decide),
      show sp - 1504#64 + BitVec.ofNat 64 8 = sp - 1496#64 by bv_omega,
      memRegion_split (sp - 1496#64) 8 _ (by decide),
      show sp - 1496#64 + BitVec.ofNat 64 8 = sp - 1488#64 by bv_omega,
      memRegion_split (sp - 1488#64) 24 _ (by decide),
      show sp - 1488#64 + BitVec.ofNat 64 24 = sp - 1464#64 by bv_omega,
      memRegion_split (sp - 1464#64) 8 _ (by decide),
      show sp - 1464#64 + BitVec.ofNat 64 8 = sp - 1456#64 by bv_omega,
      memRegion_split (sp - 1456#64) 8 _ (by decide),
      show sp - 1456#64 + BitVec.ofNat 64 8 = sp - 1448#64 by bv_omega,
      memRegion_split (sp - 1448#64) 264 _ (by decide),
      show sp - 1448#64 + BitVec.ofNat 64 264 = sp - 1184#64 by bv_omega,
      memRegion_split (sp - 1184#64) 8 _ (by decide),
      show sp - 1184#64 + BitVec.ofNat 64 8 = sp - 1176#64 by bv_omega,
      memRegion_split (sp - 1176#64) 8 _ (by decide),
      show sp - 1176#64 + BitVec.ofNat 64 8 = sp - 1168#64 by bv_omega,
      memRegion_split (sp - 1168#64) 8 _ (by decide),
      show sp - 1168#64 + BitVec.ofNat 64 8 = sp - 1160#64 by bv_omega,
      memRegion_split (sp - 1160#64) 16 _ (by decide),
      show sp - 1160#64 + BitVec.ofNat 64 16 = sp - 1144#64 by bv_omega,
      memRegion_split (sp - 1144#64) 8 _ (by decide),
      show sp - 1144#64 + BitVec.ofNat 64 8 = sp - 1136#64 by bv_omega,
      memRegion_split (sp - 1136#64) 8 _ (by decide),
      show sp - 1136#64 + BitVec.ofNat 64 8 = sp - 1128#64 by bv_omega,
      memRegion_split (sp - 1128#64) 8 _ (by decide),
      show sp - 1128#64 + BitVec.ofNat 64 8 = sp - 1120#64 by bv_omega,
      memRegion_split (sp - 1120#64) 16 _ (by decide),
      show sp - 1120#64 + BitVec.ofNat 64 16 = sp - 1104#64 by bv_omega,
      memRegion_split (sp - 1104#64) 264 _ (by decide),
      show sp - 1104#64 + BitVec.ofNat 64 264 = sp - 840#64 by bv_omega,
      memRegion_split (sp - 840#64) 120 _ (by decide),
      show sp - 840#64 + BitVec.ofNat 64 120 = sp - 720#64 by bv_omega,
      memRegion_split (sp - 720#64) 8 _ (by decide),
      show sp - 720#64 + BitVec.ofNat 64 8 = sp - 712#64 by bv_omega,
      memRegion_split (sp - 712#64) 8 _ (by decide),
      show sp - 712#64 + BitVec.ofNat 64 8 = sp - 704#64 by bv_omega,
      memRegion_split (sp - 704#64) 8 _ (by decide),
      show sp - 704#64 + BitVec.ofNat 64 8 = sp - 696#64 by bv_omega,
      memRegion_split (sp - 696#64) 168 _ (by decide),
      show sp - 696#64 + BitVec.ofNat 64 168 = sp - 528#64 by bv_omega,
      memRegion_split (sp - 528#64) 8 _ (by decide),
      show sp - 528#64 + BitVec.ofNat 64 8 = sp - 520#64 by bv_omega,
      memRegion_split (sp - 520#64) 8 _ (by decide),
      show sp - 520#64 + BitVec.ofNat 64 8 = sp - 512#64 by bv_omega,
      memRegion_split (sp - 512#64) 8 0x198 (by decide),
      show sp - 512#64 + BitVec.ofNat 64 8 = sp - 504#64 by bv_omega]
  exact Entails.refl _

theorem stackAt_rootStack_of_parts (sp0 : BitVec 64) :
    stackAt (sp0 - 1504#64) tryDecryptSubStack ∗
    memRegion (sp0 - 1504#64) 1408 ∗
    memRegion (sp0 - 96#64) 96 ⊢
    stackAt sp0 rootStack := by
  have h1 := stackAt_split_bottom sp0 96 1408 (by decide)
  have h2 := stackAt_split_bottom sp0 1504 (2 ^ 18 - 1504) (by decide)
  rw [show (1504 + (2 ^ 18 - 1504) : Nat) = rootStack by rfl] at h2
  rw [show (96 + 1408 : Nat) = 1504 by decide,
      show sp0 - BitVec.ofNat 64 1504 = sp0 - 1504#64 by rfl] at h1
  rw [h2, h1, stackAt]
  exact Entails.of_eq (by
    rw [show sp0 - BitVec.ofNat 64 rootStack = sp0 - 1504#64 - BitVec.ofNat 64 tryDecryptSubStack by
          dsimp only [rootStack, tryDecryptSubStack, tryDecryptFrameSize]; bv_omega,
        show sp0 - BitVec.ofNat 64 96 = sp0 - 96#64 by rfl])

theorem trApplyStack_to_clearUpkStack (sp : BitVec 64) :
    stackAt (sp - 1504#64) trApplyStack ∗
    memRegion (sp - 262144#64) (tryDecryptSubStack - trApplyStack) ⊢
    stackAt (sp - 1504#64) clearUpkStack ∗
    memRegion (sp - 262144#64) (tryDecryptSubStack - clearUpkStack) := by
  have h1 := stackAt_sub_split (sp - 1504#64) trApplyStack (by decide)
  have h2 := stackAt_sub_split (sp - 1504#64) clearUpkStack (by decide)
  rw [show sp - 1504#64 - BitVec.ofNat 64 tryDecryptSubStack = sp - 262144#64 by
        dsimp only [tryDecryptSubStack, rootStack, tryDecryptFrameSize]; bv_omega] at h1 h2
  rw [sepConj_comm, ← h1, h2, sepConj_comm]
  exact Entails.refl _

theorem clearUpkStack_to_subStack (sp : BitVec 64) :
    stackAt (sp - 1504#64) clearUpkStack ∗
    memRegion (sp - 262144#64) (tryDecryptSubStack - clearUpkStack) ⊢
    stackAt (sp - 1504#64) tryDecryptSubStack := by
  have h1 := stackAt_sub_split (sp - 1504#64) clearUpkStack (by decide)
  rw [show sp - 1504#64 - BitVec.ofNat 64 tryDecryptSubStack = sp - 262144#64 by
        dsimp only [tryDecryptSubStack, rootStack, tryDecryptFrameSize]; bv_omega] at h1
  rw [sepConj_comm, ← h1]
  exact Entails.refl _

theorem allocHookStack_to_subStack (sp : BitVec 64) :
    stackAt (sp - 1504#64) allocHookStack ∗
    memRegion (sp - 262144#64) (tryDecryptSubStack - allocHookStack) ⊢
    stackAt (sp - 1504#64) tryDecryptSubStack := by
  have h1 := stackAt_sub_split (sp - 1504#64) allocHookStack (by decide)
  rw [show sp - 1504#64 - BitVec.ofNat 64 tryDecryptSubStack = sp - 262144#64 by
        dsimp only [tryDecryptSubStack, rootStack, tryDecryptFrameSize]; bv_omega] at h1
  rw [sepConj_comm, ← h1]
  exact Entails.refl _

theorem SepWP.setPC_setMem_ite_true {prog : Program} {target_pc : BitVec 64}
    {s : State} {m : Memory} {P : SepProp} {post : State → SepProp → Prop}
    {c : Prop} [inst : Decidable c] {pc1 pc2 : BitVec 64} (hc : c)
    (hthen : SepWP prog target_pc ((s.setPC pc1).setMem m) P post) :
    SepWP prog target_pc ((s.setPC (@ite _ c inst pc1 pc2)).setMem m) P post := by
  rw [ite_eq_left_iff.mpr fun hnc => (hnc hc).elim]; exact hthen

theorem SepWP.setPC_setMem_ite_false {prog : Program} {target_pc : BitVec 64}
    {s : State} {m : Memory} {P : SepProp} {post : State → SepProp → Prop}
    {c : Prop} [inst : Decidable c] {pc1 pc2 : BitVec 64} (hnc : ¬ c)
    (helse : SepWP prog target_pc ((s.setPC pc2).setMem m) P post) :
    SepWP prog target_pc ((s.setPC (@ite _ c inst pc1 pc2)).setMem m) P post := by
  rw [ite_eq_right_iff.mpr fun hc => (hnc hc).elim]; exact helse

theorem SepWPp.congr_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (h : P = P' ∗ emp) (hwp : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp := by
  rw [h, sepConj_emp]; exact hwp

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD
