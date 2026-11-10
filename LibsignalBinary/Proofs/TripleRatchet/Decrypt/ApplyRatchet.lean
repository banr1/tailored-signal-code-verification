/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym130
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym433
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Defs
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.AuthDecrypt

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalSession
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] BitVec.toNat_zero

/-!
# Segment 9 (`apply_to_session_state`) Proofs for `try_decrypt_with_state`

Verifies Segment 9 (`+0x6a4 → +0x4b8 → +0x394 → +0x3b0`) of `try_decrypt_with_state`, replacing
`tr.pqr_state`, writing `Ok(pt)`, applying the updated `TripleRatchet` to `SessionState`, clearing
any unacknowledged pre-key message, and returning via the shared epilogue.
-/

theorem length_optSenderChainBytes (o : Option SenderChain) {pad : List (BitVec 8)}
    (hpad : pad.length = 100) : (optSenderChainBytes o pad).length = 104 := by
  cases o with
  | none => simp [optSenderChainBytes, leBytes, hpad]
  | some sc =>
    have hpub : sc.ratchetKey.publicKey.bytes.toList.length = 32 := sc.ratchetKey.publicKey.bytes.2
    have hpriv : sc.ratchetKey.privateKey.bytes.toList.length = 32 := sc.ratchetKey.privateKey.bytes.2
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
     memRegion (G.pq.ptr + BitVec.ofNat 64 tr.pqrState.length) (G.pq.cap.toNat - tr.pqrState.length))

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
         memRegion (G.pq.ptr + BitVec.ofNat 64 tr.pqrState.length) (G.pq.cap.toNat - tr.pqrState.length))) := by
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
      memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ⊢
    trAt A (sp - 1448#64) { G with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState } := by
  have heq := trAt_eq_withoutPq A sp { G with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState }
  rw [show sp - 1504#64 + 0x38#64 = sp - 1448#64 by bv_omega] at heq
  rw [heq]
  dsimp only [trWithoutPqAt]
  simp only [sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (Entails.pure_right ⟨hle, hlt, hnz⟩ (Entails.refl _)))))

theorem applyRatchet_scr_split (sp : BitVec 64) :
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
      show (0x290 : Nat) = 8 + (8 + (8 + (16 + (8 + (8 + (8 + (16 + (264 + (120 + (8 + (8 + (8 + 168)))))))))))) by decide,
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

theorem applyRatchet_ret_split (ret : BitVec 64) :
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

theorem applyRatchet_local_frame_entails_memRegion (sp : BitVec 64)
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
  rw [show (1408 : Nat) = 8 + (8 + (24 + (8 + (8 + (264 + (8 + (8 + (8 + (16 + (8 + (8 + (8 + (16 + (264 + (120 + (8 + (8 + (8 + (168 + (8 + (8 + (8 + 0x198)))))))))))))))))))))) by decide,
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

theorem applyRatchet_from_6d0_ext (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (hTrApply : TrApplyOkExt img.base A ext)
    (hClearUpk : ClearUpkOkExt img.base A ext)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (newPqrState pt : List (BitVec 8))
    (newPqrCap newPqrPtr ptCap ptPtr : BitVec 64)
    (R : SepProp) (s0 s1 : State)
    (hok : (x.model C S uuidTryParse).1 = .ok pt)
    (hst : (x.model C S uuidTryParse).2 =
      (({ tr with pqrState := newPqrState }).applyToSessionState st1).clearUnacknowledgedPreKeyMessage)
    (hpad : trG.ratchet.senderPad.length = 100)
    (hnew_le : newPqrState.length ≤ newPqrCap.toNat)
    (hnew_lt : newPqrCap.toNat < 2 ^ 63)
    (hnew_nz : newPqrPtr ≠ 0)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hpt_lt : ptCap.toNat < 2 ^ 63)
    (hpt_nz : ptPtr ≠ 0)
    (hsp0 : s0.spAligned = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + 1744#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 1504#64)
    (hsp_al1 : s1.spAligned = true)
    (htr1 : s1.trace = s0.trace)
    (hfl1 : img.FrozenLoaded s1)
    (hsym1 : s1.symtab = img.symtab)
    (hx9_1 : s1.readReg64 .x9 = s0.sp - 800#64)
    (hx19_1 : s1.readReg64 .x19 = x.ret)
    (hx20_1 : s1.readReg64 .x20 = s0.sp - 1184#64)
    (hx21_1 : s1.readReg64 .x21 = x.ss)
    (hx24_1 : s1.readReg64 .x24 = BitVec.ofNat 64 newPqrState.length)
    (_hx29_1 : s1.readReg64 .x29 = s0.sp - 96#64)
    (hvregs_1 : calleeSavedVRegs s1 = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s1
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trWithoutPqAt A (s0.sp - 1448#64) trG.ratchet tr ∗
       ((s0.sp - 1272#64) ↦₆₄ trG.pq.cap) ∗
       ((s0.sp - 1264#64) ↦₆₄ trG.pq.ptr) ∗
       ((s0.sp - 1256#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
       (if newPqrCap = 0 then emp else (A.live newPqrPtr newPqrCap.toNat 1 ∗ (newPqrPtr ↦ₛ newPqrState)) ∗
         memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ∗
       ((s0.sp - 528#64) ↦₆₄ ptCap) ∗
       ((s0.sp - 520#64) ↦₆₄ ptPtr) ∗
       ((s0.sp - 512#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       (if ptCap = 0 then emp else (A.live ptPtr ptCap.toNat 1 ∗ (ptPtr ↦ₛ pt)) ∗
         memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
       memRegion x.ret 8 ∗
       memRegion (x.ret + 8#64) 8 ∗
       memRegion (x.ret + 16#64) 8 ∗
       memRegion (x.ret + 24#64) 8 ∗
       memRegion (x.ret + 32#64) 16 ∗
       memRegion (s0.sp - 1504#64) 8 ∗
       ((s0.sp - 1496#64) ↦₆₄ newPqrCap) ∗
       memRegion (s0.sp - 1488#64) 24 ∗
       ((s0.sp - 1464#64) ↦₆₄ newPqrPtr) ∗
       memRegion (s0.sp - 1456#64) 8 ∗
       memRegion (s0.sp - 1184#64) 8 ∗
       memRegion (s0.sp - 1176#64) 8 ∗
       memRegion (s0.sp - 1168#64) 8 ∗
       memRegion (s0.sp - 1160#64) 16 ∗
       memRegion (s0.sp - 1144#64) 8 ∗
       memRegion (s0.sp - 1136#64) 8 ∗
       memRegion (s0.sp - 1128#64) 8 ∗
       memRegion (s0.sp - 1120#64) 16 ∗
       memRegion (s0.sp - 1104#64) 264 ∗
       memRegion (s0.sp - 840#64) 120 ∗
       ((s0.sp - 720#64) ↦₆₄ ptCap) ∗
       ((s0.sp - 712#64) ↦₆₄ ptPtr) ∗
       ((s0.sp - 704#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       memRegion (s0.sp - 696#64) 168 ∗
       memRegion (s0.sp - 504#64) 0x198 ∗
       protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       tapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
       logOff img ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R)) := by
  have hfn := hfn_tryDecrypt
  decrypt_fetches_ext img.base ext hfn 0x6d0 36
  decrypt_fetches_ext img.base ext hfn 0x4b8 72
  decrypt_fetches_ext img.base ext hfn 0x394 32
  have hmemcpy := memcpy_ok_at_ext img hC
  have hbl_trApply := bl_trApply_target_ext img ext
  have hbl_clearUpk := bl_clearUpk_target_ext img ext
  dsimp only [tripleRatchetProgAtExt, TrApplyOkExt, ClearUpkOkExt] at *
  generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr trApplyName = trApply_entry at hbl_trApply hTrApply
  generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr clearUpkName = clearUpk_entry at hbl_clearUpk hClearUpk
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr tryDecryptName = entry
  simp only [wp_norm] at hpc1 hsp1 hx9_1 hx19_1 hx20_1 hx21_1 hx24_1
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1184#64) (by sep_focus) fun w1184 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1176#64) (by sep_focus) fun w1176 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1168#64) (by sep_focus) fun w1168 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1144#64) (by sep_focus) fun w1144 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1136#64) (by sep_focus) fun w1136 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1128#64) (by sep_focus) fun w1128 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 8#64) (by sep_focus) fun wret8 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 16#64) (by sep_focus) fun wret16 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 24#64) (by sep_focus) fun wret24 => ?_
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_frozen hfl1 hsym1 (mid := entry + bv% (ls_off% "memcpy" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hfl2 hsym2
  refine SepWPp.mono_focus
    (trAt_of_withoutPq A s0.sp trG tr newPqrCap newPqrPtr newPqrState hnew_le hnew_lt hnew_nz)
    (by sep_focus) ?_
  rw [trAt_eq_stack_heap A (s0.sp - 1448#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
      { tr with pqrState := newPqrState } hpad]
  refine SepWPp.elim_exists_focus
    (Φ := fun pad : BitVec 32 =>
      ((s0.sp - 1448#64) ↦ₛ trStackBytes { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
        { tr with pqrState := newPqrState } pad) ∗
      trHeapPart A { trG with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState })
    (by sep_focus) fun pad => ?_
  have hbs_len : (trStackBytes { trG with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState } pad).length = 264 :=
    length_trStackBytes _ _ pad hpad
  generalize hbs_def : trStackBytes { trG with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState } pad = bs at hbs_len ⊢
  rw [show memRegion (s0.sp - 1104#64) 264 = memRegion (s0.sp - 1104#64) bs.length by rw [hbs_len]]
  simp only [← sepConj_assoc]
  refine SepWPp.call_frame_frozen (img := img) (spec := sessionMemcpyRegionSpec)
    (x := (s0.sp - 1104#64, s0.sp - 1448#64, bs))
    (T := memRegion (s0.sp - 1104#64) bs.length ∗ ((s0.sp - 1448#64) ↦ₛ bs))
    (ret_pc := entry + bv% (1248))
    hfl2 hsym2 hmemcpy (by rfl) (by exact hrun1)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1) (by rfl)
    (by rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm, hbs_len]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ hm_pan => by dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hfl2 hsym2
  intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hfl2 hsym2
  simp only [wp_norm, hsp1] at hsp2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _hx29_2, hvregs_2⟩
  simp only [wp_norm, hx19_1, hx20_1, hx21_1, hx24_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx24_2 hvregs_2
  dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
  simp only [wp_norm, sepConj_assoc]
  apply SepWPp.elim_pure; rintro ⟨_, htr2⟩
  have htr20 : s2.trace = s0.trace := htr2.trans htr1
  rw [← hbs_def]
  refine SepWPp.mono_focus
    (trAt_of_stack_heap A (s0.sp - 1104#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
      { tr with pqrState := newPqrState } pad hpad)
    (by sep_focus) ?_
  rw [hbs_def]
  rw [stackAt_sub_split (s0.sp - 1504#64) trApplyStack (by decide)]
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_frozen hfl2 hsym2 (mid := trApply_entry)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun2)
  intro hfl3 hsym3
  refine SepWPp.call_frame_frozen (img := img) (spec := trApplySpec A)
    (x := ⟨s0.sp - 1104#64, { trG with pq := ⟨newPqrCap, newPqrPtr⟩ },
           { tr with pqrState := newPqrState }, x.ss, x.G.afterTrFrom, st1⟩)
    (T := trAt A (s0.sp - 1104#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
            { tr with pqrState := newPqrState } ∗
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          stackAt (s0.sp - 1504#64) trApplyStack ∗ A.pool)
    (ret_pc := entry + bv% (1260))
    hfl3 hsym3 hTrApply (by rfl) (by exact hrun2)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
    (by dsimp only [trApplySpec]; simp only [wp_norm, hsp2]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [trApplySpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ hm_pan => by
      have h0m : s0.trace <+: (s2.writeReg64 .x0 (s0.sp - 1104#64)
        |>.writeReg64 .x1 x.ss |>.writeReg64 .x30 (entry + bv% (1260))
        |>.setPC trApply_entry).trace := by
        rw [show (s2.writeReg64 .x0 (s0.sp - 1104#64)
          |>.writeReg64 .x1 x.ss |>.writeReg64 .x30 (entry + bv% (1260))
          |>.setPC trApply_entry).trace = s2.trace from rfl, htr20]
      exact tryDecrypt_onPanic_of_callee C A ctl S img x s0 _ sf _ R h0m hm_pan) ?_
  clear hfl3 hsym3
  intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hfl3 hsym3
  simp only [wp_norm, hsp2] at hsp3
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, _hx29_3, hvregs_3⟩
  simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx24_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx24_3 hvregs_3
  dsimp only [trApplySpec]
  simp only [wp_norm, hsp2, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr3
  have htr30 : s3.trace = s0.trace := htr3.trans htr20
  apply SepWPp.elim_exists; intro G1
  simp only [sepConj_assoc]
  apply SepWPp.elim_pure; intro hG1
  refine SepWPp.mono_focus (trApplyStack_to_clearUpkStack s0.sp) (by sep_focus) ?_
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_frozen hfl3 hsym3 (mid := clearUpk_entry)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun3)
  intro hfl4 hsym4
  refine SepWPp.call_frame_frozen (img := img) (spec := clearUpkSpec A)
    (x := ⟨x.ss, G1, ({ tr with pqrState := newPqrState }).applyToSessionState st1⟩)
    (T := sessionStateAt A x.ss G1 (({ tr with pqrState := newPqrState }).applyToSessionState st1) ∗
          A.pool ∗ stackAt (s0.sp - 1504#64) clearUpkStack)
    (ret_pc := entry + bv% (1268))
    hfl4 hsym4 hClearUpk (by rfl) (by exact hrun3)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
    (by dsimp only [clearUpkSpec]; simp only [wp_norm, hsp3]; rfl)
    (by simp only [wp_norm])
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [clearUpkSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ hm_pan => by dsimp only [clearUpkSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hfl4 hsym4
  intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hfl4 hsym4
  simp only [wp_norm, hsp3] at hsp4
  rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, _hx29_4, hvregs_4⟩
  simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx24_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx24_4 hvregs_4
  dsimp only [clearUpkSpec]
  simp only [wp_norm, hsp3, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr4
  have htr40 : s4.trace = s0.trace := htr4.trans htr30
  refine SepWPp.mono_focus (clearUpkStack_to_subStack s0.sp) (by sep_focus) ?_
  refine SepWPp.mono_focus
    (applyRatchet_local_frame_entails_memRegion s0.sp newPqrCap newPqrPtr ptCap ptPtr
      (BitVec.ofNat 64 pt.length) ptCap ptPtr (BitVec.ofNat 64 pt.length)
      ptCap ptPtr (BitVec.ofNat 64 pt.length) ptCap ptPtr (BitVec.ofNat 64 pt.length)
      bs hbs_len) (by sep_focus) ?_
  refine SepWPp.mono_focus (Entails.refl (tryDecryptSavedRegs s0.sp s0)) (by sep_focus) ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret) (by sep_focus) fun wret => ?_
  unfold tryDecryptSavedRegs
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun4)
  refine ⟨fun hmf => ?_, by simp only [wp_norm], ?_⟩
  · dsimp only [tryDecryptSpec, Spec.inImage]
    rw [hok]
    rw [← hst] at hmf
    have hdec := decRel_of_trApplyRel hG1
    have hsaved := tryDecryptSavedRegs_entails_memRegion s0.sp s0
    unfold tryDecryptSavedRegs at hsaved
    have hmf1 := Satisfies.mono_focus hsaved (by sep_focus) hmf
    have hmf3 := Satisfies.mono_focus (stackAt_rootStack_of_parts s0.sp) (by sep_focus) hmf1
    rw [show (bv% (2 ^ 64 - 2) : BitVec 64) = okTagVec from rfl] at hmf3
    have hmf4 := Satisfies.mono_focus
      (decResultAt_ok_of_parts A x.ret pt ptCap ptPtr hpt_le hpt_lt hpt_nz) (by sep_focus) hmf3
    have hss : sessionStateAt A x.ss { G1 with pending := none, kyber := none } (x.model C S uuidTryParse).2 ⊢
        ∃∗ G' : SessionGhost, ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
          sessionStateAt A x.ss G' (x.model C S uuidTryParse).2 := by
      refine Entails.trans ?_
        (Entails.sepExists_intro
          (P := fun G' : SessionGhost =>
            ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
            sessionStateAt A x.ss G' (x.model C S uuidTryParse).2)
          { G1 with pending := none, kyber := none })
      exact Entails.pure_right hdec (Entails.refl _)
    have hmf5 := Satisfies.mono_focus hss (by sep_focus) hmf4
    clear hmf hmf1 hmf3 hmf4
    have hno_pan : (Except.ok pt : Except SignalProtocolError (List (BitVec 8))) ≠ .error .panic := nofun
    simp only [wp_norm, sepConj_assoc, satisfies_pure_sepConj] at hmf5 ⊢
    refine ⟨⟨hno_pan, htr40⟩, ?_⟩
    generalize (∃∗ G', ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
      sessionStateAt A x.ss G' (x.model C S uuidTryParse).2) = SS at hmf5 ⊢
    sep_close
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, hvregs_4]

theorem applyRatchet_ok_ext (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) :
    S9SpecExt img C A ctl uuidTryParse S ext := by
  intro himg hC hTrApply hClearUpk x trG tr st1 newPqrState pt R s0 s hok hst h9
  have hfn := hfn_tryDecrypt
  decrypt_fetches_ext img.base ext hfn 0x6a4 44
  have hS9_pc := segS9PC_eq_ext himg ext
  have hdealloc := dealloc_ok_at_ext img C A ctl S ext hC
  rcases h9 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hfl, hsym, hvregs⟩,
    hx19, hx20, hx21, hx23, hx24, newPqrCap, newPqrPtr, hnew_le, hnew_lt, hnew_nz, hmem⟩
  rw [hS9_pc] at hpc
  have h6d0 := @applyRatchet_from_6d0_ext img C A ctl S ext hC hTrApply hClearUpk x trG tr st1
    newPqrState pt newPqrCap newPqrPtr
  clear hTrApply hClearUpk
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr tryDecryptName = entry
  have hpad : trG.ratchet.senderPad.length = 100 := by
    have htr_front := hmem
    rw [← sepConj_assoc, sepConj_comm (sessionStateAt A x.ss x.G.afterTrFrom st1), sepConj_assoc] at htr_front
    exact trAt_senderPad_len htr_front
  unfold tryDecryptCommonHeap at hmem
  rw [trAt_eq_withoutPq A s0.sp trG tr,
       applyRatchet_scr_split s0.sp,
       applyRatchet_ret_split x.ret,
       show s0.sp - 1504#64 + 0x3d0#64 = s0.sp - 528#64 by bv_omega,
       show s0.sp - 1504#64 + 0x8#64 = s0.sp - 1496#64 by bv_omega,
       show s0.sp - 1504#64 + 0x10#64 = s0.sp - 1488#64 by bv_omega,
       show s0.sp - 1504#64 + 0x28#64 = s0.sp - 1464#64 by bv_omega,
       show s0.sp - 1504#64 + 0x30#64 = s0.sp - 1456#64 by bv_omega,
       show s0.sp - 1504#64 + 0x3e8#64 = s0.sp - 504#64 by bv_omega] at hmem
  simp only [wp_norm] at hpc hx20 hx23 hx29
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_reaches_outcome hmem ?_
  refine SepWPp.elim_pure_focus
    (φ := tr.pqrState.length ≤ trG.pq.cap.toNat ∧ trG.pq.cap.toNat < 2 ^ 63 ∧ trG.pq.ptr ≠ 0)
    (by sep_focus) fun ⟨hpq_le, hpq_lt, hpq_nz⟩ => ?_
  refine SepWPp.elim_vecU8_focus (A := A) (a := s0.sp - 528#64) (bs := pt)
    (by sep_focus) fun ptCap ptPtr hpt_le hpt_lt hpt_nz => ?_
  rw [show s0.sp - 528#64 + 8#64 = s0.sp - 520#64 by bv_omega,
      show s0.sp - 528#64 + 16#64 = s0.sp - 512#64 by bv_omega]
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 720#64) (by sep_focus) fun w720 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 712#64) (by sep_focus) fun w712 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 704#64) (by sep_focus) fun w704 => ?_
  by_cases hpq_cap : trG.pq.cap = 0#64
  · refine SepWPp.mono_focus (newPqr_zero_prep A trG.pq.cap trG.pq.ptr tr.pqrState hpq_cap) (by sep_focus) ?_
    rw [emp_sepConj]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_frozen hfl hsym (mid := entry + bv% (1744))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    intro hfl1 hsym1
    refine SepWPp.congr_pre (by sep_focus)
      (h6d0 ptCap ptPtr R s0 _
        hok hst hpad hnew_le hnew_lt hnew_nz hpt_le hpt_lt hpt_nz
        hsp0 (by rfl) (by exact hrun) (by simp only [wp_norm, hsp])
        (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al)
        htr hfl1 hsym1
        (by simp only [wp_norm])
        (by simp only [wp_norm, hx19])
        (by simp only [wp_norm, hx20])
        (by simp only [wp_norm, hx21])
        (by simp only [wp_norm, hx24])
        (by simp only [wp_norm, hx29])
        (by simp only [wp_norm, hvregs]))
  · refine SepWPp.mono_focus (newPqr_dealloc_prep' A trG.pq.cap trG.pq.ptr tr.pqrState hpq_cap hpq_le hpq_lt) (by sep_focus) ?_
    rw [stackAt_sub_split (s0.sp - 1504#64) allocHookStack (by decide)]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_frozen hfl hsym (mid := entry + bv% (1728))
    wp_steps
    apply SepWP.setPC_setMem_ite_false (by simp only [beq_iff_eq, hpq_cap, not_false_eq_true])
    apply SepWP.done (by rfl) (by exact hrun)
    intro hfl0 hsym0
    apply SepWPp.of_sepWP_frozen hfl0 hsym0 (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    intro hfl1 hsym1
    refine SepWPp.call_frame_frozen (img := img) (spec := rustDeallocSpec A)
      (x := (trG.pq.ptr, trG.pq.cap.toNat, 1))
      (T := A.pool ∗ A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat ∗
            stackAt (s0.sp - 1504#64) allocHookStack)
      (ret_pc := entry + bv% (1740))
      hfl1 hsym1 hdealloc (by rfl) (by exact hrun)
      (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
      (by dsimp only [rustDeallocSpec]; simp only [wp_norm, hsp]; rfl)
      (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
      (by sep_focus)
      (fun _ _ _ _ h => by dsimp only [rustDeallocSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
      (fun sf _ hm_pan => by dsimp only [rustDeallocSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
    clear hfl0 hsym0 hfl1 hsym1
    intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hfl1 hsym1
    simp only [wp_norm, hsp] at hsp1
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [wp_norm, hx19, hx20, hx21, hx24, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx24_1 hx29_1 hvregs_1
    dsimp only [rustDeallocSpec]
    simp only [wp_norm, hsp, sepConj_assoc]
    apply SepWPp.elim_pure; intro htr1
    have htr10 : s1.trace = s0.trace := htr1.trans htr
    refine SepWPp.mono_focus (allocHookStack_to_subStack s0.sp) (by sep_focus) ?_
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_frozen hfl1 hsym1 (mid := entry + bv% (1744))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun1)
    intro hfl2 hsym2
    refine SepWPp.congr_pre (by sep_focus)
      (h6d0 ptCap ptPtr R s0 _
        hok hst hpad hnew_le hnew_lt hnew_nz hpt_le hpt_lt hpt_nz
        hsp0 (by rfl) (by exact hrun1) (by simp only [wp_norm, hsp1])
        (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1)
        htr10 hfl2 hsym2
        (by simp only [wp_norm])
        (by simp only [wp_norm, hx19_1])
        (by simp only [wp_norm, hx20_1])
        (by simp only [wp_norm, hx21_1])
        (by simp only [wp_norm, hx24_1])
        (by simp only [wp_norm, hx29_1])
        (by simp only [wp_norm, hvregs_1]))

theorem applyRatchet_ok (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) :
    ApplyRatchetSpec img C A ctl uuidTryParse S abs :=
  fun himg hS => applyRatchet_ok_ext img C A ctl S (tripleRatchetExterns C ctl abs) himg (Stage2Contracts.of_tripleRatchetProgAt' hS)

theorem extHookStack_to_trApplyStackX (sp : BitVec 64) :
    stackAt (sp - 1504#64) extHookStack ∗
    memRegion (sp - 262144#64) (tryDecryptSubStack - extHookStack) ⊢
    stackAt (sp - 1504#64) trApplyStackX ∗
    memRegion (sp - 262144#64) (tryDecryptSubStack - trApplyStackX) := by
  have h1 := stackAt_sub_split (sp - 1504#64) extHookStack (by decide)
  have h2 := stackAt_sub_split (sp - 1504#64) trApplyStackX (by decide)
  rw [show sp - 1504#64 - BitVec.ofNat 64 tryDecryptSubStack = sp - 262144#64 by
        dsimp only [tryDecryptSubStack, rootStack, tryDecryptFrameSize]; bv_omega] at h1 h2
  rw [sepConj_comm, ← h1, h2, sepConj_comm]
  exact Entails.refl _

theorem trApplyStackX_to_clearUpkStackX (sp : BitVec 64) :
    stackAt (sp - 1504#64) trApplyStackX ∗
    memRegion (sp - 262144#64) (tryDecryptSubStack - trApplyStackX) ⊢
    stackAt (sp - 1504#64) clearUpkStackX ∗
    memRegion (sp - 262144#64) (tryDecryptSubStack - clearUpkStackX) := by
  have h1 := stackAt_sub_split (sp - 1504#64) trApplyStackX (by decide)
  have h2 := stackAt_sub_split (sp - 1504#64) clearUpkStackX (by decide)
  rw [show sp - 1504#64 - BitVec.ofNat 64 tryDecryptSubStack = sp - 262144#64 by
        dsimp only [tryDecryptSubStack, rootStack, tryDecryptFrameSize]; bv_omega] at h1 h2
  rw [sepConj_comm, ← h1, h2, sepConj_comm]
  exact Entails.refl _

theorem clearUpkStackX_to_subStack (sp : BitVec 64) :
    stackAt (sp - 1504#64) clearUpkStackX ∗
    memRegion (sp - 262144#64) (tryDecryptSubStack - clearUpkStackX) ⊢
    stackAt (sp - 1504#64) tryDecryptSubStack := by
  have h1 := stackAt_sub_split (sp - 1504#64) clearUpkStackX (by decide)
  rw [show sp - 1504#64 - BitVec.ofNat 64 tryDecryptSubStack = sp - 262144#64 by
        dsimp only [tryDecryptSubStack, rootStack, tryDecryptFrameSize]; bv_omega] at h1
  rw [sepConj_comm, ← h1]
  exact Entails.refl _

theorem extHookStack_to_subStack (sp : BitVec 64) :
    stackAt (sp - 1504#64) extHookStack ∗
    memRegion (sp - 262144#64) (tryDecryptSubStack - extHookStack) ⊢
    stackAt (sp - 1504#64) tryDecryptSubStack := by
  have h1 := stackAt_sub_split (sp - 1504#64) extHookStack (by decide)
  rw [show sp - 1504#64 - BitVec.ofNat 64 tryDecryptSubStack = sp - 262144#64 by
        dsimp only [tryDecryptSubStack, rootStack, tryDecryptFrameSize]; bv_omega] at h1
  rw [sepConj_comm, ← h1]
  exact Entails.refl _

theorem applyRatchet_from_6d0_x (img : Obj.Image) (C : Crypto)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hC : Stage2ContractsX img C A encFn decFn ext)
    (hTrApply : TrApplyOkX img A ext)
    (hClearUpk : ClearUpkOkX img A ext)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (newPqrState pt : List (BitVec 8))
    (newPqrCap newPqrPtr ptCap ptPtr : BitVec 64)
    (R : SepProp) (s0 s1 : State)
    (hok : (x.modelFn C decFn S uuidTryParse).1 = .ok pt)
    (hst : (x.modelFn C decFn S uuidTryParse).2 =
      (({ tr with pqrState := newPqrState }).applyToSessionState st1).clearUnacknowledgedPreKeyMessage)
    (hpad : trG.ratchet.senderPad.length = 100)
    (hnew_le : newPqrState.length ≤ newPqrCap.toNat)
    (hnew_lt : newPqrCap.toNat < 2 ^ 63)
    (hnew_nz : newPqrPtr ≠ 0)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hpt_lt : ptCap.toNat < 2 ^ 63)
    (hpt_nz : ptPtr ≠ 0)
    (hsp0 : s0.spAligned = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + 1744#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 1504#64)
    (hsp_al1 : s1.spAligned = true)
    (htr1 : s1.trace = s0.trace)
    (hfl1 : img.FrozenLoaded s1)
    (hsym1 : s1.symtab = img.symtab)
    (hx9_1 : s1.readReg64 .x9 = s0.sp - 800#64)
    (hx19_1 : s1.readReg64 .x19 = x.ret)
    (hx20_1 : s1.readReg64 .x20 = s0.sp - 1184#64)
    (hx21_1 : s1.readReg64 .x21 = x.ss)
    (hx24_1 : s1.readReg64 .x24 = BitVec.ofNat 64 newPqrState.length)
    (_hx29_1 : s1.readReg64 .x29 = s0.sp - 96#64)
    (hvregs_1 : calleeSavedVRegs s1 = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s1
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trWithoutPqAt A (s0.sp - 1448#64) trG.ratchet tr ∗
       ((s0.sp - 1272#64) ↦₆₄ trG.pq.cap) ∗
       ((s0.sp - 1264#64) ↦₆₄ trG.pq.ptr) ∗
       ((s0.sp - 1256#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
       (if newPqrCap = 0 then emp else (A.live newPqrPtr newPqrCap.toNat 1 ∗ (newPqrPtr ↦ₛ newPqrState)) ∗
         memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ∗
       ((s0.sp - 528#64) ↦₆₄ ptCap) ∗
       ((s0.sp - 520#64) ↦₆₄ ptPtr) ∗
       ((s0.sp - 512#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       (if ptCap = 0 then emp else (A.live ptPtr ptCap.toNat 1 ∗ (ptPtr ↦ₛ pt)) ∗
         memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
       memRegion x.ret 8 ∗
       memRegion (x.ret + 8#64) 8 ∗
       memRegion (x.ret + 16#64) 8 ∗
       memRegion (x.ret + 24#64) 8 ∗
       memRegion (x.ret + 32#64) 16 ∗
       memRegion (s0.sp - 1504#64) 8 ∗
       ((s0.sp - 1496#64) ↦₆₄ newPqrCap) ∗
       memRegion (s0.sp - 1488#64) 24 ∗
       ((s0.sp - 1464#64) ↦₆₄ newPqrPtr) ∗
       memRegion (s0.sp - 1456#64) 8 ∗
       memRegion (s0.sp - 1184#64) 8 ∗
       memRegion (s0.sp - 1176#64) 8 ∗
       memRegion (s0.sp - 1168#64) 8 ∗
       memRegion (s0.sp - 1160#64) 16 ∗
       memRegion (s0.sp - 1144#64) 8 ∗
       memRegion (s0.sp - 1136#64) 8 ∗
       memRegion (s0.sp - 1128#64) 8 ∗
       memRegion (s0.sp - 1120#64) 16 ∗
       memRegion (s0.sp - 1104#64) 264 ∗
       memRegion (s0.sp - 840#64) 120 ∗
       ((s0.sp - 720#64) ↦₆₄ ptCap) ∗
       ((s0.sp - 712#64) ↦₆₄ ptPtr) ∗
       ((s0.sp - 704#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       memRegion (s0.sp - 696#64) 168 ∗
       memRegion (s0.sp - 504#64) 0x198 ∗
       protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       tapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
       logOff img ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (tryDecryptFnSpec C decFn A ctl uuidTryParse S img).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (tryDecryptFnSpec C decFn A ctl uuidTryParse S img).onPanic x s0 sf ∗ R)) := by
  have hfn := hfn_tryDecrypt
  decrypt_fetches_ext img.base ext hfn 0x6d0 36
  decrypt_fetches_ext img.base ext hfn 0x4b8 72
  decrypt_fetches_ext img.base ext hfn 0x394 32
  have hmemcpy := memcpy_ok_at_x img hC
  have hbl_trApply := bl_trApply_target_ext img ext
  have hbl_clearUpk := bl_clearUpk_target_ext img ext
  dsimp only [tripleRatchetProgAtExt, TrApplyOkX, ClearUpkOkX] at *
  generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr trApplyName = trApply_entry at hbl_trApply hTrApply
  generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr clearUpkName = clearUpk_entry at hbl_clearUpk hClearUpk
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr tryDecryptName = entry
  simp only [wp_norm] at hpc1 hsp1 hx9_1 hx19_1 hx20_1 hx21_1 hx24_1
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1184#64) (by sep_focus) fun w1184 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1176#64) (by sep_focus) fun w1176 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1168#64) (by sep_focus) fun w1168 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1144#64) (by sep_focus) fun w1144 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1136#64) (by sep_focus) fun w1136 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1128#64) (by sep_focus) fun w1128 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 8#64) (by sep_focus) fun wret8 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 16#64) (by sep_focus) fun wret16 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 24#64) (by sep_focus) fun wret24 => ?_
  rw [stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide)]
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_frozen hfl1 hsym1 (mid := entry + bv% (ls_off% "memcpy" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hfl2 hsym2
  refine SepWPp.mono_focus
    (trAt_of_withoutPq A s0.sp trG tr newPqrCap newPqrPtr newPqrState hnew_le hnew_lt hnew_nz)
    (by sep_focus) ?_
  rw [trAt_eq_stack_heap A (s0.sp - 1448#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
      { tr with pqrState := newPqrState } hpad]
  refine SepWPp.elim_exists_focus
    (Φ := fun pad : BitVec 32 =>
      ((s0.sp - 1448#64) ↦ₛ trStackBytes { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
        { tr with pqrState := newPqrState } pad) ∗
      trHeapPart A { trG with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState })
    (by sep_focus) fun pad => ?_
  have hbs_len : (trStackBytes { trG with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState } pad).length = 264 :=
    length_trStackBytes _ _ pad hpad
  generalize hbs_def : trStackBytes { trG with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState } pad = bs at hbs_len ⊢
  rw [show memRegion (s0.sp - 1104#64) 264 = memRegion (s0.sp - 1104#64) bs.length by rw [hbs_len]]
  simp only [← sepConj_assoc]
  refine SepWPp.call_inImage_frame (img := img) (spec := withStack sessionMemcpyRegionSpec extHookStack)
    (x := (s0.sp - 1104#64, s0.sp - 1448#64, bs))
    (T := memRegion (s0.sp - 1104#64) bs.length ∗ ((s0.sp - 1448#64) ↦ₛ bs) ∗
          stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := entry + bv% (1248))
    hfl2 hsym2 hmemcpy (by rfl) (by exact hrun1)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1) (by rfl)
    (by dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]; rw [sepConj_assoc, sepConj_assoc]; congr 3; simp only [wp_norm, hsp1])
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm, hbs_len]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ hm_pan => by dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hfl2 hsym2
  intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hfl2 hsym2
  simp only [wp_norm, hsp1] at hsp2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _hx29_2, hvregs_2⟩
  simp only [wp_norm, hx19_1, hx20_1, hx21_1, hx24_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx24_2 hvregs_2
  dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
  simp only [wp_norm, hsp1, sepConj_assoc]
  apply SepWPp.elim_pure; rintro ⟨_, htr2⟩
  have htr20 : s2.trace = s0.trace := htr2.trans htr1
  rw [← hbs_def]
  refine SepWPp.mono_focus
    (trAt_of_stack_heap A (s0.sp - 1104#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
      { tr with pqrState := newPqrState } pad hpad)
    (by sep_focus) ?_
  rw [hbs_def]
  refine SepWPp.mono_focus (extHookStack_to_trApplyStackX s0.sp) (by sep_focus) ?_
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_frozen hfl2 hsym2 (mid := trApply_entry)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun2)
  intro hfl3 hsym3
  refine SepWPp.call_inImage_frame (img := img) (spec := trApplySpecX A)
    (x := ⟨s0.sp - 1104#64, { trG with pq := ⟨newPqrCap, newPqrPtr⟩ },
           { tr with pqrState := newPqrState }, x.ss, x.G.afterTrFrom, st1⟩)
    (T := trAt A (s0.sp - 1104#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
            { tr with pqrState := newPqrState } ∗
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          stackAt (s0.sp - 1504#64) trApplyStackX ∗ A.pool)
    (ret_pc := entry + bv% (1260))
    hfl3 hsym3 hTrApply (by rfl) (by exact hrun2)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
    (by dsimp only [trApplySpecX]; simp only [wp_norm, hsp2]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [trApplySpecX] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ hm_pan => by
      have h0m : s0.trace <+: (s2.writeReg64 .x0 (s0.sp - 1104#64)
        |>.writeReg64 .x1 x.ss |>.writeReg64 .x30 (entry + bv% (1260))
        |>.setPC trApply_entry).trace := by
        rw [show (s2.writeReg64 .x0 (s0.sp - 1104#64)
          |>.writeReg64 .x1 x.ss |>.writeReg64 .x30 (entry + bv% (1260))
          |>.setPC trApply_entry).trace = s2.trace from rfl, htr20]
      exact tryDecryptFn_onPanic_of_callee C decFn A ctl S img x s0 _ sf _ R h0m hm_pan) ?_
  clear hfl3 hsym3
  intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hfl3 hsym3
  simp only [wp_norm, hsp2] at hsp3
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, _hx29_3, hvregs_3⟩
  simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx24_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx24_3 hvregs_3
  dsimp only [trApplySpecX]
  simp only [wp_norm, hsp2, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr3
  have htr30 : s3.trace = s0.trace := htr3.trans htr20
  apply SepWPp.elim_exists; intro G1
  simp only [sepConj_assoc]
  apply SepWPp.elim_pure; intro hG1
  refine SepWPp.mono_focus (trApplyStackX_to_clearUpkStackX s0.sp) (by sep_focus) ?_
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_frozen hfl3 hsym3 (mid := clearUpk_entry)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun3)
  intro hfl4 hsym4
  refine SepWPp.call_inImage_frame (img := img) (spec := clearUpkSpecX A)
    (x := ⟨x.ss, G1, ({ tr with pqrState := newPqrState }).applyToSessionState st1⟩)
    (T := sessionStateAt A x.ss G1 (({ tr with pqrState := newPqrState }).applyToSessionState st1) ∗
          A.pool ∗ stackAt (s0.sp - 1504#64) clearUpkStackX)
    (ret_pc := entry + bv% (1268))
    hfl4 hsym4 hClearUpk (by rfl) (by exact hrun3)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
    (by dsimp only [clearUpkSpecX]; simp only [wp_norm, hsp3]; rfl)
    (by simp only [wp_norm])
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [clearUpkSpecX] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ hm_pan => by dsimp only [clearUpkSpecX] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hfl4 hsym4
  intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hfl4 hsym4
  simp only [wp_norm, hsp3] at hsp4
  rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, _hx29_4, hvregs_4⟩
  simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx24_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx24_4 hvregs_4
  dsimp only [clearUpkSpecX]
  simp only [wp_norm, hsp3, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr4
  have htr40 : s4.trace = s0.trace := htr4.trans htr30
  refine SepWPp.mono_focus (clearUpkStackX_to_subStack s0.sp) (by sep_focus) ?_
  refine SepWPp.mono_focus
    (applyRatchet_local_frame_entails_memRegion s0.sp newPqrCap newPqrPtr ptCap ptPtr
      (BitVec.ofNat 64 pt.length) ptCap ptPtr (BitVec.ofNat 64 pt.length)
      ptCap ptPtr (BitVec.ofNat 64 pt.length) ptCap ptPtr (BitVec.ofNat 64 pt.length)
      bs hbs_len) (by sep_focus) ?_
  refine SepWPp.mono_focus (Entails.refl (tryDecryptSavedRegs s0.sp s0)) (by sep_focus) ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret) (by sep_focus) fun wret => ?_
  unfold tryDecryptSavedRegs
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun4)
  refine ⟨fun hmf => ?_, by simp only [wp_norm], ?_⟩
  · dsimp only [tryDecryptFnSpec, Spec.inImage]
    rw [hok]
    rw [← hst] at hmf
    have hdec := decRel_of_trApplyRel hG1
    have hsaved := tryDecryptSavedRegs_entails_memRegion s0.sp s0
    unfold tryDecryptSavedRegs at hsaved
    have hmf1 := Satisfies.mono_focus hsaved (by sep_focus) hmf
    have hmf3 := Satisfies.mono_focus (stackAt_rootStack_of_parts s0.sp) (by sep_focus) hmf1
    rw [show (bv% (2 ^ 64 - 2) : BitVec 64) = okTagVec from rfl] at hmf3
    have hmf4 := Satisfies.mono_focus
      (decResultAt_ok_of_parts A x.ret pt ptCap ptPtr hpt_le hpt_lt hpt_nz) (by sep_focus) hmf3
    have hss : sessionStateAt A x.ss { G1 with pending := none, kyber := none } (x.modelFn C decFn S uuidTryParse).2 ⊢
        ∃∗ G' : SessionGhost, ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
          sessionStateAt A x.ss G' (x.modelFn C decFn S uuidTryParse).2 := by
      refine Entails.trans ?_
        (Entails.sepExists_intro
          (P := fun G' : SessionGhost =>
            ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
            sessionStateAt A x.ss G' (x.modelFn C decFn S uuidTryParse).2)
          { G1 with pending := none, kyber := none })
      exact Entails.pure_right hdec (Entails.refl _)
    have hmf5 := Satisfies.mono_focus hss (by sep_focus) hmf4
    clear hmf hmf1 hmf3 hmf4
    have hno_pan : (Except.ok pt : Except SignalProtocolError (List (BitVec 8))) ≠ .error .panic := nofun
    simp only [wp_norm, sepConj_assoc, satisfies_pure_sepConj] at hmf5 ⊢
    refine ⟨⟨hno_pan, htr40⟩, ?_⟩
    generalize (∃∗ G', ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
      sessionStateAt A x.ss G' (x.modelFn C decFn S uuidTryParse).2) = SS at hmf5 ⊢
    change _ ⊨ SS ∗ vecResultAt A x.ret (.ok pt) ∗ _
    sep_close
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, hvregs_4]

theorem applyRatchet_ok_x (img : Obj.Image) (C : Crypto)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) :
    S9SpecX img C encFn decFn A ctl uuidTryParse S ext := by
  intro himg hC hTrApply hClearUpk x trG tr st1 newPqrState pt R s0 s hok hst h9
  have hfn := hfn_tryDecrypt
  decrypt_fetches_ext img.base ext hfn 0x6a4 44
  have hS9_pc := segS9PC_eq_ext himg ext
  have hdealloc := dealloc_ok_at_x img C A encFn decFn ext hC
  rcases h9 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hfl, hsym, hvregs⟩,
    hx19, hx20, hx21, hx23, hx24, newPqrCap, newPqrPtr, hnew_le, hnew_lt, hnew_nz, hmem⟩
  rw [hS9_pc] at hpc
  have h6d0 := @applyRatchet_from_6d0_x img C encFn decFn A ctl S ext hC hTrApply hClearUpk x trG tr st1
    newPqrState pt newPqrCap newPqrPtr
  clear hTrApply hClearUpk
  dsimp only [tripleRatchetProgAtExt] at *
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr tryDecryptName = entry
  have hpad : trG.ratchet.senderPad.length = 100 := by
    have htr_front := hmem
    rw [← sepConj_assoc, sepConj_comm (sessionStateAt A x.ss x.G.afterTrFrom st1), sepConj_assoc] at htr_front
    exact trAt_senderPad_len htr_front
  unfold tryDecryptCommonHeap at hmem
  rw [trAt_eq_withoutPq A s0.sp trG tr,
       applyRatchet_scr_split s0.sp,
       applyRatchet_ret_split x.ret,
       show s0.sp - 1504#64 + 0x3d0#64 = s0.sp - 528#64 by bv_omega,
       show s0.sp - 1504#64 + 0x8#64 = s0.sp - 1496#64 by bv_omega,
       show s0.sp - 1504#64 + 0x10#64 = s0.sp - 1488#64 by bv_omega,
       show s0.sp - 1504#64 + 0x28#64 = s0.sp - 1464#64 by bv_omega,
       show s0.sp - 1504#64 + 0x30#64 = s0.sp - 1456#64 by bv_omega,
       show s0.sp - 1504#64 + 0x3e8#64 = s0.sp - 504#64 by bv_omega] at hmem
  simp only [wp_norm] at hpc hx20 hx23 hx29
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_reaches_outcome hmem ?_
  refine SepWPp.elim_pure_focus
    (φ := tr.pqrState.length ≤ trG.pq.cap.toNat ∧ trG.pq.cap.toNat < 2 ^ 63 ∧ trG.pq.ptr ≠ 0)
    (by sep_focus) fun ⟨hpq_le, hpq_lt, hpq_nz⟩ => ?_
  refine SepWPp.elim_vecU8_focus (A := A) (a := s0.sp - 528#64) (bs := pt)
    (by sep_focus) fun ptCap ptPtr hpt_le hpt_lt hpt_nz => ?_
  rw [show s0.sp - 528#64 + 8#64 = s0.sp - 520#64 by bv_omega,
      show s0.sp - 528#64 + 16#64 = s0.sp - 512#64 by bv_omega]
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 720#64) (by sep_focus) fun w720 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 712#64) (by sep_focus) fun w712 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 704#64) (by sep_focus) fun w704 => ?_
  by_cases hpq_cap : trG.pq.cap = 0#64
  · refine SepWPp.mono_focus (newPqr_zero_prep A trG.pq.cap trG.pq.ptr tr.pqrState hpq_cap) (by sep_focus) ?_
    rw [emp_sepConj]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_frozen hfl hsym (mid := entry + bv% (1744))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    intro hfl1 hsym1
    refine SepWPp.congr_pre (by sep_focus)
      (h6d0 ptCap ptPtr R s0 _
        hok hst hpad hnew_le hnew_lt hnew_nz hpt_le hpt_lt hpt_nz
        hsp0 (by rfl) (by exact hrun) (by simp only [wp_norm, hsp])
        (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al)
        htr hfl1 hsym1
        (by simp only [wp_norm])
        (by simp only [wp_norm, hx19])
        (by simp only [wp_norm, hx20])
        (by simp only [wp_norm, hx21])
        (by simp only [wp_norm, hx24])
        (by simp only [wp_norm, hx29])
        (by simp only [wp_norm, hvregs]))
  · refine SepWPp.mono_focus (newPqr_dealloc_prep' A trG.pq.cap trG.pq.ptr tr.pqrState hpq_cap hpq_le hpq_lt) (by sep_focus) ?_
    rw [stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide)]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_frozen hfl hsym (mid := entry + bv% (1728))
    wp_steps
    apply SepWP.setPC_setMem_ite_false (by simp only [beq_iff_eq, hpq_cap, not_false_eq_true])
    apply SepWP.done (by rfl) (by exact hrun)
    intro hfl0 hsym0
    apply SepWPp.of_sepWP_frozen hfl0 hsym0 (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    intro hfl1 hsym1
    refine SepWPp.call_inImage_frame (img := img) (spec := rustDeallocExternSpecWithStack A extHookStack)
      (x := (trG.pq.ptr, trG.pq.cap.toNat, 1))
      (T := A.pool ∗ A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat ∗
            stackAt (s0.sp - 1504#64) extHookStack)
      (ret_pc := entry + bv% (1740))
      hfl1 hsym1 hdealloc (by rfl) (by exact hrun)
      (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
      (by dsimp only [rustDeallocExternSpecWithStack]; simp only [wp_norm, hsp]; rfl)
      (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                  layoutOk_of_cap_ne_zero hpq_cap hpq_lt⟩)
      (by sep_focus)
      (fun _ _ _ _ h => by dsimp only [rustDeallocExternSpecWithStack] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
      (fun sf _ hm_pan => by dsimp only [rustDeallocExternSpecWithStack] at hm_pan; exact noPanic_callee hm_pan) ?_
    clear hfl0 hsym0 hfl1 hsym1
    intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hfl1 hsym1
    simp only [wp_norm, hsp] at hsp1
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [wp_norm, hx19, hx20, hx21, hx24, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx24_1 hx29_1 hvregs_1
    dsimp only [rustDeallocExternSpecWithStack, rustDeallocSpecWithStack]
    simp only [wp_norm, hsp, sepConj_assoc]
    apply SepWPp.elim_pure; intro htr1
    have htr10 : s1.trace = s0.trace := htr1.trans htr
    refine SepWPp.mono_focus (extHookStack_to_subStack s0.sp) (by sep_focus) ?_
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_frozen hfl1 hsym1 (mid := entry + bv% (1744))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun1)
    intro hfl2 hsym2
    refine SepWPp.congr_pre (by sep_focus)
      (h6d0 ptCap ptPtr R s0 _
        hok hst hpad hnew_le hnew_lt hnew_nz hpt_le hpt_lt hpt_nz
        hsp0 (by rfl) (by exact hrun1) (by simp only [wp_norm, hsp1])
        (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1)
        htr10 hfl2 hsym2
        (by simp only [wp_norm])
        (by simp only [wp_norm, hx19_1])
        (by simp only [wp_norm, hx20_1])
        (by simp only [wp_norm, hx21_1])
        (by simp only [wp_norm, hx24_1])
        (by simp only [wp_norm, hx29_1])
        (by simp only [wp_norm, hvregs_1]))

/-! ## Relocatable `[LibsignalPlacement]` Segment 9 Proofs (Blocks `130` and `549`) -/

theorem applyRatchet_from_6d0_159_placed [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hTrApply : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 58) (withLsCodeRoLoaded lsmpl (trApplySpec A)))
    (hClearUpk : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 35) (withLsCodeRoLoaded lsmpl (clearUpkSpec A)))
    (hmemcpy : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (newPqrState pt : List (BitVec 8))
    (newPqrCap newPqrPtr ptCap ptPtr : BitVec 64)
    (R : SepProp) (s0 s1 : State)
    (hok : (x.model C S uuidTryParse).1 = .ok pt)
    (hst : (x.model C S uuidTryParse).2 =
      (({ tr with pqrState := newPqrState }).applyToSessionState st1).clearUnacknowledgedPreKeyMessage)
    (hpad : trG.ratchet.senderPad.length = 100)
    (hnew_le : newPqrState.length ≤ newPqrCap.toNat)
    (hnew_lt : newPqrCap.toNat < 2 ^ 63)
    (hnew_nz : newPqrPtr ≠ 0)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hpt_lt : ptCap.toNat < 2 ^ 63)
    (hpt_nz : ptPtr ≠ 0)
    (hsp0 : s0.spAligned = true)
    (hpc1 : s1.pc = (blkPl_131).base + 1744#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 1504#64)
    (hsp_al1 : s1.spAligned = true)
    (htr1 : s1.trace = s0.trace)
    (hcl1 : LibsignalCodeRoLoaded lsmpl s1.mem)
    (hx9_1 : s1.readReg64 .x9 = s0.sp - 800#64)
    (hx19_1 : s1.readReg64 .x19 = x.ret)
    (hx20_1 : s1.readReg64 .x20 = s0.sp - 1184#64)
    (hx21_1 : s1.readReg64 .x21 = x.ss)
    (hx24_1 : s1.readReg64 .x24 = BitVec.ofNat 64 newPqrState.length)
    (_hx29_1 : s1.readReg64 .x29 = s0.sp - 96#64)
    (hvregs_1 : calleeSavedVRegs s1 = calleeSavedVRegs s0) :
    SepWPp ((blkPC_131).rebase (blkPl_131).base H) (s0.readReg64 .lr) s1
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trWithoutPqAt A (s0.sp - 1448#64) trG.ratchet tr ∗
       ((s0.sp - 1272#64) ↦₆₄ trG.pq.cap) ∗
       ((s0.sp - 1264#64) ↦₆₄ trG.pq.ptr) ∗
       ((s0.sp - 1256#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
       (if newPqrCap = 0 then emp else (A.live newPqrPtr newPqrCap.toNat 1 ∗ (newPqrPtr ↦ₛ newPqrState)) ∗
         memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ∗
       ((s0.sp - 528#64) ↦₆₄ ptCap) ∗
       ((s0.sp - 520#64) ↦₆₄ ptPtr) ∗
       ((s0.sp - 512#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       (if ptCap = 0 then emp else (A.live ptPtr ptCap.toNat 1 ∗ (ptPtr ↦ₛ pt)) ∗
         memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
       memRegion x.ret 8 ∗
       memRegion (x.ret + 8#64) 8 ∗
       memRegion (x.ret + 16#64) 8 ∗
       memRegion (x.ret + 24#64) 8 ∗
       memRegion (x.ret + 32#64) 16 ∗
       memRegion (s0.sp - 1504#64) 8 ∗
       ((s0.sp - 1496#64) ↦₆₄ newPqrCap) ∗
       memRegion (s0.sp - 1488#64) 24 ∗
       ((s0.sp - 1464#64) ↦₆₄ newPqrPtr) ∗
       memRegion (s0.sp - 1456#64) 8 ∗
       memRegion (s0.sp - 1184#64) 8 ∗
       memRegion (s0.sp - 1176#64) 8 ∗
       memRegion (s0.sp - 1168#64) 8 ∗
       memRegion (s0.sp - 1160#64) 16 ∗
       memRegion (s0.sp - 1144#64) 8 ∗
       memRegion (s0.sp - 1136#64) 8 ∗
       memRegion (s0.sp - 1128#64) 8 ∗
       memRegion (s0.sp - 1120#64) 16 ∗
       memRegion (s0.sp - 1104#64) 264 ∗
       memRegion (s0.sp - 840#64) 120 ∗
       ((s0.sp - 720#64) ↦₆₄ ptCap) ∗
       ((s0.sp - 712#64) ↦₆₄ ptPtr) ∗
       ((s0.sp - 704#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       memRegion (s0.sp - 696#64) 168 ∗
       memRegion (s0.sp - 504#64) 0x198 ∗
       protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       tapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
       logOff tryDecryptPlacedImg ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 sf ∗ R)) := by
  simp only [wp_norm] at hpc1 hsp1 hx9_1 hx19_1 hx20_1 hx21_1 hx24_1
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1184#64) (by sep_focus) fun w1184 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1176#64) (by sep_focus) fun w1176 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1168#64) (by sep_focus) fun w1168 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1144#64) (by sep_focus) fun w1144 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1136#64) (by sep_focus) fun w1136 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1128#64) (by sep_focus) fun w1128 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 8#64) (by sep_focus) fun wret8 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 16#64) (by sep_focus) fun wret16 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 24#64) (by sep_focus) fun wret24 => ?_
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl1 (mid := lsρ lsMemcpySym)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hcl2
  refine SepWPp.mono_focus
    (trAt_of_withoutPq A s0.sp trG tr newPqrCap newPqrPtr newPqrState hnew_le hnew_lt hnew_nz)
    (by sep_focus) ?_
  rw [trAt_eq_stack_heap A (s0.sp - 1448#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
      { tr with pqrState := newPqrState } hpad]
  refine SepWPp.elim_exists_focus
    (Φ := fun pad : BitVec 32 =>
      ((s0.sp - 1448#64) ↦ₛ trStackBytes { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
        { tr with pqrState := newPqrState } pad) ∗
      trHeapPart A { trG with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState })
    (by sep_focus) fun pad => ?_
  have hbs_len : (trStackBytes { trG with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState } pad).length = 264 :=
    length_trStackBytes _ _ pad hpad
  generalize hbs_def : trStackBytes { trG with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState } pad = bs at hbs_len ⊢
  rw [show memRegion (s0.sp - 1104#64) 264 = memRegion (s0.sp - 1104#64) bs.length by rw [hbs_len]]
  simp only [← sepConj_assoc]
  refine SepWPp.call_frame_placed (spec := sessionMemcpyRegionSpec)
    (x := (s0.sp - 1104#64, s0.sp - 1448#64, bs))
    (T := memRegion (s0.sp - 1104#64) bs.length ∗ ((s0.sp - 1448#64) ↦ₛ bs))
    (ret_pc := (blkPl_131).base + bv% (1248))
    hcl2 hmemcpy (by rfl) (by exact hrun1)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1) (by rfl)
    (by rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm, hbs_len]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ hm_pan => by dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl2
  intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hcl2
  simp only [wp_norm, hsp1] at hsp2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _hx29_2, hvregs_2⟩
  simp only [wp_norm, hx19_1, hx20_1, hx21_1, hx24_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx24_2 hvregs_2
  dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
  simp only [wp_norm, sepConj_assoc]
  apply SepWPp.elim_pure; rintro ⟨_, htr2⟩
  have htr20 : s2.trace = s0.trace := htr2.trans htr1
  rw [← hbs_def]
  refine SepWPp.mono_focus
    (trAt_of_stack_heap A (s0.sp - 1104#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
      { tr with pqrState := newPqrState } pad hpad)
    (by sep_focus) ?_
  rw [hbs_def]
  rw [stackAt_sub_split (s0.sp - 1504#64) trApplyStack (by decide)]
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl2 (mid := lsmpl.base 58)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun2)
  intro hcl3
  refine SepWPp.call_cro_frame_placed (spec := trApplySpec A)
    (x := ⟨s0.sp - 1104#64, { trG with pq := ⟨newPqrCap, newPqrPtr⟩ },
           { tr with pqrState := newPqrState }, x.ss, x.G.afterTrFrom, st1⟩)
    (T := trAt A (s0.sp - 1104#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
            { tr with pqrState := newPqrState } ∗
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          stackAt (s0.sp - 1504#64) trApplyStack ∗ A.pool)
    (ret_pc := (blkPl_131).base + bv% (1260))
    hcl3 hTrApply (by rfl) (by exact hrun2)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
    (by dsimp only [trApplySpec]; simp only [wp_norm, hsp2]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [trApplySpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ hm_pan => by
      have h0m : s0.trace <+: (s2.writeReg64 .x0 (s0.sp - 1104#64)
        |>.writeReg64 .x1 x.ss |>.writeReg64 .x30 ((blkPl_131).base + bv% (1260))
        |>.setPC (lsmpl.base 58)).trace := by
        rw [show (s2.writeReg64 .x0 (s0.sp - 1104#64)
          |>.writeReg64 .x1 x.ss |>.writeReg64 .x30 ((blkPl_131).base + bv% (1260))
          |>.setPC (lsmpl.base 58)).trace = s2.trace from rfl, htr20]
      exact tryDecrypt_onPanic_of_callee_placed C A ctl S x s0 _ sf _ R h0m hm_pan) ?_
  clear hcl3
  intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hcl3
  simp only [wp_norm, hsp2] at hsp3
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, _hx29_3, hvregs_3⟩
  simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx24_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx24_3 hvregs_3
  dsimp only [trApplySpec]
  simp only [wp_norm, hsp2, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr3
  have htr30 : s3.trace = s0.trace := htr3.trans htr20
  apply SepWPp.elim_exists; intro G1
  simp only [sepConj_assoc]
  apply SepWPp.elim_pure; intro hG1
  refine SepWPp.mono_focus (trApplyStack_to_clearUpkStack s0.sp) (by sep_focus) ?_
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl3 (mid := lsmpl.base 35)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun3)
  intro hcl4
  refine SepWPp.call_cro_frame_placed (spec := clearUpkSpec A)
    (x := ⟨x.ss, G1, ({ tr with pqrState := newPqrState }).applyToSessionState st1⟩)
    (T := sessionStateAt A x.ss G1 (({ tr with pqrState := newPqrState }).applyToSessionState st1) ∗
          A.pool ∗ stackAt (s0.sp - 1504#64) clearUpkStack)
    (ret_pc := (blkPl_131).base + bv% (1268))
    hcl4 hClearUpk (by rfl) (by exact hrun3)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
    (by dsimp only [clearUpkSpec]; simp only [wp_norm, hsp3]; rfl)
    (by simp only [wp_norm])
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [clearUpkSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ hm_pan => by dsimp only [clearUpkSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl4
  intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hcl4
  simp only [wp_norm, hsp3] at hsp4
  rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, _hx29_4, hvregs_4⟩
  simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx24_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx24_4 hvregs_4
  dsimp only [clearUpkSpec]
  simp only [wp_norm, hsp3, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr4
  have htr40 : s4.trace = s0.trace := htr4.trans htr30
  refine SepWPp.mono_focus (clearUpkStack_to_subStack s0.sp) (by sep_focus) ?_
  refine SepWPp.mono_focus
    (applyRatchet_local_frame_entails_memRegion s0.sp newPqrCap newPqrPtr ptCap ptPtr
      (BitVec.ofNat 64 pt.length) ptCap ptPtr (BitVec.ofNat 64 pt.length)
      ptCap ptPtr (BitVec.ofNat 64 pt.length) ptCap ptPtr (BitVec.ofNat 64 pt.length)
      bs hbs_len) (by sep_focus) ?_
  refine SepWPp.mono_focus (Entails.refl (tryDecryptSavedRegs s0.sp s0)) (by sep_focus) ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret) (by sep_focus) fun wret => ?_
  unfold tryDecryptSavedRegs
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun4)
  refine ⟨fun hmf => ?_, by simp only [wp_norm], ?_⟩
  · dsimp only [tryDecryptSpecPlaced, withLsCodeRoLoaded, tryDecryptRawSpecPlaced, tryDecryptSpec, Spec.inImage]
    rw [hok]
    rw [← hst] at hmf
    have hdec := decRel_of_trApplyRel hG1
    have hsaved := tryDecryptSavedRegs_entails_memRegion s0.sp s0
    unfold tryDecryptSavedRegs at hsaved
    have hmf1 := Satisfies.mono_focus hsaved (by sep_focus) hmf
    have hmf3 := Satisfies.mono_focus (stackAt_rootStack_of_parts s0.sp) (by sep_focus) hmf1
    rw [show (bv% (2 ^ 64 - 2) : BitVec 64) = okTagVec from rfl] at hmf3
    have hmf4 := Satisfies.mono_focus
      (decResultAt_ok_of_parts A x.ret pt ptCap ptPtr hpt_le hpt_lt hpt_nz) (by sep_focus) hmf3
    have hss : sessionStateAt A x.ss { G1 with pending := none, kyber := none } (x.model C S uuidTryParse).2 ⊢
        ∃∗ G' : SessionGhost, ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
          sessionStateAt A x.ss G' (x.model C S uuidTryParse).2 := by
      refine Entails.trans ?_
        (Entails.sepExists_intro
          (P := fun G' : SessionGhost =>
            ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
            sessionStateAt A x.ss G' (x.model C S uuidTryParse).2)
          { G1 with pending := none, kyber := none })
      exact Entails.pure_right hdec (Entails.refl _)
    have hmf5 := Satisfies.mono_focus hss (by sep_focus) hmf4
    clear hmf hmf1 hmf3 hmf4
    have hno_pan : (Except.ok pt : Except SignalProtocolError (List (BitVec 8))) ≠ .error .panic := nofun
    simp only [wp_norm, sepConj_assoc, satisfies_pure_sepConj] at hmf5 ⊢
    refine ⟨⟨hno_pan, htr40⟩, ?_⟩
    generalize (∃∗ G', ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
      sessionStateAt A x.ss G' (x.model C S uuidTryParse).2) = SS at hmf5 ⊢
    sep_close
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, hvregs_4]

theorem applyRatchet_159_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hTrApply : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 58) (withLsCodeRoLoaded lsmpl (trApplySpec A)))
    (hClearUpk : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 35) (withLsCodeRoLoaded lsmpl (clearUpkSpec A)))
    (hmemcpy : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (hdealloc : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsρ lsRustDeallocSym) (rustDeallocSpec A)) :
    S9SeamPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base C A ctl uuidTryParse S := by
  intro x trG tr st1 newPqrState pt R s0 s hok hst h9
  rcases h9 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx23, hx24, newPqrCap, newPqrPtr, hnew_le, hnew_lt, hnew_nz, hmem⟩
  have h6d0 := @applyRatchet_from_6d0_159_placed _ C A ctl S H hTrApply hClearUpk hmemcpy x trG tr st1
    newPqrState pt newPqrCap newPqrPtr
  clear hTrApply hClearUpk
  have hpad : trG.ratchet.senderPad.length = 100 := by
    have htr_front := hmem
    rw [← sepConj_assoc, sepConj_comm (sessionStateAt A x.ss x.G.afterTrFrom st1), sepConj_assoc] at htr_front
    exact trAt_senderPad_len htr_front
  unfold tryDecryptCommonHeap at hmem
  rw [trAt_eq_withoutPq A s0.sp trG tr,
       applyRatchet_scr_split s0.sp,
       applyRatchet_ret_split x.ret,
       show s0.sp - 1504#64 + 0x3d0#64 = s0.sp - 528#64 by bv_omega,
       show s0.sp - 1504#64 + 0x8#64 = s0.sp - 1496#64 by bv_omega,
       show s0.sp - 1504#64 + 0x10#64 = s0.sp - 1488#64 by bv_omega,
       show s0.sp - 1504#64 + 0x28#64 = s0.sp - 1464#64 by bv_omega,
       show s0.sp - 1504#64 + 0x30#64 = s0.sp - 1456#64 by bv_omega,
       show s0.sp - 1504#64 + 0x3e8#64 = s0.sp - 504#64 by bv_omega] at hmem
  change s.pc = (blkPl_131).base + 1700#64 at hpc
  simp only [wp_norm] at hx20 hx23 hx29
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_reaches_outcome hmem ?_
  refine SepWPp.elim_pure_focus
    (φ := tr.pqrState.length ≤ trG.pq.cap.toNat ∧ trG.pq.cap.toNat < 2 ^ 63 ∧ trG.pq.ptr ≠ 0)
    (by sep_focus) fun ⟨hpq_le, hpq_lt, hpq_nz⟩ => ?_
  refine SepWPp.elim_vecU8_focus (A := A) (a := s0.sp - 528#64) (bs := pt)
    (by sep_focus) fun ptCap ptPtr hpt_le hpt_lt hpt_nz => ?_
  rw [show s0.sp - 528#64 + 8#64 = s0.sp - 520#64 by bv_omega,
      show s0.sp - 528#64 + 16#64 = s0.sp - 512#64 by bv_omega]
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 720#64) (by sep_focus) fun w720 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 712#64) (by sep_focus) fun w712 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 704#64) (by sep_focus) fun w704 => ?_
  by_cases hpq_cap : trG.pq.cap = 0#64
  · refine SepWPp.mono_focus (newPqr_zero_prep A trG.pq.cap trG.pq.ptr tr.pqrState hpq_cap) (by sep_focus) ?_
    rw [emp_sepConj]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl (mid := (blkPl_131).base + bv% (1744))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    intro hcl1
    refine SepWPp.congr_pre (by sep_focus)
      (h6d0 ptCap ptPtr R s0 _
        hok hst hpad hnew_le hnew_lt hnew_nz hpt_le hpt_lt hpt_nz
        hsp0 (by rfl) (by exact hrun) (by simp only [wp_norm, hsp])
        (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al)
        htr hcl1
        (by simp only [wp_norm])
        (by simp only [wp_norm, hx19])
        (by simp only [wp_norm, hx20])
        (by simp only [wp_norm, hx21])
        (by simp only [wp_norm, hx24])
        (by simp only [wp_norm, hx29])
        (by simp only [wp_norm, hvregs]))
  · refine SepWPp.mono_focus (newPqr_dealloc_prep' A trG.pq.cap trG.pq.ptr tr.pqrState hpq_cap hpq_le hpq_lt) (by sep_focus) ?_
    rw [stackAt_sub_split (s0.sp - 1504#64) allocHookStack (by decide)]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl (mid := (blkPl_131).base + bv% (1728))
    wp_steps
    apply SepWP.setPC_setMem_ite_false (by simp only [beq_iff_eq, hpq_cap, not_false_eq_true])
    apply SepWP.done (by rfl) (by exact hrun)
    intro hcl0
    apply SepWPp.of_sepWP_placed hcl0 (mid := lsρ lsRustDeallocSym)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    intro hcl1
    refine SepWPp.call_frame_placed (spec := rustDeallocSpec A)
      (x := (trG.pq.ptr, trG.pq.cap.toNat, 1))
      (T := A.pool ∗ A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat ∗
            stackAt (s0.sp - 1504#64) allocHookStack)
      (ret_pc := (blkPl_131).base + bv% (1740))
      hcl1 hdealloc (by rfl) (by exact hrun)
      (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
      (by dsimp only [rustDeallocSpec]; simp only [wp_norm, hsp]; rfl)
      (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
      (by sep_focus)
      (fun _ _ _ _ h => by dsimp only [rustDeallocSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
      (fun sf _ hm_pan => by dsimp only [rustDeallocSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
    clear hcl0 hcl1
    intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hcl1
    simp only [wp_norm, hsp] at hsp1
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [wp_norm, hx19, hx20, hx21, hx24, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx24_1 hx29_1 hvregs_1
    dsimp only [rustDeallocSpec]
    simp only [wp_norm, hsp, sepConj_assoc]
    apply SepWPp.elim_pure; intro htr1
    have htr10 : s1.trace = s0.trace := htr1.trans htr
    refine SepWPp.mono_focus (allocHookStack_to_subStack s0.sp) (by sep_focus) ?_
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl1 (mid := (blkPl_131).base + bv% (1744))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun1)
    intro hcl2
    rw [← logOff_tryDecryptPlacedImg]
    refine SepWPp.congr_pre (by sep_focus)
      (h6d0 ptCap ptPtr R s0 _
        hok hst hpad hnew_le hnew_lt hnew_nz hpt_le hpt_lt hpt_nz
        hsp0 (by rfl) (by exact hrun1) (by simp only [wp_norm, hsp1])
        (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1)
        htr10 hcl2
        (by simp only [wp_norm])
        (by simp only [wp_norm, hx19_1])
        (by simp only [wp_norm, hx20_1])
        (by simp only [wp_norm, hx21_1])
        (by simp only [wp_norm, hx24_1])
        (by simp only [wp_norm, hx29_1])
        (by simp only [wp_norm, hvregs_1]))

theorem applyRatchet_from_6d0_159_placed_x [LibsignalPlacement]
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hTrApply : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 58) (withLsCodeRoLoaded lsmpl (trApplySpecX A)))
    (hClearUpk : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 35) (withLsCodeRoLoaded lsmpl (clearUpkSpecX A)))
    (hmemcpy : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsρ lsMemcpySym) (withStack sessionMemcpyRegionSpec extHookStack))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (newPqrState pt : List (BitVec 8))
    (newPqrCap newPqrPtr ptCap ptPtr : BitVec 64)
    (R : SepProp) (s0 s1 : State)
    (hok : (x.modelFn C decFn S uuidTryParse).1 = .ok pt)
    (hst : (x.modelFn C decFn S uuidTryParse).2 =
      (({ tr with pqrState := newPqrState }).applyToSessionState st1).clearUnacknowledgedPreKeyMessage)
    (hpad : trG.ratchet.senderPad.length = 100)
    (hnew_le : newPqrState.length ≤ newPqrCap.toNat)
    (hnew_lt : newPqrCap.toNat < 2 ^ 63)
    (hnew_nz : newPqrPtr ≠ 0)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hpt_lt : ptCap.toNat < 2 ^ 63)
    (hpt_nz : ptPtr ≠ 0)
    (hsp0 : s0.spAligned = true)
    (hpc1 : s1.pc = (blkPl_131).base + 1744#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 1504#64)
    (hsp_al1 : s1.spAligned = true)
    (htr1 : s1.trace = s0.trace)
    (hcl1 : LibsignalCodeRoLoaded lsmpl s1.mem)
    (hx9_1 : s1.readReg64 .x9 = s0.sp - 800#64)
    (hx19_1 : s1.readReg64 .x19 = x.ret)
    (hx20_1 : s1.readReg64 .x20 = s0.sp - 1184#64)
    (hx21_1 : s1.readReg64 .x21 = x.ss)
    (hx24_1 : s1.readReg64 .x24 = BitVec.ofNat 64 newPqrState.length)
    (_hx29_1 : s1.readReg64 .x29 = s0.sp - 96#64)
    (hvregs_1 : calleeSavedVRegs s1 = calleeSavedVRegs s0) :
    SepWPp ((blkPC_131).rebase (blkPl_131).base H) (s0.readReg64 .lr) s1
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trWithoutPqAt A (s0.sp - 1448#64) trG.ratchet tr ∗
       ((s0.sp - 1272#64) ↦₆₄ trG.pq.cap) ∗
       ((s0.sp - 1264#64) ↦₆₄ trG.pq.ptr) ∗
       ((s0.sp - 1256#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
       (if newPqrCap = 0 then emp else (A.live newPqrPtr newPqrCap.toNat 1 ∗ (newPqrPtr ↦ₛ newPqrState)) ∗
         memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ∗
       ((s0.sp - 528#64) ↦₆₄ ptCap) ∗
       ((s0.sp - 520#64) ↦₆₄ ptPtr) ∗
       ((s0.sp - 512#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       (if ptCap = 0 then emp else (A.live ptPtr ptCap.toNat 1 ∗ (ptPtr ↦ₛ pt)) ∗
         memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
       memRegion x.ret 8 ∗
       memRegion (x.ret + 8#64) 8 ∗
       memRegion (x.ret + 16#64) 8 ∗
       memRegion (x.ret + 24#64) 8 ∗
       memRegion (x.ret + 32#64) 16 ∗
       memRegion (s0.sp - 1504#64) 8 ∗
       ((s0.sp - 1496#64) ↦₆₄ newPqrCap) ∗
       memRegion (s0.sp - 1488#64) 24 ∗
       ((s0.sp - 1464#64) ↦₆₄ newPqrPtr) ∗
       memRegion (s0.sp - 1456#64) 8 ∗
       memRegion (s0.sp - 1184#64) 8 ∗
       memRegion (s0.sp - 1176#64) 8 ∗
       memRegion (s0.sp - 1168#64) 8 ∗
       memRegion (s0.sp - 1160#64) 16 ∗
       memRegion (s0.sp - 1144#64) 8 ∗
       memRegion (s0.sp - 1136#64) 8 ∗
       memRegion (s0.sp - 1128#64) 8 ∗
       memRegion (s0.sp - 1120#64) 16 ∗
       memRegion (s0.sp - 1104#64) 264 ∗
       memRegion (s0.sp - 840#64) 120 ∗
       ((s0.sp - 720#64) ↦₆₄ ptCap) ∗
       ((s0.sp - 712#64) ↦₆₄ ptPtr) ∗
       ((s0.sp - 704#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       memRegion (s0.sp - 696#64) 168 ∗
       memRegion (s0.sp - 504#64) 0x198 ∗
       protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       tapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
       logOff tryDecryptPlacedImg ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl uuidTryParse S).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl uuidTryParse S).onPanic x s0 sf ∗ R)) := by
  simp only [wp_norm] at hpc1 hsp1 hx9_1 hx19_1 hx20_1 hx21_1 hx24_1
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1184#64) (by sep_focus) fun w1184 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1176#64) (by sep_focus) fun w1176 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1168#64) (by sep_focus) fun w1168 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1144#64) (by sep_focus) fun w1144 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1136#64) (by sep_focus) fun w1136 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1128#64) (by sep_focus) fun w1128 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 8#64) (by sep_focus) fun wret8 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 16#64) (by sep_focus) fun wret16 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 24#64) (by sep_focus) fun wret24 => ?_
  rw [stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide)]
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl1 (mid := lsρ lsMemcpySym)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hcl2
  refine SepWPp.mono_focus
    (trAt_of_withoutPq A s0.sp trG tr newPqrCap newPqrPtr newPqrState hnew_le hnew_lt hnew_nz)
    (by sep_focus) ?_
  rw [trAt_eq_stack_heap A (s0.sp - 1448#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
      { tr with pqrState := newPqrState } hpad]
  refine SepWPp.elim_exists_focus
    (Φ := fun pad : BitVec 32 =>
      ((s0.sp - 1448#64) ↦ₛ trStackBytes { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
        { tr with pqrState := newPqrState } pad) ∗
      trHeapPart A { trG with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState })
    (by sep_focus) fun pad => ?_
  have hbs_len : (trStackBytes { trG with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState } pad).length = 264 :=
    length_trStackBytes _ _ pad hpad
  generalize hbs_def : trStackBytes { trG with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState } pad = bs at hbs_len ⊢
  rw [show memRegion (s0.sp - 1104#64) 264 = memRegion (s0.sp - 1104#64) bs.length by rw [hbs_len]]
  simp only [← sepConj_assoc]
  refine SepWPp.call_frame_placed (spec := withStack sessionMemcpyRegionSpec extHookStack)
    (x := (s0.sp - 1104#64, s0.sp - 1448#64, bs))
    (T := memRegion (s0.sp - 1104#64) bs.length ∗ ((s0.sp - 1448#64) ↦ₛ bs) ∗
          stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := (blkPl_131).base + bv% (1248))
    hcl2 hmemcpy (by rfl) (by exact hrun1)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1) (by rfl)
    (by dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]; rw [sepConj_assoc, sepConj_assoc]; congr 3; simp only [wp_norm, hsp1])
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm, hbs_len]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ hm_pan => by dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl2
  intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hcl2
  simp only [wp_norm, hsp1] at hsp2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _hx29_2, hvregs_2⟩
  simp only [wp_norm, hx19_1, hx20_1, hx21_1, hx24_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx24_2 hvregs_2
  dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
  simp only [wp_norm, hsp1, sepConj_assoc]
  apply SepWPp.elim_pure; rintro ⟨_, htr2⟩
  have htr20 : s2.trace = s0.trace := htr2.trans htr1
  rw [← hbs_def]
  refine SepWPp.mono_focus
    (trAt_of_stack_heap A (s0.sp - 1104#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
      { tr with pqrState := newPqrState } pad hpad)
    (by sep_focus) ?_
  rw [hbs_def]
  refine SepWPp.mono_focus (extHookStack_to_trApplyStackX s0.sp) (by sep_focus) ?_
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl2 (mid := lsmpl.base 58)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun2)
  intro hcl3
  refine SepWPp.call_cro_frame_placed (spec := trApplySpecX A)
    (x := ⟨s0.sp - 1104#64, { trG with pq := ⟨newPqrCap, newPqrPtr⟩ },
           { tr with pqrState := newPqrState }, x.ss, x.G.afterTrFrom, st1⟩)
    (T := trAt A (s0.sp - 1104#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
            { tr with pqrState := newPqrState } ∗
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          stackAt (s0.sp - 1504#64) trApplyStackX ∗ A.pool)
    (ret_pc := (blkPl_131).base + bv% (1260))
    hcl3 hTrApply (by rfl) (by exact hrun2)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
    (by dsimp only [trApplySpecX]; simp only [wp_norm, hsp2]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [trApplySpecX] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ hm_pan => by
      have h0m : s0.trace <+: (s2.writeReg64 .x0 (s0.sp - 1104#64)
        |>.writeReg64 .x1 x.ss |>.writeReg64 .x30 ((blkPl_131).base + bv% (1260))
        |>.setPC (lsmpl.base 58)).trace := by
        rw [show (s2.writeReg64 .x0 (s0.sp - 1104#64)
          |>.writeReg64 .x1 x.ss |>.writeReg64 .x30 ((blkPl_131).base + bv% (1260))
          |>.setPC (lsmpl.base 58)).trace = s2.trace from rfl, htr20]
      exact tryDecryptFn_onPanic_of_callee_placed C decFn A ctl S x s0 _ sf _ R h0m hm_pan) ?_
  clear hcl3
  intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hcl3
  simp only [wp_norm, hsp2] at hsp3
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, _hx29_3, hvregs_3⟩
  simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx24_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx24_3 hvregs_3
  dsimp only [trApplySpecX]
  simp only [wp_norm, hsp2, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr3
  have htr30 : s3.trace = s0.trace := htr3.trans htr20
  apply SepWPp.elim_exists; intro G1
  simp only [sepConj_assoc]
  apply SepWPp.elim_pure; intro hG1
  refine SepWPp.mono_focus (trApplyStackX_to_clearUpkStackX s0.sp) (by sep_focus) ?_
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl3 (mid := lsmpl.base 35)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun3)
  intro hcl4
  refine SepWPp.call_cro_frame_placed (spec := clearUpkSpecX A)
    (x := ⟨x.ss, G1, ({ tr with pqrState := newPqrState }).applyToSessionState st1⟩)
    (T := sessionStateAt A x.ss G1 (({ tr with pqrState := newPqrState }).applyToSessionState st1) ∗
          A.pool ∗ stackAt (s0.sp - 1504#64) clearUpkStackX)
    (ret_pc := (blkPl_131).base + bv% (1268))
    hcl4 hClearUpk (by rfl) (by exact hrun3)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
    (by dsimp only [clearUpkSpecX]; simp only [wp_norm, hsp3]; rfl)
    (by simp only [wp_norm])
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [clearUpkSpecX] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ hm_pan => by dsimp only [clearUpkSpecX] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl4
  intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hcl4
  simp only [wp_norm, hsp3] at hsp4
  rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, _hx29_4, hvregs_4⟩
  simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx24_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx24_4 hvregs_4
  dsimp only [clearUpkSpecX]
  simp only [wp_norm, hsp3, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr4
  have htr40 : s4.trace = s0.trace := htr4.trans htr30
  refine SepWPp.mono_focus (clearUpkStackX_to_subStack s0.sp) (by sep_focus) ?_
  refine SepWPp.mono_focus
    (applyRatchet_local_frame_entails_memRegion s0.sp newPqrCap newPqrPtr ptCap ptPtr
      (BitVec.ofNat 64 pt.length) ptCap ptPtr (BitVec.ofNat 64 pt.length)
      ptCap ptPtr (BitVec.ofNat 64 pt.length) ptCap ptPtr (BitVec.ofNat 64 pt.length)
      bs hbs_len) (by sep_focus) ?_
  refine SepWPp.mono_focus (Entails.refl (tryDecryptSavedRegs s0.sp s0)) (by sep_focus) ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret) (by sep_focus) fun wret => ?_
  unfold tryDecryptSavedRegs
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun4)
  refine ⟨fun hmf => ?_, by simp only [wp_norm], ?_⟩
  · dsimp only [tryDecryptFnSpecPlaced, withLsCodeRoLoaded, tryDecryptFnRawSpecPlaced, tryDecryptFnSpec, Spec.inImage]
    rw [hok]
    rw [← hst] at hmf
    have hdec := decRel_of_trApplyRel hG1
    have hsaved := tryDecryptSavedRegs_entails_memRegion s0.sp s0
    unfold tryDecryptSavedRegs at hsaved
    have hmf1 := Satisfies.mono_focus hsaved (by sep_focus) hmf
    have hmf3 := Satisfies.mono_focus (stackAt_rootStack_of_parts s0.sp) (by sep_focus) hmf1
    rw [show (bv% (2 ^ 64 - 2) : BitVec 64) = okTagVec from rfl] at hmf3
    have hmf4 := Satisfies.mono_focus
      (decResultAt_ok_of_parts A x.ret pt ptCap ptPtr hpt_le hpt_lt hpt_nz) (by sep_focus) hmf3
    have hss : sessionStateAt A x.ss { G1 with pending := none, kyber := none } (x.modelFn C decFn S uuidTryParse).2 ⊢
        ∃∗ G' : SessionGhost, ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
          sessionStateAt A x.ss G' (x.modelFn C decFn S uuidTryParse).2 := by
      refine Entails.trans ?_
        (Entails.sepExists_intro
          (P := fun G' : SessionGhost =>
            ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
            sessionStateAt A x.ss G' (x.modelFn C decFn S uuidTryParse).2)
          { G1 with pending := none, kyber := none })
      exact Entails.pure_right hdec (Entails.refl _)
    have hmf5 := Satisfies.mono_focus hss (by sep_focus) hmf4
    clear hmf hmf1 hmf3 hmf4
    have hno_pan : (Except.ok pt : Except SignalProtocolError (List (BitVec 8))) ≠ .error .panic := nofun
    simp only [wp_norm, sepConj_assoc, satisfies_pure_sepConj] at hmf5 ⊢
    refine ⟨⟨hno_pan, htr40⟩, ?_⟩
    generalize (∃∗ G', ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
      sessionStateAt A x.ss G' (x.modelFn C decFn S uuidTryParse).2) = SS at hmf5 ⊢
    change _ ⊨ SS ∗ vecResultAt A x.ret (.ok pt) ∗ _
    sep_close
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, hvregs_4]

theorem applyRatchet_159_placed_ok_x [LibsignalPlacement]
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hTrApply : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 58) (withLsCodeRoLoaded lsmpl (trApplySpecX A)))
    (hClearUpk : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 35) (withLsCodeRoLoaded lsmpl (clearUpkSpecX A)))
    (hmemcpy : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsρ lsMemcpySym) (withStack sessionMemcpyRegionSpec extHookStack))
    (hdealloc : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsρ lsRustDeallocSym) (rustDeallocExternSpecWithStack A extHookStack)) :
    S9SeamXPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base C decFn A ctl uuidTryParse S := by
  intro x trG tr st1 newPqrState pt R s0 s hok hst h9
  rcases h9 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx23, hx24, newPqrCap, newPqrPtr, hnew_le, hnew_lt, hnew_nz, hmem⟩
  have h6d0 := @applyRatchet_from_6d0_159_placed_x _ C decFn A ctl S H hTrApply hClearUpk hmemcpy x trG tr st1
    newPqrState pt newPqrCap newPqrPtr
  clear hTrApply hClearUpk
  have hpad : trG.ratchet.senderPad.length = 100 := by
    have htr_front := hmem
    rw [← sepConj_assoc, sepConj_comm (sessionStateAt A x.ss x.G.afterTrFrom st1), sepConj_assoc] at htr_front
    exact trAt_senderPad_len htr_front
  unfold tryDecryptCommonHeap at hmem
  rw [trAt_eq_withoutPq A s0.sp trG tr,
       applyRatchet_scr_split s0.sp,
       applyRatchet_ret_split x.ret,
       show s0.sp - 1504#64 + 0x3d0#64 = s0.sp - 528#64 by bv_omega,
       show s0.sp - 1504#64 + 0x8#64 = s0.sp - 1496#64 by bv_omega,
       show s0.sp - 1504#64 + 0x10#64 = s0.sp - 1488#64 by bv_omega,
       show s0.sp - 1504#64 + 0x28#64 = s0.sp - 1464#64 by bv_omega,
       show s0.sp - 1504#64 + 0x30#64 = s0.sp - 1456#64 by bv_omega,
       show s0.sp - 1504#64 + 0x3e8#64 = s0.sp - 504#64 by bv_omega] at hmem
  change s.pc = (blkPl_131).base + 1700#64 at hpc
  simp only [wp_norm] at hx20 hx23 hx29
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_reaches_outcome hmem ?_
  refine SepWPp.elim_pure_focus
    (φ := tr.pqrState.length ≤ trG.pq.cap.toNat ∧ trG.pq.cap.toNat < 2 ^ 63 ∧ trG.pq.ptr ≠ 0)
    (by sep_focus) fun ⟨hpq_le, hpq_lt, hpq_nz⟩ => ?_
  refine SepWPp.elim_vecU8_focus (A := A) (a := s0.sp - 528#64) (bs := pt)
    (by sep_focus) fun ptCap ptPtr hpt_le hpt_lt hpt_nz => ?_
  rw [show s0.sp - 528#64 + 8#64 = s0.sp - 520#64 by bv_omega,
      show s0.sp - 528#64 + 16#64 = s0.sp - 512#64 by bv_omega]
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 720#64) (by sep_focus) fun w720 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 712#64) (by sep_focus) fun w712 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 704#64) (by sep_focus) fun w704 => ?_
  by_cases hpq_cap : trG.pq.cap = 0#64
  · refine SepWPp.mono_focus (newPqr_zero_prep A trG.pq.cap trG.pq.ptr tr.pqrState hpq_cap) (by sep_focus) ?_
    rw [emp_sepConj]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl (mid := (blkPl_131).base + bv% (1744))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    intro hcl1
    refine SepWPp.congr_pre (by sep_focus)
      (h6d0 ptCap ptPtr R s0 _
        hok hst hpad hnew_le hnew_lt hnew_nz hpt_le hpt_lt hpt_nz
        hsp0 (by rfl) (by exact hrun) (by simp only [wp_norm, hsp])
        (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al)
        htr hcl1
        (by simp only [wp_norm])
        (by simp only [wp_norm, hx19])
        (by simp only [wp_norm, hx20])
        (by simp only [wp_norm, hx21])
        (by simp only [wp_norm, hx24])
        (by simp only [wp_norm, hx29])
        (by simp only [wp_norm, hvregs]))
  · refine SepWPp.mono_focus (newPqr_dealloc_prep' A trG.pq.cap trG.pq.ptr tr.pqrState hpq_cap hpq_le hpq_lt) (by sep_focus) ?_
    rw [stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide)]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl (mid := (blkPl_131).base + bv% (1728))
    wp_steps
    apply SepWP.setPC_setMem_ite_false (by simp only [beq_iff_eq, hpq_cap, not_false_eq_true])
    apply SepWP.done (by rfl) (by exact hrun)
    intro hcl0
    apply SepWPp.of_sepWP_placed hcl0 (mid := lsρ lsRustDeallocSym)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    intro hcl1
    refine SepWPp.call_frame_placed (spec := rustDeallocExternSpecWithStack A extHookStack)
      (x := (trG.pq.ptr, trG.pq.cap.toNat, 1))
      (T := A.pool ∗ A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat ∗
            stackAt (s0.sp - 1504#64) extHookStack)
      (ret_pc := (blkPl_131).base + bv% (1740))
      hcl1 hdealloc (by rfl) (by exact hrun)
      (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
      (by dsimp only [rustDeallocExternSpecWithStack]; simp only [wp_norm, hsp]; rfl)
      (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                  layoutOk_of_cap_ne_zero hpq_cap hpq_lt⟩)
      (by sep_focus)
      (fun _ _ _ _ h => by dsimp only [rustDeallocExternSpecWithStack] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
      (fun sf _ hm_pan => by dsimp only [rustDeallocExternSpecWithStack] at hm_pan; exact noPanic_callee hm_pan) ?_
    clear hcl0 hcl1
    intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hcl1
    simp only [wp_norm, hsp] at hsp1
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [wp_norm, hx19, hx20, hx21, hx24, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx24_1 hx29_1 hvregs_1
    dsimp only [rustDeallocExternSpecWithStack, rustDeallocSpecWithStack]
    simp only [wp_norm, hsp, sepConj_assoc]
    apply SepWPp.elim_pure; intro htr1
    have htr10 : s1.trace = s0.trace := htr1.trans htr
    refine SepWPp.mono_focus (extHookStack_to_subStack s0.sp) (by sep_focus) ?_
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl1 (mid := (blkPl_131).base + bv% (1744))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun1)
    intro hcl2
    rw [← logOff_tryDecryptPlacedImg]
    refine SepWPp.congr_pre (by sep_focus)
      (h6d0 ptCap ptPtr R s0 _
        hok hst hpad hnew_le hnew_lt hnew_nz hpt_le hpt_lt hpt_nz
        hsp0 (by rfl) (by exact hrun1) (by simp only [wp_norm, hsp1])
        (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1)
        htr10 hcl2
        (by simp only [wp_norm])
        (by simp only [wp_norm, hx19_1])
        (by simp only [wp_norm, hx20_1])
        (by simp only [wp_norm, hx21_1])
        (by simp only [wp_norm, hx24_1])
        (by simp only [wp_norm, hx29_1])
        (by simp only [wp_norm, hvregs_1]))

theorem applyRatchet_from_6d0_549_placed [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hTrApply : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 58) (withLsCodeRoLoaded lsmpl (trApplySpec A)))
    (hClearUpk : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 35) (withLsCodeRoLoaded lsmpl (clearUpkSpec A)))
    (hmemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (newPqrState pt : List (BitVec 8))
    (newPqrCap newPqrPtr ptCap ptPtr : BitVec 64)
    (R : SepProp) (s0 s1 : State)
    (hok : (x.model C S uuidTryParse).1 = .ok pt)
    (hst : (x.model C S uuidTryParse).2 =
      (({ tr with pqrState := newPqrState }).applyToSessionState st1).clearUnacknowledgedPreKeyMessage)
    (hpad : trG.ratchet.senderPad.length = 100)
    (hnew_le : newPqrState.length ≤ newPqrCap.toNat)
    (hnew_lt : newPqrCap.toNat < 2 ^ 63)
    (hnew_nz : newPqrPtr ≠ 0)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hpt_lt : ptCap.toNat < 2 ^ 63)
    (hpt_nz : ptPtr ≠ 0)
    (hsp0 : s0.spAligned = true)
    (hpc1 : s1.pc = (blkPl_434).base + 1744#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 1504#64)
    (hsp_al1 : s1.spAligned = true)
    (htr1 : s1.trace = s0.trace)
    (hcl1 : LibsignalCodeRoLoaded lsmpl s1.mem)
    (hx9_1 : s1.readReg64 .x9 = s0.sp - 800#64)
    (hx19_1 : s1.readReg64 .x19 = x.ret)
    (hx20_1 : s1.readReg64 .x20 = s0.sp - 1184#64)
    (hx21_1 : s1.readReg64 .x21 = x.ss)
    (hx24_1 : s1.readReg64 .x24 = BitVec.ofNat 64 newPqrState.length)
    (_hx29_1 : s1.readReg64 .x29 = s0.sp - 96#64)
    (hvregs_1 : calleeSavedVRegs s1 = calleeSavedVRegs s0) :
    SepWPp ((blkPC_434).rebase (blkPl_434).base H) (s0.readReg64 .lr) s1
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trWithoutPqAt A (s0.sp - 1448#64) trG.ratchet tr ∗
       ((s0.sp - 1272#64) ↦₆₄ trG.pq.cap) ∗
       ((s0.sp - 1264#64) ↦₆₄ trG.pq.ptr) ∗
       ((s0.sp - 1256#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
       (if newPqrCap = 0 then emp else (A.live newPqrPtr newPqrCap.toNat 1 ∗ (newPqrPtr ↦ₛ newPqrState)) ∗
         memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ∗
       ((s0.sp - 528#64) ↦₆₄ ptCap) ∗
       ((s0.sp - 520#64) ↦₆₄ ptPtr) ∗
       ((s0.sp - 512#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       (if ptCap = 0 then emp else (A.live ptPtr ptCap.toNat 1 ∗ (ptPtr ↦ₛ pt)) ∗
         memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
       memRegion x.ret 8 ∗
       memRegion (x.ret + 8#64) 8 ∗
       memRegion (x.ret + 16#64) 8 ∗
       memRegion (x.ret + 24#64) 8 ∗
       memRegion (x.ret + 32#64) 16 ∗
       memRegion (s0.sp - 1504#64) 8 ∗
       ((s0.sp - 1496#64) ↦₆₄ newPqrCap) ∗
       memRegion (s0.sp - 1488#64) 24 ∗
       ((s0.sp - 1464#64) ↦₆₄ newPqrPtr) ∗
       memRegion (s0.sp - 1456#64) 8 ∗
       memRegion (s0.sp - 1184#64) 8 ∗
       memRegion (s0.sp - 1176#64) 8 ∗
       memRegion (s0.sp - 1168#64) 8 ∗
       memRegion (s0.sp - 1160#64) 16 ∗
       memRegion (s0.sp - 1144#64) 8 ∗
       memRegion (s0.sp - 1136#64) 8 ∗
       memRegion (s0.sp - 1128#64) 8 ∗
       memRegion (s0.sp - 1120#64) 16 ∗
       memRegion (s0.sp - 1104#64) 264 ∗
       memRegion (s0.sp - 840#64) 120 ∗
       ((s0.sp - 720#64) ↦₆₄ ptCap) ∗
       ((s0.sp - 712#64) ↦₆₄ ptPtr) ∗
       ((s0.sp - 704#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       memRegion (s0.sp - 696#64) 168 ∗
       memRegion (s0.sp - 504#64) 0x198 ∗
       protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       tapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
       logOff tryDecryptPlacedImg ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 sf ∗ R)) := by
  simp only [wp_norm] at hpc1 hsp1 hx9_1 hx19_1 hx20_1 hx21_1 hx24_1
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1184#64) (by sep_focus) fun w1184 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1176#64) (by sep_focus) fun w1176 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1168#64) (by sep_focus) fun w1168 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1144#64) (by sep_focus) fun w1144 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1136#64) (by sep_focus) fun w1136 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1128#64) (by sep_focus) fun w1128 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 8#64) (by sep_focus) fun wret8 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 16#64) (by sep_focus) fun wret16 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 24#64) (by sep_focus) fun wret24 => ?_
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl1 (mid := lsρ lsMemcpySym)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hcl2
  refine SepWPp.mono_focus
    (trAt_of_withoutPq A s0.sp trG tr newPqrCap newPqrPtr newPqrState hnew_le hnew_lt hnew_nz)
    (by sep_focus) ?_
  rw [trAt_eq_stack_heap A (s0.sp - 1448#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
      { tr with pqrState := newPqrState } hpad]
  refine SepWPp.elim_exists_focus
    (Φ := fun pad : BitVec 32 =>
      ((s0.sp - 1448#64) ↦ₛ trStackBytes { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
        { tr with pqrState := newPqrState } pad) ∗
      trHeapPart A { trG with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState })
    (by sep_focus) fun pad => ?_
  have hbs_len : (trStackBytes { trG with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState } pad).length = 264 :=
    length_trStackBytes _ _ pad hpad
  generalize hbs_def : trStackBytes { trG with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState } pad = bs at hbs_len ⊢
  rw [show memRegion (s0.sp - 1104#64) 264 = memRegion (s0.sp - 1104#64) bs.length by rw [hbs_len]]
  simp only [← sepConj_assoc]
  refine SepWPp.call_frame_placed (spec := sessionMemcpyRegionSpec)
    (x := (s0.sp - 1104#64, s0.sp - 1448#64, bs))
    (T := memRegion (s0.sp - 1104#64) bs.length ∗ ((s0.sp - 1448#64) ↦ₛ bs))
    (ret_pc := (blkPl_434).base + bv% (1248))
    hcl2 hmemcpy (by rfl) (by exact hrun1)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1) (by rfl)
    (by rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm, hbs_len]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ hm_pan => by dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl2
  intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hcl2
  simp only [wp_norm, hsp1] at hsp2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _hx29_2, hvregs_2⟩
  simp only [wp_norm, hx19_1, hx20_1, hx21_1, hx24_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx24_2 hvregs_2
  dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
  simp only [wp_norm, sepConj_assoc]
  apply SepWPp.elim_pure; rintro ⟨_, htr2⟩
  have htr20 : s2.trace = s0.trace := htr2.trans htr1
  rw [← hbs_def]
  refine SepWPp.mono_focus
    (trAt_of_stack_heap A (s0.sp - 1104#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
      { tr with pqrState := newPqrState } pad hpad)
    (by sep_focus) ?_
  rw [hbs_def]
  rw [stackAt_sub_split (s0.sp - 1504#64) trApplyStack (by decide)]
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl2 (mid := lsmpl.base 58)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun2)
  intro hcl3
  refine SepWPp.call_cro_frame_placed (spec := trApplySpec A)
    (x := ⟨s0.sp - 1104#64, { trG with pq := ⟨newPqrCap, newPqrPtr⟩ },
           { tr with pqrState := newPqrState }, x.ss, x.G.afterTrFrom, st1⟩)
    (T := trAt A (s0.sp - 1104#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
            { tr with pqrState := newPqrState } ∗
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          stackAt (s0.sp - 1504#64) trApplyStack ∗ A.pool)
    (ret_pc := (blkPl_434).base + bv% (1260))
    hcl3 hTrApply (by rfl) (by exact hrun2)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
    (by dsimp only [trApplySpec]; simp only [wp_norm, hsp2]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [trApplySpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ hm_pan => by
      have h0m : s0.trace <+: (s2.writeReg64 .x0 (s0.sp - 1104#64)
        |>.writeReg64 .x1 x.ss |>.writeReg64 .x30 ((blkPl_434).base + bv% (1260))
        |>.setPC (lsmpl.base 58)).trace := by
        rw [show (s2.writeReg64 .x0 (s0.sp - 1104#64)
          |>.writeReg64 .x1 x.ss |>.writeReg64 .x30 ((blkPl_434).base + bv% (1260))
          |>.setPC (lsmpl.base 58)).trace = s2.trace from rfl, htr20]
      exact tryDecrypt_onPanic_of_callee_placed C A ctl S x s0 _ sf _ R h0m hm_pan) ?_
  clear hcl3
  intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hcl3
  simp only [wp_norm, hsp2] at hsp3
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, _hx29_3, hvregs_3⟩
  simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx24_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx24_3 hvregs_3
  dsimp only [trApplySpec]
  simp only [wp_norm, hsp2, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr3
  have htr30 : s3.trace = s0.trace := htr3.trans htr20
  apply SepWPp.elim_exists; intro G1
  simp only [sepConj_assoc]
  apply SepWPp.elim_pure; intro hG1
  refine SepWPp.mono_focus (trApplyStack_to_clearUpkStack s0.sp) (by sep_focus) ?_
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl3 (mid := lsmpl.base 35)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun3)
  intro hcl4
  refine SepWPp.call_cro_frame_placed (spec := clearUpkSpec A)
    (x := ⟨x.ss, G1, ({ tr with pqrState := newPqrState }).applyToSessionState st1⟩)
    (T := sessionStateAt A x.ss G1 (({ tr with pqrState := newPqrState }).applyToSessionState st1) ∗
          A.pool ∗ stackAt (s0.sp - 1504#64) clearUpkStack)
    (ret_pc := (blkPl_434).base + bv% (1268))
    hcl4 hClearUpk (by rfl) (by exact hrun3)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
    (by dsimp only [clearUpkSpec]; simp only [wp_norm, hsp3]; rfl)
    (by simp only [wp_norm])
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [clearUpkSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ hm_pan => by dsimp only [clearUpkSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl4
  intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hcl4
  simp only [wp_norm, hsp3] at hsp4
  rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, _hx29_4, hvregs_4⟩
  simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx24_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx24_4 hvregs_4
  dsimp only [clearUpkSpec]
  simp only [wp_norm, hsp3, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr4
  have htr40 : s4.trace = s0.trace := htr4.trans htr30
  refine SepWPp.mono_focus (clearUpkStack_to_subStack s0.sp) (by sep_focus) ?_
  refine SepWPp.mono_focus
    (applyRatchet_local_frame_entails_memRegion s0.sp newPqrCap newPqrPtr ptCap ptPtr
      (BitVec.ofNat 64 pt.length) ptCap ptPtr (BitVec.ofNat 64 pt.length)
      ptCap ptPtr (BitVec.ofNat 64 pt.length) ptCap ptPtr (BitVec.ofNat 64 pt.length)
      bs hbs_len) (by sep_focus) ?_
  refine SepWPp.mono_focus (Entails.refl (tryDecryptSavedRegs s0.sp s0)) (by sep_focus) ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret) (by sep_focus) fun wret => ?_
  unfold tryDecryptSavedRegs
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun4)
  refine ⟨fun hmf => ?_, by simp only [wp_norm], ?_⟩
  · dsimp only [tryDecryptSpecPlaced, withLsCodeRoLoaded, tryDecryptRawSpecPlaced, tryDecryptSpec, Spec.inImage]
    rw [hok]
    rw [← hst] at hmf
    have hdec := decRel_of_trApplyRel hG1
    have hsaved := tryDecryptSavedRegs_entails_memRegion s0.sp s0
    unfold tryDecryptSavedRegs at hsaved
    have hmf1 := Satisfies.mono_focus hsaved (by sep_focus) hmf
    have hmf3 := Satisfies.mono_focus (stackAt_rootStack_of_parts s0.sp) (by sep_focus) hmf1
    rw [show (bv% (2 ^ 64 - 2) : BitVec 64) = okTagVec from rfl] at hmf3
    have hmf4 := Satisfies.mono_focus
      (decResultAt_ok_of_parts A x.ret pt ptCap ptPtr hpt_le hpt_lt hpt_nz) (by sep_focus) hmf3
    have hss : sessionStateAt A x.ss { G1 with pending := none, kyber := none } (x.model C S uuidTryParse).2 ⊢
        ∃∗ G' : SessionGhost, ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
          sessionStateAt A x.ss G' (x.model C S uuidTryParse).2 := by
      refine Entails.trans ?_
        (Entails.sepExists_intro
          (P := fun G' : SessionGhost =>
            ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
            sessionStateAt A x.ss G' (x.model C S uuidTryParse).2)
          { G1 with pending := none, kyber := none })
      exact Entails.pure_right hdec (Entails.refl _)
    have hmf5 := Satisfies.mono_focus hss (by sep_focus) hmf4
    clear hmf hmf1 hmf3 hmf4
    have hno_pan : (Except.ok pt : Except SignalProtocolError (List (BitVec 8))) ≠ .error .panic := nofun
    simp only [wp_norm, sepConj_assoc, satisfies_pure_sepConj] at hmf5 ⊢
    refine ⟨⟨hno_pan, htr40⟩, ?_⟩
    generalize (∃∗ G', ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
      sessionStateAt A x.ss G' (x.model C S uuidTryParse).2) = SS at hmf5 ⊢
    sep_close
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, hvregs_4]

theorem applyRatchet_549_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hTrApply : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 58) (withLsCodeRoLoaded lsmpl (trApplySpec A)))
    (hClearUpk : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 35) (withLsCodeRoLoaded lsmpl (clearUpkSpec A)))
    (hmemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (hdealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsRustDeallocSym) (rustDeallocSpec A)) :
    S9SeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C A ctl uuidTryParse S := by
  intro x trG tr st1 newPqrState pt R s0 s hok hst h9
  rcases h9 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx23, hx24, newPqrCap, newPqrPtr, hnew_le, hnew_lt, hnew_nz, hmem⟩
  have h6d0 := @applyRatchet_from_6d0_549_placed _ C A ctl S H hTrApply hClearUpk hmemcpy x trG tr st1
    newPqrState pt newPqrCap newPqrPtr
  clear hTrApply hClearUpk
  have hpad : trG.ratchet.senderPad.length = 100 := by
    have htr_front := hmem
    rw [← sepConj_assoc, sepConj_comm (sessionStateAt A x.ss x.G.afterTrFrom st1), sepConj_assoc] at htr_front
    exact trAt_senderPad_len htr_front
  unfold tryDecryptCommonHeap at hmem
  rw [trAt_eq_withoutPq A s0.sp trG tr,
       applyRatchet_scr_split s0.sp,
       applyRatchet_ret_split x.ret,
       show s0.sp - 1504#64 + 0x3d0#64 = s0.sp - 528#64 by bv_omega,
       show s0.sp - 1504#64 + 0x8#64 = s0.sp - 1496#64 by bv_omega,
       show s0.sp - 1504#64 + 0x10#64 = s0.sp - 1488#64 by bv_omega,
       show s0.sp - 1504#64 + 0x28#64 = s0.sp - 1464#64 by bv_omega,
       show s0.sp - 1504#64 + 0x30#64 = s0.sp - 1456#64 by bv_omega,
       show s0.sp - 1504#64 + 0x3e8#64 = s0.sp - 504#64 by bv_omega] at hmem
  change s.pc = (blkPl_434).base + 1700#64 at hpc
  simp only [wp_norm] at hx20 hx23 hx29
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_reaches_outcome hmem ?_
  refine SepWPp.elim_pure_focus
    (φ := tr.pqrState.length ≤ trG.pq.cap.toNat ∧ trG.pq.cap.toNat < 2 ^ 63 ∧ trG.pq.ptr ≠ 0)
    (by sep_focus) fun ⟨hpq_le, hpq_lt, hpq_nz⟩ => ?_
  refine SepWPp.elim_vecU8_focus (A := A) (a := s0.sp - 528#64) (bs := pt)
    (by sep_focus) fun ptCap ptPtr hpt_le hpt_lt hpt_nz => ?_
  rw [show s0.sp - 528#64 + 8#64 = s0.sp - 520#64 by bv_omega,
      show s0.sp - 528#64 + 16#64 = s0.sp - 512#64 by bv_omega]
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 720#64) (by sep_focus) fun w720 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 712#64) (by sep_focus) fun w712 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 704#64) (by sep_focus) fun w704 => ?_
  by_cases hpq_cap : trG.pq.cap = 0#64
  · refine SepWPp.mono_focus (newPqr_zero_prep A trG.pq.cap trG.pq.ptr tr.pqrState hpq_cap) (by sep_focus) ?_
    rw [emp_sepConj]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl (mid := (blkPl_434).base + bv% (1744))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    intro hcl1
    refine SepWPp.congr_pre (by sep_focus)
      (h6d0 ptCap ptPtr R s0 _
        hok hst hpad hnew_le hnew_lt hnew_nz hpt_le hpt_lt hpt_nz
        hsp0 (by rfl) (by exact hrun) (by simp only [wp_norm, hsp])
        (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al)
        htr hcl1
        (by simp only [wp_norm])
        (by simp only [wp_norm, hx19])
        (by simp only [wp_norm, hx20])
        (by simp only [wp_norm, hx21])
        (by simp only [wp_norm, hx24])
        (by simp only [wp_norm, hx29])
        (by simp only [wp_norm, hvregs]))
  · refine SepWPp.mono_focus (newPqr_dealloc_prep' A trG.pq.cap trG.pq.ptr tr.pqrState hpq_cap hpq_le hpq_lt) (by sep_focus) ?_
    rw [stackAt_sub_split (s0.sp - 1504#64) allocHookStack (by decide)]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl (mid := (blkPl_434).base + bv% (1728))
    wp_steps
    apply SepWP.setPC_setMem_ite_false (by simp only [beq_iff_eq, hpq_cap, not_false_eq_true])
    apply SepWP.done (by rfl) (by exact hrun)
    intro hcl0
    apply SepWPp.of_sepWP_placed hcl0 (mid := lsρ lsRustDeallocSym)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    intro hcl1
    refine SepWPp.call_frame_placed (spec := rustDeallocSpec A)
      (x := (trG.pq.ptr, trG.pq.cap.toNat, 1))
      (T := A.pool ∗ A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat ∗
            stackAt (s0.sp - 1504#64) allocHookStack)
      (ret_pc := (blkPl_434).base + bv% (1740))
      hcl1 hdealloc (by rfl) (by exact hrun)
      (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
      (by dsimp only [rustDeallocSpec]; simp only [wp_norm, hsp]; rfl)
      (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm]⟩)
      (by sep_focus)
      (fun _ _ _ _ h => by dsimp only [rustDeallocSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
      (fun sf _ hm_pan => by dsimp only [rustDeallocSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
    clear hcl0 hcl1
    intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hcl1
    simp only [wp_norm, hsp] at hsp1
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [wp_norm, hx19, hx20, hx21, hx24, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx24_1 hx29_1 hvregs_1
    dsimp only [rustDeallocSpec]
    simp only [wp_norm, hsp, sepConj_assoc]
    apply SepWPp.elim_pure; intro htr1
    have htr10 : s1.trace = s0.trace := htr1.trans htr
    refine SepWPp.mono_focus (allocHookStack_to_subStack s0.sp) (by sep_focus) ?_
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl1 (mid := (blkPl_434).base + bv% (1744))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun1)
    intro hcl2
    rw [← logOff_tryDecryptPlacedImg]
    refine SepWPp.congr_pre (by sep_focus)
      (h6d0 ptCap ptPtr R s0 _
        hok hst hpad hnew_le hnew_lt hnew_nz hpt_le hpt_lt hpt_nz
        hsp0 (by rfl) (by exact hrun1) (by simp only [wp_norm, hsp1])
        (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1)
        htr10 hcl2
        (by simp only [wp_norm])
        (by simp only [wp_norm, hx19_1])
        (by simp only [wp_norm, hx20_1])
        (by simp only [wp_norm, hx21_1])
        (by simp only [wp_norm, hx24_1])
        (by simp only [wp_norm, hx29_1])
        (by simp only [wp_norm, hvregs_1]))

theorem applyRatchet_from_6d0_549_placed_x [LibsignalPlacement]
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hTrApply : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 58) (withLsCodeRoLoaded lsmpl (trApplySpecX A)))
    (hClearUpk : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 35) (withLsCodeRoLoaded lsmpl (clearUpkSpecX A)))
    (hmemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsMemcpySym) (withStack sessionMemcpyRegionSpec extHookStack))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (newPqrState pt : List (BitVec 8))
    (newPqrCap newPqrPtr ptCap ptPtr : BitVec 64)
    (R : SepProp) (s0 s1 : State)
    (hok : (x.modelFn C decFn S uuidTryParse).1 = .ok pt)
    (hst : (x.modelFn C decFn S uuidTryParse).2 =
      (({ tr with pqrState := newPqrState }).applyToSessionState st1).clearUnacknowledgedPreKeyMessage)
    (hpad : trG.ratchet.senderPad.length = 100)
    (hnew_le : newPqrState.length ≤ newPqrCap.toNat)
    (hnew_lt : newPqrCap.toNat < 2 ^ 63)
    (hnew_nz : newPqrPtr ≠ 0)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hpt_lt : ptCap.toNat < 2 ^ 63)
    (hpt_nz : ptPtr ≠ 0)
    (hsp0 : s0.spAligned = true)
    (hpc1 : s1.pc = (blkPl_434).base + 1744#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 1504#64)
    (hsp_al1 : s1.spAligned = true)
    (htr1 : s1.trace = s0.trace)
    (hcl1 : LibsignalCodeRoLoaded lsmpl s1.mem)
    (hx9_1 : s1.readReg64 .x9 = s0.sp - 800#64)
    (hx19_1 : s1.readReg64 .x19 = x.ret)
    (hx20_1 : s1.readReg64 .x20 = s0.sp - 1184#64)
    (hx21_1 : s1.readReg64 .x21 = x.ss)
    (hx24_1 : s1.readReg64 .x24 = BitVec.ofNat 64 newPqrState.length)
    (_hx29_1 : s1.readReg64 .x29 = s0.sp - 96#64)
    (hvregs_1 : calleeSavedVRegs s1 = calleeSavedVRegs s0) :
    SepWPp ((blkPC_434).rebase (blkPl_434).base H) (s0.readReg64 .lr) s1
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trWithoutPqAt A (s0.sp - 1448#64) trG.ratchet tr ∗
       ((s0.sp - 1272#64) ↦₆₄ trG.pq.cap) ∗
       ((s0.sp - 1264#64) ↦₆₄ trG.pq.ptr) ∗
       ((s0.sp - 1256#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
       (if newPqrCap = 0 then emp else (A.live newPqrPtr newPqrCap.toNat 1 ∗ (newPqrPtr ↦ₛ newPqrState)) ∗
         memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ∗
       ((s0.sp - 528#64) ↦₆₄ ptCap) ∗
       ((s0.sp - 520#64) ↦₆₄ ptPtr) ∗
       ((s0.sp - 512#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       (if ptCap = 0 then emp else (A.live ptPtr ptCap.toNat 1 ∗ (ptPtr ↦ₛ pt)) ∗
         memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
       memRegion x.ret 8 ∗
       memRegion (x.ret + 8#64) 8 ∗
       memRegion (x.ret + 16#64) 8 ∗
       memRegion (x.ret + 24#64) 8 ∗
       memRegion (x.ret + 32#64) 16 ∗
       memRegion (s0.sp - 1504#64) 8 ∗
       ((s0.sp - 1496#64) ↦₆₄ newPqrCap) ∗
       memRegion (s0.sp - 1488#64) 24 ∗
       ((s0.sp - 1464#64) ↦₆₄ newPqrPtr) ∗
       memRegion (s0.sp - 1456#64) 8 ∗
       memRegion (s0.sp - 1184#64) 8 ∗
       memRegion (s0.sp - 1176#64) 8 ∗
       memRegion (s0.sp - 1168#64) 8 ∗
       memRegion (s0.sp - 1160#64) 16 ∗
       memRegion (s0.sp - 1144#64) 8 ∗
       memRegion (s0.sp - 1136#64) 8 ∗
       memRegion (s0.sp - 1128#64) 8 ∗
       memRegion (s0.sp - 1120#64) 16 ∗
       memRegion (s0.sp - 1104#64) 264 ∗
       memRegion (s0.sp - 840#64) 120 ∗
       ((s0.sp - 720#64) ↦₆₄ ptCap) ∗
       ((s0.sp - 712#64) ↦₆₄ ptPtr) ∗
       ((s0.sp - 704#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       memRegion (s0.sp - 696#64) 168 ∗
       memRegion (s0.sp - 504#64) 0x198 ∗
       protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       tapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
       logOff tryDecryptPlacedImg ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl uuidTryParse S).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl uuidTryParse S).onPanic x s0 sf ∗ R)) := by
  simp only [wp_norm] at hpc1 hsp1 hx9_1 hx19_1 hx20_1 hx21_1 hx24_1
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1184#64) (by sep_focus) fun w1184 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1176#64) (by sep_focus) fun w1176 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1168#64) (by sep_focus) fun w1168 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1144#64) (by sep_focus) fun w1144 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1136#64) (by sep_focus) fun w1136 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 1128#64) (by sep_focus) fun w1128 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 8#64) (by sep_focus) fun wret8 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 16#64) (by sep_focus) fun wret16 => ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret + 24#64) (by sep_focus) fun wret24 => ?_
  rw [stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide)]
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl1 (mid := lsρ lsMemcpySym)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun1)
  intro hcl2
  refine SepWPp.mono_focus
    (trAt_of_withoutPq A s0.sp trG tr newPqrCap newPqrPtr newPqrState hnew_le hnew_lt hnew_nz)
    (by sep_focus) ?_
  rw [trAt_eq_stack_heap A (s0.sp - 1448#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
      { tr with pqrState := newPqrState } hpad]
  refine SepWPp.elim_exists_focus
    (Φ := fun pad : BitVec 32 =>
      ((s0.sp - 1448#64) ↦ₛ trStackBytes { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
        { tr with pqrState := newPqrState } pad) ∗
      trHeapPart A { trG with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState })
    (by sep_focus) fun pad => ?_
  have hbs_len : (trStackBytes { trG with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState } pad).length = 264 :=
    length_trStackBytes _ _ pad hpad
  generalize hbs_def : trStackBytes { trG with pq := ⟨newPqrCap, newPqrPtr⟩ } { tr with pqrState := newPqrState } pad = bs at hbs_len ⊢
  rw [show memRegion (s0.sp - 1104#64) 264 = memRegion (s0.sp - 1104#64) bs.length by rw [hbs_len]]
  simp only [← sepConj_assoc]
  refine SepWPp.call_frame_placed (spec := withStack sessionMemcpyRegionSpec extHookStack)
    (x := (s0.sp - 1104#64, s0.sp - 1448#64, bs))
    (T := memRegion (s0.sp - 1104#64) bs.length ∗ ((s0.sp - 1448#64) ↦ₛ bs) ∗
          stackAt (s0.sp - 1504#64) extHookStack)
    (ret_pc := (blkPl_434).base + bv% (1248))
    hcl2 hmemcpy (by rfl) (by exact hrun1)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1) (by rfl)
    (by dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]; rw [sepConj_assoc, sepConj_assoc]; congr 3; simp only [wp_norm, hsp1])
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm, hbs_len]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ hm_pan => by dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl2
  intro s2 hpc2 hrun2 hsp2 hsp_al2 hcs2 hcl2
  simp only [wp_norm, hsp1] at hsp2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _hx29_2, hvregs_2⟩
  simp only [wp_norm, hx19_1, hx20_1, hx21_1, hx24_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx24_2 hvregs_2
  dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
  simp only [wp_norm, hsp1, sepConj_assoc]
  apply SepWPp.elim_pure; rintro ⟨_, htr2⟩
  have htr20 : s2.trace = s0.trace := htr2.trans htr1
  rw [← hbs_def]
  refine SepWPp.mono_focus
    (trAt_of_stack_heap A (s0.sp - 1104#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
      { tr with pqrState := newPqrState } pad hpad)
    (by sep_focus) ?_
  rw [hbs_def]
  refine SepWPp.mono_focus (extHookStack_to_trApplyStackX s0.sp) (by sep_focus) ?_
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl2 (mid := lsmpl.base 58)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun2)
  intro hcl3
  refine SepWPp.call_cro_frame_placed (spec := trApplySpecX A)
    (x := ⟨s0.sp - 1104#64, { trG with pq := ⟨newPqrCap, newPqrPtr⟩ },
           { tr with pqrState := newPqrState }, x.ss, x.G.afterTrFrom, st1⟩)
    (T := trAt A (s0.sp - 1104#64) { trG with pq := ⟨newPqrCap, newPqrPtr⟩ }
            { tr with pqrState := newPqrState } ∗
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          stackAt (s0.sp - 1504#64) trApplyStackX ∗ A.pool)
    (ret_pc := (blkPl_434).base + bv% (1260))
    hcl3 hTrApply (by rfl) (by exact hrun2)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al2) (by rfl)
    (by dsimp only [trApplySpecX]; simp only [wp_norm, hsp2]; rfl)
    (by refine ⟨by simp only [wp_norm], by simp only [wp_norm]⟩)
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [trApplySpecX] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ hm_pan => by
      have h0m : s0.trace <+: (s2.writeReg64 .x0 (s0.sp - 1104#64)
        |>.writeReg64 .x1 x.ss |>.writeReg64 .x30 ((blkPl_434).base + bv% (1260))
        |>.setPC (lsmpl.base 58)).trace := by
        rw [show (s2.writeReg64 .x0 (s0.sp - 1104#64)
          |>.writeReg64 .x1 x.ss |>.writeReg64 .x30 ((blkPl_434).base + bv% (1260))
          |>.setPC (lsmpl.base 58)).trace = s2.trace from rfl, htr20]
      exact tryDecryptFn_onPanic_of_callee_placed C decFn A ctl S x s0 _ sf _ R h0m hm_pan) ?_
  clear hcl3
  intro s3 hpc3 hrun3 hsp3 hsp_al3 hcs3 hcl3
  simp only [wp_norm, hsp2] at hsp3
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, _hx29_3, hvregs_3⟩
  simp only [wp_norm, hx19_2, hx20_2, hx21_2, hx24_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx24_3 hvregs_3
  dsimp only [trApplySpecX]
  simp only [wp_norm, hsp2, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr3
  have htr30 : s3.trace = s0.trace := htr3.trans htr20
  apply SepWPp.elim_exists; intro G1
  simp only [sepConj_assoc]
  apply SepWPp.elim_pure; intro hG1
  refine SepWPp.mono_focus (trApplyStackX_to_clearUpkStackX s0.sp) (by sep_focus) ?_
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_placed hcl3 (mid := lsmpl.base 35)
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun3)
  intro hcl4
  refine SepWPp.call_cro_frame_placed (spec := clearUpkSpecX A)
    (x := ⟨x.ss, G1, ({ tr with pqrState := newPqrState }).applyToSessionState st1⟩)
    (T := sessionStateAt A x.ss G1 (({ tr with pqrState := newPqrState }).applyToSessionState st1) ∗
          A.pool ∗ stackAt (s0.sp - 1504#64) clearUpkStackX)
    (ret_pc := (blkPl_434).base + bv% (1268))
    hcl4 hClearUpk (by rfl) (by exact hrun3)
    (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al3) (by rfl)
    (by dsimp only [clearUpkSpecX]; simp only [wp_norm, hsp3]; rfl)
    (by simp only [wp_norm])
    (by sep_focus)
    (fun _ _ _ _ h => by dsimp only [clearUpkSpecX] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
    (fun sf _ hm_pan => by dsimp only [clearUpkSpecX] at hm_pan; exact noPanic_callee hm_pan) ?_
  clear hcl4
  intro s4 hpc4 hrun4 hsp4 hsp_al4 hcs4 hcl4
  simp only [wp_norm, hsp3] at hsp4
  rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, _hx29_4, hvregs_4⟩
  simp only [wp_norm, hx19_3, hx20_3, hx21_3, hx24_3, hvregs_3] at hx19_4 hx20_4 hx21_4 hx24_4 hvregs_4
  dsimp only [clearUpkSpecX]
  simp only [wp_norm, hsp3, sepConj_assoc]
  apply SepWPp.elim_pure; intro htr4
  have htr40 : s4.trace = s0.trace := htr4.trans htr30
  refine SepWPp.mono_focus (clearUpkStackX_to_subStack s0.sp) (by sep_focus) ?_
  refine SepWPp.mono_focus
    (applyRatchet_local_frame_entails_memRegion s0.sp newPqrCap newPqrPtr ptCap ptPtr
      (BitVec.ofNat 64 pt.length) ptCap ptPtr (BitVec.ofNat 64 pt.length)
      ptCap ptPtr (BitVec.ofNat 64 pt.length) ptCap ptPtr (BitVec.ofNat 64 pt.length)
      bs hbs_len) (by sep_focus) ?_
  refine SepWPp.mono_focus (Entails.refl (tryDecryptSavedRegs s0.sp s0)) (by sep_focus) ?_
  refine SepWPp.elim_memRegion8_focus (a := x.ret) (by sep_focus) fun wret => ?_
  unfold tryDecryptSavedRegs
  simp only [← sepConj_assoc]
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun4)
  refine ⟨fun hmf => ?_, by simp only [wp_norm], ?_⟩
  · dsimp only [tryDecryptFnSpecPlaced, withLsCodeRoLoaded, tryDecryptFnRawSpecPlaced, tryDecryptFnSpec, Spec.inImage]
    rw [hok]
    rw [← hst] at hmf
    have hdec := decRel_of_trApplyRel hG1
    have hsaved := tryDecryptSavedRegs_entails_memRegion s0.sp s0
    unfold tryDecryptSavedRegs at hsaved
    have hmf1 := Satisfies.mono_focus hsaved (by sep_focus) hmf
    have hmf3 := Satisfies.mono_focus (stackAt_rootStack_of_parts s0.sp) (by sep_focus) hmf1
    rw [show (bv% (2 ^ 64 - 2) : BitVec 64) = okTagVec from rfl] at hmf3
    have hmf4 := Satisfies.mono_focus
      (decResultAt_ok_of_parts A x.ret pt ptCap ptPtr hpt_le hpt_lt hpt_nz) (by sep_focus) hmf3
    have hss : sessionStateAt A x.ss { G1 with pending := none, kyber := none } (x.modelFn C decFn S uuidTryParse).2 ⊢
        ∃∗ G' : SessionGhost, ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
          sessionStateAt A x.ss G' (x.modelFn C decFn S uuidTryParse).2 := by
      refine Entails.trans ?_
        (Entails.sepExists_intro
          (P := fun G' : SessionGhost =>
            ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
            sessionStateAt A x.ss G' (x.modelFn C decFn S uuidTryParse).2)
          { G1 with pending := none, kyber := none })
      exact Entails.pure_right hdec (Entails.refl _)
    have hmf5 := Satisfies.mono_focus hss (by sep_focus) hmf4
    clear hmf hmf1 hmf3 hmf4
    have hno_pan : (Except.ok pt : Except SignalProtocolError (List (BitVec 8))) ≠ .error .panic := nofun
    simp only [wp_norm, sepConj_assoc, satisfies_pure_sepConj] at hmf5 ⊢
    refine ⟨⟨hno_pan, htr40⟩, ?_⟩
    generalize (∃∗ G', ⌜x.G.AfterTryDecrypt (Except.ok pt : Except SignalProtocolError (List (BitVec 8))).toBool G'⌝ ∗
      sessionStateAt A x.ss G' (x.modelFn C decFn S uuidTryParse).2) = SS at hmf5 ⊢
    change _ ⊨ SS ∗ vecResultAt A x.ret (.ok pt) ∗ _
    sep_close
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, hvregs_4]

theorem applyRatchet_549_placed_ok_x [LibsignalPlacement]
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hTrApply : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 58) (withLsCodeRoLoaded lsmpl (trApplySpecX A)))
    (hClearUpk : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 35) (withLsCodeRoLoaded lsmpl (clearUpkSpecX A)))
    (hmemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsMemcpySym) (withStack sessionMemcpyRegionSpec extHookStack))
    (hdealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsρ lsRustDeallocSym) (rustDeallocExternSpecWithStack A extHookStack)) :
    S9SeamXPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C decFn A ctl uuidTryParse S := by
  intro x trG tr st1 newPqrState pt R s0 s hok hst h9
  rcases h9 with ⟨hpc, ⟨hrun, hsp, hsp0, hsp_al, hx29, htr, hcl, hvregs⟩,
    hx19, hx20, hx21, hx23, hx24, newPqrCap, newPqrPtr, hnew_le, hnew_lt, hnew_nz, hmem⟩
  have h6d0 := @applyRatchet_from_6d0_549_placed_x _ C decFn A ctl S H hTrApply hClearUpk hmemcpy x trG tr st1
    newPqrState pt newPqrCap newPqrPtr
  clear hTrApply hClearUpk
  have hpad : trG.ratchet.senderPad.length = 100 := by
    have htr_front := hmem
    rw [← sepConj_assoc, sepConj_comm (sessionStateAt A x.ss x.G.afterTrFrom st1), sepConj_assoc] at htr_front
    exact trAt_senderPad_len htr_front
  unfold tryDecryptCommonHeap at hmem
  rw [trAt_eq_withoutPq A s0.sp trG tr,
       applyRatchet_scr_split s0.sp,
       applyRatchet_ret_split x.ret,
       show s0.sp - 1504#64 + 0x3d0#64 = s0.sp - 528#64 by bv_omega,
       show s0.sp - 1504#64 + 0x8#64 = s0.sp - 1496#64 by bv_omega,
       show s0.sp - 1504#64 + 0x10#64 = s0.sp - 1488#64 by bv_omega,
       show s0.sp - 1504#64 + 0x28#64 = s0.sp - 1464#64 by bv_omega,
       show s0.sp - 1504#64 + 0x30#64 = s0.sp - 1456#64 by bv_omega,
       show s0.sp - 1504#64 + 0x3e8#64 = s0.sp - 504#64 by bv_omega] at hmem
  change s.pc = (blkPl_434).base + 1700#64 at hpc
  simp only [wp_norm] at hx20 hx23 hx29
  simp only [← sepConj_assoc] at hmem
  refine sepWPp_to_reaches_outcome hmem ?_
  refine SepWPp.elim_pure_focus
    (φ := tr.pqrState.length ≤ trG.pq.cap.toNat ∧ trG.pq.cap.toNat < 2 ^ 63 ∧ trG.pq.ptr ≠ 0)
    (by sep_focus) fun ⟨hpq_le, hpq_lt, hpq_nz⟩ => ?_
  refine SepWPp.elim_vecU8_focus (A := A) (a := s0.sp - 528#64) (bs := pt)
    (by sep_focus) fun ptCap ptPtr hpt_le hpt_lt hpt_nz => ?_
  rw [show s0.sp - 528#64 + 8#64 = s0.sp - 520#64 by bv_omega,
      show s0.sp - 528#64 + 16#64 = s0.sp - 512#64 by bv_omega]
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 720#64) (by sep_focus) fun w720 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 712#64) (by sep_focus) fun w712 => ?_
  refine SepWPp.elim_memRegion8_focus (a := s0.sp - 704#64) (by sep_focus) fun w704 => ?_
  by_cases hpq_cap : trG.pq.cap = 0#64
  · refine SepWPp.mono_focus (newPqr_zero_prep A trG.pq.cap trG.pq.ptr tr.pqrState hpq_cap) (by sep_focus) ?_
    rw [emp_sepConj]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl (mid := (blkPl_434).base + bv% (1744))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    intro hcl1
    refine SepWPp.congr_pre (by sep_focus)
      (h6d0 ptCap ptPtr R s0 _
        hok hst hpad hnew_le hnew_lt hnew_nz hpt_le hpt_lt hpt_nz
        hsp0 (by rfl) (by exact hrun) (by simp only [wp_norm, hsp])
        (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al)
        htr hcl1
        (by simp only [wp_norm])
        (by simp only [wp_norm, hx19])
        (by simp only [wp_norm, hx20])
        (by simp only [wp_norm, hx21])
        (by simp only [wp_norm, hx24])
        (by simp only [wp_norm, hx29])
        (by simp only [wp_norm, hvregs]))
  · refine SepWPp.mono_focus (newPqr_dealloc_prep' A trG.pq.cap trG.pq.ptr tr.pqrState hpq_cap hpq_le hpq_lt) (by sep_focus) ?_
    rw [stackAt_sub_split (s0.sp - 1504#64) extHookStack (by decide)]
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl (mid := (blkPl_434).base + bv% (1728))
    wp_steps
    apply SepWP.setPC_setMem_ite_false (by simp only [beq_iff_eq, hpq_cap, not_false_eq_true])
    apply SepWP.done (by rfl) (by exact hrun)
    intro hcl0
    apply SepWPp.of_sepWP_placed hcl0 (mid := lsρ lsRustDeallocSym)
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    intro hcl1
    refine SepWPp.call_frame_placed (spec := rustDeallocExternSpecWithStack A extHookStack)
      (x := (trG.pq.ptr, trG.pq.cap.toNat, 1))
      (T := A.pool ∗ A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat ∗
            stackAt (s0.sp - 1504#64) extHookStack)
      (ret_pc := (blkPl_434).base + bv% (1740))
      hcl1 hdealloc (by rfl) (by exact hrun)
      (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al) (by rfl)
      (by dsimp only [rustDeallocExternSpecWithStack]; simp only [wp_norm, hsp]; rfl)
      (by refine ⟨by simp only [wp_norm], by simp only [wp_norm], by simp only [wp_norm],
                  layoutOk_of_cap_ne_zero hpq_cap hpq_lt⟩)
      (by sep_focus)
      (fun _ _ _ _ h => by dsimp only [rustDeallocExternSpecWithStack] at h; rw [satisfies_pure_sepConj] at h; exact h.1)
      (fun sf _ hm_pan => by dsimp only [rustDeallocExternSpecWithStack] at hm_pan; exact noPanic_callee hm_pan) ?_
    clear hcl0 hcl1
    intro s1 hpc1 hrun1 hsp1 hsp_al1 hcs1 hcl1
    simp only [wp_norm, hsp] at hsp1
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [wp_norm, hx19, hx20, hx21, hx24, hx29, hvregs] at hx19_1 hx20_1 hx21_1 hx24_1 hx29_1 hvregs_1
    dsimp only [rustDeallocExternSpecWithStack, rustDeallocSpecWithStack]
    simp only [wp_norm, hsp, sepConj_assoc]
    apply SepWPp.elim_pure; intro htr1
    have htr10 : s1.trace = s0.trace := htr1.trans htr
    refine SepWPp.mono_focus (extHookStack_to_subStack s0.sp) (by sep_focus) ?_
    simp only [← sepConj_assoc]
    apply SepWPp.of_sepWP_placed hcl1 (mid := (blkPl_434).base + bv% (1744))
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun1)
    intro hcl2
    rw [← logOff_tryDecryptPlacedImg]
    refine SepWPp.congr_pre (by sep_focus)
      (h6d0 ptCap ptPtr R s0 _
        hok hst hpad hnew_le hnew_lt hnew_nz hpt_le hpt_lt hpt_nz
        hsp0 (by rfl) (by exact hrun1) (by simp only [wp_norm, hsp1])
        (AuthDecryptFacts.spAligned_of_sp_eq (by simp only [wp_norm]) hsp_al1)
        htr10 hcl2
        (by simp only [wp_norm])
        (by simp only [wp_norm, hx19_1])
        (by simp only [wp_norm, hx20_1])
        (by simp only [wp_norm, hx21_1])
        (by simp only [wp_norm, hx24_1])
        (by simp only [wp_norm, hx29_1])
        (by simp only [wp_norm, hvregs_1]))

end CryptoVerification.LibsignalTripleRatchet.Decrypt.AuthDecrypt
