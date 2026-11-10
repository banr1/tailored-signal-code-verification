/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.Common
import ProofLib.SepLogic.WPp

/-!
# `TripleRatchet::from_session_state` Segment Helpers (`S1Spec`)

Framing and branch-staging helpers around `TripleRatchet::from_session_state` (`+0x1d8 → +0x2a4 /
+0x384 → +0x3b0`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.DecryptPq

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Segment S1 (`+0x1d8 → +0x2a4 / +0x384 → +0x3b0`) -/

theorem memRegion_0x38_split_trFrom (sp : BitVec 64) :
    memRegion (sp + 0x38#64) 0x548 =
      memRegion (sp + 0x38#64) 0x158 ∗
      memRegion (sp + 0x190#64) 264 ∗
      memRegion (sp + 0x298#64) 0x2e8 := by
  rw [memRegion_split (sp + 0x38#64) 0x158 0x3f0 (by decide),
      show (sp + 0x38#64) + BitVec.ofNat 64 0x158 = sp + 0x190#64 by bv_omega,
      memRegion_split (sp + 0x190#64) 264 0x2e8 (by decide),
      show (sp + 0x190#64) + BitVec.ofNat 64 264 = sp + 0x298#64 by bv_omega]

theorem mut_exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with
      | (.ok a, s') => Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  unfold Mut.exec
  change (ExceptT.run (m >>= f)).run s = _
  rw [ExceptT.run_bind]
  simp only [StateT.run_bind]
  rcases (m.run).run s with ⟨r, s'⟩
  cases r <;> rfl

theorem fromSessionState_exec (st : SessionState (List (BitVec 8))) :
    Mut.exec TripleRatchet.fromSessionState st =
      match st.remoteIdentity with
      | some remote =>
        (.ok ⟨⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩,
              st.pqRatchetState, st.localIdentity, remote⟩,
         { st with receiverChains := [], pqRatchetState := default })
      | none =>
        (.error (.invalidSessionStructure .missingRemoteIdentity),
         { st with receiverChains := [], pqRatchetState := default }) := by
  rcases st with ⟨sv, li, ri, rk, pc, sc, rcs, ppk, pqr⟩
  cases ri <;> rfl

theorem fromSessionState_error_imp (C : Crypto) (S : SpqrModel)
    (x : TryDecryptGhost) (e : SignalProtocolError) (st1 : SessionState (List (BitVec 8)))
    (h : Mut.exec TripleRatchet.fromSessionState x.st = (.error e, st1)) :
    e = .invalidSessionStructure .missingRemoteIdentity ∧
    e ≠ .panic ∧
    decryptDraws C x.st x.msg.senderRatchetKey x.rest = 0 ∧
    x.model C S uuidTryParse = (.error e, st1) := by
  have hexec := fromSessionState_exec x.st
  have hrem : x.st.remoteIdentity = none ∧
      e = .invalidSessionStructure .missingRemoteIdentity := by
    rw [hexec] at h
    cases hri : x.st.remoteIdentity <;> rw [hri] at h
    · injection h with h1 _
      injection h1 with h2
      exact ⟨rfl, h2.symm⟩
    · injection h with h1 _
      cases h1
  rcases hrem with ⟨hri, rfl⟩
  refine ⟨rfl, by decide, ?_, ?_⟩
  · simp [decryptDraws, drawsCoins, hri]
  · unfold TryDecryptGhost.model SessionState.tryDecryptWithState
    rw [mut_exec_bind, h]

/-- The 256-byte inline body of `trAt A t trG tr` at `p = t + 8#64`. -/
def trBodyAt (p : BitVec 64) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8))) : SepProp :=
  (p ↦₆₄ trG.ratchet.chainsPtr) ∗
  ((p + 8#64) ↦₆₄ BitVec.ofNat 64 (trG.ratchet.chains.zip tr.ratchet.receiverChains).length) ∗
  ((p + 16#64) ↦ₛ optSenderChainBytes tr.ratchet.senderChain trG.ratchet.senderPad) ∗
  ((p + 120#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) ∗
  ((p + 152#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
  ((p + 160#64) ↦₃₂ tr.ratchet.previousCounter) ∗
  memRegion (p + 164#64) 4 ∗
  ((p + 168#64) ↦₆₄ trG.pq.cap) ∗
  ((p + 176#64) ↦₆₄ trG.pq.ptr) ∗
  ((p + 184#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
  ((p + 192#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
  ((p + 224#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)

/-- The address-independent heap and pure invariants of `trAt A t trG tr`. -/
def trHeapAt (A : RustAlloc) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8))) : SepProp :=
  ⌜∀ sc, tr.ratchet.senderChain = some sc →
    Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes⌝ ∗
  ⌜trG.ratchet.chains.length = tr.ratchet.receiverChains.length ∧
    trG.ratchet.senderPad.length = 100 ∧
    tr.ratchet.maxForwardJumps < 2 ^ 64⌝ ∗
  ⌜tr.pqrState.length ≤ trG.pq.cap.toNat ∧
    trG.pq.cap.toNat < 2 ^ 63 ∧
    trG.pq.ptr ≠ 0⌝ ∗
  vecBuf A 104 8 (chainAt A) trG.ratchet.chainsCap trG.ratchet.chainsPtr
    (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
  (if trG.pq.cap = 0 then emp
   else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
     (trG.pq.ptr ↦ₛ tr.pqrState) ∗
     memRegion (trG.pq.ptr + BitVec.ofNat 64 tr.pqrState.length)
       (trG.pq.cap.toNat - tr.pqrState.length))

theorem trAt_eq_cap_body_heap (A : RustAlloc) (t : BitVec 64) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) :
    trAt A t trG tr =
      (t ↦₆₄ trG.ratchet.chainsCap) ∗
      trBodyAt (t + 8#64) trG tr ∗
      trHeapAt A trG tr := by
  unfold trAt ratchetAt vecU8At vecAt vecHeader trBodyAt trHeapAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

theorem relocBytes_trBodyAt (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (hpad : trG.ratchet.senderPad.length = 100) :
    RelocBytes 256 (fun p => trBodyAt p trG tr) := by
  have h_sc : (optSenderChainBytes tr.ratchet.senderChain trG.ratchet.senderPad).length = 104 :=
    optSenderChainBytes_length tr.ratchet.senderChain trG.ratchet.senderPad hpad
  have h_rk : (keyToBytes32 tr.ratchet.rootKey).length = 32 := by
    simp [keyToBytes32]
  have h_lik : tr.localIdentityKey.publicKey.bytes.toList.length = 32 :=
    List.Vector.toList_length _
  have h_rik : tr.remoteIdentityKey.publicKey.bytes.toList.length = 32 :=
    List.Vector.toList_length _
  have h16 := relocBytes_append
    (relocBytes_pointsTo64 trG.ratchet.chainsPtr)
    (relocBytes_pointsTo64 (BitVec.ofNat 64 (trG.ratchet.chains.zip
      tr.ratchet.receiverChains).length)) rfl
  have h120 := relocBytes_append h16
    (relocBytes_pointsToBytes _ h_sc) rfl
  have h152 := relocBytes_append h120
    (relocBytes_pointsToBytes _ h_rk) rfl
  have h160 := relocBytes_append h152
    (relocBytes_pointsTo64 (BitVec.ofNat 64 tr.ratchet.maxForwardJumps)) rfl
  have h164 := relocBytes_append h160
    (relocBytes_pointsTo32 tr.ratchet.previousCounter) rfl
  have h168 := relocBytes_append h164
    (relocBytes_memRegion 4 (by decide)) rfl
  have h176 := relocBytes_append h168
    (relocBytes_pointsTo64 trG.pq.cap) rfl
  have h184 := relocBytes_append h176
    (relocBytes_pointsTo64 trG.pq.ptr) rfl
  have h192 := relocBytes_append h184
    (relocBytes_pointsTo64 (BitVec.ofNat 64 tr.pqrState.length)) rfl
  have h224 := relocBytes_append h192
    (relocBytes_pointsToBytes _ h_lik) rfl
  have h256 := relocBytes_append h224
    (relocBytes_pointsToBytes _ h_rik) rfl
  refine relocBytes_congr (fun p => ?_) h256
  unfold trBodyAt
  simp only [Nat.reduceAdd]
  sep_ac_rfl

theorem trHeapAt_facts {A : RustAlloc} {trG : TrGhost}
    {tr : TripleRatchet (List (BitVec 8))} {R : SepProp} {m : Memory}
    (hm : m ⊨ trHeapAt A trG tr ∗ R) :
    trG.ratchet.senderPad.length = 100 ∧
    trG.ratchet.chainsCap + 1#64 ≠ 0#64 := by
  have hm' : m ⊨
      ⌜trG.ratchet.chains.length = tr.ratchet.receiverChains.length ∧
        trG.ratchet.senderPad.length = 100 ∧
        tr.ratchet.maxForwardJumps < 2 ^ 64⌝ ∗
      ⌜(trG.ratchet.chains.zip tr.ratchet.receiverChains).length ≤ trG.ratchet.chainsCap.toNat ∧
        trG.ratchet.chainsCap.toNat * 104 < 2 ^ 63 ∧
        trG.ratchet.chainsPtr ≠ 0⌝ ∗
      (⌜∀ sc, tr.ratchet.senderChain = some sc →
          Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes⌝ ∗
       ⌜tr.pqrState.length ≤ trG.pq.cap.toNat ∧
         trG.pq.cap.toNat < 2 ^ 63 ∧
         trG.pq.ptr ≠ 0⌝ ∗
       (if trG.ratchet.chainsCap = 0 then emp
        else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
          arrayAt (chainAt A) 104 trG.ratchet.chainsPtr
            (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
          memRegion
            (trG.ratchet.chainsPtr +
              BitVec.ofNat 64 ((trG.ratchet.chains.zip tr.ratchet.receiverChains).length * 104))
            ((trG.ratchet.chainsCap.toNat -
              (trG.ratchet.chains.zip tr.ratchet.receiverChains).length) * 104)) ∗
       (if trG.pq.cap = 0 then emp
        else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
          (trG.pq.ptr ↦ₛ tr.pqrState) ∗
          memRegion (trG.pq.ptr + BitVec.ofNat 64 tr.pqrState.length)
            (trG.pq.cap.toNat - tr.pqrState.length)) ∗ R) := by
    unfold trHeapAt vecBuf at hm
    convert hm using 1; sep_ac_rfl
  rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hm'
  rcases hm' with ⟨⟨_, hpad, _⟩, ⟨_, hcap_lt, _⟩, _⟩
  refine ⟨hpad, ?_⟩
  bv_omega

theorem words32At_198_eq (sp w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
    w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 : BitVec 64) :
    words32At (sp + 0x198#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 =
    words4At (sp + 0x198#64) w0 w1 w2 w3 ∗
    ((sp + 0x1b8#64) ↦₆₄ w4) ∗
    ((sp + 0x1c0#64) ↦₆₄ w5) ∗
    ((sp + 0x1c8#64) ↦₆₄ w6) ∗
    ((sp + 0x1d0#64) ↦₆₄ w7) ∗
    ((sp + 0x1d8#64) ↦₆₄ w8) ∗
    ((sp + 0x1e0#64) ↦₆₄ w9) ∗
    ((sp + 0x1e8#64) ↦₆₄ w10) ∗
    ((sp + 0x1f0#64) ↦₆₄ w11) ∗
    words4At (sp + 0x1f8#64) w12 w13 w14 w15 ∗
    ((sp + 0x218#64) ↦₆₄ w16) ∗
    ((sp + 0x220#64) ↦₆₄ w17) ∗
    ((sp + 0x228#64) ↦₆₄ w18) ∗
    ((sp + 0x230#64) ↦₆₄ w19) ∗
    words4At (sp + 0x238#64) w20 w21 w22 w23 ∗
    words8At (sp + 0x258#64) w24 w25 w26 w27 w28 w29 w30 w31 := by
  unfold words32At words16At words8At words4At
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem words32At_40_eq (sp w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
    w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 : BitVec 64) :
    words32At (sp + 0x40#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 =
    words8At (sp + 0x40#64) w0 w1 w2 w3 w4 w5 w6 w7 ∗
    words8At (sp + 0x80#64) w8 w9 w10 w11 w12 w13 w14 w15 ∗
    words8At (sp + 0xc0#64) w16 w17 w18 w19 w20 w21 w22 w23 ∗
    words8At (sp + 0x100#64) w24 w25 w26 w27 w28 w29 w30 w31 := by
  unfold words32At words16At
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA
