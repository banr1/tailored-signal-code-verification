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
# `TripleRatchet` Field Exposure for `ErrTailSpec`

Decomposition of `trAt A (sp + 0x38#64) trG tr` into its `receiver_chains` vector, `pqr_state`
buffer, and surrounding `memRegion` blocks for the `ErrTail` drop sequence (`+0x30c → +0x394`).
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

/-- Expose the fields of `trAt A (sp + 0x38#64) trG tr` needed by `ErrTail`:
- `receiver_chains` header at `sp + 0x38..0x50`, its `arrayAt` elements, and its spare/live block;
- `pqr_state` header `(cap, ptr)` at `sp + 0xe8..0xf8` and its heap allocation;
- the remaining `152 + 72 = 224` bytes of `trAt` collapsed into `memRegion (sp + 0x50#64) 0x98 ∗
  memRegion (sp + 0xf8#64) 0x48`. -/
theorem trAt_expose_errTail {A : RustAlloc} {sp : BitVec 64} {trG : TrGhost}
    {tr : TripleRatchet (List (BitVec 8))} {R : SepProp} {m : Memory}
    (hm : m ⊨ trAt A (sp + 0x38#64) trG tr ∗ R) :
    let cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
    cs.length ≤ trG.ratchet.chainsCap.toNat ∧
    trG.ratchet.chainsCap.toNat * 104 < 2 ^ 63 ∧
    trG.ratchet.chainsPtr ≠ 0#64 ∧
    tr.pqrState.length ≤ trG.pq.cap.toNat ∧
    trG.pq.cap.toNat < 2 ^ 63 ∧
    trG.pq.ptr ≠ 0#64 ∧
    (m ⊨
      (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
       memRegion (sp + 0x50#64) 0x98 ∗
       ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
       ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
       memRegion (sp + 0xf8#64) 0x48 ∗
       arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
       (if trG.ratchet.chainsCap = 0#64 then emp
        else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
          memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
            ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
       (if trG.pq.cap = 0#64 then emp
        else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
          memRegion trG.pq.ptr trG.pq.cap.toNat)) ∗ R) := by
  dsimp only
  unfold trAt ratchetAt vecU8At vecAt vecBuf vecHeader at hm
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨_, ⟨_, hpad, _⟩, hm⟩
  have hm_cs :
      m ⊨ ⌜(trG.ratchet.chains.zip tr.ratchet.receiverChains).length ≤ trG.ratchet.chainsCap.toNat ∧
            trG.ratchet.chainsCap.toNat * 104 < 2 ^ 63 ∧
            trG.ratchet.chainsPtr ≠ 0#64⌝ ∗
        (⌜tr.pqrState.length ≤ trG.pq.cap.toNat ∧
          trG.pq.cap.toNat < 2 ^ 63 ∧
          trG.pq.ptr ≠ 0#64⌝ ∗
         (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
          ((sp + 0x38#64 + 8#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
          ((sp + 0x38#64 + 16#64) ↦₆₄
            BitVec.ofNat 64 (trG.ratchet.chains.zip tr.ratchet.receiverChains).length) ∗
          (if trG.ratchet.chainsCap = 0#64 then emp
           else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
             arrayAt (chainAt A) 104 trG.ratchet.chainsPtr
               (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
             memRegion
               (trG.ratchet.chainsPtr +
                 BitVec.ofNat 64 ((trG.ratchet.chains.zip tr.ratchet.receiverChains).length * 104))
               ((trG.ratchet.chainsCap.toNat -
                 (trG.ratchet.chains.zip tr.ratchet.receiverChains).length) * 104)) ∗
          ((sp + 0x38#64 + 24#64) ↦ₛ
            optSenderChainBytes tr.ratchet.senderChain trG.ratchet.senderPad) ∗
          ((sp + 0x38#64 + 128#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) ∗
          ((sp + 0x38#64 + 160#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
          ((sp + 0x38#64 + 168#64) ↦₃₂ tr.ratchet.previousCounter) ∗
          memRegion (sp + 0x38#64 + 172#64) 4 ∗
          ((sp + 0x38#64 + 0xb0#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0x38#64 + 0xb0#64 + 8#64) ↦₆₄ trG.pq.ptr) ∗
          ((sp + 0x38#64 + 0xb0#64 + 16#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
          (if trG.pq.cap = 0#64 then emp
           else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
             (trG.pq.ptr ↦ₛ tr.pqrState) ∗
             memRegion (trG.pq.ptr + BitVec.ofNat 64 tr.pqrState.length)
               (trG.pq.cap.toNat - tr.pqrState.length)) ∗
          ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
          ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗ R)) := by
    convert hm using 1
    sep_ac_rfl
  rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hm_cs
  rcases hm_cs with ⟨⟨hcs_le, hcs_lt, hcs_ptr⟩, ⟨hpq_le, hpq_lt, hpq_ptr⟩, hm⟩
  refine ⟨hcs_le, hcs_lt, hcs_ptr, hpq_le, hpq_lt, hpq_ptr, ?_⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm
  have h50 :
      (((sp + 0x50#64) ↦ₛ optSenderChainBytes tr.ratchet.senderChain trG.ratchet.senderPad) ∗
       ((sp + 0xb8#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) ∗
       ((sp + 0xd8#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
       ((sp + 0xe0#64) ↦₃₂ tr.ratchet.previousCounter) ∗
       memRegion (sp + 0xe4#64) 4) ⊢
      memRegion (sp + 0x50#64) 0x98 := by
    have hsc_len := optSenderChainBytes_length tr.ratchet.senderChain trG.ratchet.senderPad hpad
    have hrk_len : (keyToBytes32 tr.ratchet.rootKey).length = 32 := by
      simp [keyToBytes32]
    refine Entails.trans
      (sepConj_mono (hsc_len ▸ pointsToBytes_entails_memRegion _ _)
      (sepConj_mono (hrk_len ▸ pointsToBytes_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
        (Entails.refl _))))) ?_
    rw [show sp + 0xe4#64 = (sp + 0xe0#64) + 4#64 by bv_omega,
        ← memRegion_split (sp + 0xe0#64) 4 4 (by decide),
        show sp + 0xe0#64 = (sp + 0xd8#64) + 8#64 by bv_omega,
        ← memRegion_split (sp + 0xd8#64) 8 8 (by decide),
        show sp + 0xd8#64 = (sp + 0xb8#64) + 32#64 by bv_omega,
        ← memRegion_split (sp + 0xb8#64) 32 16 (by decide),
        show sp + 0xb8#64 = (sp + 0x50#64) + 104#64 by bv_omega,
        ← memRegion_split (sp + 0x50#64) 104 48 (by decide)]
    exact Entails.refl _
  have hf8 :
      (((sp + 0xf8#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
       ((sp + 0x100#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
       ((sp + 0x120#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)) ⊢
      memRegion (sp + 0xf8#64) 0x48 := by
    have hloc_len : tr.localIdentityKey.publicKey.bytes.toList.length = 32 :=
      List.Vector.toList_length _
    have hrem_len : tr.remoteIdentityKey.publicKey.bytes.toList.length = 32 :=
      List.Vector.toList_length _
    refine Entails.trans
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (hloc_len ▸ pointsToBytes_entails_memRegion _ _)
        (hrem_len ▸ pointsToBytes_entails_memRegion _ _))) ?_
    rw [show sp + 0x120#64 = (sp + 0x100#64) + 32#64 by bv_omega,
        ← memRegion_split (sp + 0x100#64) 32 32 (by decide),
        show sp + 0x100#64 = (sp + 0xf8#64) + 8#64 by bv_omega,
        ← memRegion_split (sp + 0xf8#64) 8 64 (by decide)]
    exact Entails.refl _
  have hcs_buf :
      (if trG.ratchet.chainsCap = 0#64 then emp
       else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr
           (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
         memRegion
           (trG.ratchet.chainsPtr +
             BitVec.ofNat 64 ((trG.ratchet.chains.zip tr.ratchet.receiverChains).length * 104))
           ((trG.ratchet.chainsCap.toNat -
             (trG.ratchet.chains.zip tr.ratchet.receiverChains).length) * 104)) ⊢
      arrayAt (chainAt A) 104 trG.ratchet.chainsPtr
        (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
      (if trG.ratchet.chainsCap = 0#64 then emp
       else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
         memRegion
           (trG.ratchet.chainsPtr +
             BitVec.ofNat 64 ((trG.ratchet.chains.zip tr.ratchet.receiverChains).length * 104))
           ((trG.ratchet.chainsCap.toNat -
             (trG.ratchet.chains.zip tr.ratchet.receiverChains).length) * 104)) := by
    split
    · next hcap0 =>
      have hlen0 : (trG.ratchet.chains.zip tr.ratchet.receiverChains).length = 0 := by
        simpa [hcap0] using hcs_le
      rw [List.eq_nil_of_length_eq_zero hlen0, arrayAt, emp_sepConj]
      exact Entails.refl _
    · have hcomm :
          (A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            arrayAt (chainAt A) 104 trG.ratchet.chainsPtr
              (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
            memRegion
              (trG.ratchet.chainsPtr +
                BitVec.ofNat 64 ((trG.ratchet.chains.zip tr.ratchet.receiverChains).length * 104))
              ((trG.ratchet.chainsCap.toNat -
                (trG.ratchet.chains.zip tr.ratchet.receiverChains).length) * 104)) =
          (arrayAt (chainAt A) 104 trG.ratchet.chainsPtr
              (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
            (A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
             memRegion
              (trG.ratchet.chainsPtr +
                BitVec.ofNat 64 ((trG.ratchet.chains.zip tr.ratchet.receiverChains).length * 104))
              ((trG.ratchet.chainsCap.toNat -
                (trG.ratchet.chains.zip tr.ratchet.receiverChains).length) * 104))) := by
        sep_ac_rfl
      rw [hcomm]
      exact Entails.refl _
  have hpq_buf :
      (if trG.pq.cap = 0#64 then emp
       else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
         (trG.pq.ptr ↦ₛ tr.pqrState) ∗
         memRegion (trG.pq.ptr + BitVec.ofNat 64 tr.pqrState.length)
           (trG.pq.cap.toNat - tr.pqrState.length)) ⊢
      (if trG.pq.cap = 0#64 then emp
       else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
         memRegion trG.pq.ptr trG.pq.cap.toNat) := by
    split
    · exact Entails.refl _
    · refine sepConj_mono_right ?_
      refine Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion _ _)) ?_
      rw [← memRegion_split trG.pq.ptr tr.pqrState.length
            (trG.pq.cap.toNat - tr.pqrState.length) (by omega),
          Nat.add_sub_of_le hpq_le]
      exact Entails.refl _
  have hm_re :
      m ⊨
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
         ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄
           BitVec.ofNat 64 (trG.ratchet.chains.zip tr.ratchet.receiverChains).length) ∗
         (((sp + 0x50#64) ↦ₛ optSenderChainBytes tr.ratchet.senderChain trG.ratchet.senderPad) ∗
          ((sp + 0xb8#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) ∗
          ((sp + 0xd8#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
          ((sp + 0xe0#64) ↦₃₂ tr.ratchet.previousCounter) ∗
          memRegion (sp + 0xe4#64) 4) ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
         (((sp + 0xf8#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
          ((sp + 0x100#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
          ((sp + 0x120#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)) ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            arrayAt (chainAt A) 104 trG.ratchet.chainsPtr
              (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
            memRegion
              (trG.ratchet.chainsPtr +
                BitVec.ofNat 64 ((trG.ratchet.chains.zip tr.ratchet.receiverChains).length * 104))
              ((trG.ratchet.chainsCap.toNat -
                (trG.ratchet.chains.zip tr.ratchet.receiverChains).length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            (trG.pq.ptr ↦ₛ tr.pqrState) ∗
            memRegion (trG.pq.ptr + BitVec.ofNat 64 tr.pqrState.length)
              (trG.pq.cap.toNat - tr.pqrState.length))) ∗ R := by
    convert hm using 1
    sep_ac_rfl
  have hm_out := Satisfies.mono
    (sepConj_mono_left
      (sepConj_mono_right
      (sepConj_mono_right
      (sepConj_mono_right
      (sepConj_mono h50
      (sepConj_mono_right
      (sepConj_mono_right
      (sepConj_mono hf8
      (sepConj_mono hcs_buf hpq_buf)))))))))
    hm_re
  convert hm_out using 1
  sep_ac_rfl

theorem chains_recombine_entails {A : RustAlloc} {chainsCap chainsPtr : BitVec 64} {n : Nat}
    (hle : n ≤ chainsCap.toNat) (hlt : chainsCap.toNat * 104 < 2 ^ 63) :
    (memRegion chainsPtr (n * 104) ∗
     (if chainsCap = 0#64 then emp
      else A.live chainsPtr (chainsCap.toNat * 104) 8 ∗
        memRegion (chainsPtr + BitVec.ofNat 64 (n * 104)) ((chainsCap.toNat - n) * 104))) ⊢
    (if chainsCap = 0#64 then emp
     else A.live chainsPtr (chainsCap.toNat * 104) 8 ∗
       memRegion chainsPtr (chainsCap.toNat * 104)) := by
  split
  · next hcap0 =>
    have hn0 : n = 0 := by simpa [hcap0] using hle
    subst hn0
    rw [Nat.zero_mul, memRegion_zero, emp_sepConj]
    exact Entails.refl _
  · have hre :
        (memRegion chainsPtr (n * 104) ∗
          (A.live chainsPtr (chainsCap.toNat * 104) 8 ∗
           memRegion (chainsPtr + BitVec.ofNat 64 (n * 104)) ((chainsCap.toNat - n) * 104))) =
        (A.live chainsPtr (chainsCap.toNat * 104) 8 ∗
          (memRegion chainsPtr (n * 104) ∗
           memRegion (chainsPtr + BitVec.ofNat 64 (n * 104)) ((chainsCap.toNat - n) * 104))) := by
      sep_ac_rfl
    rw [hre, ← memRegion_split chainsPtr (n * 104) ((chainsCap.toNat - n) * 104) (by omega),
        show n * 104 + (chainsCap.toNat - n) * 104 = chainsCap.toNat * 104 by
          rw [← Nat.add_mul, Nat.add_sub_of_le hle]]
    exact Entails.refl _

theorem errTail_stack_recombine (sp c0 c1 c2 p0 p1 w0 w1 w2 w3 w4 : BitVec 64) :
    (memRegion sp 0x38 ∗
     ((sp + 0x38#64) ↦₆₄ c0) ∗
     ((sp + 0x40#64) ↦₆₄ c1) ∗
     ((sp + 0x48#64) ↦₆₄ c2) ∗
     memRegion (sp + 0x50#64) 0x98 ∗
     ((sp + 0xe8#64) ↦₆₄ p0) ∗
     ((sp + 0xf0#64) ↦₆₄ p1) ∗
     memRegion (sp + 0xf8#64) 0x48 ∗
     ((sp + 0x140#64) ↦₆₄ w0) ∗
     ((sp + 0x148#64) ↦₆₄ w1) ∗
     ((sp + 0x150#64) ↦₆₄ w2) ∗
     memRegion (sp + 0x158#64) 16 ∗
     words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
     memRegion (sp + 0x190#64) 0x3f0) ⊢
    memRegion sp 1408 := by
  refine Entails.trans
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (words5At_entails_memRegion _ _ _ _ _ _)
      (Entails.refl _)))))))))))))) ?_
  rw [show sp + 0x190#64 = (sp + 0x168#64) + 40#64 by bv_omega,
      ← memRegion_split (sp + 0x168#64) 40 0x3f0 (by decide),
      show sp + 0x168#64 = (sp + 0x158#64) + 16#64 by bv_omega,
      ← memRegion_split (sp + 0x158#64) 16 1048 (by decide),
      show sp + 0x158#64 = (sp + 0x150#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 0x150#64) 8 1064 (by decide),
      show sp + 0x150#64 = (sp + 0x148#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 0x148#64) 8 1072 (by decide),
      show sp + 0x148#64 = (sp + 0x140#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 0x140#64) 8 1080 (by decide),
      show sp + 0x140#64 = (sp + 0xf8#64) + 72#64 by bv_omega,
      ← memRegion_split (sp + 0xf8#64) 72 1088 (by decide),
      show sp + 0xf8#64 = (sp + 0xf0#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 0xf0#64) 8 1160 (by decide),
      show sp + 0xf0#64 = (sp + 0xe8#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 0xe8#64) 8 1168 (by decide),
      show sp + 0xe8#64 = (sp + 0x50#64) + 152#64 by bv_omega,
      ← memRegion_split (sp + 0x50#64) 152 1176 (by decide),
      show sp + 0x50#64 = (sp + 0x48#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 0x48#64) 8 1328 (by decide),
      show sp + 0x48#64 = (sp + 0x40#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 0x40#64) 8 1336 (by decide),
      show sp + 0x40#64 = (sp + 0x38#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 0x38#64) 8 1344 (by decide),
      ← memRegion_split sp 0x38 1352 (by decide)]
  exact Entails.refl _

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA
