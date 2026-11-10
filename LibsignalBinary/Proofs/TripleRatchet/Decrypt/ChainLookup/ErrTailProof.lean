/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common
public import LibsignalBinary.Proofs.TripleRatchet.Getters.ClearUnacknowledgedPreKeyMessage
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailSym
import ProofLib.SepLogic.WPp

/-!
# `ErrTail` Error-Cleanup Contracts for `try_decrypt_with_state`

Proves `errTail_ok_ext`, `errTail_ok_x`, and relocatable `[LibsignalPlacement]` `ErrTail` contracts
(`+0x30c → +0x394 → +0x3b0`), writing the error result to `x.ret`, dropping `receiver_chains` and
`pqr_state`, and returning via the shared epilogue.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt

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
            trG.ratchet.chainsCap.toNat * 104 < 2 ^ 63 ∧ trG.ratchet.chainsPtr ≠ 0#64⌝ ∗
        (⌜tr.pqrState.length ≤ trG.pq.cap.toNat ∧ trG.pq.cap.toNat < 2 ^ 63 ∧ trG.pq.ptr ≠ 0#64⌝ ∗
         (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x38#64 + 8#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
          ((sp + 0x38#64 + 16#64) ↦₆₄ BitVec.ofNat 64 (trG.ratchet.chains.zip tr.ratchet.receiverChains).length) ∗
          (if trG.ratchet.chainsCap = 0#64 then emp
           else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
             arrayAt (chainAt A) 104 trG.ratchet.chainsPtr (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
             memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 ((trG.ratchet.chains.zip tr.ratchet.receiverChains).length * 104))
               ((trG.ratchet.chainsCap.toNat - (trG.ratchet.chains.zip tr.ratchet.receiverChains).length) * 104)) ∗
          ((sp + 0x38#64 + 24#64) ↦ₛ optSenderChainBytes tr.ratchet.senderChain trG.ratchet.senderPad) ∗
          ((sp + 0x38#64 + 128#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) ∗
          ((sp + 0x38#64 + 160#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
          ((sp + 0x38#64 + 168#64) ↦₃₂ tr.ratchet.previousCounter) ∗ memRegion (sp + 0x38#64 + 172#64) 4 ∗
          ((sp + 0x38#64 + 0xb0#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0x38#64 + 0xb0#64 + 8#64) ↦₆₄ trG.pq.ptr) ∗
          ((sp + 0x38#64 + 0xb0#64 + 16#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
          (if trG.pq.cap = 0#64 then emp
           else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ (trG.pq.ptr ↦ₛ tr.pqrState) ∗
             memRegion (trG.pq.ptr + BitVec.ofNat 64 tr.pqrState.length) (trG.pq.cap.toNat - tr.pqrState.length)) ∗
          ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
          ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗ R)) := by
    convert hm using 1; sep_ac_rfl
  rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hm_cs
  rcases hm_cs with ⟨⟨hcs_le, hcs_lt, hcs_ptr⟩, ⟨hpq_le, hpq_lt, hpq_ptr⟩, hm⟩
  refine ⟨hcs_le, hcs_lt, hcs_ptr, hpq_le, hpq_lt, hpq_ptr, ?_⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm
  have h50 :
      (((sp + 0x50#64) ↦ₛ optSenderChainBytes tr.ratchet.senderChain trG.ratchet.senderPad) ∗
       ((sp + 0xb8#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) ∗
       ((sp + 0xd8#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
       ((sp + 0xe0#64) ↦₃₂ tr.ratchet.previousCounter) ∗ memRegion (sp + 0xe4#64) 4) ⊢
      memRegion (sp + 0x50#64) 0x98 := by
    have hsc_len := optSenderChainBytes_length tr.ratchet.senderChain trG.ratchet.senderPad hpad
    have hrk_len : (keyToBytes32 tr.ratchet.rootKey).length = 32 := by simp [keyToBytes32]
    refine Entails.trans
      (sepConj_mono (hsc_len ▸ pointsToBytes_entails_memRegion _ _)
      (sepConj_mono (hrk_len ▸ pointsToBytes_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _) (Entails.refl _))))) ?_
    rw [show sp + 0xe4#64 = (sp + 0xe0#64) + 4#64 by bv_omega,
        ← memRegion_split (sp + 0xe0#64) 4 4 (by decide),
        show sp + 0xe0#64 = (sp + 0xd8#64) + 8#64 by bv_omega,
        ← memRegion_split (sp + 0xd8#64) 8 8 (by decide),
        show sp + 0xd8#64 = (sp + 0xb8#64) + 32#64 by bv_omega,
        ← memRegion_split (sp + 0xb8#64) 32 16 (by decide),
        show sp + 0xb8#64 = (sp + 0x50#64) + 104#64 by bv_omega,
        ← memRegion_split (sp + 0x50#64) 104 48 (by decide)]; exact Entails.refl _
  have hf8 :
      (((sp + 0xf8#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
       ((sp + 0x100#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
       ((sp + 0x120#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)) ⊢
      memRegion (sp + 0xf8#64) 0x48 := by
    have hloc_len : tr.localIdentityKey.publicKey.bytes.toList.length = 32 := List.Vector.toList_length _
    have hrem_len : tr.remoteIdentityKey.publicKey.bytes.toList.length = 32 := List.Vector.toList_length _
    refine Entails.trans
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (hloc_len ▸ pointsToBytes_entails_memRegion _ _)
        (hrem_len ▸ pointsToBytes_entails_memRegion _ _))) ?_
    rw [show sp + 0x120#64 = (sp + 0x100#64) + 32#64 by bv_omega,
        ← memRegion_split (sp + 0x100#64) 32 32 (by decide),
        show sp + 0x100#64 = (sp + 0xf8#64) + 8#64 by bv_omega,
        ← memRegion_split (sp + 0xf8#64) 8 64 (by decide)]; exact Entails.refl _
  have hcs_buf :
      (if trG.ratchet.chainsCap = 0#64 then emp
       else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
         memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 ((trG.ratchet.chains.zip tr.ratchet.receiverChains).length * 104))
           ((trG.ratchet.chainsCap.toNat - (trG.ratchet.chains.zip tr.ratchet.receiverChains).length) * 104)) ⊢
      arrayAt (chainAt A) 104 trG.ratchet.chainsPtr (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
      (if trG.ratchet.chainsCap = 0#64 then emp
       else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
         memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 ((trG.ratchet.chains.zip tr.ratchet.receiverChains).length * 104))
           ((trG.ratchet.chainsCap.toNat - (trG.ratchet.chains.zip tr.ratchet.receiverChains).length) * 104)) := by
    split
    · next hcap0 =>
      have hlen0 : (trG.ratchet.chains.zip tr.ratchet.receiverChains).length = 0 := by simpa [hcap0] using hcs_le
      rw [List.eq_nil_of_length_eq_zero hlen0, arrayAt, emp_sepConj]; exact Entails.refl _
    · have hcomm :
          (A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            arrayAt (chainAt A) 104 trG.ratchet.chainsPtr (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 ((trG.ratchet.chains.zip tr.ratchet.receiverChains).length * 104))
              ((trG.ratchet.chainsCap.toNat - (trG.ratchet.chains.zip tr.ratchet.receiverChains).length) * 104)) =
          (arrayAt (chainAt A) 104 trG.ratchet.chainsPtr (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
            (A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
             memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 ((trG.ratchet.chains.zip tr.ratchet.receiverChains).length * 104))
              ((trG.ratchet.chainsCap.toNat - (trG.ratchet.chains.zip tr.ratchet.receiverChains).length) * 104))) := by sep_ac_rfl
      rw [hcomm]; exact Entails.refl _
  have hpq_buf :
      (if trG.pq.cap = 0#64 then emp
       else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ (trG.pq.ptr ↦ₛ tr.pqrState) ∗
         memRegion (trG.pq.ptr + BitVec.ofNat 64 tr.pqrState.length) (trG.pq.cap.toNat - tr.pqrState.length)) ⊢
      (if trG.pq.cap = 0#64 then emp
       else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) := by
    split
    · exact Entails.refl _
    · refine sepConj_mono_right ?_
      refine Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion _ _)) ?_
      rw [← memRegion_split trG.pq.ptr tr.pqrState.length (trG.pq.cap.toNat - tr.pqrState.length) (by omega),
          Nat.add_sub_of_le hpq_le]; exact Entails.refl _
  have hm_re :
      m ⊨
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (trG.ratchet.chains.zip tr.ratchet.receiverChains).length) ∗
         (((sp + 0x50#64) ↦ₛ optSenderChainBytes tr.ratchet.senderChain trG.ratchet.senderPad) ∗
          ((sp + 0xb8#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) ∗
          ((sp + 0xd8#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
          ((sp + 0xe0#64) ↦₃₂ tr.ratchet.previousCounter) ∗ memRegion (sp + 0xe4#64) 4) ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
         (((sp + 0xf8#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
          ((sp + 0x100#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
          ((sp + 0x120#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)) ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            arrayAt (chainAt A) 104 trG.ratchet.chainsPtr (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 ((trG.ratchet.chains.zip tr.ratchet.receiverChains).length * 104))
              ((trG.ratchet.chainsCap.toNat - (trG.ratchet.chains.zip tr.ratchet.receiverChains).length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ (trG.pq.ptr ↦ₛ tr.pqrState) ∗
            memRegion (trG.pq.ptr + BitVec.ofNat 64 tr.pqrState.length) (trG.pq.cap.toNat - tr.pqrState.length))) ∗ R := by
    convert hm using 1; sep_ac_rfl
  have hm_out := Satisfies.mono
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono h50
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono hf8 (sepConj_mono hcs_buf hpq_buf))))))))) hm_re
  convert hm_out using 1; sep_ac_rfl


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

private theorem errTail_chains_re_entails {A : RustAlloc}
    {sp : BitVec 64} {S_in S_out : Nat} {R_rem : SepProp}
    (hstack : stackAt sp S_in = stackAt sp S_out ∗ R_rem)
    {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {w0 w1 w2 w3 w4 ret tag : BitVec 64}
    (hcs_le : (trG.ratchet.chains.zip tr.ratchet.receiverChains).length ≤ trG.ratchet.chainsCap.toNat)
    (hcs_lt : trG.ratchet.chainsCap.toNat * 104 < 2 ^ 63) :
    let cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
    (((memRegion trG.ratchet.chainsPtr (cs.length * 104) ∗ A.pool ∗ stackAt sp S_in) ∗
      (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
       ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
       ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
       words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
       (if trG.ratchet.chainsCap = 0#64 then emp
        else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
          memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
       (if trG.pq.cap = 0#64 then emp
        else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat)))) ⊢
    ((((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
      (if trG.ratchet.chainsCap = 0#64 then emp
       else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
         memRegion trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104)) ∗
      A.pool ∗ stackAt sp S_out) ∗
     (R_rem ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
      ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
      ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
      ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
      words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
      (if trG.pq.cap = 0#64 then emp
       else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat))) := by
  dsimp only; set cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
  rw [hstack]
  have hcomm1 :
      (((memRegion trG.ratchet.chainsPtr (cs.length * 104) ∗ A.pool ∗ (stackAt sp S_out ∗ R_rem)) ∗
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
         ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
         words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat)))) =
      (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       (memRegion trG.ratchet.chainsPtr (cs.length * 104) ∗
        (if trG.ratchet.chainsCap = 0#64 then emp
         else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
           memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104))) ∗
       (A.pool ∗ stackAt sp S_out ∗ R_rem ∗
        ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
        ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
        ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗ ((sp + 0x150#64) ↦₆₄ w2) ∗
        words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
        words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
        (if trG.pq.cap = 0#64 then emp
         else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat))) := by sep_ac_rfl
  have hcomm2 :
      ((((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
        (if trG.ratchet.chainsCap = 0#64 then emp
         else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
           memRegion trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104)) ∗
        A.pool ∗ stackAt sp S_out) ∗
       (R_rem ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
        ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
        ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
        ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
        words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
        (if trG.pq.cap = 0#64 then emp
         else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat))) =
      (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       (if trG.ratchet.chainsCap = 0#64 then emp
        else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
          memRegion trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104)) ∗
       (A.pool ∗ stackAt sp S_out ∗ R_rem ∗
        ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
        ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
        ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗ ((sp + 0x150#64) ↦₆₄ w2) ∗
        words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
        words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
        (if trG.pq.cap = 0#64 then emp
         else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat))) := by sep_ac_rfl
  rw [hcomm1, hcomm2]
  exact sepConj_mono_right (sepConj_mono_left (chains_recombine_entails hcs_le hcs_lt))

/-- `ErrTail` contract (`+0x30c → +0x394 → +0x3b0`): writes `speAt` to `x.ret`, drops
`tr.ratchet.receiver_chains` and `tr.pqr_state`, and executes the return epilogue. -/
theorem errTail_ok_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)} :
    ErrTailSpecExt img C A ctl uuidTryParse S ext := by
  intro himg hA hdrop x trG tr st1 e R s0 s he hmod1 hmod2 herr
  rcases herr with ⟨hpc, hmeta, hx19, hx20, hx26, hmem⟩
  have hmeta_wp : tryDecryptWPInv s0 s := tryDecryptMidMeta.to_wpInv hmeta
  let sp := s0.sp - 1504#64
  set draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
  set cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
  have hmem_tr :
      s.mem ⊨ trAt A (sp + 0x38#64) trG tr ∗
        (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗ speBodyAt A (utf8 "decrypt") (sp + 0x168#64) e ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
    dsimp only [sp]; convert hmem using 1; sep_ac_rfl
  obtain ⟨hcs_le, hcs_lt, _, _, _, _, hmem1⟩ := trAt_expose_errTail hmem_tr
  have hmem_spe :
      s.mem ⊨ speBodyAt A (utf8 "decrypt") (sp + 0x168#64) e ∗
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗ memRegion (sp + 0x190#64) 0x3f0 ∗
         tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
    dsimp only [sp] at hmem1 ⊢; convert hmem1 using 1; sep_ac_rfl
  obtain ⟨w0, w1, w2, w3, w4, H_spe, hmem2, hspe_ent⟩ := exists_words5_of_speBodyAt he hmem_spe
  have hmem_ret :
      s.mem ⊨ memRegion x.ret 48 ∗
        (words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion sp 0x38 ∗ memRegion (sp + 0x140#64) 0x28 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
    dsimp only [sp] at hmem2 ⊢; convert hmem2 using 1; sep_ac_rfl
  obtain ⟨r0, r1, r2, r3, r4, r5, hmem3⟩ := exists_words6_of_memRegion_48 hmem_ret
  have h140_split :
      memRegion (sp + 0x140#64) 0x28 = memRegion (sp + 0x140#64) 24 ∗ memRegion (sp + 0x158#64) 16 := by
    rw [show (0x28 : Nat) = 24 + 16 by decide, memRegion_split (sp + 0x140#64) 24 16 (by decide),
        show (sp + 0x140#64) + 24#64 = sp + 0x158#64 by simp only [BitVec.add_assoc, BitVec.reduceAdd]]
  have hmem_t :
      s.mem ⊨ memRegion (sp + 0x140#64) 24 ∗
        (memRegion (sp + 0x158#64) 16 ∗ (x.ret ↦₆₄ r0) ∗ words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗
         words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion sp 0x38 ∗ memRegion (sp + 0x190#64) 0x3f0 ∗
         tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
    rw [h140_split] at hmem3; dsimp only [sp] at hmem3 ⊢; convert hmem3 using 1; sep_ac_rfl
  obtain ⟨t0, t1, t2, hmem4⟩ := exists_words3_of_memRegion_24 hmem_t
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmem4
  have hwp :
      SepWP (tripleRatchetProgAtExt img.base ext) (retEpiloguePC img) s
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ t0) ∗ ((sp + 0x148#64) ↦₆₄ t1) ∗
         ((sp + 0x150#64) ↦₆₄ t2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (x.ret ↦₆₄ r0) ∗
         words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗ arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         A.pool ∗ stackAt sp dropChainStack)
        (fun sf P =>
          P = (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
               ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
               ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
               ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (x.ret ↦₆₄ speTag e) ∗
               words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ A.pool ∗ stackAt sp dropChainStack) ∧
          tryDecryptWPInv s0 sf) := by
    have hcopy := errTail_copy_spe_wp (img := img) (ext := ext)
      (chainsPtr := trG.ratchet.chainsPtr) (chainsLen := BitVec.ofNat 64 cs.length)
      (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
      (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
      (t0 := t0) (t1 := t1) (t2 := t2) himg hpc hmeta_wp hx19 hx20 hx26
    refine SepWP.bind_framed
      (F := ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
            (if trG.ratchet.chainsCap = 0#64 then emp
             else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
               memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
            A.pool ∗ stackAt sp dropChainStack) hcopy ?_ ?_
    · dsimp only [sp]; sep_ac_rfl
    intro s1 P1 ⟨hP1, hmeta1, hx20_1, hx21_1⟩ hpc1; subst hP1
    have hcs_lt' : cs.length * 104 < 2 ^ 63 := Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 104 hcs_le) hcs_lt
    have hdrop_cs := errTail_drop_chains_wp (img := img) (A := A) (ext := ext)
      himg hdrop hcs_lt' hpc1 hmeta1 hx20_1 hx21_1
    refine SepWP.bind_framed
      (F := ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
            ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
            ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (x.ret ↦₆₄ speTag e) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
            (if trG.ratchet.chainsCap = 0#64 then emp
             else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
               memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat)) hdrop_cs ?_ ?_
    · dsimp only [sp]; sep_ac_rfl
    intro s2 P2 ⟨hP2, hmeta2, hx20_2⟩ hpc2; subst hP2
    refine SepWP.mono_pre (errTail_chains_re_entails (stackAt_dropChainStack_sub sp) hcs_le hcs_lt) ?_
    have hdealloc_cs := errTail_dealloc_chains_wp (img := img) (A := A) (ext := ext)
      himg hA.toAllocContracts hcs_lt hpc2 hmeta2 hx20_2
    refine SepWP.bind_framed
      (F := memRegion (sp - 4144#64) 48 ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
            ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
            ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (x.ret ↦₆₄ speTag e) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat)) hdealloc_cs ?_ ?_
    · dsimp only [sp]
    intro s3 P3 ⟨hP3, hmeta3⟩ hpc3; subst hP3
    have hdealloc_pq := errTail_dealloc_pq_wp (img := img) (A := A) (ext := ext)
      (pqCap := trG.pq.cap) (pqPtr := trG.pq.ptr) himg hA.toAllocContracts hpc3 hmeta3
    refine SepWP.bind_framed
      (F := memRegion (sp - 4144#64) 48 ∗ ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
            ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗ ((sp + 0x150#64) ↦₆₄ w2) ∗
            words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (x.ret ↦₆₄ speTag e) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4) hdealloc_pq ?_ ?_
    · dsimp only [sp]; sep_ac_rfl
    intro sf Pf ⟨hPf, hmeta_f⟩ hpcf; subst hPf
    refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f⟩
    rw [stackAt_dropChainStack_sub sp]; dsimp only [sp]; sep_ac_rfl
  unfold tryDecryptCommonHeap at hmem4
  rw [stackAt_tryDecryptSubStack_sub s0.sp dropChainStack (by decide)] at hmem4
  have hmem_start :
      s.mem ⊨
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ t0) ∗ ((sp + 0x148#64) ↦₆₄ t1) ∗
         ((sp + 0x150#64) ↦₆₄ t2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (x.ret ↦₆₄ r0) ∗
         words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗ arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         A.pool ∗ stackAt sp dropChainStack) ∗
        (memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack) ∗ H_spe ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x50#64) 0x98 ∗ memRegion (sp + 0xf8#64) 0x48 ∗ memRegion (sp + 0x158#64) 16 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest draws ∗ logOff img ∗
         tryDecryptSavedRegs s0.sp s0 ∗ R) := by
    dsimp only [sp] at hmem4 ⊢; convert hmem4 using 1; sep_ac_rfl
  have hnpan : (x.model C S uuidTryParse).1 ≠ .error .panic := by
    rw [hmod1]; exact fun h => he (Except.error.inj h)
  have hG' : x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool x.G.afterTrFrom := by
    rw [hmod1]; exact decRel_afterTrFrom x.G
  apply reaches_epilogue_to_outcome himg x x.G.afterTrFrom R s0 s hnpan hG'
  refine reaches_pc_mono (sepWP_to_reaches_pc_midMeta hmeta hwp hmem_start) ?_
  intro sf _ _ ⟨Pf, hm_sf, hPf, hmeta_f⟩; subst hPf
  refine ⟨hmeta_f, ?_⟩
  unfold tryDecryptCommonHeap
  rw [hmod2, stackAt_tryDecryptSubStack_sub s0.sp dropChainStack (by decide)]
  have hdec_ent :
      ((x.ret ↦₆₄ speTag e) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ⊢
      vecResultAt A x.ret (x.model C S uuidTryParse).1 := by
    rw [hmod1]; exact hspe_ent x.ret
  have hmem_f_re :
      sf.mem ⊨
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         ((x.ret ↦₆₄ speTag e) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ∗
         (memRegion sp 0x38 ∗ ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
          ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
          memRegion (sp + 0x50#64) 0x98 ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
          ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗ ((sp + 0x150#64) ↦₆₄ w2) ∗
          memRegion (sp + 0x158#64) 16 ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
          memRegion (sp + 0x190#64) 0x3f0) ∗
         (protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest draws ∗ logOff img ∗
          (stackAt sp dropChainStack ∗ memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack)) ∗
          tryDecryptSavedRegs s0.sp s0 ∗ A.pool) ∗ R := by
    dsimp only [sp] at hm_sf ⊢; convert hm_sf using 1; sep_ac_rfl
  exact Satisfies.mono
    (sepConj_mono_right (sepConj_mono hdec_ent (sepConj_mono_left
      (errTail_stack_recombine sp trG.ratchet.chainsCap trG.ratchet.chainsPtr
        (BitVec.ofNat 64 cs.length) trG.pq.cap trG.pq.ptr w0 w1 w2 w3 w4)))) hmem_f_re

theorem errTail_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)} :
    ErrTailSpec img C A ctl uuidTryParse S abs :=
  fun himg hH hdrop => errTail_ok_ext himg (Stage2Contracts.of_tripleRatchetProgAt img.base C A ctl S abs hH) hdrop

/-- `Stage2ContractsX` `ErrTail` contract (`+0x30c → +0x394 → +0x3b0`): writes `decResultFnAt` to
`x.ret`, drops `tr.ratchet.receiver_chains` and `tr.pqr_state`, and executes the return epilogue. -/
theorem errTail_ok_x {img : Obj.Image} {C : Crypto}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)} :
    ErrTailSpecX img C encFn decFn A ctl uuidTryParse S ext := by
  intro himg hA hdrop x trG tr st1 e R s0 s he hmod1 hmod2 herr
  rcases herr with ⟨hpc, hmeta, hx19, hx20, b, hb, hx26, hmem⟩
  have hmeta_wp : tryDecryptWPInv s0 s := tryDecryptMidMeta.to_wpInv hmeta
  have hinv : img.FrozenLoaded s ∧ s.symtab = img.symtab :=
    ⟨hmeta.2.2.2.2.2.2.1, hmeta.2.2.2.2.2.2.2.1⟩
  let sp := s0.sp - 1504#64
  set draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
  set cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
  set tag := if b then speTag e else speWord 20
  have hmem_tr :
      s.mem ⊨ trAt A (sp + 0x38#64) trG tr ∗
        (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗
         (if b then speBodyAt A (utf8 "decrypt") (sp + 0x168#64) e else memRegion (sp + 0x168#64) 40) ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
    dsimp only [sp]; convert hmem using 1; sep_ac_rfl
  obtain ⟨hcs_le, hcs_lt, _, _, hpq_lt, _, hmem1⟩ := trAt_expose_errTail hmem_tr
  have hmem_spe :
      s.mem ⊨ (if b then speBodyAt A (utf8 "decrypt") (sp + 0x168#64) e else memRegion (sp + 0x168#64) 40) ∗
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗ memRegion (sp + 0x190#64) 0x3f0 ∗
         tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
    dsimp only [sp] at hmem1 ⊢; convert hmem1 using 1; sep_ac_rfl
  obtain ⟨w0, w1, w2, w3, w4, H_spe, hmem2, hspe_ent⟩ := exists_words5_of_errTailBody he hb hmem_spe
  have hmem_ret :
      s.mem ⊨ memRegion x.ret 48 ∗
        (words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion sp 0x38 ∗ memRegion (sp + 0x140#64) 0x28 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
    dsimp only [sp] at hmem2 ⊢; convert hmem2 using 1; sep_ac_rfl
  obtain ⟨r0, r1, r2, r3, r4, r5, hmem3⟩ := exists_words6_of_memRegion_48 hmem_ret
  have h140_split :
      memRegion (sp + 0x140#64) 0x28 = memRegion (sp + 0x140#64) 24 ∗ memRegion (sp + 0x158#64) 16 := by
    rw [show (0x28 : Nat) = 24 + 16 by decide, memRegion_split (sp + 0x140#64) 24 16 (by decide),
        show (sp + 0x140#64) + 24#64 = sp + 0x158#64 by simp only [BitVec.add_assoc, BitVec.reduceAdd]]
  have hmem_t :
      s.mem ⊨ memRegion (sp + 0x140#64) 24 ∗
        (memRegion (sp + 0x158#64) 16 ∗ (x.ret ↦₆₄ r0) ∗ words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗
         words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion sp 0x38 ∗ memRegion (sp + 0x190#64) 0x3f0 ∗
         tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
    rw [h140_split] at hmem3; dsimp only [sp] at hmem3 ⊢; convert hmem3 using 1; sep_ac_rfl
  obtain ⟨t0, t1, t2, hmem4⟩ := exists_words3_of_memRegion_24 hmem_t
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmem4
  have hwp :
      SepWP (tripleRatchetProgAtExt img.base ext) (retEpiloguePC img) s
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ t0) ∗ ((sp + 0x148#64) ↦₆₄ t1) ∗
         ((sp + 0x150#64) ↦₆₄ t2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (x.ret ↦₆₄ r0) ∗
         words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗ arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         A.pool ∗ stackAt sp dropChainStackX)
        (fun sf P =>
          P = (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
               ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
               ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
               ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (x.ret ↦₆₄ tag) ∗
               words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ A.pool ∗ stackAt sp dropChainStackX) ∧
          tryDecryptWPInv s0 sf) := by
    have hcopy := errTail_copy_spe_wp (img := img) (ext := ext)
      (chainsPtr := trG.ratchet.chainsPtr) (chainsLen := BitVec.ofNat 64 cs.length)
      (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
      (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
      (t0 := t0) (t1 := t1) (t2 := t2) himg hpc hmeta_wp hx19 hx20 hx26
    refine SepWP.bind_framed_callInv
      (F := ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
            (if trG.ratchet.chainsCap = 0#64 then emp
             else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
               memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
            A.pool ∗ stackAt sp dropChainStackX) hinv hcopy ?_ ?_
    · dsimp only [sp]; sep_ac_rfl
    intro s1 P1 ⟨hP1, hmeta1, hx20_1, hx21_1⟩ hpc1 hinv1; subst hP1
    have hcs_lt' : cs.length * 104 < 2 ^ 63 := Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 104 hcs_le) hcs_lt
    have hdrop_cs := errTail_drop_chains_x_wp (img := img) (A := A) (ext := ext)
      himg hdrop hcs_lt' hpc1 hmeta1 hinv1 hx20_1 hx21_1
    refine SepWP.bind_framed_callInv
      (F := ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
            ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
            ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (x.ret ↦₆₄ tag) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
            (if trG.ratchet.chainsCap = 0#64 then emp
             else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
               memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat)) hinv1 hdrop_cs ?_ ?_
    · dsimp only [sp]; sep_ac_rfl
    intro s2 P2 ⟨hP2, hmeta2, hx20_2⟩ hpc2 hinv2; subst hP2
    refine SepWP.mono_pre (errTail_chains_re_entails (stackAt_dropChainStackX_sub sp) hcs_le hcs_lt) ?_
    have hdealloc_cs := errTail_dealloc_chains_x_wp (img := img) (A := A) (ext := ext)
      himg hA.toAllocContractsX hcs_lt hpc2 hmeta2 hinv2 hx20_2
    refine SepWP.bind_framed_callInv
      (F := memRegion (sp - 16432#64) 48 ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
            ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
            ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (x.ret ↦₆₄ tag) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat)) hinv2 hdealloc_cs ?_ ?_
    · dsimp only [sp]
    intro s3 P3 ⟨hP3, hmeta3⟩ hpc3 hinv3; subst hP3
    have hdealloc_pq := errTail_dealloc_pq_x_wp (img := img) (A := A) (ext := ext)
      (pqCap := trG.pq.cap) (pqPtr := trG.pq.ptr) himg hA.toAllocContractsX hpq_lt hpc3 hmeta3 hinv3
    refine SepWP.bind_framed
      (F := memRegion (sp - 16432#64) 48 ∗ ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
            ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗ ((sp + 0x150#64) ↦₆₄ w2) ∗
            words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (x.ret ↦₆₄ tag) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4) hdealloc_pq ?_ ?_
    · dsimp only [sp]; sep_ac_rfl
    intro sf Pf ⟨hPf, hmeta_f⟩ hpcf; subst hPf
    refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f⟩
    rw [stackAt_dropChainStackX_sub sp]; dsimp only [sp]; sep_ac_rfl
  unfold tryDecryptCommonHeap at hmem4
  rw [stackAt_tryDecryptSubStack_sub s0.sp dropChainStackX (by decide)] at hmem4
  have hmem_start :
      s.mem ⊨
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ t0) ∗ ((sp + 0x148#64) ↦₆₄ t1) ∗
         ((sp + 0x150#64) ↦₆₄ t2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (x.ret ↦₆₄ r0) ∗
         words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗ arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         A.pool ∗ stackAt sp dropChainStackX) ∗
        (memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStackX) ∗ H_spe ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x50#64) 0x98 ∗ memRegion (sp + 0xf8#64) 0x48 ∗ memRegion (sp + 0x158#64) 16 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest draws ∗ logOff img ∗
         tryDecryptSavedRegs s0.sp s0 ∗ R) := by
    dsimp only [sp] at hmem4 ⊢; convert hmem4 using 1; sep_ac_rfl
  have hnpan : (x.modelFn C decFn S uuidTryParse).1 ≠ .error .panic := by
    rw [hmod1]; exact fun h => he (Except.error.inj h)
  have hG' : x.G.AfterTryDecrypt (x.modelFn C decFn S uuidTryParse).1.toBool x.G.afterTrFrom := by
    rw [hmod1]; exact decRel_afterTrFrom x.G
  apply reaches_epilogue_to_outcome_fn himg x x.G.afterTrFrom R s0 s hnpan hG'
  refine reaches_pc_mono (sepWP_to_reaches_pc_midMeta hmeta hwp hmem_start) ?_
  intro sf _ _ ⟨Pf, hm_sf, hPf, hmeta_f⟩; subst hPf
  refine ⟨hmeta_f, ?_⟩
  unfold tryDecryptCommonHeap
  rw [hmod2, stackAt_tryDecryptSubStack_sub s0.sp dropChainStackX (by decide)]
  have hdec_ent :
      ((x.ret ↦₆₄ tag) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ⊢
      decResultFnAt A x.ret (x.modelFn C decFn S uuidTryParse).1 := by
    rw [hmod1]; exact hspe_ent x.ret
  have hmem_f_re :
      sf.mem ⊨
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         ((x.ret ↦₆₄ tag) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ∗
         (memRegion sp 0x38 ∗ ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
          ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
          memRegion (sp + 0x50#64) 0x98 ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
          ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗ ((sp + 0x150#64) ↦₆₄ w2) ∗
          memRegion (sp + 0x158#64) 16 ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
          memRegion (sp + 0x190#64) 0x3f0) ∗
         (protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest draws ∗ logOff img ∗
          (stackAt sp dropChainStackX ∗ memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStackX)) ∗
          tryDecryptSavedRegs s0.sp s0 ∗ A.pool) ∗ R := by
    dsimp only [sp] at hm_sf ⊢; convert hm_sf using 1; sep_ac_rfl
  exact Satisfies.mono
    (sepConj_mono_right (sepConj_mono hdec_ent (sepConj_mono_left
      (errTail_stack_recombine sp trG.ratchet.chainsCap trG.ratchet.chainsPtr
        (BitVec.ofNat 64 cs.length) trG.pq.cap trG.pq.ptr w0 w1 w2 w3 w4)))) hmem_f_re

/-! ## Multi-Placed (`[LibsignalPlacement]`) `ErrTail` Contracts -/

theorem errTail_all_steps_wp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    {ret tag : BitVec 64} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {w0 w1 w2 w3 w4 r0 r1 r2 r3 r4 r5 t0 t1 t2 : BitVec 64} {s0 s : State}
    (hcs_le : (trG.ratchet.chains.zip tr.ratchet.receiverChains).length ≤ trG.ratchet.chainsCap.toNat)
    (hcs_lt : trG.ratchet.chainsCap.toNat * 104 < 2 ^ 63)
    (hpc : s.pc = errTailPC_placed)
    (hmeta : tryDecryptWPInv s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx26 : s.readReg64 .x26 = tag) :
    let sp := s0.sp - 1504#64
    let cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
    SepWP ((blkPC_131).rebase (blkPl_131).base H) retEpiloguePC_placed s
      (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
       ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ t0) ∗ ((sp + 0x148#64) ↦₆₄ t1) ∗
       ((sp + 0x150#64) ↦₆₄ t2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ r0) ∗
       words5At (ret + 8#64) r1 r2 r3 r4 r5 ∗ arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
       (if trG.ratchet.chainsCap = 0#64 then emp
        else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
          memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
       (if trG.pq.cap = 0#64 then emp
        else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
       A.pool ∗ stackAt sp dropChainStack)
      (fun sf P =>
        P = (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
             ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
             ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
             ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
             words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗ A.pool ∗ stackAt sp dropChainStack) ∧
        tryDecryptWPInv s0 sf) := by
  dsimp only; let sp := s0.sp - 1504#64; set cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
  have hcopy := errTail_copy_spe_wp_placed (H := H)
    (chainsPtr := trG.ratchet.chainsPtr) (chainsLen := BitVec.ofNat 64 cs.length)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
    (t0 := t0) (t1 := t1) (t2 := t2) hpc hmeta hx19 hx20 hx26
  refine SepWP.bind_framed_lscl
    (F := ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
          (if trG.ratchet.chainsCap = 0#64 then emp
           else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
             memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
          (if trG.pq.cap = 0#64 then emp
           else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
          A.pool ∗ stackAt sp dropChainStack) hcl hcopy ?_ ?_
  · dsimp only [sp]; sep_ac_rfl
  intro s1 P1 ⟨hP1, hmeta1, hx20_1, hx21_1⟩ hpc1 hcl1; subst hP1
  have hcs_lt' : cs.length * 104 < 2 ^ 63 := Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 104 hcs_le) hcs_lt
  have hdrop_cs := errTail_drop_chains_wp_placed (A := A) (H := H)
    hdealloc hcs_lt' hpc1 hmeta1 hcl1 hx20_1 hx21_1
  refine SepWP.bind_framed
    (F := ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
          ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
          ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
          words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
          (if trG.ratchet.chainsCap = 0#64 then emp
           else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
             memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
          (if trG.pq.cap = 0#64 then emp
           else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat)) hdrop_cs ?_ ?_
  · dsimp only [sp]; sep_ac_rfl
  intro s2 P2 ⟨hP2, hmeta2, hx20_2⟩ hpc2; subst hP2
  refine SepWP.mono_pre (errTail_chains_re_entails (stackAt_dropChainStack_sub sp) hcs_le hcs_lt) ?_
  have hdealloc_cs := errTail_dealloc_chains_wp_placed (A := A) (H := H)
    hdealloc hcs_lt hpc2 hmeta2 hx20_2
  refine SepWP.bind_framed
    (F := memRegion (sp - 4144#64) 48 ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
          ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗
          ((sp + 0x150#64) ↦₆₄ w2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
          words5At (ret + 8#64) w0 w1 w2 w3 w4 ∗
          (if trG.pq.cap = 0#64 then emp
           else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat)) hdealloc_cs ?_ ?_
  · dsimp only [sp]
  intro s3 P3 ⟨hP3, hmeta3⟩ hpc3; subst hP3
  have hdealloc_pq := errTail_dealloc_pq_wp_placed (A := A) (H := H)
    (pqCap := trG.pq.cap) (pqPtr := trG.pq.ptr) hdealloc hpc3 hmeta3
  refine SepWP.bind_framed
    (F := memRegion (sp - 4144#64) 48 ∗ ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
          ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
          ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗ ((sp + 0x150#64) ↦₆₄ w2) ∗
          words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (ret ↦₆₄ tag) ∗
          words5At (ret + 8#64) w0 w1 w2 w3 w4) hdealloc_pq ?_ ?_
  · dsimp only [sp]; sep_ac_rfl
  intro sf Pf ⟨hPf, hmeta_f⟩ hpcf; subst hPf
  refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f⟩
  rw [stackAt_dropChainStack_sub sp]; dsimp only [sp]; sep_ac_rfl

theorem errTail_placed_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
    (R : SepProp) (s0 s : State)
    (he : e ≠ .panic)
    (hmod1 : (x.model C S uuidTryParse).1 = .error e)
    (hmod2 : (x.model C S uuidTryParse).2 = st1)
    (herr : ErrTailState_placed A ctl x trG tr st1 e
      (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s) :
    reaches_outcome ((blkPC_131).rebase (blkPl_131).base H)
      (tryDecryptSpec C A ctl uuidTryParse S tryDecryptDummyImg) x R s0 s := by
  rcases herr with ⟨hpc, hmeta, hx19, hx20, hx26, hmem⟩
  have hmeta_wp : tryDecryptWPInv s0 s := tryDecryptMidMeta_placed.to_wpInv hmeta
  have hcl : LibsignalCodeLoaded lsmpl s.mem := hmeta.2.2.2.2.2.2.1
  let sp := s0.sp - 1504#64
  set draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
  set cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
  have hmem_tr :
      s.mem ⊨ trAt A (sp + 0x38#64) trG tr ∗
        (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗ speBodyAt A (utf8 "decrypt") (sp + 0x168#64) e ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ tryDecryptCommonHeap A ctl tryDecryptDummyImg x draws s0 ∗ R) := by
    dsimp only [sp]; convert hmem using 1; sep_ac_rfl
  obtain ⟨hcs_le, hcs_lt, _, _, _, _, hmem1⟩ := trAt_expose_errTail hmem_tr
  have hmem_spe :
      s.mem ⊨ speBodyAt A (utf8 "decrypt") (sp + 0x168#64) e ∗
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗ memRegion (sp + 0x190#64) 0x3f0 ∗
         tryDecryptCommonHeap A ctl tryDecryptDummyImg x draws s0 ∗ R) := by
    dsimp only [sp] at hmem1 ⊢; convert hmem1 using 1; sep_ac_rfl
  obtain ⟨w0, w1, w2, w3, w4, H_spe, hmem2, hspe_ent⟩ := exists_words5_of_speBodyAt he hmem_spe
  have hmem_ret :
      s.mem ⊨ memRegion x.ret 48 ∗
        (words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion sp 0x38 ∗ memRegion (sp + 0x140#64) 0x28 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ tryDecryptCommonHeap A ctl tryDecryptDummyImg x draws s0 ∗ R) := by
    dsimp only [sp] at hmem2 ⊢; convert hmem2 using 1; sep_ac_rfl
  obtain ⟨r0, r1, r2, r3, r4, r5, hmem3⟩ := exists_words6_of_memRegion_48 hmem_ret
  have h140_split :
      memRegion (sp + 0x140#64) 0x28 = memRegion (sp + 0x140#64) 24 ∗ memRegion (sp + 0x158#64) 16 := by
    rw [show (0x28 : Nat) = 24 + 16 by decide, memRegion_split (sp + 0x140#64) 24 16 (by decide),
        show (sp + 0x140#64) + 24#64 = sp + 0x158#64 by simp only [BitVec.add_assoc, BitVec.reduceAdd]]
  have hmem_t :
      s.mem ⊨ memRegion (sp + 0x140#64) 24 ∗
        (memRegion (sp + 0x158#64) 16 ∗ (x.ret ↦₆₄ r0) ∗ words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗
         words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion sp 0x38 ∗ memRegion (sp + 0x190#64) 0x3f0 ∗
         tryDecryptCommonHeap A ctl tryDecryptDummyImg x draws s0 ∗ R) := by
    rw [h140_split] at hmem3; dsimp only [sp] at hmem3 ⊢; convert hmem3 using 1; sep_ac_rfl
  obtain ⟨t0, t1, t2, hmem4⟩ := exists_words3_of_memRegion_24 hmem_t
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmem4
  have hwp := errTail_all_steps_wp_placed (A := A) (H := H)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
    (t0 := t0) (t1 := t1) (t2 := t2)
    hdealloc hcs_le hcs_lt hpc hmeta_wp hcl hx19 hx20 hx26
  unfold tryDecryptCommonHeap at hmem4
  rw [stackAt_tryDecryptSubStack_sub s0.sp dropChainStack (by decide)] at hmem4
  have hmem_start :
      s.mem ⊨
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ t0) ∗ ((sp + 0x148#64) ↦₆₄ t1) ∗
         ((sp + 0x150#64) ↦₆₄ t2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (x.ret ↦₆₄ r0) ∗
         words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗ arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         A.pool ∗ stackAt sp dropChainStack) ∗
        (memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack) ∗ H_spe ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x50#64) 0x98 ∗ memRegion (sp + 0xf8#64) 0x48 ∗ memRegion (sp + 0x158#64) 16 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest draws ∗ logOff tryDecryptDummyImg ∗
         tryDecryptSavedRegs s0.sp s0 ∗ R) := by
    dsimp only [sp] at hmem4 ⊢; convert hmem4 using 1; sep_ac_rfl
  have hnpan : (x.model C S uuidTryParse).1 ≠ .error .panic := by
    rw [hmod1]; exact fun h => he (Except.error.inj h)
  have hG' : x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool x.G.afterTrFrom := by
    rw [hmod1]; exact decRel_afterTrFrom x.G
  apply reaches_epilogue_to_outcome_placed x x.G.afterTrFrom R s0 s hnpan hG'
  refine reaches_pc_mono (sepWP_to_reaches_pc_midMeta_placed hmeta hwp hmem_start) ?_
  intro sf _ _ ⟨Pf, hm_sf, hPf, hmeta_f⟩; subst hPf
  refine ⟨hmeta_f, ?_⟩
  unfold tryDecryptCommonHeap
  rw [hmod2, stackAt_tryDecryptSubStack_sub s0.sp dropChainStack (by decide)]
  have hdec_ent :
      ((x.ret ↦₆₄ speTag e) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ⊢
      vecResultAt A x.ret (x.model C S uuidTryParse).1 := by
    rw [hmod1]; exact hspe_ent x.ret
  have hmem_f_re :
      sf.mem ⊨
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         ((x.ret ↦₆₄ speTag e) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ∗
         (memRegion sp 0x38 ∗ ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
          ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
          memRegion (sp + 0x50#64) 0x98 ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
          ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗ ((sp + 0x150#64) ↦₆₄ w2) ∗
          memRegion (sp + 0x158#64) 16 ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
          memRegion (sp + 0x190#64) 0x3f0) ∗
         (protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest draws ∗ logOff tryDecryptDummyImg ∗
          (stackAt sp dropChainStack ∗ memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack)) ∗
          tryDecryptSavedRegs s0.sp s0 ∗ A.pool) ∗ R := by
    dsimp only [sp] at hm_sf ⊢; convert hm_sf using 1; sep_ac_rfl
  exact Satisfies.mono
    (sepConj_mono_right (sepConj_mono hdec_ent (sepConj_mono_left
      (errTail_stack_recombine sp trG.ratchet.chainsCap trG.ratchet.chainsPtr
        (BitVec.ofNat 64 cs.length) trG.pq.cap trG.pq.ptr w0 w1 w2 w3 w4)))) hmem_f_re

theorem errTail_placed_ok_x [LibsignalPlacement] {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
    (R : SepProp) (s0 s : State)
    (he : e ≠ .panic)
    (hmod1 : (x.modelFn C decFn S uuidTryParse).1 = .error e)
    (hmod2 : (x.modelFn C decFn S uuidTryParse).2 = st1)
    (herr : ErrTailStateX_placed A ctl x trG tr st1 e
      (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s) :
    reaches_outcome ((blkPC_131).rebase (blkPl_131).base H)
      (tryDecryptFnSpec C decFn A ctl uuidTryParse S tryDecryptDummyImg) x R s0 s := by
  rcases herr with ⟨hpc, hmeta, hx19, hx20, b, hb, hx26, hmem⟩
  have hmeta_wp : tryDecryptWPInv s0 s := tryDecryptMidMeta_placed.to_wpInv hmeta
  have hcl : LibsignalCodeLoaded lsmpl s.mem := hmeta.2.2.2.2.2.2.1
  let sp := s0.sp - 1504#64
  set draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
  set cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
  set tag := if b then speTag e else speWord 20
  have hmem_tr :
      s.mem ⊨ trAt A (sp + 0x38#64) trG tr ∗
        (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗
         (if b then speBodyAt A (utf8 "decrypt") (sp + 0x168#64) e else memRegion (sp + 0x168#64) 40) ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ tryDecryptCommonHeap A ctl tryDecryptDummyImg x draws s0 ∗ R) := by
    dsimp only [sp]; convert hmem using 1; sep_ac_rfl
  obtain ⟨hcs_le, hcs_lt, _, _, _, _, hmem1⟩ := trAt_expose_errTail hmem_tr
  have hmem_spe :
      s.mem ⊨ (if b then speBodyAt A (utf8 "decrypt") (sp + 0x168#64) e else memRegion (sp + 0x168#64) 40) ∗
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗ memRegion (sp + 0x190#64) 0x3f0 ∗
         tryDecryptCommonHeap A ctl tryDecryptDummyImg x draws s0 ∗ R) := by
    dsimp only [sp] at hmem1 ⊢; convert hmem1 using 1; sep_ac_rfl
  obtain ⟨w0, w1, w2, w3, w4, H_spe, hmem2, hspe_ent⟩ := exists_words5_of_errTailBody he hb hmem_spe
  have hmem_ret :
      s.mem ⊨ memRegion x.ret 48 ∗
        (words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion sp 0x38 ∗ memRegion (sp + 0x140#64) 0x28 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ tryDecryptCommonHeap A ctl tryDecryptDummyImg x draws s0 ∗ R) := by
    dsimp only [sp] at hmem2 ⊢; convert hmem2 using 1; sep_ac_rfl
  obtain ⟨r0, r1, r2, r3, r4, r5, hmem3⟩ := exists_words6_of_memRegion_48 hmem_ret
  have h140_split :
      memRegion (sp + 0x140#64) 0x28 = memRegion (sp + 0x140#64) 24 ∗ memRegion (sp + 0x158#64) 16 := by
    rw [show (0x28 : Nat) = 24 + 16 by decide, memRegion_split (sp + 0x140#64) 24 16 (by decide),
        show (sp + 0x140#64) + 24#64 = sp + 0x158#64 by simp only [BitVec.add_assoc, BitVec.reduceAdd]]
  have hmem_t :
      s.mem ⊨ memRegion (sp + 0x140#64) 24 ∗
        (memRegion (sp + 0x158#64) 16 ∗ (x.ret ↦₆₄ r0) ∗ words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗
         words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion sp 0x38 ∗ memRegion (sp + 0x190#64) 0x3f0 ∗
         tryDecryptCommonHeap A ctl tryDecryptDummyImg x draws s0 ∗ R) := by
    rw [h140_split] at hmem3; dsimp only [sp] at hmem3 ⊢; convert hmem3 using 1; sep_ac_rfl
  obtain ⟨t0, t1, t2, hmem4⟩ := exists_words3_of_memRegion_24 hmem_t
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmem4
  have hwp := errTail_all_steps_wp_placed (A := A) (H := H)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
    (t0 := t0) (t1 := t1) (t2 := t2)
    hdealloc hcs_le hcs_lt hpc hmeta_wp hcl hx19 hx20 hx26
  unfold tryDecryptCommonHeap at hmem4
  rw [stackAt_tryDecryptSubStack_sub s0.sp dropChainStack (by decide)] at hmem4
  have hmem_start :
      s.mem ⊨
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ t0) ∗ ((sp + 0x148#64) ↦₆₄ t1) ∗
         ((sp + 0x150#64) ↦₆₄ t2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (x.ret ↦₆₄ r0) ∗
         words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗ arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         A.pool ∗ stackAt sp dropChainStack) ∗
        (memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack) ∗ H_spe ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x50#64) 0x98 ∗ memRegion (sp + 0xf8#64) 0x48 ∗ memRegion (sp + 0x158#64) 16 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest draws ∗ logOff tryDecryptDummyImg ∗
         tryDecryptSavedRegs s0.sp s0 ∗ R) := by
    dsimp only [sp] at hmem4 ⊢; convert hmem4 using 1; sep_ac_rfl
  have hnpan : (x.modelFn C decFn S uuidTryParse).1 ≠ .error .panic := by
    rw [hmod1]; exact fun h => he (Except.error.inj h)
  have hG' : x.G.AfterTryDecrypt (x.modelFn C decFn S uuidTryParse).1.toBool x.G.afterTrFrom := by
    rw [hmod1]; exact decRel_afterTrFrom x.G
  apply reaches_epilogue_to_outcome_fn_placed x x.G.afterTrFrom R s0 s hnpan hG'
  refine reaches_pc_mono (sepWP_to_reaches_pc_midMeta_placed hmeta hwp hmem_start) ?_
  intro sf _ _ ⟨Pf, hm_sf, hPf, hmeta_f⟩; subst hPf
  refine ⟨hmeta_f, ?_⟩
  unfold tryDecryptCommonHeap
  rw [hmod2, stackAt_tryDecryptSubStack_sub s0.sp dropChainStack (by decide)]
  have hdec_ent :
      ((x.ret ↦₆₄ tag) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ⊢
      decResultFnAt A x.ret (x.modelFn C decFn S uuidTryParse).1 := by
    rw [hmod1]; exact hspe_ent x.ret
  have hmem_f_re :
      sf.mem ⊨
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         ((x.ret ↦₆₄ tag) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ∗
         (memRegion sp 0x38 ∗ ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
          ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
          memRegion (sp + 0x50#64) 0x98 ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
          ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗ ((sp + 0x150#64) ↦₆₄ w2) ∗
          memRegion (sp + 0x158#64) 16 ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
          memRegion (sp + 0x190#64) 0x3f0) ∗
         (protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest draws ∗ logOff tryDecryptDummyImg ∗
          (stackAt sp dropChainStack ∗ memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack)) ∗
          tryDecryptSavedRegs s0.sp s0 ∗ A.pool) ∗ R := by
    dsimp only [sp] at hm_sf ⊢; convert hm_sf using 1; sep_ac_rfl
  exact Satisfies.mono
    (sepConj_mono_right (sepConj_mono hdec_ent (sepConj_mono_left
      (errTail_stack_recombine sp trG.ratchet.chainsCap trG.ratchet.chainsPtr
        (BitVec.ofNat 64 cs.length) trG.pq.cap trG.pq.ptr w0 w1 w2 w3 w4)))) hmem_f_re

end CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
