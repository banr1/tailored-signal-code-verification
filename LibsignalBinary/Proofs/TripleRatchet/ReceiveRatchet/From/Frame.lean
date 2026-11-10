/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.Defs
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WPp

/-!
# Frame and Session Exposure Helpers for `TripleRatchet::from_session_state`

SessionState and sender-chain spatial exposure/reassembly lemmas and 496-byte stack frame
decompositions for `<TripleRatchet>::from_session_state` (`0x1c60c`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Getters
open ProofLib.ProgramReflection

namespace ReceiveRatchetFrom

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem exists_chainKey_split_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (d0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
      (w23 : BitVec 64) (b31 : BitVec 8),
      (∀ a : BitVec 64,
        (a ↦ₛ bs) =
          ((a ↦₃₂ d0) ∗
           ((a + 4#64) ↦₁₆ (b5 ++ b4)) ∗
           ((a + 6#64) ↦₈ b6) ∗
           ((a + 7#64) ↦₆₄ (b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7)) ∗
           ((a + 15#64) ↦₆₄ (b22 ++ b21 ++ b20 ++ b19 ++ b18 ++ b17 ++ b16 ++ b15)) ∗
           ((a + 23#64) ↦₆₄ w23) ∗
           ((a + 31#64) ↦₈ b31))) ∧
      (∀ a : BitVec 64,
        (a ↦ₛ bs) =
          ((a ↦₃₂ d0) ∗
           ((a + 4#64) ↦₆₄ (b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6 ++ b5 ++ b4)) ∗
           ((a + 12#64) ↦₁₆ (b13 ++ b12)) ∗
           ((a + 14#64) ↦₈ b14) ∗
           ((a + 15#64) ↦₃₂ (b18 ++ b17 ++ b16 ++ b15)) ∗
           ((a + 19#64) ↦₈ b19) ∗
           ((a + 20#64) ↦₁₆ (b21 ++ b20)) ∗
           ((a + 22#64) ↦₈ b22) ∗
           ((a + 23#64) ↦₆₄ w23) ∗
           ((a + 31#64) ↦₈ b31))) := by
  obtain ⟨u0, u1, u2, u3, _, hp⟩ := exists_unpack64_of_length_32 h
  rcases exists_bytes_of_bv64 u0 with ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩
  rcases exists_bytes_of_bv64 u1 with ⟨b8, b9, b10, b11, b12, b13, b14, b15, rfl⟩
  rcases exists_bytes_of_bv64 u2 with ⟨b16, b17, b18, b19, b20, b21, b22, b23, rfl⟩
  rcases exists_bytes_of_bv64 u3 with ⟨b24, b25, b26, b27, b28, b29, b30, b31, rfl⟩
  refine ⟨b3 ++ b2 ++ b1 ++ b0, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
    b15, b16, b17, b18, b19, b20, b21, b22,
    b30 ++ b29 ++ b28 ++ b27 ++ b26 ++ b25 ++ b24 ++ b23,
    b31, fun a => ?_, fun a => ?_⟩
  · rw [hp]
    simp only [pointsTo64_eq_bytes8, pointsTo32_eq_bytes4, pointsTo16_eq_bytes2,
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  · rw [hp]
    simp only [pointsTo64_eq_bytes8, pointsTo32_eq_bytes4, pointsTo16_eq_bytes2,
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

def sessionFromFrame (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : SepProp :=
  ⌜(match st.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
    G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧
    (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
  vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
  vecGhostAt A G.alice (ss + 0x60#64) ∗
  optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
  optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
  ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗
  ((ss + 0x150#64) ↦ₛ G.regIds)

theorem vecAt_nil_chains_0_8 (A : RustAlloc) (v : BitVec 64) :
    ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 8#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) ⊢
      vecAt A 104 8 (chainAt A) v 0#64 8#64 [] := by
  unfold vecAt vecHeader vecBuf
  have hite : (if (0#64 : BitVec 64) = 0 then emp
    else A.live (8#64) ((0#64 : BitVec 64).toNat * 104) 8 ∗
      arrayAt (chainAt A) 104 8#64 [] ∗
      memRegion (8#64 + BitVec.ofNat 64 (([] : List (ChainGhost × ReceiverChain)).length * 104))
        (((0#64 : BitVec 64).toNat - ([] : List (ChainGhost × ReceiverChain)).length) * 104)) = emp := rfl
  rw [hite]
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_emp]
  have hp : 0 ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0 := by decide
  exact Entails.pure_right hp (Entails.refl _)

theorem vecU8At_nil_0_1 (A : RustAlloc) (v : BitVec 64) :
    ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) ⊢
      vecU8At A v 0#64 1#64 [] := by
  rw [vecU8At_eq_header_sep_buf]
  unfold vecHeader vecU8Buf
  have hite : (if (0#64 : BitVec 64) = 0 then emp
    else A.live (1#64) (0#64 : BitVec 64).toNat 1 ∗
      (1#64 ↦ₛ ([] : List (BitVec 8))) ∗
      memRegion (1#64 + BitVec.ofNat 64 ([] : List (BitVec 8)).length)
        ((0#64 : BitVec 64).toNat - ([] : List (BitVec 8)).length)) = emp := rfl
  rw [hite]
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_emp]
  have hp : ([] : List (BitVec 8)).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0 := by decide
  exact Entails.pure_right hp (Entails.refl _)

theorem SepWP.intro_rodata_missingRemoteIdentity {prog : Program} {img : Obj.Image}
    {target_pc : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img) (hfl : img.FrozenLoaded s)
    (h : SepWP prog target_pc s (((img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752))) ↦ᵣ invalidSessionStructureStr .missingRemoteIdentity) ∗ P) post) :
    SepWP prog target_pc s P post := by
  refine ProofLib.SepWP.of_reaches_pc fun R hm => ProofLib.SepWP.to_reaches_pc h ?_
  rw [sepConj_assoc]
  exact rodata_missingRemoteIdentity_intro himg hfl.roData hm

theorem entails_exists_right {α : Type _} {P : SepProp} {Q : α → SepProp} (a : α)
    (h : P ⊢ Q a) : P ⊢ (∃∗ x, Q x) :=
  Entails.sepExists_right a h

theorem speAt_missingRemoteIdentity_intro (A : RustAlloc) (a p : BitVec 64) :
    ((a ↦₆₄ 0x8000000000000014#64) ∗
     ((a + 8#64) ↦₆₄ p) ∗ ((a + 16#64) ↦₆₄ 27#64) ∗
     (p ↦ᵣ invalidSessionStructureStr .missingRemoteIdentity) ∗
     memRegion (a + 24#64) 24) ⊢
      speAt A (utf8 "decrypt") a (.invalidSessionStructure .missingRemoteIdentity) := by
  dsimp only [speAt, strRefAt]
  have hlen : BitVec.ofNat 64 (invalidSessionStructureStr .missingRemoteIdentity).length = 27#64 := by rfl_kernel
  have hw : speWord 20 = 0x8000000000000014#64 := rfl
  simp only [BitVec.add_assoc, BitVec.reduceAdd, hlen, hw]
  refine sepConj_mono (Entails.refl _) ?_
  rw [← sepConj_assoc, ← sepConj_assoc]
  exact sepConj_mono
    (entails_exists_right p (by simpa only [sepConj_assoc] using Entails.refl _))
    (Entails.refl _)

theorem trResultAt_err_missingRemoteIdentity_intro (A : RustAlloc) (r : BitVec 64) (G : SessionGhost)
    (p : BitVec 64) :
    ((r ↦₆₄ 0xffffffffffffffff#64) ∗
     ((r + 8#64) ↦₆₄ 0x8000000000000014#64) ∗
     ((r + 16#64) ↦₆₄ p) ∗ ((r + 24#64) ↦₆₄ 27#64) ∗
     (p ↦ᵣ invalidSessionStructureStr .missingRemoteIdentity) ∗
     memRegion (r + 32#64) 24 ∗
     memRegion (r + 56#64) 208) ⊢
      trResultAt A r G (.error (.invalidSessionStructure .missingRemoteIdentity)) := by
  unfold trResultAt errResultAt
  have herr : errTag = 0xffffffffffffffff#64 := rfl
  rw [herr]
  have hspe := speAt_missingRemoteIdentity_intro A (r + 8#64) p
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hspe ⊢
  refine sepConj_mono (Entails.refl _) ?_
  rw [← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc]
  refine sepConj_mono ?_ (Entails.refl _)
  simpa only [sepConj_assoc] using hspe

theorem trResultAt_ok_intro (A : RustAlloc) (r : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) (rem : IdentityKey) (senderPad : List (BitVec 8))
    (hclamp : ∀ sc, st.senderChain = some sc →
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes)
    (hchains : G.chains.length = st.receiverChains.length)
    (hpad : senderPad.length = 100) :
    ((r ↦₆₄ G.chainsCap) ∗
     ((r + 8#64) ↦₆₄ G.chainsPtr) ∗
     ((r + 16#64) ↦₆₄ BitVec.ofNat 64 st.receiverChains.length) ∗
     vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
     ((r + 24#64) ↦ₛ optSenderChainBytes st.senderChain senderPad) ∗
     ((r + 128#64) ↦ₛ CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
     ((r + 160#64) ↦₆₄ 25000#64) ∗
     ((r + 168#64) ↦₃₂ st.previousCounter) ∗
     memRegion (r + 172#64) 4 ∗
     ((r + 176#64) ↦₆₄ G.pq.cap) ∗
     ((r + 184#64) ↦₆₄ G.pq.ptr) ∗
     ((r + 192#64) ↦₆₄ BitVec.ofNat 64 st.pqRatchetState.length) ∗
     vecU8Buf A G.pq.cap G.pq.ptr st.pqRatchetState ∗
     ((r + 200#64) ↦ₛ st.localIdentity.publicKey.bytes.toList) ∗
     ((r + 232#64) ↦ₛ rem.publicKey.bytes.toList)) ⊢
      trResultAt A r G (.ok ⟨⟨st.rootKey, st.senderChain, st.receiverChains,
        st.previousCounter, maxForwardJumps⟩, st.pqRatchetState, st.localIdentity, rem⟩) := by
  dsimp only [trResultAt]
  apply entails_exists_right senderPad
  unfold trAt ratchetAt
  apply Entails.pure_right hclamp
  simp only [sepConj_assoc]
  have hmax : maxForwardJumps < 2 ^ 64 := by decide
  apply Entails.pure_right ⟨hchains, hpad, hmax⟩
  have hzip_len : (G.chains.zip st.receiverChains).length = st.receiverChains.length := by
    simp [hchains]
  unfold vecAt
  rw [hzip_len, vecU8At_eq_header_sep_buf]
  unfold vecHeader
  have hmfj : BitVec.ofNat 64 maxForwardJumps = 25000#64 := rfl
  rw [hmfj]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.refl _

theorem base_aligned_of_loads {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img) :
    img.base &&& 0xfff#64 = 0#64 :=
  ProofLib.ObjectLoad.base_aligned_of_loads h

theorem memRegion_32_to_bytes (a : BitVec 64) :
    memRegion a 32 ⊢ ∃∗ bs : List (BitVec 8), ⌜bs.length = 32⌝ ∗ (a ↦ₛ bs) := by
  have h2a : memRegion a 32 = memRegion a 8 ∗ memRegion (a + 8#64) 24 :=
    memRegion_split' (by decide) rfl (by decide)
  have h2b : memRegion (a + 8#64) 24 =
      memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 8 ∗ memRegion (a + 24#64) 8 := by
    rw [mr_cut_add a 8 8 16 (by decide)]
    rw [mr_cut_add a 16 8 8 (by decide)]
  rw [h2a, h2b, memRegion_eight a, memRegion_eight (a + 8#64),
      memRegion_eight (a + 16#64), memRegion_eight (a + 24#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w0
  let out32 := unpack64 w0 ++ unpack64 w1 ++ unpack64 w2 ++ unpack64 w3
  have hout_len : out32.length = 32 := by simp [out32]
  have h8 : ∀ w : BitVec 64, (unpack64 w).length = 8 := fun _ => rfl
  have hout_pts : (a ↦ₛ out32) =
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
       ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3)) := by
    dsimp only [out32]
    simp only [List.append_assoc, pointsToBytes_append, h8,
      ← pointsTo64_eq_pointsToBytes, BitVec.add_assoc, BitVec.reduceAdd]
  apply entails_exists_right out32
  apply Entails.pure_right hout_len
  rw [hout_pts]
  exact Entails.refl _

theorem memRegion_33_to_tag_and_32 (a : BitVec 64) :
    memRegion a 33 ⊢
      ∃∗ tag0 : BitVec 8, ∃∗ out32 : List (BitVec 8),
        ⌜out32.length = 32⌝ ∗ (a ↦₈ tag0) ∗ ((a + 1#64) ↦ₛ out32) := by
  have h1 : memRegion a 33 = memRegion a 1 ∗ memRegion (a + 1#64) 32 :=
    memRegion_split' (by decide) rfl (by decide)
  rw [h1, memRegion_one a]
  refine Entails.trans (sepConj_mono (Entails.refl _) (memRegion_32_to_bytes (a + 1#64))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro out32
  apply Entails.sepExists_elim; intro tag0
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; intro hout_len
  apply entails_exists_right tag0
  apply entails_exists_right out32
  exact Entails.pure_right hout_len (Entails.refl _)

theorem stackAt_dropVecChain_eq_remoteIdentityKey (sp : BitVec 64) :
    stackAt (sp - 496#64) dropVecChainStack =
      memRegion (sp - 4688#64) 4048 ∗ stackAt (sp - 496#64) remoteIdentityKeyStack := by
  rw [ReceiveRatchetApply.stackAt_sub_split (sp - 496#64) dropVecChainStack remoteIdentityKeyStack
    (by decide) (by decide)]
  have heq : sp - 496#64 - BitVec.ofNat 64 dropVecChainStack = sp - 4688#64 := by
    simp only [dropVecChainStack, dropVecMessageKeyStack, allocHookStack]; bv_omega
  rw [heq]; rfl

theorem stackAt_dropVecChain_eq_dropSpe (sp : BitVec 64) :
    stackAt (sp - 496#64) dropVecChainStack =
      memRegion (sp - 4688#64) 64 ∗ stackAt (sp - 496#64) dropSpeStack := by
  rw [ReceiveRatchetApply.stackAt_sub_split (sp - 496#64) dropVecChainStack dropSpeStack
    (by decide) (by decide)]
  have heq : sp - 496#64 - BitVec.ofNat 64 dropVecChainStack = sp - 4688#64 := by
    simp only [dropVecChainStack, dropVecMessageKeyStack, allocHookStack]; bv_omega
  rw [heq]; rfl

theorem stackAt_dropVecChain_eq_allocHook (sp : BitVec 64) :
    stackAt (sp - 496#64) dropVecChainStack =
      memRegion (sp - 4688#64) 96 ∗ stackAt (sp - 496#64) allocHookStack := by
  rw [ReceiveRatchetApply.stackAt_sub_split (sp - 496#64) dropVecChainStack allocHookStack
    (by decide) (by decide)]
  have heq : sp - 496#64 - BitVec.ofNat 64 dropVecChainStack = sp - 4688#64 := by
    simp only [dropVecChainStack, dropVecMessageKeyStack, allocHookStack]; bv_omega
  rw [heq]; rfl

theorem stackAt_dropVecChain_eq_remoteIdentityKey_x (sp : BitVec 64) :
    stackAt (sp - 496#64) dropVecChainStackX =
      memRegion (sp - 16976#64) 16336 ∗ stackAt (sp - 496#64) remoteIdentityKeyStack := by
  rw [ReceiveRatchetApply.stackAt_sub_split (sp - 496#64) dropVecChainStackX remoteIdentityKeyStack
    (by decide) (by decide)]
  have heq : sp - 496#64 - BitVec.ofNat 64 dropVecChainStackX = sp - 16976#64 := by
    simp only [dropVecChainStackX, dropVecMessageKeyStackX, extHookStack]; bv_omega
  rw [heq]; rfl

theorem stackAt_dropVecChain_eq_dropSpe_x (sp : BitVec 64) :
    stackAt (sp - 496#64) dropVecChainStackX =
      memRegion (sp - 16976#64) 64 ∗ stackAt (sp - 496#64) dropSpeStackX := by
  rw [ReceiveRatchetApply.stackAt_sub_split (sp - 496#64) dropVecChainStackX dropSpeStackX
    (by decide) (by decide)]
  have heq : sp - 496#64 - BitVec.ofNat 64 dropVecChainStackX = sp - 16976#64 := by
    simp only [dropVecChainStackX, dropVecMessageKeyStackX, extHookStack]; bv_omega
  rw [heq]; rfl

theorem stackAt_dropVecChain_eq_allocHook_x (sp : BitVec 64) :
    stackAt (sp - 496#64) dropVecChainStackX =
      memRegion (sp - 16976#64) 96 ∗ stackAt (sp - 496#64) extHookStack := by
  rw [ReceiveRatchetApply.stackAt_sub_split (sp - 496#64) dropVecChainStackX extHookStack
    (by decide) (by decide)]
  have heq : sp - 496#64 - BitVec.ofNat 64 dropVecChainStackX = sp - 16976#64 := by
    simp only [dropVecChainStackX, dropVecMessageKeyStackX, extHookStack]; bv_omega
  rw [heq]; rfl

def vecU8Rest (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
  A.live ptr cap.toNat 1 ∗
  memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)

theorem vecU8At_expose_slice (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hne : 0 < bs.length) :
    vecU8At A v cap ptr bs ⊢
      ⌜(cap + 1#64 == 0#64) = false ∧ bs.length < 2 ^ 63 ∧
        (BitVec.ofNat 64 bs.length).toNat = bs.length⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗ vecU8Rest A cap ptr bs := by
  rw [vecU8At_eq_header_sep_buf]
  unfold vecHeader vecU8Buf vecU8Rest
  simp only [sepConj_assoc]
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
  apply Entails.pure_left
  rintro ⟨hle, hlt, hptr⟩
  have hpos : 0 < cap.toNat := by omega
  have hcap_ne : cap ≠ 0 := fun h => by subst h; simp at hpos
  have hcap_cmn : (cap + 1#64 == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro heq
    have : cap = 0xffffffffffffffff#64 := by bv_omega
    subst this; revert hlt; decide
  have hbs_lt : bs.length < 2 ^ 63 := by omega
  have hbs_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat]; omega
  rw [ite_eq_right_iff.mpr (fun h => (hcap_ne h).elim)]
  apply Entails.pure_right ⟨hcap_cmn, hbs_lt, hbs_toNat⟩
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
    sepConj_pure_left_comm]
  apply Entails.pure_right ⟨hle, hlt, hptr⟩
  exact Entails.of_eq (by ac_rfl)

theorem vecU8At_reassemble_slice (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hne : 0 < bs.length) :
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
     (ptr ↦ₛ bs) ∗ vecU8Rest A cap ptr bs) ⊢
      vecU8At A v cap ptr bs := by
  rw [vecU8At_eq_header_sep_buf]
  unfold vecHeader vecU8Buf vecU8Rest
  simp only [sepConj_assoc]
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
    sepConj_pure_left_comm]
  apply Entails.pure_left
  rintro ⟨hle, hlt, hptr⟩
  have hpos : 0 < cap.toNat := by omega
  have hcap_ne : cap ≠ 0 := fun h => by subst h; simp at hpos
  rw [ite_eq_right_iff.mpr (fun h => (hcap_ne h).elim)]
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
  apply Entails.pure_right ⟨hle, hlt, hptr⟩
  exact Entails.of_eq (by ac_rfl)

theorem vecBuf_chains_cmn (A : RustAlloc) (cap ptr : BitVec 64)
    (xs : List (ChainGhost × ReceiverChain)) :
    vecBuf A 104 8 (chainAt A) cap ptr xs ⊢
      ⌜(cap + 1#64 == 0#64) = false⌝ ∗ vecBuf A 104 8 (chainAt A) cap ptr xs := by
  unfold vecBuf
  apply Entails.pure_left
  rintro ⟨hle, hlt, hptr⟩
  have hcmn : (cap + 1#64 == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro heq
    have : cap = 0xffffffffffffffff#64 := by bv_omega
    subst this; revert hlt; decide
  exact Entails.pure_right hcmn (Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _))

theorem vecU8Buf_expose_pq (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢
      ⌜(cap == 0#64) = decide (cap = 0) ∧
        (cap ≠ 0 → 0 < cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0)⌝ ∗
      vecU8Buf A cap ptr bs := by
  unfold vecU8Buf
  apply Entails.pure_left
  rintro ⟨hle, hlt, hptr⟩
  have hbeq : (cap == 0#64) = decide (cap = 0) := by
    cases h : decide (cap = 0) <;> simp_all
  have hne : cap ≠ 0 → 0 < cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0 := by
    intro hc
    exact ⟨Nat.pos_of_ne_zero (fun h0 => hc (BitVec.eq_of_toNat_eq h0)), hlt, hptr⟩
  exact Entails.pure_right ⟨hbeq, hne⟩ (Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _))

theorem sessionStateAt_expose_from (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st ⊢
      ⌜PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
        (BitVec.ofNat 64 G.localIk.bytes.length).toNat = G.localIk.bytes.length ∧
        G.chains.length = st.receiverChains.length ∧
        (G.chainsCap + 1#64 == 0#64) = false ∧
        (G.pq.cap == 0#64) = decide (G.pq.cap = 0) ∧
        (G.pq.cap ≠ 0 → 0 < G.pq.cap.toNat ∧ G.pq.cap.toNat < 2 ^ 63 ∧ G.pq.ptr ≠ 0) ∧
        G.sender.isSome = st.senderChain.isSome⌝ ∗
      sessionFromFrame A ss G st ∗
      (ss ↦₆₄ G.localIk.cap) ∗ ((ss + 8#64) ↦₆₄ G.localIk.ptr) ∗
      ((ss + 16#64) ↦₆₄ BitVec.ofNat 64 G.localIk.bytes.length) ∗
      (G.localIk.ptr ↦ₛ G.localIk.bytes) ∗
      vecU8Rest A G.localIk.cap G.localIk.ptr G.localIk.bytes ∗
      ((ss + 48#64) ↦₆₄ G.root.cap) ∗ ((ss + 56#64) ↦₆₄ G.root.ptr) ∗
      ((ss + 64#64) ↦₆₄ 32#64) ∗
      (G.root.ptr ↦ₛ CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
      vecU8Rest A G.root.cap G.root.ptr (CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
      ((ss + 72#64) ↦₆₄ G.chainsCap) ∗ ((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
      ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 st.receiverChains.length) ∗
      vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
      ((ss + 120#64) ↦₆₄ G.pq.cap) ∗ ((ss + 128#64) ↦₆₄ G.pq.ptr) ∗
      ((ss + 136#64) ↦₆₄ BitVec.ofNat 64 st.pqRatchetState.length) ∗
      vecU8Buf A G.pq.cap G.pq.ptr st.pqRatchetState ∗
      optSenderChainAt A (ss + 144#64) G.sender st.senderChain ∗
      ((ss + 332#64) ↦₃₂ st.previousCounter) := by
  have h1 : sessionStateAt A ss G st ⊢
      ⌜PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
        G.chains.length = st.receiverChains.length⌝ ∗
      sessionFromFrame A ss G st ∗
      vecU8At A ss G.localIk.cap G.localIk.ptr G.localIk.bytes ∗
      vecU8At A (ss + 48#64) G.root.cap G.root.ptr (CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
      vecAt A 104 8 (chainAt A) (ss + 72#64) G.chainsCap G.chainsPtr
        (G.chains.zip st.receiverChains) ∗
      vecU8At A (ss + 120#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
      optSenderChainAt A (ss + 144#64) G.sender st.senderChain ∗
      ((ss + 332#64) ↦₃₂ st.previousCounter) := by
    unfold sessionStateAt sessionFromFrame vecGhostAt
    apply Entails.pure_left
    rintro ⟨hlik, hrik, hchains, hpend, hreg, hlik33, hrik33⟩
    apply Entails.pure_right ⟨hlik, hchains⟩
    simp only [sepConj_assoc]
    apply Entails.pure_right ⟨hrik, hpend, hreg, hlik33, hrik33⟩
    exact Entails.of_eq (by ac_rfl)
  refine Entails.trans h1 ?_
  apply Entails.pure_left
  rintro ⟨hlik, hchains⟩
  have hlik_ne : 0 < G.localIk.bytes.length := ReceiveRatchetApply.deserialize_ok_nonempty hlik
  have hlik_exp := vecU8At_expose_slice A ss G.localIk.cap G.localIk.ptr G.localIk.bytes hlik_ne
  have hroot_exp := vecU8At_expose_slice A (ss + 48#64) G.root.cap G.root.ptr
    (CryptoGames.HMAC.keyToBytes32 st.rootKey) (by rw [length_keyToBytes32]; decide)
  rw [length_keyToBytes32] at hroot_exp
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hroot_exp
  have hchains_exp : vecAt A 104 8 (chainAt A) (ss + 72#64) G.chainsCap G.chainsPtr
      (G.chains.zip st.receiverChains) ⊢
      ⌜(G.chainsCap + 1#64 == 0#64) = false⌝ ∗
      ((ss + 72#64) ↦₆₄ G.chainsCap) ∗ ((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
      ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 st.receiverChains.length) ∗
      vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) := by
    unfold vecAt vecHeader
    have hzip : (G.chains.zip st.receiverChains).length = st.receiverChains.length := by
      simp [hchains]
    rw [hzip]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine Entails.trans (sepConj_mono (Entails.refl _)
      (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
        (vecBuf_chains_cmn A G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains))))) ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    exact Entails.refl _
  have hpq_exp : vecU8At A (ss + 120#64) G.pq.cap G.pq.ptr st.pqRatchetState ⊢
      ⌜(G.pq.cap == 0#64) = decide (G.pq.cap = 0) ∧
        (G.pq.cap ≠ 0 → 0 < G.pq.cap.toNat ∧ G.pq.cap.toNat < 2 ^ 63 ∧ G.pq.ptr ≠ 0)⌝ ∗
      ((ss + 120#64) ↦₆₄ G.pq.cap) ∗ ((ss + 128#64) ↦₆₄ G.pq.ptr) ∗
      ((ss + 136#64) ↦₆₄ BitVec.ofNat 64 st.pqRatchetState.length) ∗
      vecU8Buf A G.pq.cap G.pq.ptr st.pqRatchetState := by
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine Entails.trans (sepConj_mono (Entails.refl _)
      (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
        (vecU8Buf_expose_pq A G.pq.cap G.pq.ptr st.pqRatchetState)))) ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    exact Entails.refl _
  have hsc_eq : optSenderChainAt A (ss + 144#64) G.sender st.senderChain ⊢
      ⌜G.sender.isSome = st.senderChain.isSome⌝ ∗
      optSenderChainAt A (ss + 144#64) G.sender st.senderChain := by
    cases G.sender <;> cases st.senderChain <;> dsimp only [optSenderChainAt]
    · exact Entails.pure_right rfl (Entails.refl _)
    · exact Entails.pure_left_only False.elim
    · exact Entails.pure_left_only False.elim
    · exact Entails.pure_right rfl (Entails.refl _)
  refine Entails.trans (sepConj_mono (Entails.refl _)
    (sepConj_mono hlik_exp (sepConj_mono hroot_exp
      (sepConj_mono hchains_exp (sepConj_mono hpq_exp (sepConj_mono hsc_eq (Entails.refl _))))))) ?_
  simp only [sepConj_assoc]
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨_, _, hlik_toNat⟩
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
    sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
  apply Entails.pure_left; intro _
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
    sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
    sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
    sepConj_pure_left_comm, sepConj_pure_left_comm]
  apply Entails.pure_left; intro hcmn
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
    sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
    sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
    sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
    sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨hpq1, hpq2⟩
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
    sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
    sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
    sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
    sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
    sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
    sepConj_pure_left_comm]
  apply Entails.pure_left; intro hsc
  apply Entails.pure_right ⟨hlik, hlik_toNat, hchains, hcmn, hpq1, hpq2, hsc⟩
  exact Entails.refl _

theorem sessionStateAt_reassemble_from (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8)))
    (hlik : PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey) :
    (sessionFromFrame A ss G st ∗
      (ss ↦₆₄ G.localIk.cap) ∗ ((ss + 8#64) ↦₆₄ G.localIk.ptr) ∗
      ((ss + 16#64) ↦₆₄ BitVec.ofNat 64 G.localIk.bytes.length) ∗
      (G.localIk.ptr ↦ₛ G.localIk.bytes) ∗
      vecU8Rest A G.localIk.cap G.localIk.ptr G.localIk.bytes ∗
      ((ss + 48#64) ↦₆₄ G.root.cap) ∗ ((ss + 56#64) ↦₆₄ G.root.ptr) ∗
      ((ss + 64#64) ↦₆₄ 32#64) ∗
      (G.root.ptr ↦ₛ CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
      vecU8Rest A G.root.cap G.root.ptr (CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
      vecAt A 104 8 (chainAt A) (ss + 72#64) 0#64 8#64 [] ∗
      vecU8At A (ss + 120#64) 0#64 1#64 [] ∗
      optSenderChainAt A (ss + 144#64) G.sender st.senderChain ∗
      ((ss + 332#64) ↦₃₂ st.previousCounter)) ⊢
      sessionStateAt A ss G.afterTrFrom
        { st with receiverChains := [], pqRatchetState := [] } := by
  have hlik_ne : 0 < G.localIk.bytes.length := ReceiveRatchetApply.deserialize_ok_nonempty hlik
  have hlik_re := vecU8At_reassemble_slice A ss G.localIk.cap G.localIk.ptr G.localIk.bytes hlik_ne
  have hroot_re := vecU8At_reassemble_slice A (ss + 48#64) G.root.cap G.root.ptr
    (CryptoGames.HMAC.keyToBytes32 st.rootKey) (by rw [length_keyToBytes32]; decide)
  rw [length_keyToBytes32] at hroot_re
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hroot_re
  have h1 :
      (sessionFromFrame A ss G st ∗
        ((ss ↦₆₄ G.localIk.cap) ∗ ((ss + 8#64) ↦₆₄ G.localIk.ptr) ∗
         ((ss + 16#64) ↦₆₄ BitVec.ofNat 64 G.localIk.bytes.length) ∗
         (G.localIk.ptr ↦ₛ G.localIk.bytes) ∗
         vecU8Rest A G.localIk.cap G.localIk.ptr G.localIk.bytes) ∗
        (((ss + 48#64) ↦₆₄ G.root.cap) ∗ ((ss + 56#64) ↦₆₄ G.root.ptr) ∗
         ((ss + 64#64) ↦₆₄ 32#64) ∗
         (G.root.ptr ↦ₛ CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
         vecU8Rest A G.root.cap G.root.ptr (CryptoGames.HMAC.keyToBytes32 st.rootKey)) ∗
        vecAt A 104 8 (chainAt A) (ss + 72#64) 0#64 8#64 [] ∗
        vecU8At A (ss + 120#64) 0#64 1#64 [] ∗
        optSenderChainAt A (ss + 144#64) G.sender st.senderChain ∗
        ((ss + 332#64) ↦₃₂ st.previousCounter)) ⊢
      (sessionFromFrame A ss G st ∗
        vecU8At A ss G.localIk.cap G.localIk.ptr G.localIk.bytes ∗
        vecU8At A (ss + 48#64) G.root.cap G.root.ptr (CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
        vecAt A 104 8 (chainAt A) (ss + 72#64) 0#64 8#64 [] ∗
        vecU8At A (ss + 120#64) 0#64 1#64 [] ∗
        optSenderChainAt A (ss + 144#64) G.sender st.senderChain ∗
        ((ss + 332#64) ↦₃₂ st.previousCounter)) :=
    sepConj_mono (Entails.refl _)
      (sepConj_mono hlik_re (sepConj_mono hroot_re (Entails.refl _)))
  simp only [sepConj_assoc] at h1
  refine Entails.trans h1 ?_
  unfold sessionStateAt SessionGhost.afterTrFrom sessionFromFrame vecGhostAt
  simp only [sepConj_assoc]
  apply Entails.pure_left
  rintro ⟨hrik, hpend, hreg, hlik33, hrik33⟩
  apply Entails.pure_right ⟨hlik, hrik, rfl, hpend, hreg, hlik33, hrik33⟩
  exact Entails.of_eq (by ac_rfl)

def senderChainFromFrame (A : RustAlloc) (ss : BitVec 64)
    (sg : SenderChainGhost) (sc : SenderChain) : SepProp :=
  ⌜PublicKey.deserialize sg.srk.bytes = .ok sc.ratchetKey.publicKey ∧
    sg.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
    Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
    sg.srk.bytes.length = 33⌝ ∗
  vecU8Rest A sg.srk.cap sg.srk.ptr sg.srk.bytes ∗
  ((ss + 168#64) ↦₆₄ sg.priv.cap) ∗
  vecU8Rest A sg.priv.cap sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList ∗
  vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
  vecU8Rest A sg.ck.cap sg.ck.ptr (CryptoGames.HMAC.keyToBytes32 sc.chainKey.key) ∗
  memRegion (ss + 244#64) 4

theorem optSenderChainAt_some_expose_from (A : RustAlloc) (ss : BitVec 64)
    (sg : SenderChainGhost) (sc : SenderChain) :
    optSenderChainAt A (ss + 144#64) (some sg) (some sc) ⊢
      ⌜PublicKey.deserialize sg.srk.bytes = .ok sc.ratchetKey.publicKey ∧
        sg.srk.bytes.length < 2 ^ 63 ∧
        (BitVec.ofNat 64 sg.srk.bytes.length).toNat = sg.srk.bytes.length ∧
        Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
        (sg.srk.cap + 1#64 == 0#64) = false ∧
        (sg.ck.cap + 1#64 == 0#64) = false⌝ ∗
      senderChainFromFrame A ss sg sc ∗
      ((ss + 144#64) ↦₆₄ sg.srk.cap) ∗ ((ss + 152#64) ↦₆₄ sg.srk.ptr) ∗
      ((ss + 160#64) ↦₆₄ BitVec.ofNat 64 sg.srk.bytes.length) ∗
      (sg.srk.ptr ↦ₛ sg.srk.bytes) ∗
      ((ss + 176#64) ↦₆₄ sg.priv.ptr) ∗ ((ss + 184#64) ↦₆₄ 32#64) ∗
      (sg.priv.ptr ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
      ((ss + 216#64) ↦₆₄ sg.ck.cap) ∗ ((ss + 224#64) ↦₆₄ sg.ck.ptr) ∗
      ((ss + 232#64) ↦₆₄ 32#64) ∗
      (sg.ck.ptr ↦ₛ CryptoGames.HMAC.keyToBytes32 sc.chainKey.key) ∗
      ((ss + 240#64) ↦₃₂ sc.chainKey.index) := by
  unfold optSenderChainAt vecGhostAt optChainKeyAt
  apply Entails.pure_left
  rintro ⟨hsrk, hpriv, hclamp, hsrk33⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hsrk_ne : 0 < sg.srk.bytes.length := ReceiveRatchetApply.deserialize_ok_nonempty hsrk
  have hsrk_exp := vecU8At_expose_slice A (ss + 144#64) sg.srk.cap sg.srk.ptr sg.srk.bytes hsrk_ne
  have hpriv_exp := vecU8At_expose_slice A (ss + 168#64) sg.priv.cap sg.priv.ptr
    sc.ratchetKey.privateKey.bytes.toList (by rw [List.Vector.toList_length]; decide)
  rw [List.Vector.toList_length] at hpriv_exp
  have hck_exp := vecU8At_expose_slice A (ss + 216#64) sg.ck.cap sg.ck.ptr
    (CryptoGames.HMAC.keyToBytes32 sc.chainKey.key) (by rw [length_keyToBytes32]; decide)
  rw [length_keyToBytes32] at hck_exp
  rw [hpriv]
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsrk_exp hpriv_exp hck_exp
  refine Entails.trans (sepConj_mono hsrk_exp (sepConj_mono hpriv_exp
    (sepConj_mono (Entails.refl _) (sepConj_mono hck_exp (Entails.refl _))))) ?_
  simp only [sepConj_assoc]
  apply Entails.pure_left; rintro ⟨hsrk_cmn, hsrk_lt, hsrk_toNat⟩
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
    sepConj_pure_left_comm, sepConj_pure_left_comm]
  apply Entails.pure_left; intro _
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
    sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
    sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
    sepConj_pure_left_comm, sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨hck_cmn, _, _⟩
  apply Entails.pure_right ⟨hsrk, hsrk_lt, hsrk_toNat, hclamp, hsrk_cmn, hck_cmn⟩
  unfold senderChainFromFrame
  simp only [sepConj_assoc]
  apply Entails.pure_right ⟨hsrk, hpriv, hclamp, hsrk33⟩
  exact Entails.of_eq (by ac_rfl)

theorem optSenderChainAt_some_reassemble_from (A : RustAlloc) (ss : BitVec 64)
    (sg : SenderChainGhost) (sc : SenderChain) :
    (senderChainFromFrame A ss sg sc ∗
      ((ss + 144#64) ↦₆₄ sg.srk.cap) ∗ ((ss + 152#64) ↦₆₄ sg.srk.ptr) ∗
      ((ss + 160#64) ↦₆₄ BitVec.ofNat 64 sg.srk.bytes.length) ∗
      (sg.srk.ptr ↦ₛ sg.srk.bytes) ∗
      ((ss + 176#64) ↦₆₄ sg.priv.ptr) ∗ ((ss + 184#64) ↦₆₄ 32#64) ∗
      (sg.priv.ptr ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
      ((ss + 216#64) ↦₆₄ sg.ck.cap) ∗ ((ss + 224#64) ↦₆₄ sg.ck.ptr) ∗
      ((ss + 232#64) ↦₆₄ 32#64) ∗
      (sg.ck.ptr ↦ₛ CryptoGames.HMAC.keyToBytes32 sc.chainKey.key) ∗
      ((ss + 240#64) ↦₃₂ sc.chainKey.index)) ⊢
      optSenderChainAt A (ss + 144#64) (some sg) (some sc) := by
  unfold senderChainFromFrame optSenderChainAt vecGhostAt optChainKeyAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  apply Entails.pure_left
  rintro ⟨hsrk, hpriv, hclamp, hsrk33⟩
  apply Entails.pure_right ⟨hsrk, hpriv, hclamp, hsrk33⟩
  rw [hpriv]
  have hsrk_ne : 0 < sg.srk.bytes.length := ReceiveRatchetApply.deserialize_ok_nonempty hsrk
  have hsrk_re := vecU8At_reassemble_slice A (ss + 144#64) sg.srk.cap sg.srk.ptr sg.srk.bytes hsrk_ne
  have hpriv_re := vecU8At_reassemble_slice A (ss + 168#64) sg.priv.cap sg.priv.ptr
    sc.ratchetKey.privateKey.bytes.toList (by rw [List.Vector.toList_length]; decide)
  rw [List.Vector.toList_length] at hpriv_re
  have hck_re := vecU8At_reassemble_slice A (ss + 216#64) sg.ck.cap sg.ck.ptr
    (CryptoGames.HMAC.keyToBytes32 sc.chainKey.key) (by rw [length_keyToBytes32]; decide)
  rw [length_keyToBytes32] at hck_re
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsrk_re hpriv_re hck_re
  have h1 :
      (((ss + 144#64) ↦₆₄ sg.srk.cap) ∗ ((ss + 152#64) ↦₆₄ sg.srk.ptr) ∗
       ((ss + 160#64) ↦₆₄ BitVec.ofNat 64 sg.srk.bytes.length) ∗
       (sg.srk.ptr ↦ₛ sg.srk.bytes) ∗
       vecU8Rest A sg.srk.cap sg.srk.ptr sg.srk.bytes) ∗
      (((ss + 168#64) ↦₆₄ sg.priv.cap) ∗ ((ss + 176#64) ↦₆₄ sg.priv.ptr) ∗
       ((ss + 184#64) ↦₆₄ 32#64) ∗
       (sg.priv.ptr ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
       vecU8Rest A sg.priv.cap sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList) ∗
      vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
      (((ss + 216#64) ↦₆₄ sg.ck.cap) ∗ ((ss + 224#64) ↦₆₄ sg.ck.ptr) ∗
       ((ss + 232#64) ↦₆₄ 32#64) ∗
       (sg.ck.ptr ↦ₛ CryptoGames.HMAC.keyToBytes32 sc.chainKey.key) ∗
       vecU8Rest A sg.ck.cap sg.ck.ptr (CryptoGames.HMAC.keyToBytes32 sc.chainKey.key)) ∗
      ((ss + 240#64) ↦₃₂ sc.chainKey.index) ∗ memRegion (ss + 244#64) 4 ⊢
      vecU8At A (ss + 144#64) sg.srk.cap sg.srk.ptr sg.srk.bytes ∗
      vecU8At A (ss + 168#64) sg.priv.cap sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList ∗
      vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
      vecU8At A (ss + 216#64) sg.ck.cap sg.ck.ptr (CryptoGames.HMAC.keyToBytes32 sc.chainKey.key) ∗
      ((ss + 240#64) ↦₃₂ sc.chainKey.index) ∗ memRegion (ss + 244#64) 4 :=
    sepConj_mono hsrk_re (sepConj_mono hpriv_re
      (sepConj_mono (Entails.refl _) (sepConj_mono hck_re (Entails.refl _))))
  refine Entails.trans ?_ h1
  exact Entails.of_eq (by ac_rfl)

theorem exists_bytes_of_bv16 (w : BitVec 16) :
    ∃ b0 b1 : BitVec 8, w = b1 ++ b0 :=
  ⟨w.extractLsb' 0 8, w.extractLsb' 8 8, by bv_kernel⟩

theorem pointsTo64_of_8_8_32_16 (a : BitVec 64) (b0 b1 : BitVec 8) (d2 : BitVec 32) (h6 : BitVec 16) :
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₃₂ d2) ∗ ((a + 6#64) ↦₁₆ h6)) =
      (a ↦₆₄ (h6 ++ d2 ++ b1 ++ b0)) := by
  rcases exists_bytes_of_bv32 d2 with ⟨c0, c1, c2, c3, rfl⟩
  rcases exists_bytes_of_bv16 h6 with ⟨c4, c5, rfl⟩
  have hassoc : (c5 ++ c4) ++ (c3 ++ c2 ++ c1 ++ c0) ++ b1 ++ b0 =
      c5 ++ c4 ++ c3 ++ c2 ++ c1 ++ c0 ++ b1 ++ b0 := by bv_kernel
  rw [hassoc, pointsTo64_eq_bytes8, pointsTo32_eq_bytes4, pointsTo16_eq_bytes2]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem exists_err22_split (p w16 : BitVec 64) :
    ∃ (d0 : BitVec 32) (h4 : BitVec 16) (w6 w14 : BitVec 64) (h22 : BitVec 16),
      (∀ a : BitVec 64,
        ((a ↦₆₄ p) ∗ ((a + 8#64) ↦₆₄ 27#64) ∗ ((a + 16#64) ↦₆₄ w16)) =
          ((a ↦₃₂ d0) ∗ ((a + 4#64) ↦₁₆ h4) ∗ ((a + 6#64) ↦₆₄ w6) ∗
           ((a + 14#64) ↦₆₄ w14) ∗ ((a + 22#64) ↦₁₆ h22))) ∧
      (∀ a : BitVec 64, ∀ r22 : BitVec 16,
        ((a ↦₃₂ d0) ∗ ((a + 4#64) ↦₁₆ h4) ∗ ((a + 6#64) ↦₆₄ w6) ∗
         ((a + 14#64) ↦₆₄ w14) ∗ ((a + 22#64) ↦₁₆ r22)) ⊢
          ((a ↦₆₄ p) ∗ ((a + 8#64) ↦₆₄ 27#64) ∗ memRegion (a + 16#64) 8)) := by
  rcases exists_bytes_of_bv64 p with ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩
  rcases exists_bytes_of_bv64 27#64 with ⟨b8, b9, b10, b11, b12, b13, b14, b15, h27⟩
  rcases exists_bytes_of_bv64 w16 with ⟨b16, b17, b18, b19, b20, b21, b22, b23, rfl⟩
  refine ⟨b3 ++ b2 ++ b1 ++ b0, b5 ++ b4,
    b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6,
    b21 ++ b20 ++ b19 ++ b18 ++ b17 ++ b16 ++ b15 ++ b14,
    b23 ++ b22, fun a => ?_, fun a r22 => ?_⟩
  · rw [h27]
    simp only [pointsTo64_eq_bytes8, pointsTo32_eq_bytes4, pointsTo16_eq_bytes2,
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  · rcases exists_bytes_of_bv16 r22 with ⟨c22, c23, rfl⟩
    have heq : ((a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ ((a + 4#64) ↦₁₆ (b5 ++ b4)) ∗
        ((a + 6#64) ↦₆₄ (b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6)) ∗
        ((a + 14#64) ↦₆₄ (b21 ++ b20 ++ b19 ++ b18 ++ b17 ++ b16 ++ b15 ++ b14)) ∗
        ((a + 22#64) ↦₁₆ (c23 ++ c22))) =
        ((a ↦₆₄ (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0)) ∗
         ((a + 8#64) ↦₆₄ 27#64) ∗
         ((a + 16#64) ↦₆₄ (c23 ++ c22 ++ b21 ++ b20 ++ b19 ++ b18 ++ b17 ++ b16))) := by
      rw [h27]
      simp only [pointsTo64_eq_bytes8, pointsTo32_eq_bytes4, pointsTo16_eq_bytes2,
        BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    rw [heq]
    exact sepConj_mono (Entails.refl _)
      (sepConj_mono (Entails.refl _) (pointsTo64_entails_memRegion _ _))

theorem memRegion_34_of_tag_32_1 (a : BitVec 64) (tag : BitVec 8) (bs : List (BitVec 8))
    (h : bs.length = 32) :
    ((a ↦₈ tag) ∗ ((a + 1#64) ↦ₛ bs) ∗ memRegion (a + 33#64) 1) ⊢ memRegion a 34 := by
  have h1a : memRegion a 34 = memRegion a 1 ∗ memRegion (a + 1#64) 33 :=
    memRegion_split' (by decide) rfl (by decide)
  have h1b : memRegion (a + 1#64) 33 = memRegion (a + 1#64) 32 ∗ memRegion (a + 33#64) 1 :=
    mr_cut_add a 1 32 1 (by decide)
  rw [h1a, h1b]
  exact sepConj_mono (pointsTo8_entails_memRegion a tag)
    (sepConj_mono (h ▸ pointsToBytes_entails_memRegion (a + 1#64) bs) (Entails.refl _))

def remoteIdentityTag : Option IdentityKey → BitVec 8
  | none => 0#8
  | some _ => 1#8

theorem remoteIdentityOkAt_unified (a : BitVec 64) (rem : Option IdentityKey) :
    remoteIdentityOkAt a rem ⊢
      ∃∗ bs : List (BitVec 8),
        ⌜bs.length = 32 ∧ (∀ ik, rem = some ik → bs = ik.publicKey.bytes.toList)⌝ ∗
        (a ↦₈ 0#8) ∗ ((a + 1#64) ↦₈ remoteIdentityTag rem) ∗ ((a + 2#64) ↦ₛ bs) := by
  cases rem with
  | none =>
    dsimp only [remoteIdentityOkAt, remoteIdentityTag]
    refine Entails.trans (sepConj_mono (Entails.refl _)
      (sepConj_mono (Entails.refl _) (memRegion_32_to_bytes (a + 2#64)))) ?_
    simp only [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro bs
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm]
    apply Entails.pure_left; intro hlen
    apply entails_exists_right bs
    exact Entails.pure_right ⟨hlen, fun _ h => by cases h⟩ (Entails.refl _)
  | some ik =>
    dsimp only [remoteIdentityOkAt, remoteIdentityTag]
    apply entails_exists_right ik.publicKey.bytes.toList
    refine Entails.pure_right ⟨ik.publicKey.bytes.toList_length, ?_⟩ (Entails.refl _)
    rintro _ ⟨rfl⟩; rfl

def sessionFromBase (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : SepProp :=
  ⌜(match st.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
    G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧
    (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
  vecGhostAt A G.alice (ss + 0x60#64) ∗
  optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
  optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
  ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗
  ((ss + 0x150#64) ↦ₛ G.regIds)

theorem sessionFromFrame_expose_remoteIk (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) :
    sessionFromFrame A ss G st ⊢
      ⌜match st.remoteIdentity with
       | none => G.remoteIk.bytes = []
       | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey⌝ ∗
      vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
      sessionFromBase A ss G st := by
  unfold sessionFromFrame sessionFromBase
  apply Entails.pure_left
  rintro ⟨hrik, hpend, hreg⟩
  apply Entails.pure_right hrik
  rw [sepConj_pure_left_comm]
  exact Entails.pure_right ⟨hrik, hpend, hreg⟩ (Entails.refl _)

theorem sessionFromFrame_reassemble_remoteIk (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) :
    (vecGhostAt A G.remoteIk (ss + 0x18#64) ∗ sessionFromBase A ss G st) ⊢
      sessionFromFrame A ss G st := by
  unfold sessionFromFrame sessionFromBase
  rw [sepConj_pure_left_comm]
  exact Entails.refl _

def sessionAfter208Frame (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : SepProp :=
  sessionFromBase A ss G st ∗
  (ss ↦₆₄ G.localIk.cap) ∗ ((ss + 8#64) ↦₆₄ G.localIk.ptr) ∗
  ((ss + 16#64) ↦₆₄ BitVec.ofNat 64 G.localIk.bytes.length) ∗
  vecU8Rest A G.localIk.cap G.localIk.ptr G.localIk.bytes ∗
  ((ss + 48#64) ↦₆₄ G.root.cap) ∗ ((ss + 56#64) ↦₆₄ G.root.ptr) ∗
  ((ss + 64#64) ↦₆₄ 32#64) ∗
  (G.root.ptr ↦ₛ CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
  vecU8Rest A G.root.cap G.root.ptr (CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
  vecAt A 104 8 (chainAt A) (ss + 72#64) 0#64 8#64 [] ∗
  vecU8At A (ss + 120#64) 0#64 1#64 [] ∗
  optSenderChainAt A (ss + 144#64) G.sender st.senderChain ∗
  ((ss + 332#64) ↦₃₂ st.previousCounter)

theorem sessionStateAt_reassemble_after208 (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8)))
    (hlik : PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey) :
    (sessionAfter208Frame A ss G st ∗
      (G.localIk.ptr ↦ₛ G.localIk.bytes) ∗
      vecGhostAt A G.remoteIk (ss + 0x18#64)) ⊢
      sessionStateAt A ss G.afterTrFrom
        { st with receiverChains := [], pqRatchetState := [] } := by
  refine Entails.trans ?_ (sessionStateAt_reassemble_from A ss G st hlik)
  unfold sessionAfter208Frame
  refine Entails.trans ?_
    (sepConj_mono (sessionFromFrame_reassemble_remoteIk A ss G st) (Entails.refl _))
  exact Entails.of_eq (by ac_rfl)

theorem stack_496_40_split (sp : BitVec 64) :
    memRegion (sp - 496#64) 40 =
      memRegion (sp - 496#64) 8 ∗
      (∃∗ u_488 : BitVec 32, (sp - 488#64) ↦₃₂ u_488) ∗
      (∃∗ u_484 : BitVec 32, (sp - 484#64) ↦₃₂ u_484) ∗
      (∃∗ u_480 : BitVec 64, (sp - 480#64) ↦₆₄ u_480) ∗
      (∃∗ u_472 : BitVec 64, (sp - 472#64) ↦₆₄ u_472) ∗
      (∃∗ u_464 : BitVec 64, (sp - 464#64) ↦₆₄ u_464) := by
  rw [mr_cut' sp 496 488 8 32 40 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 488 484 4 28 32 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 484 480 4 24 28 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 480 472 8 16 24 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 472 464 8 8 16 rfl rfl (by decide) (by decide) (by decide)]
  simp only [memRegion_four, memRegion_eight]

theorem stack_496_40_fold (sp : BitVec 64) (u_488 u_484 : BitVec 32)
    (u_480 u_472 u_464 : BitVec 64) :
    (memRegion (sp - 496#64) 8 ∗
      ((sp - 488#64) ↦₃₂ u_488) ∗ ((sp - 484#64) ↦₃₂ u_484) ∗
      ((sp - 480#64) ↦₆₄ u_480) ∗ ((sp - 472#64) ↦₆₄ u_472) ∗
      ((sp - 464#64) ↦₆₄ u_464)) ⊢
      memRegion (sp - 496#64) 40 := by
  rw [mr_cut' sp 496 488 8 32 40 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 488 484 4 28 32 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 484 480 4 24 28 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 480 472 8 16 24 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 472 464 8 8 16 rfl rfl (by decide) (by decide) (by decide)]
  refine sepConj_mono (Entails.refl _) ?_
  refine sepConj_mono (pointsTo32_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo32_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)

theorem stack_280_184_split (sp : BitVec 64) :
    memRegion (sp - 280#64) 184 =
      (∃∗ u_280 : BitVec 64, (sp - 280#64) ↦₆₄ u_280) ∗
      (∃∗ u_272 : BitVec 8, (sp - 272#64) ↦₈ u_272) ∗
      memRegion (sp - 271#64) 7 ∗
      (∃∗ u_264 : BitVec 32, (sp - 264#64) ↦₃₂ u_264) ∗
      (∃∗ u_260 : BitVec 16, (sp - 260#64) ↦₁₆ u_260) ∗
      memRegion (sp - 258#64) 26 ∗
      (∃∗ u_232 : BitVec 32, (sp - 232#64) ↦₃₂ u_232) ∗
      (∃∗ u_228 : BitVec 16, (sp - 228#64) ↦₁₆ u_228) ∗
      memRegion (sp - 226#64) 18 ∗
      (∃∗ u_208 : BitVec 32, (sp - 208#64) ↦₃₂ u_208) ∗
      memRegion (sp - 204#64) 20 ∗
      (∃∗ u_184 : BitVec 64, (sp - 184#64) ↦₆₄ u_184) ∗
      (∃∗ u_176 : BitVec 16, (sp - 176#64) ↦₁₆ u_176) ∗
      memRegion (sp - 174#64) 14 ∗
      memRegion (sp - 160#64) 33 ∗
      memRegion (sp - 127#64) 1 ∗
      memRegion (sp - 126#64) 14 ∗
      memRegion (sp - 112#64) 16 := by
  rw [mr_cut' sp 280 272 8 176 184 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 272 271 1 175 176 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 271 264 7 168 175 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 264 260 4 164 168 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 260 258 2 162 164 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 258 232 26 136 162 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 232 228 4 132 136 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 228 226 2 130 132 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 226 208 18 112 130 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 208 204 4 108 112 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 204 184 20 88 108 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 184 176 8 80 88 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 176 174 2 78 80 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 174 160 14 64 78 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 160 127 33 31 64 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 127 126 1 30 31 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 126 112 14 16 30 rfl rfl (by decide) (by decide) (by decide)]
  simp only [memRegion_eight, memRegion_four, memRegion_two, memRegion_one]

theorem memRegion_48_split_8_2_38 (sp : BitVec 64) :
    memRegion (sp - 160#64) 48 =
      (∃∗ u_160 : BitVec 64, (sp - 160#64) ↦₆₄ u_160) ∗
      (∃∗ u_152 : BitVec 16, (sp - 152#64) ↦₁₆ u_152) ∗
      memRegion (sp - 150#64) 38 := by
  rw [mr_cut' sp 160 152 8 40 48 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 152 150 2 38 40 rfl rfl (by decide) (by decide) (by decide)]
  simp only [memRegion_eight, memRegion_two]

theorem memRegion_24_of_8_2_14 (sp : BitVec 64) (w136 : BitVec 64) (h128 : BitVec 16) :
    (((sp - 136#64) ↦₆₄ w136) ∗ ((sp - 128#64) ↦₁₆ h128) ∗ memRegion (sp - 126#64) 14) ⊢
      memRegion (sp - 136#64) 24 := by
  rw [mr_cut' sp 136 128 8 16 24 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 128 126 2 14 16 rfl rfl (by decide) (by decide) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo16_entails_memRegion _ _) (Entails.refl _))

theorem ret_264_split_some (r : BitVec 64) :
    memRegion r 264 =
      (∃∗ w0 : BitVec 64, r ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (r + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (r + 16#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (r + 24#64) ↦₆₄ w3) ∗
      (∃∗ w4 : BitVec 64, (r + 32#64) ↦₆₄ w4) ∗
      (∃∗ w5 : BitVec 64, (r + 40#64) ↦₆₄ w5) ∗
      (∃∗ w6 : BitVec 64, (r + 48#64) ↦₆₄ w6) ∗
      (∃∗ w7 : BitVec 64, (r + 56#64) ↦₆₄ w7) ∗
      (∃∗ w8 : BitVec 64, (r + 64#64) ↦₆₄ w8) ∗
      (∃∗ w9 : BitVec 64, (r + 72#64) ↦₆₄ w9) ∗
      (∃∗ w10 : BitVec 64, (r + 80#64) ↦₆₄ w10) ∗
      (∃∗ w11 : BitVec 64, (r + 88#64) ↦₆₄ w11) ∗
      (∃∗ w12 : BitVec 64, (r + 96#64) ↦₆₄ w12) ∗
      (∃∗ w13 : BitVec 64, (r + 104#64) ↦₆₄ w13) ∗
      (∃∗ w14 : BitVec 64, (r + 112#64) ↦₆₄ w14) ∗
      (∃∗ w15 : BitVec 64, (r + 120#64) ↦₆₄ w15) ∗
      (∃∗ w16 : BitVec 64, (r + 128#64) ↦₆₄ w16) ∗
      (∃∗ w17 : BitVec 64, (r + 136#64) ↦₆₄ w17) ∗
      (∃∗ w18 : BitVec 64, (r + 144#64) ↦₆₄ w18) ∗
      (∃∗ w19 : BitVec 64, (r + 152#64) ↦₆₄ w19) ∗
      (∃∗ w20 : BitVec 64, (r + 160#64) ↦₆₄ w20) ∗
      (∃∗ w21 : BitVec 64, (r + 168#64) ↦₆₄ w21) ∗
      (∃∗ w22 : BitVec 64, (r + 176#64) ↦₆₄ w22) ∗
      (∃∗ w23 : BitVec 64, (r + 184#64) ↦₆₄ w23) ∗
      (∃∗ w24 : BitVec 64, (r + 192#64) ↦₆₄ w24) ∗
      memRegion (r + 200#64) 32 ∗
      memRegion (r + 232#64) 32 := by
  have h0 : memRegion r 264 = memRegion r 8 ∗ memRegion (r + 8#64) 256 :=
    memRegion_split' (by decide) rfl (by decide)
  rw [h0]
  rw [mr_cut_add r 8 8 248 (by decide)]
  rw [mr_cut_add r 16 8 240 (by decide)]
  rw [mr_cut_add r 24 8 232 (by decide)]
  rw [mr_cut_add r 32 8 224 (by decide)]
  rw [mr_cut_add r 40 8 216 (by decide)]
  rw [mr_cut_add r 48 8 208 (by decide)]
  rw [mr_cut_add r 56 8 200 (by decide)]
  rw [mr_cut_add r 64 8 192 (by decide)]
  rw [mr_cut_add r 72 8 184 (by decide)]
  rw [mr_cut_add r 80 8 176 (by decide)]
  rw [mr_cut_add r 88 8 168 (by decide)]
  rw [mr_cut_add r 96 8 160 (by decide)]
  rw [mr_cut_add r 104 8 152 (by decide)]
  rw [mr_cut_add r 112 8 144 (by decide)]
  rw [mr_cut_add r 120 8 136 (by decide)]
  rw [mr_cut_add r 128 8 128 (by decide)]
  rw [mr_cut_add r 136 8 120 (by decide)]
  rw [mr_cut_add r 144 8 112 (by decide)]
  rw [mr_cut_add r 152 8 104 (by decide)]
  rw [mr_cut_add r 160 8 96 (by decide)]
  rw [mr_cut_add r 168 8 88 (by decide)]
  rw [mr_cut_add r 176 8 80 (by decide)]
  rw [mr_cut_add r 184 8 72 (by decide)]
  rw [mr_cut_add r 192 8 64 (by decide)]
  rw [mr_cut_add r 200 32 32 (by decide)]
  simp only [memRegion_eight]

theorem ret_264_split_none (r : BitVec 64) :
    memRegion r 264 =
      (∃∗ r0 : BitVec 64, r ↦₆₄ r0) ∗
      (∃∗ r8 : BitVec 64, (r + 8#64) ↦₆₄ r8) ∗
      (∃∗ r16 : BitVec 32, (r + 16#64) ↦₃₂ r16) ∗
      (∃∗ r20 : BitVec 16, (r + 20#64) ↦₁₆ r20) ∗
      (∃∗ r22 : BitVec 64, (r + 22#64) ↦₆₄ r22) ∗
      (∃∗ r30 : BitVec 64, (r + 30#64) ↦₆₄ r30) ∗
      (∃∗ r38 : BitVec 16, (r + 38#64) ↦₁₆ r38) ∗
      memRegion (r + 40#64) 16 ∗
      memRegion (r + 56#64) 208 := by
  have h0 : memRegion r 264 = memRegion r 8 ∗ memRegion (r + 8#64) 256 :=
    memRegion_split' (by decide) rfl (by decide)
  rw [h0]
  rw [mr_cut_add r 8 8 248 (by decide)]
  rw [mr_cut_add r 16 4 244 (by decide)]
  rw [mr_cut_add r 20 2 242 (by decide)]
  rw [mr_cut_add r 22 8 234 (by decide)]
  rw [mr_cut_add r 30 8 226 (by decide)]
  rw [mr_cut_add r 38 2 224 (by decide)]
  rw [mr_cut_add r 40 16 208 (by decide)]
  simp only [memRegion_eight, memRegion_four, memRegion_two]

theorem memRegion_48_of_8_2_38 (sp : BitVec 64) (u_160 : BitVec 64) (u_152 : BitVec 16) :
    (((sp - 160#64) ↦₆₄ u_160) ∗ ((sp - 152#64) ↦₁₆ u_152) ∗ memRegion (sp - 150#64) 38) ⊢
      memRegion (sp - 160#64) 48 := by
  rw [mr_cut' sp 160 152 8 40 48 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 152 150 2 38 40 rfl rfl (by decide) (by decide) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo16_entails_memRegion _ _) (Entails.refl _))

theorem memRegion_48_of_8_8_8_8_2_14 (sp : BitVec 64)
    (w160 w152 w144 w136 : BitVec 64) (h128 : BitVec 16) :
    (((sp - 160#64) ↦₆₄ w160) ∗ ((sp - 152#64) ↦₆₄ w152) ∗
     ((sp - 144#64) ↦₆₄ w144) ∗ ((sp - 136#64) ↦₆₄ w136) ∗
     ((sp - 128#64) ↦₁₆ h128) ∗ memRegion (sp - 126#64) 14) ⊢
      memRegion (sp - 160#64) 48 := by
  rw [mr_cut' sp 160 152 8 40 48 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 152 144 8 32 40 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 144 136 8 24 32 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 136 128 8 16 24 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 128 126 2 14 16 rfl rfl (by decide) (by decide) (by decide)]
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  exact sepConj_mono (pointsTo16_entails_memRegion _ _) (Entails.refl _)

theorem memRegion_24_of_8_8_8 (sp : BitVec 64) (w0 w1 w2 : BitVec 64) :
    (((sp - 456#64) ↦₆₄ w0) ∗ ((sp - 448#64) ↦₆₄ w1) ∗ ((sp - 440#64) ↦₆₄ w2)) ⊢
      memRegion (sp - 456#64) 24 := by
  rw [mr_cut' sp 456 448 8 16 24 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 448 440 8 8 16 rfl rfl (by decide) (by decide) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))

theorem stack_280_184_fold (sp : BitVec 64)
    (u_280 : BitVec 64) (u_272 : BitVec 8) (u_264 : BitVec 32) (u_260 : BitVec 16)
    (u_232 : BitVec 32) (u_228 : BitVec 16) (u_208 : BitVec 32)
    (u_184 : BitVec 64) (u_176 : BitVec 16) :
    (((sp - 280#64) ↦₆₄ u_280) ∗ ((sp - 272#64) ↦₈ u_272) ∗ memRegion (sp - 271#64) 7 ∗
     ((sp - 264#64) ↦₃₂ u_264) ∗ ((sp - 260#64) ↦₁₆ u_260) ∗ memRegion (sp - 258#64) 26 ∗
     ((sp - 232#64) ↦₃₂ u_232) ∗ ((sp - 228#64) ↦₁₆ u_228) ∗ memRegion (sp - 226#64) 18 ∗
     ((sp - 208#64) ↦₃₂ u_208) ∗ memRegion (sp - 204#64) 20 ∗
     ((sp - 184#64) ↦₆₄ u_184) ∗ ((sp - 176#64) ↦₁₆ u_176) ∗ memRegion (sp - 174#64) 14 ∗
     memRegion (sp - 160#64) 48 ∗ memRegion (sp - 112#64) 16) ⊢
      memRegion (sp - 280#64) 184 := by
  rw [mr_cut' sp 280 272 8 176 184 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 272 271 1 175 176 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 271 264 7 168 175 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 264 260 4 164 168 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 260 258 2 162 164 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 258 232 26 136 162 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 232 228 4 132 136 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 228 226 2 130 132 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 226 208 18 112 130 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 208 204 4 108 112 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 204 184 20 88 108 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 184 176 8 80 88 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 176 174 2 78 80 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 174 160 14 64 78 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 160 112 48 16 64 rfl rfl (by decide) (by decide) (by decide)]
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (Entails.refl _) ?_
  refine sepConj_mono (pointsTo32_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo16_entails_memRegion _ _) ?_
  refine sepConj_mono (Entails.refl _) ?_
  refine sepConj_mono (pointsTo32_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo16_entails_memRegion _ _) ?_
  refine sepConj_mono (Entails.refl _) ?_
  refine sepConj_mono (pointsTo32_entails_memRegion _ _) ?_
  refine sepConj_mono (Entails.refl _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo16_entails_memRegion _ _) ?_
  exact sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (Entails.refl _))

theorem stack_400_fold (sp : BitVec 64) (bs104 bs32 : List (BitVec 8))
    (h104 : bs104.length = 104) (h32 : bs32.length = 32)
    (w296 : BitVec 64) (d288 d284 : BitVec 32) :
    (memRegion (sp - 496#64) 40 ∗
     memRegion (sp - 456#64) 24 ∗
     ((sp - 432#64) ↦ₛ bs104) ∗
     ((sp - 328#64) ↦ₛ bs32) ∗
     ((sp - 296#64) ↦₆₄ w296) ∗
     ((sp - 288#64) ↦₃₂ d288) ∗
     ((sp - 284#64) ↦₃₂ d284) ∗
     memRegion (sp - 280#64) 184) ⊢
      memRegion (sp - 496#64) 400 := by
  rw [mr_cut' sp 496 456 40 360 400 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 456 432 24 336 360 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 432 328 104 232 336 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 328 296 32 200 232 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 296 288 8 192 200 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 288 284 4 188 192 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 284 280 4 184 188 rfl rfl (by decide) (by decide) (by decide)]
  refine sepConj_mono (Entails.refl _) ?_
  refine sepConj_mono (Entails.refl _) ?_
  refine sepConj_mono (h104 ▸ pointsToBytes_entails_memRegion _ _) ?_
  refine sepConj_mono (h32 ▸ pointsToBytes_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo32_entails_memRegion _ _) ?_
  exact sepConj_mono (pointsTo32_entails_memRegion _ _) (Entails.refl _)

theorem vecAt_chains_stack_fold (A : RustAlloc) (sp : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) (hchains : G.chains.length = st.receiverChains.length) :
    (((sp - 456#64) ↦₆₄ G.chainsCap) ∗
     ((sp - 448#64) ↦₆₄ G.chainsPtr) ∗
     ((sp - 440#64) ↦₆₄ BitVec.ofNat 64 st.receiverChains.length) ∗
     vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains)) ⊢
      vecAt A 104 8 (chainAt A) (sp - 456#64) G.chainsCap G.chainsPtr
        (G.chains.zip st.receiverChains) := by
  unfold vecAt vecHeader
  have hzip : (G.chains.zip st.receiverChains).length = st.receiverChains.length := by
    simp [hchains]
  rw [hzip]
  have h1 : sp - 456#64 + 8#64 = sp - 448#64 := by bv_omega
  have h2 : sp - 456#64 + 16#64 = sp - 440#64 := by bv_omega
  rw [h1, h2]
  simp only [sepConj_assoc]
  exact Entails.refl _


end ReceiveRatchetFrom
end CryptoVerification.LibsignalTripleRatchet
