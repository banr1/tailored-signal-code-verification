/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Decode
import all Init.Data.String.Defs
import ProofLib.SepLogic.WPp

/-!
# Frame and Four-Case Decomposition for `OutgoingTripleRatchet::from_session_state`

Stack-frame, `sessionStateAt`, and `ret`-buffer split/fold lemmas and the four-way branch
combinator (`subroutine_ok_of_cases4`) for `<OutgoingTripleRatchet>::from_session_state`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.Ratchet CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_setWidth32 zeroExtend64_setWidth16 zeroExtend32_setWidth16
  zeroExtend64_setWidth8 zeroExtend32_setWidth8
  localIk_bytes0_7_low32 localIk_bytes0_7_mid16 localIk_bytes0_7_hi8
  shift40_shift16_eq_shift56

/-! ## `sessionStateAt` and frame decomposition for `OTR::from_session_state` -/

theorem sessionStateAt_sender_none (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) (hsc : st.senderChain = none) :
    sessionStateAt A ss G st ⊢ ⌜G.sender = none⌝ ∗ sessionStateAt A ss G st := by
  cases hGs : G.sender with
  | none => exact Entails.pure_right rfl (Entails.refl _)
  | some sg =>
    have hpull : sessionStateAt A ss G st = (⌜False⌝ ∗
        (⌜PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
          (match st.remoteIdentity with
           | none => G.remoteIk.bytes = []
           | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
          G.chains.length = st.receiverChains.length ∧
          G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
          G.localIk.bytes.length = 33 ∧
          (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
        vecGhostAt A G.localIk ss ∗
        vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
        vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
        vecAt A 104 8 (chainAt A) (ss + 0x48#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        vecGhostAt A G.alice (ss + 0x60#64) ∗
        vecU8At A (ss + 0x78#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
        optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
        optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
        ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗
        ((ss + 0x14c#64) ↦₃₂ st.previousCounter) ∗
        ((ss + 0x150#64) ↦ₛ G.regIds))) := by
      unfold sessionStateAt
      rw [hsc, hGs]
      simp only [optSenderChainAt]
      ac_rfl
    rw [hpull]
    exact Entails.pure_left fun h => False.elim h

def sessionFromNoneFrame (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : SepProp :=
  ⌜PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
    G.chains.length = st.receiverChains.length ∧
    G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧
    (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
    vecGhostAt A G.localIk ss ∗
    vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
    vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
    vecAt A 104 8 (chainAt A) (ss + 0x48#64) G.chainsCap G.chainsPtr
      (G.chains.zip st.receiverChains) ∗
    vecGhostAt A G.alice (ss + 0x60#64) ∗
    vecU8At A (ss + 0x78#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
    memRegion (ss + 0x98#64) 96 ∗
    optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
    optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
    ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗
    ((ss + 0x14c#64) ↦₃₂ st.previousCounter) ∗
    ((ss + 0x150#64) ↦ₛ G.regIds)

theorem sessionStateAt_eq_from_none (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) (hsc : st.senderChain = none) (hGs : G.sender = none) :
    sessionStateAt A ss G st =
      (((ss + 0x90#64) ↦₆₄ noneCap) ∗ sessionFromNoneFrame A ss G st) := by
  unfold sessionStateAt sessionFromNoneFrame
  rw [hsc, hGs]
  simp only [optSenderChainAt, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  ac_rfl

def vecU8Live (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8Buf_eq_bytes_live_of_ne_zero (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (h : cap ≠ 0) :
    vecU8Buf A cap ptr bs = (ptr ↦ₛ bs) ∗ vecU8Live A cap ptr bs := by
  unfold vecU8Buf vecU8Live
  rw [ite_eq_right_iff.mpr (fun hc => absurd hc h),
      ite_eq_right_iff.mpr (fun hc => absurd hc h)]
  ac_rfl

theorem vecU8Buf_bounds (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8Buf
  exact Entails.pure_left fun h => Entails.pure_right h (Entails.pure_right h (Entails.refl _))

theorem vecU8Buf_empty_intro (A : RustAlloc) :
    emp ⊢ vecU8Buf A 0#64 1#64 [] := by
  dsimp only [vecU8Buf, ↓reduceIte]
  exact Entails.pure_right ⟨by decide, by decide, by decide⟩ (Entails.refl _)

/-- Frame of `sessionStateAt` fields never touched at all in `OTR::from_session_state`. -/
def sessionFromUntouched (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) (sg : SenderChainGhost) : SepProp :=
  (ss ↦₆₄ G.localIk.cap) ∗
    vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
    vecAt A 104 8 (chainAt A) (ss + 0x48#64) G.chainsCap G.chainsPtr
      (G.chains.zip st.receiverChains) ∗
    vecGhostAt A G.alice (ss + 0x60#64) ∗
    ((ss + 0xa8#64) ↦₆₄ sg.priv.cap) ∗
    vecAt A 104 8 (messageKeyAt A) (ss + 0xc0#64) sg.mkCap sg.mkPtr [] ∗
    memRegion (ss + 0xf4#64) 4 ∗
    optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
    optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
    ((ss + 0x150#64) ↦ₛ G.regIds)

theorem sessionStateAt_eq_from_some (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) (sg : SenderChainGhost) (sc : SenderChain)
    (hGs : G.sender = some sg) (hsc : st.senderChain = some sc)
    (pqPin : VecPin) (pqBs : List (BitVec 8)) :
    sessionStateAt A ss { G with pq := pqPin } { st with pqRatchetState := pqBs } =
      (⌜PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
        (match st.remoteIdentity with
         | none => G.remoteIk.bytes = []
         | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
        G.chains.length = st.receiverChains.length ∧
        G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
        G.localIk.bytes.length = 33 ∧
        (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
       ⌜PublicKey.deserialize sg.srk.bytes = .ok sc.ratchetKey.publicKey ∧
        sg.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
        Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
        sg.srk.bytes.length = 33⌝ ∗
       ((ss + 0x08#64) ↦₆₄ G.localIk.ptr) ∗
       ((ss + 0x10#64) ↦₆₄ BitVec.ofNat 64 G.localIk.bytes.length) ∗
       vecU8Buf A G.localIk.cap G.localIk.ptr G.localIk.bytes ∗
       vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
       ((ss + 0x78#64) ↦₆₄ pqPin.cap) ∗ ((ss + 0x80#64) ↦₆₄ pqPin.ptr) ∗
       ((ss + 0x88#64) ↦₆₄ BitVec.ofNat 64 pqBs.length) ∗
       vecU8Buf A pqPin.cap pqPin.ptr pqBs ∗
       ((ss + 0x90#64) ↦₆₄ sg.srk.cap) ∗ ((ss + 0x98#64) ↦₆₄ sg.srk.ptr) ∗
       ((ss + 0xa0#64) ↦₆₄ BitVec.ofNat 64 sg.srk.bytes.length) ∗
       vecU8Buf A sg.srk.cap sg.srk.ptr sg.srk.bytes ∗
       ((ss + 0xb0#64) ↦₆₄ sg.priv.ptr) ∗
       ((ss + 0xb8#64) ↦₆₄ BitVec.ofNat 64 sg.priv.bytes.length) ∗
       vecU8Buf A sg.priv.cap sg.priv.ptr sg.priv.bytes ∗
       ((ss + 0xd8#64) ↦₆₄ sg.ck.cap) ∗ ((ss + 0xe0#64) ↦₆₄ sg.ck.ptr) ∗
       ((ss + 0xe8#64) ↦₆₄ 32#64) ∗ ((ss + 0xf0#64) ↦₃₂ sc.chainKey.index) ∗
       vecU8Buf A sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key) ∗
       ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗
       ((ss + 0x14c#64) ↦₃₂ st.previousCounter) ∗
       sessionFromUntouched A ss G st sg) := by
  unfold sessionStateAt sessionFromUntouched
  dsimp only
  rw [hGs, hsc]
  unfold optSenderChainAt vecGhostAt optChainKeyAt
  simp only [vecU8At_eq_cells_buf, keyToBytes32_length,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  ac_rfl

/-! ## Sret, stack-frame, and `ret` buffer split/fold lemmas -/

private theorem isBlock_pointsToBytes_vector (a : BitVec 64) {n : Nat} (v : List.Vector (BitVec 8) n) :
    IsBlock (a ↦ₛ v.toList) a n (fun m => n ≤ 2 ^ 64 ∧ m.readBytes a n = v.toList) := by
  have h := IsBlock.pointsToBytes a v.toList
  rwa [v.toList_length] at h

theorem memRegion_vector (a : BitVec 64) (n : Nat) (hn : n ≤ 2 ^ 64 := by decide) :
    memRegion a n = ∃∗ v : List.Vector (BitVec 8) n, a ↦ₛ v.toList :=
  IsBlock.eq_of_iff (IsBlock.memRegion a n)
    (IsBlock.sepExists fun v => isBlock_pointsToBytes_vector a v)
    (fun m => ⟨fun _ => ⟨⟨m.readBytes a n, Memory.readBytes_length m a n⟩, hn, rfl⟩,
      fun _ => trivial⟩)

theorem sret33_entails_memRegion40 (a : BitVec 64) (b0 : BitVec 8) (bs : List (BitVec 8))
    (h : bs.length = 32) :
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦ₛ bs) ∗ memRegion (a + 33#64) 7) ⊢ memRegion a 40 := by
  have h1 := pointsTo8_entails_memRegion a b0
  have h2 := pointsToBytes_entails_memRegion (a + 1#64) bs
  rw [h] at h2
  rw [memRegion_split a 1 39 (by decide), mr_cut_add a 1 32 7 (by decide)]
  exact sepConj_mono h1 (sepConj_mono h2 (Entails.refl _))

theorem memRegion40_split_deser (a : BitVec 64) :
    memRegion a 40 =
      (∃∗ tag0 : BitVec 8, a ↦₈ tag0) ∗
      (∃∗ v : List.Vector (BitVec 8) 32, (a + 1#64) ↦ₛ v.toList) ∗
      memRegion (a + 33#64) 7 := by
  rw [memRegion_split a 1 39 (by decide), mr_cut_add a 1 32 7 (by decide),
      memRegion_one a, memRegion_vector (a + 1#64) 32]

theorem memRegion40_split_ck (a : BitVec 64) :
    memRegion a 40 =
      (∃∗ c0 : BitVec 16, a ↦₁₆ c0) ∗
      (∃∗ c2 : BitVec 8, (a + 2#64) ↦₈ c2) ∗
      (∃∗ c3 : BitVec 64, (a + 3#64) ↦₆₄ c3) ∗
      memRegion (a + 11#64) 29 := by
  rw [memRegion_split a 2 38 (by decide),
      mr_cut_add a 2 1 37 (by decide),
      mr_cut_add a 3 8 29 (by decide),
      memRegion_two a, memRegion_one (a + 2#64), memRegion_eight (a + 3#64)]

theorem ck_scratch_entails_memRegion40 (a w0 : BitVec 64) (w8 : BitVec 16) (w10 : BitVec 8) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₁₆ w8) ∗ ((a + 10#64) ↦₈ w10) ∗ memRegion (a + 11#64) 29) ⊢
      memRegion a 40 := by
  have h0 := pointsTo64_entails_memRegion a w0
  have h8 := pointsTo16_entails_memRegion (a + 8#64) w8
  have h10 := pointsTo8_entails_memRegion (a + 10#64) w10
  rw [memRegion_split a 8 32 (by decide),
      mr_cut_add a 8 2 30 (by decide),
      mr_cut_add a 10 1 29 (by decide)]
  exact sepConj_mono h0 (sepConj_mono h8 (sepConj_mono h10 (Entails.refl _)))

theorem pointsTo64_of_1_1_4_2_entails (a : BitVec 64) (b0 b1 : BitVec 8)
    (v2 : BitVec 32) (v6 : BitVec 16) :
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₃₂ v2) ∗ ((a + 6#64) ↦₁₆ v6)) ⊢
      ∃∗ w : BitVec 64, a ↦₆₄ w := by
  rw [← memRegion_eight a,
      memRegion_split a 1 7 (by decide),
      mr_cut_add a 1 1 6 (by decide),
      mr_cut_add a 2 4 2 (by decide)]
  exact sepConj_mono (pointsTo8_entails_memRegion a b0)
    (sepConj_mono (pointsTo8_entails_memRegion (a + 1#64) b1)
      (sepConj_mono (pointsTo32_entails_memRegion (a + 2#64) v2)
        (pointsTo16_entails_memRegion (a + 6#64) v6)))

theorem issStr_missingSenderChain_len :
    BitVec.ofNat 64 (invalidSessionStructureStr .missingSenderChain).length = 20#64 := by rfl_kernel

theorem issStr_versionTooLarge_len :
    BitVec.ofNat 64 (invalidSessionStructureStr .versionTooLarge).length = 26#64 := by rfl_kernel

theorem issStr_missingRemoteIdentity_len :
    BitVec.ofNat 64 (invalidSessionStructureStr .missingRemoteIdentity).length = 27#64 := by rfl_kernel

theorem spe_missingRemote_at_sret (A : RustAlloc) (a p w24 : BitVec 64) (w32 : BitVec 16) :
    ((a ↦₆₄ speWord 20) ∗ ((a + 8#64) ↦₆₄ p) ∗
      ((a + 16#64) ↦₆₄ 27#64) ∗ (p ↦ᵣ invalidSessionStructureStr .missingRemoteIdentity) ∗
      ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₁₆ w32) ∗
      memRegion (a + 34#64) 6 ∗ memRegion (a + 40#64) 8) ⊢
    speAt A [] a (.invalidSessionStructure .missingRemoteIdentity) := by
  dsimp only [speAt, strRefAt]
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_lin
  rw [h16, issStr_missingRemoteIdentity_len]
  have h24 :
      (((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₁₆ w32) ∗
        memRegion (a + 34#64) 6 ∗ memRegion (a + 40#64) 8) ⊢
      memRegion (a + 24#64) 24 := by
    rw [mr_cut_add a 24 8 16 (by decide),
        mr_cut_add a 32 2 14 (by decide),
        mr_cut_add a 34 6 8 (by decide)]
    exact sepConj_mono (pointsTo64_entails_memRegion (a + 24#64) w24)
      (sepConj_mono (pointsTo16_entails_memRegion (a + 32#64) w32)
        (sepConj_mono (Entails.refl _) (Entails.refl _)))
  have hgrp :
      ((a ↦₆₄ speWord 20) ∗ ((a + 8#64) ↦₆₄ p) ∗
        ((a + 16#64) ↦₆₄ 27#64) ∗ (p ↦ᵣ invalidSessionStructureStr .missingRemoteIdentity) ∗
        ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₁₆ w32) ∗
        memRegion (a + 34#64) 6 ∗ memRegion (a + 40#64) 8) =
      ((a ↦₆₄ speWord 20) ∗
        (((a + 8#64) ↦₆₄ p) ∗ ((a + 16#64) ↦₆₄ 27#64) ∗
          (p ↦ᵣ invalidSessionStructureStr .missingRemoteIdentity)) ∗
        (((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₁₆ w32) ∗
          memRegion (a + 34#64) 6 ∗ memRegion (a + 40#64) 8)) := by
    simp only [sepConj_assoc]
  rw [hgrp]
  exact sepConj_mono_right (sepConj_mono
    (Entails.sepExists_intro p (P := fun q =>
      ((a + 8#64) ↦₆₄ q) ∗ ((a + 16#64) ↦₆₄ 27#64) ∗
        (q ↦ᵣ invalidSessionStructureStr .missingRemoteIdentity))) h24)

/-- Split `memRegion (sp - 384#64) 288` for Phase A (`0xb7cc..0xb8f0`). -/
theorem frame288_split_phaseA (sp : BitVec 64) :
    memRegion (sp - 384#64) 288 =
      memRegion (sp - 384#64) 128 ∗
      (∃∗ u80 : BitVec 32, (sp - 256#64) ↦₃₂ u80) ∗
      (∃∗ u84 : BitVec 16, (sp - 252#64) ↦₁₆ u84) ∗
      memRegion (sp - 250#64) 2 ∗
      (∃∗ u88 : BitVec 64, (sp - 248#64) ↦₆₄ u88) ∗
      (∃∗ u90 : BitVec 8, (sp - 240#64) ↦₈ u90) ∗
      memRegion (sp - 239#64) 7 ∗
      (∃∗ u98 : BitVec 32, (sp - 232#64) ↦₃₂ u98) ∗
      (∃∗ u9c : BitVec 16, (sp - 228#64) ↦₁₆ u9c) ∗
      (∃∗ u9e : BitVec 8, (sp - 226#64) ↦₈ u9e) ∗
      memRegion (sp - 225#64) 33 ∗
      (∃∗ uc0 : BitVec 64, (sp - 192#64) ↦₆₄ uc0) ∗
      (∃∗ uc8 : BitVec 8, (sp - 184#64) ↦₈ uc8) ∗
      memRegion (sp - 183#64) 15 ∗
      (∃∗ ud8 : BitVec 64, (sp - 168#64) ↦₆₄ ud8) ∗
      (∃∗ ue0 : BitVec 8, (sp - 160#64) ↦₈ ue0) ∗
      memRegion (sp - 159#64) 7 ∗
      memRegion (sp - 152#64) 40 ∗
      memRegion (sp - 112#64) 16 := by
  rw [mr_cut' sp 384 256 128 160 288 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 256 252 4 156 160 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 252 250 2 154 156 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 250 248 2 152 154 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 248 240 8 144 152 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 240 239 1 143 144 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 239 232 7 136 143 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 232 228 4 132 136 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 228 226 2 130 132 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 226 225 1 129 130 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 225 192 33 96 129 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 192 184 8 88 96 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 184 183 1 87 88 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 183 168 15 72 87 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 168 160 8 64 72 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 160 159 1 63 64 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 159 152 7 56 63 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 152 112 40 16 56 rfl rfl (by decide) (by decide) (by decide)]
  rw [memRegion_four (sp - BitVec.ofNat 64 256),
      memRegion_two (sp - BitVec.ofNat 64 252),
      memRegion_eight (sp - BitVec.ofNat 64 248),
      memRegion_one (sp - BitVec.ofNat 64 240),
      memRegion_four (sp - BitVec.ofNat 64 232),
      memRegion_two (sp - BitVec.ofNat 64 228),
      memRegion_one (sp - BitVec.ofNat 64 226),
      memRegion_eight (sp - BitVec.ofNat 64 192),
      memRegion_one (sp - BitVec.ofNat 64 184),
      memRegion_eight (sp - BitVec.ofNat 64 168),
      memRegion_one (sp - BitVec.ofNat 64 160)]

/-- Fold Phase A stack slots back into `memRegion (sp - 384#64) 288` (used in Branch 2). -/
theorem frame288_fold_phaseA (sp : BitVec 64)
    (u80 u98 : BitVec 32) (u84 u9c : BitVec 16) (u88 uc0 ud8 : BitVec 64)
    (u90 u9e uc8 ue0 : BitVec 8) :
    (memRegion (sp - 384#64) 128 ∗
      ((sp - 256#64) ↦₃₂ u80) ∗ ((sp - 252#64) ↦₁₆ u84) ∗
      memRegion (sp - 250#64) 2 ∗ ((sp - 248#64) ↦₆₄ u88) ∗
      ((sp - 240#64) ↦₈ u90) ∗ memRegion (sp - 239#64) 7 ∗
      ((sp - 232#64) ↦₃₂ u98) ∗ ((sp - 228#64) ↦₁₆ u9c) ∗
      ((sp - 226#64) ↦₈ u9e) ∗ memRegion (sp - 225#64) 33 ∗
      ((sp - 192#64) ↦₆₄ uc0) ∗ ((sp - 184#64) ↦₈ uc8) ∗
      memRegion (sp - 183#64) 15 ∗ ((sp - 168#64) ↦₆₄ ud8) ∗
      ((sp - 160#64) ↦₈ ue0) ∗ memRegion (sp - 159#64) 7 ∗
      memRegion (sp - 152#64) 40 ∗ memRegion (sp - 112#64) 16) ⊢
    memRegion (sp - 384#64) 288 := by
  rw [frame288_split_phaseA sp]
  refine sepConj_mono (Entails.refl _) (sepConj_mono (Entails.sepExists_intro u80) ?_)
  refine sepConj_mono (Entails.sepExists_intro u84) (sepConj_mono (Entails.refl _) ?_)
  refine sepConj_mono (Entails.sepExists_intro u88) (sepConj_mono (Entails.sepExists_intro u90) ?_)
  refine sepConj_mono (Entails.refl _) (sepConj_mono (Entails.sepExists_intro u98) ?_)
  refine sepConj_mono (Entails.sepExists_intro u9c) (sepConj_mono (Entails.sepExists_intro u9e) ?_)
  refine sepConj_mono (Entails.refl _) (sepConj_mono (Entails.sepExists_intro uc0) ?_)
  refine sepConj_mono (Entails.sepExists_intro uc8) (sepConj_mono (Entails.refl _) ?_)
  refine sepConj_mono (Entails.sepExists_intro ud8) (sepConj_mono (Entails.sepExists_intro ue0) ?_)
  exact sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (Entails.refl _))

/-- Split `memRegion (sp - 384#64) 128` for Phase B (`0xb990..`). -/
theorem frame128_split_phaseB (sp : BitVec 64) :
    memRegion (sp - 384#64) 128 =
      (∃∗ s00 : BitVec 64, (sp - 384#64) ↦₆₄ s00) ∗
      (∃∗ s08 : BitVec 64, (sp - 376#64) ↦₆₄ s08) ∗
      (∃∗ s10 : BitVec 64, (sp - 368#64) ↦₆₄ s10) ∗
      (∃∗ s18 : BitVec 64, (sp - 360#64) ↦₆₄ s18) ∗
      (∃∗ s20 : BitVec 32, (sp - 352#64) ↦₃₂ s20) ∗
      (∃∗ s24 : BitVec 32, (sp - 348#64) ↦₃₂ s24) ∗
      (∃∗ s28 : BitVec 32, (sp - 344#64) ↦₃₂ s28) ∗
      (∃∗ s2c : BitVec 32, (sp - 340#64) ↦₃₂ s2c) ∗
      (∃∗ s30 : BitVec 64, (sp - 336#64) ↦₆₄ s30) ∗
      (∃∗ s38 : BitVec 64, (sp - 328#64) ↦₆₄ s38) ∗
      (∃∗ s40 : BitVec 64, (sp - 320#64) ↦₆₄ s40) ∗
      (∃∗ s48 : BitVec 64, (sp - 312#64) ↦₆₄ s48) ∗
      (∃∗ s50 : BitVec 64, (sp - 304#64) ↦₆₄ s50) ∗
      memRegion (sp - 296#64) 4 ∗
      (∃∗ s5c : BitVec 32, (sp - 292#64) ↦₃₂ s5c) ∗
      (∃∗ s60 : BitVec 32, (sp - 288#64) ↦₃₂ s60) ∗
      (∃∗ s64 : BitVec 32, (sp - 284#64) ↦₃₂ s64) ∗
      (∃∗ s68 : BitVec 64, (sp - 280#64) ↦₆₄ s68) ∗
      (∃∗ s70 : BitVec 64, (sp - 272#64) ↦₆₄ s70) ∗
      (∃∗ s78 : BitVec 64, (sp - 264#64) ↦₆₄ s78) := by
  rw [mr_cut' sp 384 376 8 120 128 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 376 368 8 112 120 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 368 360 8 104 112 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 360 352 8 96 104 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 352 348 4 92 96 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 348 344 4 88 92 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 344 340 4 84 88 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 340 336 4 80 84 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 336 328 8 72 80 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 328 320 8 64 72 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 320 312 8 56 64 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 312 304 8 48 56 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 304 296 8 40 48 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 296 292 4 36 40 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 292 288 4 32 36 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 288 284 4 28 32 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 284 280 4 24 28 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 280 272 8 16 24 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 272 264 8 8 16 rfl rfl (by decide) (by decide) (by decide)]
  rw [memRegion_four (sp - BitVec.ofNat 64 352),
      memRegion_four (sp - BitVec.ofNat 64 348),
      memRegion_four (sp - BitVec.ofNat 64 344),
      memRegion_four (sp - BitVec.ofNat 64 340),
      memRegion_four (sp - BitVec.ofNat 64 292),
      memRegion_four (sp - BitVec.ofNat 64 288),
      memRegion_four (sp - BitVec.ofNat 64 284)]
  simp only [memRegion_eight]

theorem frame128_fold_phaseB (sp : BitVec 64)
    (s00 s08 s10 s18 s30 s38 s40 s48 s50 s68 s70 s78 : BitVec 64)
    (s20 s24 s28 s2c s5c s60 s64 : BitVec 32) :
    (((sp - 384#64) ↦₆₄ s00) ∗ ((sp - 376#64) ↦₆₄ s08) ∗
      ((sp - 368#64) ↦₆₄ s10) ∗ ((sp - 360#64) ↦₆₄ s18) ∗
      ((sp - 352#64) ↦₃₂ s20) ∗ ((sp - 348#64) ↦₃₂ s24) ∗
      ((sp - 344#64) ↦₃₂ s28) ∗ ((sp - 340#64) ↦₃₂ s2c) ∗
      ((sp - 336#64) ↦₆₄ s30) ∗ ((sp - 328#64) ↦₆₄ s38) ∗
      ((sp - 320#64) ↦₆₄ s40) ∗ ((sp - 312#64) ↦₆₄ s48) ∗
      ((sp - 304#64) ↦₆₄ s50) ∗ memRegion (sp - 296#64) 4 ∗
      ((sp - 292#64) ↦₃₂ s5c) ∗ ((sp - 288#64) ↦₃₂ s60) ∗
      ((sp - 284#64) ↦₃₂ s64) ∗ ((sp - 280#64) ↦₆₄ s68) ∗
      ((sp - 272#64) ↦₆₄ s70) ∗ ((sp - 264#64) ↦₆₄ s78)) ⊢
    memRegion (sp - 384#64) 128 := by
  rw [frame128_split_phaseB sp]
  refine sepConj_mono (Entails.sepExists_intro s00) (sepConj_mono (Entails.sepExists_intro s08) ?_)
  refine sepConj_mono (Entails.sepExists_intro s10) (sepConj_mono (Entails.sepExists_intro s18) ?_)
  refine sepConj_mono (Entails.sepExists_intro s20) (sepConj_mono (Entails.sepExists_intro s24) ?_)
  refine sepConj_mono (Entails.sepExists_intro s28) (sepConj_mono (Entails.sepExists_intro s2c) ?_)
  refine sepConj_mono (Entails.sepExists_intro s30) (sepConj_mono (Entails.sepExists_intro s38) ?_)
  refine sepConj_mono (Entails.sepExists_intro s40) (sepConj_mono (Entails.sepExists_intro s48) ?_)
  refine sepConj_mono (Entails.sepExists_intro s50) (sepConj_mono (Entails.refl _) ?_)
  refine sepConj_mono (Entails.sepExists_intro s5c) (sepConj_mono (Entails.sepExists_intro s60) ?_)
  refine sepConj_mono (Entails.sepExists_intro s64) (sepConj_mono (Entails.sepExists_intro s68) ?_)
  exact sepConj_mono (Entails.sepExists_intro s70) (Entails.sepExists_intro s78)

/-- Split `memRegion (sp - 225#64) 33` and `memRegion (sp - 183#64) 15` for Phase B. -/
theorem frame33_split (sp : BitVec 64) :
    memRegion (sp - 225#64) 33 =
      memRegion (sp - 225#64) 1 ∗
      (∃∗ ua0 : BitVec 64, (sp - 224#64) ↦₆₄ ua0) ∗
      (∃∗ ua8 : BitVec 8, (sp - 216#64) ↦₈ ua8) ∗
      memRegion (sp - 215#64) 7 ∗
      (∃∗ ub0 : BitVec 32, (sp - 208#64) ↦₃₂ ub0) ∗
      (∃∗ ub4 : BitVec 16, (sp - 204#64) ↦₁₆ ub4) ∗
      memRegion (sp - 202#64) 2 ∗
      (∃∗ ub8 : BitVec 32, (sp - 200#64) ↦₃₂ ub8) ∗
      memRegion (sp - 196#64) 4 := by
  rw [mr_cut' sp 225 224 1 32 33 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 224 216 8 24 32 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 216 215 1 23 24 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 215 208 7 16 23 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 208 204 4 12 16 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 204 202 2 10 12 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 202 200 2 8 10 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 200 196 4 4 8 rfl rfl (by decide) (by decide) (by decide),
      memRegion_eight (sp - BitVec.ofNat 64 224),
      memRegion_one (sp - BitVec.ofNat 64 216),
      memRegion_four (sp - BitVec.ofNat 64 208),
      memRegion_two (sp - BitVec.ofNat 64 204),
      memRegion_four (sp - BitVec.ofNat 64 200)]

theorem frame33_fold (sp ua0 : BitVec 64) (ua8 : BitVec 8) (ub0 ub8 : BitVec 32) (ub4 : BitVec 16) :
    (memRegion (sp - 225#64) 1 ∗ ((sp - 224#64) ↦₆₄ ua0) ∗
      ((sp - 216#64) ↦₈ ua8) ∗ memRegion (sp - 215#64) 7 ∗
      ((sp - 208#64) ↦₃₂ ub0) ∗ ((sp - 204#64) ↦₁₆ ub4) ∗
      memRegion (sp - 202#64) 2 ∗ ((sp - 200#64) ↦₃₂ ub8) ∗
      memRegion (sp - 196#64) 4) ⊢
    memRegion (sp - 225#64) 33 := by
  rw [frame33_split sp]
  refine sepConj_mono (Entails.refl _) (sepConj_mono (Entails.sepExists_intro ua0) ?_)
  refine sepConj_mono (Entails.sepExists_intro ua8) (sepConj_mono (Entails.refl _) ?_)
  refine sepConj_mono (Entails.sepExists_intro ub0) (sepConj_mono (Entails.sepExists_intro ub4) ?_)
  exact sepConj_mono (Entails.refl _) (sepConj_mono (Entails.sepExists_intro ub8) (Entails.refl _))

theorem frame15_split (sp : BitVec 64) :
    memRegion (sp - 183#64) 15 =
      (∃∗ uc9 : BitVec 8, (sp - 183#64) ↦₈ uc9) ∗
      memRegion (sp - 182#64) 6 ∗
      (∃∗ ud0 : BitVec 32, (sp - 176#64) ↦₃₂ ud0) ∗
      (∃∗ ud4 : BitVec 16, (sp - 172#64) ↦₁₆ ud4) ∗
      memRegion (sp - 170#64) 2 := by
  rw [mr_cut' sp 183 182 1 14 15 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 182 176 6 8 14 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 176 172 4 4 8 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 172 170 2 2 4 rfl rfl (by decide) (by decide) (by decide),
      memRegion_one (sp - BitVec.ofNat 64 183),
      memRegion_four (sp - BitVec.ofNat 64 176),
      memRegion_two (sp - BitVec.ofNat 64 172)]

theorem frame15_fold_16 (sp : BitVec 64) (uc8 : BitVec 16) (ud0 : BitVec 32) (ud4 : BitVec 16) :
    (((sp - 184#64) ↦₁₆ uc8) ∗ memRegion (sp - 182#64) 6 ∗
      ((sp - 176#64) ↦₃₂ ud0) ∗ ((sp - 172#64) ↦₁₆ ud4) ∗
      memRegion (sp - 170#64) 2) ⊢
    (∃∗ b : BitVec 8, (sp - 184#64) ↦₈ b) ∗ memRegion (sp - 183#64) 15 := by
  rw [pointsTo16_eq_pointsToBytes (sp - 184#64)]
  simp only [unpack16, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, sepConj_assoc]
  have h183 : sp - 184#64 + 1#64 = sp - 183#64 := by bv_lin
  rw [h183, frame15_split sp]
  refine sepConj_mono (Entails.sepExists_intro _) ?_
  refine sepConj_mono (Entails.sepExists_intro _) (sepConj_mono (Entails.refl _) ?_)
  exact sepConj_mono (Entails.sepExists_intro ud0) (sepConj_mono (Entails.sepExists_intro ud4) (Entails.refl _))

/-- Split `memRegion ret 200` for Branch 1 (`missingSenderChain`). -/
theorem ret200_split_br1 (ret : BitVec 64) :
    memRegion ret 200 =
      (∃∗ w0 : BitVec 64, ret ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (ret + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (ret + 16#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (ret + 24#64) ↦₆₄ w3) ∗
      memRegion (ret + 32#64) 24 ∗
      memRegion (ret + 56#64) 144 := by
  rw [memRegion_split ret 8 192 (by decide),
      mr_cut_add ret 8 8 184 (by decide),
      mr_cut_add ret 16 8 176 (by decide),
      mr_cut_add ret 24 8 168 (by decide),
      mr_cut_add ret 32 24 144 (by decide)]
  simp only [memRegion_eight]

/-- Split `memRegion ret 200` for Branch 2 (`versionTooLarge`). -/
theorem ret200_split_br2 (ret : BitVec 64) :
    memRegion ret 200 =
      (∃∗ w0 : BitVec 64, ret ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (ret + 8#64) ↦₆₄ w1) ∗
      (∃∗ b16 : BitVec 8, (ret + 16#64) ↦₈ b16) ∗
      (∃∗ v17 : BitVec 32, (ret + 17#64) ↦₃₂ v17) ∗
      (∃∗ v21 : BitVec 16, (ret + 21#64) ↦₁₆ v21) ∗
      (∃∗ b23 : BitVec 8, (ret + 23#64) ↦₈ b23) ∗
      (∃∗ w3 : BitVec 64, (ret + 24#64) ↦₆₄ w3) ∗
      memRegion (ret + 32#64) 24 ∗
      memRegion (ret + 56#64) 144 := by
  rw [memRegion_split ret 8 192 (by decide),
      mr_cut_add ret 8 8 184 (by decide),
      mr_cut_add ret 16 1 183 (by decide),
      mr_cut_add ret 17 4 179 (by decide),
      mr_cut_add ret 21 2 177 (by decide),
      mr_cut_add ret 23 1 176 (by decide),
      mr_cut_add ret 24 8 168 (by decide),
      mr_cut_add ret 32 24 144 (by decide),
      memRegion_one (ret + 16#64),
      memRegion_four (ret + 17#64),
      memRegion_two (ret + 21#64),
      memRegion_one (ret + 23#64)]
  simp only [memRegion_eight]

/-- Split `memRegion ret 200` for Branch 3 (`missingRemoteIdentity`). -/
theorem ret200_split_br3 (ret : BitVec 64) :
    memRegion ret 200 =
      (∃∗ w0 : BitVec 64, ret ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (ret + 8#64) ↦₆₄ w1) ∗
      (∃∗ v16 : BitVec 32, (ret + 16#64) ↦₃₂ v16) ∗
      (∃∗ v20 : BitVec 16, (ret + 20#64) ↦₁₆ v20) ∗
      (∃∗ w22 : BitVec 64, (ret + 22#64) ↦₆₄ w22) ∗
      (∃∗ w30 : BitVec 64, (ret + 30#64) ↦₆₄ w30) ∗
      memRegion (ret + 38#64) 18 ∗
      memRegion (ret + 56#64) 144 := by
  rw [memRegion_split ret 8 192 (by decide),
      mr_cut_add ret 8 8 184 (by decide),
      mr_cut_add ret 16 4 180 (by decide),
      mr_cut_add ret 20 2 178 (by decide),
      mr_cut_add ret 22 8 170 (by decide),
      mr_cut_add ret 30 8 162 (by decide),
      mr_cut_add ret 38 18 144 (by decide),
      memRegion_four (ret + 16#64),
      memRegion_two (ret + 20#64)]
  simp only [memRegion_eight]

/-- Split `memRegion ret 200` for Branch 4 (`Ok`). -/
theorem ret200_split_ok (ret : BitVec 64) :
    memRegion ret 200 =
      (∃∗ w0 : BitVec 64, ret ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (ret + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (ret + 16#64) ↦₆₄ w2) ∗
      (∃∗ v1 : List.Vector (BitVec 8) 32, (ret + 0x18#64) ↦ₛ v1.toList) ∗
      (∃∗ v2 : List.Vector (BitVec 8) 32, (ret + 0x38#64) ↦ₛ v2.toList) ∗
      (∃∗ v3 : List.Vector (BitVec 8) 32, (ret + 0x58#64) ↦ₛ v3.toList) ∗
      (∃∗ v4 : List.Vector (BitVec 8) 32, (ret + 0x78#64) ↦ₛ v4.toList) ∗
      (∃∗ v5 : List.Vector (BitVec 8) 32, (ret + 0x98#64) ↦ₛ v5.toList) ∗
      (∃∗ idx0 : BitVec 32, (ret + 0xb8#64) ↦₃₂ idx0) ∗
      (∃∗ pc0 : BitVec 32, (ret + 0xbc#64) ↦₃₂ pc0) ∗
      (∃∗ ver0 : BitVec 8, (ret + 0xc0#64) ↦₈ ver0) ∗
      memRegion (ret + 0xc1#64) 7 := by
  rw [memRegion_split ret 8 192 (by decide),
      mr_cut_add ret 8 8 184 (by decide),
      mr_cut_add ret 16 8 176 (by decide),
      mr_cut_add ret 24 32 144 (by decide),
      mr_cut_add ret 56 32 112 (by decide),
      mr_cut_add ret 88 32 80 (by decide),
      mr_cut_add ret 120 32 48 (by decide),
      mr_cut_add ret 152 32 16 (by decide),
      mr_cut_add ret 184 4 12 (by decide),
      mr_cut_add ret 188 4 8 (by decide),
      mr_cut_add ret 192 1 7 (by decide),
      memRegion_vector (ret + 0x18#64) 32,
      memRegion_vector (ret + 0x38#64) 32,
      memRegion_vector (ret + 0x58#64) 32,
      memRegion_vector (ret + 0x78#64) 32,
      memRegion_vector (ret + 0x98#64) 32,
      memRegion_four (ret + 0xb8#64),
      memRegion_four (ret + 0xbc#64),
      memRegion_one (ret + 0xc0#64)]
  simp only [memRegion_eight]

theorem otrResultAt_ok_eq (A : RustAlloc) (ret : BitVec 64) (pq : VecPin)
    (ot : OutgoingTripleRatchet (List (BitVec 8))) :
    otrResultAt A ret pq (.ok ot) =
      (ret ↦₆₄ pq.cap) ∗ ((ret + 8#64) ↦₆₄ pq.ptr) ∗
      ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 ot.pqrState.length) ∗
      vecU8Buf A pq.cap pq.ptr ot.pqrState ∗
      ((ret + 0x18#64) ↦ₛ ot.senderRatchetKey.publicKey.bytes.toList) ∗
      ((ret + 0x38#64) ↦ₛ ot.senderRatchetKey.privateKey.bytes.toList) ∗
      ((ret + 0x58#64) ↦ₛ ot.localIdentityKey.publicKey.bytes.toList) ∗
      ((ret + 0x78#64) ↦ₛ ot.remoteIdentityKey.publicKey.bytes.toList) ∗
      ((ret + 0x98#64) ↦ₛ keyToBytes32 ot.senderChainKey.key) ∗
      ((ret + 0xb8#64) ↦₃₂ ot.senderChainKey.index) ∗
      ((ret + 0xbc#64) ↦₃₂ ot.previousCounter) ∗
      ((ret + 0xc0#64) ↦₈ ot.sessionVersion) ∗
      memRegion (ret + 0xc1#64) 7 := by
  dsimp only [otrResultAt, otrAt]
  rw [vecU8At_eq_cells_buf A ret pq.cap pq.ptr ot.pqrState,
      chainKeyBytes_pointsTo (ret + 0x98#64) ot.senderChainKey]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem memRegion48_split_dropSpe (sp : BitVec 64) :
    memRegion (sp - 152#64) 48 =
      (∃∗ d0 : BitVec 64, (sp - 152#64) ↦₆₄ d0) ∗
      (∃∗ d8 : BitVec 16, (sp - 144#64) ↦₁₆ d8) ∗
      memRegion (sp - 142#64) 38 := by
  rw [mr_cut' sp 152 144 8 40 48 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 144 142 2 38 40 rfl rfl (by decide) (by decide) (by decide),
      memRegion_eight (sp - BitVec.ofNat 64 152),
      memRegion_two (sp - BitVec.ofNat 64 144)]

theorem memRegion56_fold_ok (sp d0 : BitVec 64) (d8 : BitVec 16) :
    (((sp - 152#64) ↦₆₄ d0) ∗ ((sp - 144#64) ↦₁₆ d8) ∗
      memRegion (sp - 142#64) 38 ∗ memRegion (sp - 104#64) 8) ⊢
    memRegion (sp - 152#64) 40 ∗ memRegion (sp - 112#64) 16 := by
  have h56 :
      memRegion (sp - BitVec.ofNat 64 152) 56 =
        memRegion (sp - 152#64) 40 ∗ memRegion (sp - 112#64) 16 :=
    mr_cut' sp 152 112 40 16 56 rfl rfl (by decide) (by decide) (by decide)
  rw [← h56,
      mr_cut' sp 152 104 48 8 56 rfl rfl (by decide) (by decide) (by decide),
      memRegion48_split_dropSpe sp]
  simp only [sepConj_assoc]
  exact sepConj_mono (Entails.sepExists_intro d0)
    (sepConj_mono (Entails.sepExists_intro d8) (Entails.refl _))

/-- Split the 64 KiB `smallRootStack` into the 61024-byte unused prefix and the 4512-byte
`otrFromInternalStack` frame. -/
theorem smallRootStack_split_otrFrom (sp : BitVec 64) :
    stackAt sp smallRootStack =
      memRegion (sp - 65536#64) 61024 ∗ stackAt sp otrFromInternalStack := by
  dsimp only [stackAt, smallRootStack, otrFromInternalStack, dropSpeStack, allocHookStack]
  change memRegion (sp - 65536#64) (61024 + 4512) =
    memRegion (sp - 65536#64) 61024 ∗ memRegion (sp - 4512#64) 4512
  rw [memRegion_split (sp - 65536#64) 61024 4512 (by decide)]
  have h1 : sp - 65536#64 + BitVec.ofNat 64 61024 = sp - 4512#64 := by bv_lin
  rw [h1]

theorem rodata_otrFrom_intro {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 104) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 108))) ↦ᵣ invalidSessionStructureStr .missingSenderChain) ∗
        ((img.base + bv% (ls_str% "version does not fit in u8")) ↦ᵣ invalidSessionStructureStr .versionTooLarge) ∗
        ((img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752))) ↦ᵣ invalidSessionStructureStr .missingRemoteIdentity) ∗ P :=
  rodata_missingSenderChain_intro himg hro
    (rodata_versionTooLarge_intro himg hro
      (rodata_missingRemoteIdentity_intro himg hro hP))

theorem SepWP.add_rodata {prog : Program} {target_pc : BitVec 64}
    {s : State} {P Ro : SepProp} {post : State → SepProp → Prop}
    (hro : ∀ {Q : SepProp}, (s.mem ⊨ Q) → (s.mem ⊨ Ro ∗ Q))
    (h : SepWP prog target_pc s (Ro ∗ P) post) :
    SepWP prog target_pc s P post := by
  refine SepWP.weaken_pre_frame (fun R hm => ?_) h
  rw [sepConj_assoc]
  exact hro hm

theorem sret_srk_entails_memRegion40 (sp : BitVec 64)
    (b0 b1 b32 : BitVec 8) (v2 : BitVec 16) (v4 : BitVec 32) (w8 w16 w24 : BitVec 64) :
    (((sp - 152#64) ↦₈ b0) ∗ ((sp - 151#64) ↦₈ b1) ∗
      ((sp - 150#64) ↦₁₆ v2) ∗ ((sp - 148#64) ↦₃₂ v4) ∗
      ((sp - 144#64) ↦₆₄ w8) ∗ ((sp - 136#64) ↦₆₄ w16) ∗
      ((sp - 128#64) ↦₆₄ w24) ∗ ((sp - 120#64) ↦₈ b32) ∗
      memRegion (sp - 119#64) 7) ⊢
    memRegion (sp - 152#64) 40 := by
  rw [mr_cut' sp 152 151 1 39 40 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 151 150 1 38 39 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 150 148 2 36 38 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 148 144 4 32 36 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 144 136 8 24 32 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 136 128 8 16 24 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 128 120 8 8 16 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 120 119 1 7 8 rfl rfl (by decide) (by decide) (by decide)]
  refine sepConj_mono (pointsTo8_entails_memRegion _ b0) (sepConj_mono (pointsTo8_entails_memRegion _ b1) ?_)
  refine sepConj_mono (pointsTo16_entails_memRegion _ v2) (sepConj_mono (pointsTo32_entails_memRegion _ v4) ?_)
  refine sepConj_mono (pointsTo64_entails_memRegion _ w8) (sepConj_mono (pointsTo64_entails_memRegion _ w16) ?_)
  exact sepConj_mono (pointsTo64_entails_memRegion _ w24)
    (sepConj_mono (pointsTo8_entails_memRegion _ b32) (Entails.refl _))

theorem sret_localIk_entails_memRegion34_6 (sp : BitVec 64)
    (b0 b7 b8 b9 b32 : BitVec 8) (v5 v14 : BitVec 16) (v1 v10 : BitVec 32) (w16 w24 : BitVec 64) :
    (((sp - 152#64) ↦₈ b0) ∗ ((sp - 151#64) ↦₃₂ v1) ∗
      ((sp - 147#64) ↦₁₆ v5) ∗ ((sp - 145#64) ↦₈ b7) ∗
      ((sp - 144#64) ↦₈ b8) ∗ ((sp - 143#64) ↦₈ b9) ∗
      ((sp - 142#64) ↦₃₂ v10) ∗ ((sp - 138#64) ↦₁₆ v14) ∗
      ((sp - 136#64) ↦₆₄ w16) ∗ ((sp - 128#64) ↦₆₄ w24) ∗
      ((sp - 120#64) ↦₈ b32) ∗ memRegion (sp - 119#64) 7) ⊢
    memRegion (sp - 152#64) 34 ∗ memRegion (sp - 118#64) 6 := by
  have h40 :
      memRegion (sp - BitVec.ofNat 64 152) 40 =
        memRegion (sp - 152#64) 34 ∗ memRegion (sp - 118#64) 6 :=
    mr_cut' sp 152 118 34 6 40 rfl rfl (by decide) (by decide) (by decide)
  rw [← h40,
      mr_cut' sp 152 151 1 39 40 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 151 147 4 35 39 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 147 145 2 33 35 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 145 144 1 32 33 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 144 143 1 31 32 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 143 142 1 30 31 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 142 138 4 26 30 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 138 136 2 24 26 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 136 128 8 16 24 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 128 120 8 8 16 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 120 119 1 7 8 rfl rfl (by decide) (by decide) (by decide)]
  refine sepConj_mono (pointsTo8_entails_memRegion _ b0) (sepConj_mono (pointsTo32_entails_memRegion _ v1) ?_)
  refine sepConj_mono (pointsTo16_entails_memRegion _ v5) (sepConj_mono (pointsTo8_entails_memRegion _ b7) ?_)
  refine sepConj_mono (pointsTo8_entails_memRegion _ b8) (sepConj_mono (pointsTo8_entails_memRegion _ b9) ?_)
  refine sepConj_mono (pointsTo32_entails_memRegion _ v10) (sepConj_mono (pointsTo16_entails_memRegion _ v14) ?_)
  refine sepConj_mono (pointsTo64_entails_memRegion _ w16) (sepConj_mono (pointsTo64_entails_memRegion _ w24) ?_)
  exact sepConj_mono (pointsTo8_entails_memRegion _ b32) (Entails.refl _)

theorem sessionStateAt_eq_from_some_self (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) (sg : SenderChainGhost) (sc : SenderChain)
    (hGs : G.sender = some sg) (hsc : st.senderChain = some sc) :
    sessionStateAt A ss G st =
      sessionStateAt A ss { G with pq := G.pq } { st with pqRatchetState := st.pqRatchetState } := by
  have h1 : ({ G with pq := G.pq } : SessionGhost) = G := by cases G; rfl
  have h2 : ({ st with pqRatchetState := st.pqRatchetState } : SessionState (List (BitVec 8))) = st := by
    cases st; rfl
  rw [h1, h2]

theorem version_word_eq (st : SessionState (List (BitVec 8))) :
    (if (st.sessionVersion == 0#32) = true then 2#32 else st.sessionVersion) = st.version := by
  unfold SessionState.version
  by_cases h : st.sessionVersion = 0#32
  · simp [h]
  · have hb : (st.sessionVersion == 0#32) = false := beq_eq_false_iff_ne.mpr h
    simp [h, hb]

private theorem subsPState32_255_ls_true {v : BitVec 32} (hbv : v.ule 255#32 = true) :
    ConditionHolds CondCode.LS (subsPState32 v 255#32) = true := by
  rw [conditionHolds_ls_subsPState32]
  exact hbv

private theorem subsPState32_255_ls_false {v : BitVec 32} (hbv : v.ule 255#32 = false) :
    ConditionHolds CondCode.LS (subsPState32 v 255#32) = false := by
  rw [conditionHolds_ls_subsPState32]
  exact hbv

theorem subsPState32_255_ls_iff (v : BitVec 32) :
    ConditionHolds CondCode.LS (subsPState32 v 255#32) = decide (¬ 256 ≤ v.toNat) := by
  by_cases h : 256 ≤ v.toNat
  · simp only [h, not_true_eq_false, decide_false]
    apply subsPState32_255_ls_false
    rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]
    change ¬ (v.toNat ≤ 255)
    omega
  · simp only [h, not_false_eq_true, decide_true]
    apply subsPState32_255_ls_true
    rw [BitVec.ule_eq_decide, decide_eq_true_eq]
    change v.toNat ≤ 255
    omega

theorem memRegion40_split_deser_sp (sp : BitVec 64) :
    memRegion (sp - 152#64) 40 =
      (∃∗ tag0 : BitVec 8, (sp - 152#64) ↦₈ tag0) ∗
      (∃∗ v : List.Vector (BitVec 8) 32, (sp - 151#64) ↦ₛ v.toList) ∗
      memRegion (sp - 119#64) 7 := by
  rw [memRegion40_split_deser (sp - 152#64)]
  have h1 : sp - 152#64 + 1#64 = sp - 151#64 := by bv_lin
  have h33 : sp - 152#64 + 33#64 = sp - 119#64 := by bv_lin
  rw [h1, h33]

theorem memRegion40_split_ck_sp (sp : BitVec 64) :
    memRegion (sp - 152#64) 40 =
      (∃∗ c0 : BitVec 16, (sp - 152#64) ↦₁₆ c0) ∗
      (∃∗ c2 : BitVec 8, (sp - 150#64) ↦₈ c2) ∗
      (∃∗ c3 : BitVec 64, (sp - 149#64) ↦₆₄ c3) ∗
      memRegion (sp - 141#64) 29 := by
  rw [memRegion40_split_ck (sp - 152#64)]
  have h2 : sp - 152#64 + 2#64 = sp - 150#64 := by bv_lin
  have h3 : sp - 152#64 + 3#64 = sp - 149#64 := by bv_lin
  have h11 : sp - 152#64 + 11#64 = sp - 141#64 := by bv_lin
  rw [h2, h3, h11]

theorem sessionStateAt_from_none_fold (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) (hsc : st.senderChain = none) (hGs : G.sender = none) :
    (((ss + 0x90#64) ↦₆₄ noneCap) ∗ sessionFromNoneFrame A ss G st) ⊢
      sessionStateAt A ss G st := by
  rw [sessionStateAt_eq_from_none A ss G st hsc hGs]
  exact Entails.refl _

/-! ## 4-case decomposition for `OTR::from_session_state` -/

def otrFromCaseSpec (A : RustAlloc) (img : Obj.Image) (P : OtrFromGhost → Prop) :
    Spec OtrFromGhost where
  pre := fun x s =>
    ⌜P x ∧ img.FrozenLoaded s ∧ s.symtab = img.symtab ∧
      s.readReg64 .x0 = x.ss ∧ s.readReg64 .x8 = x.ret⌝ ∗ sessionStateAt A x.ss x.G x.st ∗
      memRegion x.ret 200 ∗ logOff img ∗ stackAt s.sp smallRootStack ∗ A.pool
  post := (otrFromSpec A img).post
  onPanic := (otrFromSpec A img).onPanic

theorem otrFromCaseSpec_pre_of_pre {A : RustAlloc} {img : Obj.Image} {P : OtrFromGhost → Prop}
    {x : OtrFromGhost} {s0 : State} {R : SepProp} (hx : P x)
    (hpre : s0.mem ⊨ (otrFromSpec A img).pre x s0 ∗ R) :
    s0.mem ⊨ (otrFromCaseSpec A img P).pre x s0 ∗ R := by
  dsimp only [otrFromCaseSpec, otrFromSpec, Spec.inImage] at hpre ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  exact ⟨⟨hx, hpre.1.1, hpre.1.2, hpre.2.1.1, hpre.2.1.2⟩, hpre.2.2⟩

theorem subroutine_ok_of_cases4 {prog : Program} {entry : BitVec 64} {A : RustAlloc} {img : Obj.Image}
    {P₁ P₂ P₃ P₄ : OtrFromGhost → Prop}
    (hcov : ∀ x, P₁ x ∨ P₂ x ∨ P₃ x ∨ P₄ x)
    (h1 : subroutine_ok prog entry (otrFromCaseSpec A img P₁))
    (h2 : subroutine_ok prog entry (otrFromCaseSpec A img P₂))
    (h3 : subroutine_ok prog entry (otrFromCaseSpec A img P₃))
    (h4 : subroutine_ok prog entry (otrFromCaseSpec A img P₄)) :
    subroutine_ok prog entry (otrFromSpec A img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  rcases hcov x with hx | hx | hx | hx
  · exact h1.mono_outcome x R s0 hpc hrun (otrFromCaseSpec_pre_of_pre hx hpre) hsp fun _ hout => hout
  · exact h2.mono_outcome x R s0 hpc hrun (otrFromCaseSpec_pre_of_pre hx hpre) hsp fun _ hout => hout
  · exact h3.mono_outcome x R s0 hpc hrun (otrFromCaseSpec_pre_of_pre hx hpre) hsp fun _ hout => hout
  · exact h4.mono_outcome x R s0 hpc hrun (otrFromCaseSpec_pre_of_pre hx hpre) hsp fun _ hout => hout

theorem SepWP.instantiate_otrFrom_post {prog : Program} {target_pc : BitVec 64}
    {s s0 : State} {P R : SepProp} {A : RustAlloc} {img : Obj.Image}
    (x : OtrFromGhost) (G' : SessionGhost)
    (h : SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ (⌜x.model.1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
          (⌜x.G.AgreeExceptPq G'⌝ ∗ sessionStateAt A x.ss G' x.model.2) ∗
          otrResultAt A x.ret x.G.pq x.model.1 ∗
          logOff img ∗ stackAt s0.sp smallRootStack ∗ A.pool) ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)) :
    SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ (⌜x.model.1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
          (∃∗ G', ⌜x.G.AgreeExceptPq G'⌝ ∗ sessionStateAt A x.ss G' x.model.2) ∗
          otrResultAt A x.ret x.G.pq x.model.1 ∗
          logOff img ∗ stackAt s0.sp smallRootStack ∗ A.pool) ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) :=
  SepWP.mono h fun _ _ _ _ ⟨h1, h2⟩ =>
    ⟨fun hm => Satisfies.mono
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro G'))))
      (h1 hm), h2⟩

/-! ### Case 1: `x.st.senderChain = none` (`missingSenderChain`) -/

/-! ### Case 2: `st.senderChain = some sc` and `256 ≤ st.version.toNat` (`versionTooLarge`) -/

theorem ent_of_eq {P Q : SepProp} (h : P = Q) : P ⊢ Q := by
  rw [h]; exact Entails.refl Q

theorem sub_add_eq_sub (sp a b c : BitVec 64) (h : b - a = c := by rfl) :
    sp - b + a = sp - c := by
  subst h; bv_lin

theorem bytes32_split_sp151 (sp : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    ((sp - 151#64) ↦ₛ bs) ⊢
      ((sp - 151#64) ↦₃₂ pack32 (bs.take 4)) ∗
      ((sp - 147#64) ↦₁₆ pack16 ((bs.drop 4).take 2)) ∗
      ((sp - 145#64) ↦₈ pack8 ((bs.drop 6).take 1)) ∗
      ((sp - 144#64) ↦₆₄ pack64 ((bs.drop 7).take 8)) ∗
      ((sp - 136#64) ↦₆₄ pack64 ((bs.drop 15).take 8)) ∗
      ((sp - 128#64) ↦₆₄ pack64 ((bs.drop 23).take 8)) ∗
      ((sp - 120#64) ↦₈ pack8 (bs.drop 31)) := by
  rw [bytes32_eq_4_2_1_8_8_8_1 (sp - 151#64) bs h,
      sub_add_eq_sub sp 4#64 151#64 147#64,
      sub_add_eq_sub sp 6#64 151#64 145#64,
      sub_add_eq_sub sp 7#64 151#64 144#64,
      sub_add_eq_sub sp 15#64 151#64 136#64,
      sub_add_eq_sub sp 23#64 151#64 128#64,
      sub_add_eq_sub sp 31#64 151#64 120#64]
  exact Entails.refl _

theorem sevenBytes_421_to_124_sp151 (sp : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    (((sp - 151#64) ↦₃₂ pack32 (bs.take 4)) ∗
     ((sp - 147#64) ↦₁₆ pack16 ((bs.drop 4).take 2)) ∗
     ((sp - 145#64) ↦₈ pack8 ((bs.drop 6).take 1))) ⊢
    (((sp - 151#64) ↦₈ pack8 (bs.take 1)) ∗
     ((sp - 150#64) ↦₁₆ pack16 ((bs.drop 1).take 2)) ∗
     ((sp - 148#64) ↦₃₂ pack32 ((bs.drop 3).take 4))) := by
  have h1 := ent_of_eq (sevenBytes_4_2_1_eq_1_2_4 (sp - 151#64) bs h)
  rw [sub_add_eq_sub sp 4#64 151#64 147#64,
      sub_add_eq_sub sp 6#64 151#64 145#64,
      sub_add_eq_sub sp 1#64 151#64 150#64,
      sub_add_eq_sub sp 3#64 151#64 148#64] at h1
  exact h1

theorem sevenBytes_after_store_at_0_sp232 (sp : BitVec 64) (u4 : BitVec 16) (u6 : BitVec 8)
    (bs : List (BitVec 8)) (h : bs.length = 32) :
    (((sp - 232#64) ↦₃₂ pack32 (bs.take 4)) ∗
     ((sp - 228#64) ↦₁₆ u4) ∗
     ((sp - 226#64) ↦₈ u6)) ⊢
    (((sp - 232#64) ↦₈ pack8 (bs.take 1)) ∗
     ((sp - 231#64) ↦₁₆ pack16 ((bs.drop 1).take 2)) ∗
     ((sp - 229#64) ↦₃₂ pack32 ((bs.drop 3).take 1 ++ unpack16 u4 ++ [u6]))) := by
  have h1 := ent_of_eq (sevenBytes_after_store_at_0 (sp - 232#64) u4 u6 bs h)
  rw [sub_add_eq_sub sp 4#64 232#64 228#64,
      sub_add_eq_sub sp 6#64 232#64 226#64,
      sub_add_eq_sub sp 1#64 232#64 231#64,
      sub_add_eq_sub sp 3#64 232#64 229#64] at h1
  exact h1

theorem sevenBytes_124_to_421_sp232 (sp : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    (((sp - 232#64) ↦₈ pack8 (bs.take 1)) ∗
     ((sp - 231#64) ↦₁₆ pack16 ((bs.drop 1).take 2)) ∗
     ((sp - 229#64) ↦₃₂ pack32 ((bs.drop 3).take 4))) ⊢
    (((sp - 232#64) ↦₃₂ pack32 (bs.take 4)) ∗
     ((sp - 228#64) ↦₁₆ pack16 ((bs.drop 4).take 2)) ∗
     ((sp - 226#64) ↦₈ pack8 ((bs.drop 6).take 1))) := by
  have h1 := ent_of_eq (sevenBytes_4_2_1_eq_1_2_4 (sp - 232#64) bs h).symm
  rw [sub_add_eq_sub sp 1#64 232#64 231#64,
      sub_add_eq_sub sp 3#64 232#64 229#64,
      sub_add_eq_sub sp 4#64 232#64 228#64,
      sub_add_eq_sub sp 6#64 232#64 226#64] at h1
  exact h1

theorem memRegion40_split_ck_sp_entails (sp : BitVec 64) :
    memRegion (sp - 152#64) 40 ⊢
      (∃∗ c0 : BitVec 16, (sp - 152#64) ↦₁₆ c0) ∗
      (∃∗ c2 : BitVec 8, (sp - 150#64) ↦₈ c2) ∗
      (∃∗ c3 : BitVec 64, (sp - 149#64) ↦₆₄ c3) ∗
      memRegion (sp - 141#64) 29 :=
  ent_of_eq (memRegion40_split_ck_sp sp)

theorem elevenBytes_218_to_821_sp152 (sp : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    (((sp - 152#64) ↦₁₆ pack16 ((bs.drop 4).take 2)) ∗
     ((sp - 150#64) ↦₈ pack8 ((bs.drop 6).take 1)) ∗
     ((sp - 149#64) ↦₆₄ pack64 ((bs.drop 7).take 8))) ⊢
    (((sp - 152#64) ↦₆₄ pack64 ((bs.drop 4).take 8)) ∗
     ((sp - 144#64) ↦₁₆ pack16 ((bs.drop 12).take 2)) ∗
     ((sp - 142#64) ↦₈ pack8 ((bs.drop 14).take 1))) := by
  have h1 := ent_of_eq (elevenBytes_2_1_8_eq_8_2_1 (sp - 152#64) bs h)
  rw [sub_add_eq_sub sp 2#64 152#64 150#64,
      sub_add_eq_sub sp 3#64 152#64 149#64,
      sub_add_eq_sub sp 8#64 152#64 144#64,
      sub_add_eq_sub sp 10#64 152#64 142#64] at h1
  exact h1

theorem ck_scratch_entails_memRegion40_sp152 (sp w0 : BitVec 64) (w8 : BitVec 16) (w10 : BitVec 8) :
    (((sp - 152#64) ↦₆₄ w0) ∗ ((sp - 144#64) ↦₁₆ w8) ∗
     ((sp - 142#64) ↦₈ w10) ∗ memRegion (sp - 141#64) 29) ⊢
    memRegion (sp - 152#64) 40 := by
  have h1 := ck_scratch_entails_memRegion40 (sp - 152#64) w0 w8 w10
  rw [sub_add_eq_sub sp 8#64 152#64 144#64,
      sub_add_eq_sub sp 10#64 152#64 142#64,
      sub_add_eq_sub sp 11#64 152#64 141#64] at h1
  exact h1

theorem ret16_pointsTo64_of_1_4_2_1 (ret p : BitVec 64)
    (v0 : BitVec 8) (v1 : BitVec 32) (v5 : BitVec 16) (v7 : BitVec 8)
    (hv0 : v0 = ((p.setWidth 32).zeroExtend 64).setWidth 8)
    (hv1 : v1 = (((p >>> 8).setWidth 32).zeroExtend 64).setWidth 32)
    (hv5 : v5 = (((p >>> 40).setWidth 32).zeroExtend 64).setWidth 16)
    (hv7 : v7 = (((p >>> 56).setWidth 32).zeroExtend 64).setWidth 8) :
    (((ret + 16#64) ↦₈ v0) ∗
     ((ret + 17#64) ↦₃₂ v1) ∗
     ((ret + 21#64) ↦₁₆ v5) ∗
     ((ret + 23#64) ↦₈ v7)) ⊢
    ((ret + 16#64) ↦₆₄ p) := by
  subst v0 v1 v5 v7
  have h := ent_of_eq (pointsTo64_of_1_4_2_1 (ret + 16#64) p)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  exact h

theorem agreeExceptPq_of_sender (G : SessionGhost) (pq' : VecPin) (sg : SenderChainGhost)
    (hGs : G.sender = some sg) :
    G.AgreeExceptPq { G with pq := pq', sender := some sg } := by
  unfold SessionGhost.AgreeExceptPq
  cases G; cases hGs; rfl

theorem bytes32_fold_1_4_2_8_8_8_1 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    ((a ↦₈ pack8 (bs.take 1)) ∗
     ((a + 1#64) ↦₃₂ pack32 ((bs.drop 1).take 4)) ∗
     ((a + 5#64) ↦₁₆ pack16 ((bs.drop 5).take 2)) ∗
     ((a + 7#64) ↦₆₄ pack64 ((bs.drop 7).take 8)) ∗
     ((a + 15#64) ↦₆₄ pack64 ((bs.drop 15).take 8)) ∗
     ((a + 23#64) ↦₆₄ pack64 ((bs.drop 23).take 8)) ∗
     ((a + 31#64) ↦₈ pack8 (bs.drop 31))) ⊢
    (a ↦ₛ bs) :=
  ent_of_eq (bytes32_eq_1_4_2_8_8_8_1 a bs h).symm

theorem bytes32_fold_4_2_1_8_8_8_1 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    ((a ↦₃₂ pack32 (bs.take 4)) ∗
     ((a + 4#64) ↦₁₆ pack16 ((bs.drop 4).take 2)) ∗
     ((a + 6#64) ↦₈ pack8 ((bs.drop 6).take 1)) ∗
     ((a + 7#64) ↦₆₄ pack64 ((bs.drop 7).take 8)) ∗
     ((a + 15#64) ↦₆₄ pack64 ((bs.drop 15).take 8)) ∗
     ((a + 23#64) ↦₆₄ pack64 ((bs.drop 23).take 8)) ∗
     ((a + 31#64) ↦₈ pack8 (bs.drop 31))) ⊢
    (a ↦ₛ bs) :=
  ent_of_eq (bytes32_eq_4_2_1_8_8_8_1 a bs h).symm

theorem vecU8Buf_fold_of_ne_zero (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (h : cap ≠ 0) :
    ((ptr ↦ₛ bs) ∗ vecU8Live A cap ptr bs) ⊢ vecU8Buf A cap ptr bs :=
  ent_of_eq (vecU8Buf_eq_bytes_live_of_ne_zero A cap ptr bs h).symm

theorem pq_empty_cells_intro (A : RustAlloc) (ss : BitVec 64) :
    ((ss + 0x88#64) ↦₆₄ 0#64) ⊢ ((ss + 0x88#64) ↦₆₄ 0#64) ∗ vecU8Buf A 0#64 1#64 [] := by
  conv_lhs => rw [← sepConj_emp ((ss + 0x88#64) ↦₆₄ 0#64)]
  exact sepConj_mono_right (vecU8Buf_empty_intro A)

theorem sessionStateAt_from_some_pq_empty_fold (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) (sg : SenderChainGhost) (sc : SenderChain)
    (hGs : G.sender = some sg) (hsc : st.senderChain = some sc)
    (hinv1 : PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
      (match st.remoteIdentity with
       | none => G.remoteIk.bytes = []
       | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
      G.chains.length = st.receiverChains.length ∧
      G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
      G.localIk.bytes.length = 33 ∧
      (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33))
    (hdeser_srk : PublicKey.deserialize sg.srk.bytes = .ok sc.ratchetKey.publicKey)
    (hpriv_eq : sg.priv.bytes = sc.ratchetKey.privateKey.bytes.toList)
    (hpriv_clamp : Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes)
    (hsrk_len : sg.srk.bytes.length = 33) :
    (((ss + 0x08#64) ↦₆₄ G.localIk.ptr) ∗
     ((ss + 0x10#64) ↦₆₄ BitVec.ofNat 64 G.localIk.bytes.length) ∗
     vecU8Buf A G.localIk.cap G.localIk.ptr G.localIk.bytes ∗
     vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
     ((ss + 0x78#64) ↦₆₄ 0#64) ∗ ((ss + 0x80#64) ↦₆₄ 1#64) ∗
     ((ss + 0x88#64) ↦₆₄ 0#64) ∗
     vecU8Buf A 0#64 1#64 [] ∗
     ((ss + 0x90#64) ↦₆₄ sg.srk.cap) ∗ ((ss + 0x98#64) ↦₆₄ sg.srk.ptr) ∗
     ((ss + 0xa0#64) ↦₆₄ BitVec.ofNat 64 sg.srk.bytes.length) ∗
     vecU8Buf A sg.srk.cap sg.srk.ptr sg.srk.bytes ∗
     ((ss + 0xb0#64) ↦₆₄ sg.priv.ptr) ∗
     ((ss + 0xb8#64) ↦₆₄ 32#64) ∗
     vecU8Buf A sg.priv.cap sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList ∗
     ((ss + 0xd8#64) ↦₆₄ sg.ck.cap) ∗ ((ss + 0xe0#64) ↦₆₄ sg.ck.ptr) ∗
     ((ss + 0xe8#64) ↦₆₄ 32#64) ∗ ((ss + 0xf0#64) ↦₃₂ sc.chainKey.index) ∗
     vecU8Buf A sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key) ∗
     ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗
     ((ss + 0x14c#64) ↦₃₂ st.previousCounter) ∗
     sessionFromUntouched A ss G st sg) ⊢
    sessionStateAt A ss { G with pq := ⟨0#64, 1#64⟩ } { st with pqRatchetState := [] } := by
  rw [sessionStateAt_eq_from_some A ss G st sg sc hGs hsc ⟨0#64, 1#64⟩ []]
  have hpriv_len : BitVec.ofNat 64 sg.priv.bytes.length = 32#64 := by
    rw [hpriv_eq, List.Vector.toList_length]
  refine Entails.pure_right hinv1 (Entails.pure_right ⟨hdeser_srk, hpriv_eq, hpriv_clamp, hsrk_len⟩ ?_)
  rw [hpriv_len, hpriv_eq]
  exact Entails.refl _

theorem addsPState64_neg1_eq_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]; bv_omega

theorem vecU8_cap_ne_zero_of_ge {cap : BitVec 64} {n : Nat} (hle : n ≤ cap.toNat) (hn : 0 < n) :
    cap ≠ 0 := by
  intro hc; subst hc; simp at hle; omega

/-! ### Case 3 (`st.remoteIdentity = none`) and Case 4 (`st.remoteIdentity = some rem`) helpers -/

theorem bytes32_split_localIk_sp151 (sp : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    ((sp - 151#64) ↦ₛ bs) ⊢
      ((sp - 151#64) ↦₃₂ pack32 (bs.take 4)) ∗
      ((sp - 147#64) ↦₁₆ pack16 ((bs.drop 4).take 2)) ∗
      ((sp - 145#64) ↦₈ pack8 ((bs.drop 6).take 1)) ∗
      ((sp - 144#64) ↦₈ pack8 ((bs.drop 7).take 1)) ∗
      ((sp - 143#64) ↦₈ pack8 ((bs.drop 8).take 1)) ∗
      ((sp - 142#64) ↦₃₂ pack32 ((bs.drop 9).take 4)) ∗
      ((sp - 138#64) ↦₁₆ pack16 ((bs.drop 13).take 2)) ∗
      ((sp - 136#64) ↦₆₄ pack64 ((bs.drop 15).take 8)) ∗
      ((sp - 128#64) ↦₆₄ pack64 ((bs.drop 23).take 8)) ∗
      ((sp - 120#64) ↦₈ pack8 (bs.drop 31)) := by
  have h1 := ent_of_eq (bytes32_eq_4_2_1_8_8_8_1 (sp - 151#64) bs h)
  rw [eightBytes_at_7_eq_1_1_4_2 (sp - 151#64) bs h,
      sub_add_eq_sub sp 4#64 151#64 147#64,
      sub_add_eq_sub sp 6#64 151#64 145#64,
      sub_add_eq_sub sp 7#64 151#64 144#64,
      sub_add_eq_sub sp 8#64 151#64 143#64,
      sub_add_eq_sub sp 9#64 151#64 142#64,
      sub_add_eq_sub sp 13#64 151#64 138#64,
      sub_add_eq_sub sp 15#64 151#64 136#64,
      sub_add_eq_sub sp 23#64 151#64 128#64,
      sub_add_eq_sub sp 31#64 151#64 120#64] at h1
  simp only [sepConj_assoc] at h1
  exact h1

theorem sp184_pair8_to_16 (sp : BitVec 64) (b0 b1 : BitVec 8) :
    (((sp - 184#64) ↦₈ b0) ∗ ((sp - 183#64) ↦₈ b1)) ⊢
      ((sp - 184#64) ↦₁₆ (b0.zeroExtend 16 ||| (b1.zeroExtend 16 <<< 8))) := by
  have h1 := ent_of_eq (pointsTo8_pair_eq_pointsTo16 (sp - 184#64) b0 b1)
  rw [sub_add_eq_sub sp 1#64 184#64 183#64] at h1
  exact h1

theorem pointsTo64_of_1_1_4_2_sp152 (sp : BitVec 64) (b0 b1 : BitVec 8)
    (v2 : BitVec 32) (v6 : BitVec 16) :
    (((sp - 152#64) ↦₈ b0) ∗ ((sp - 151#64) ↦₈ b1) ∗
     ((sp - 150#64) ↦₃₂ v2) ∗ ((sp - 146#64) ↦₁₆ v6)) ⊢
    ∃∗ w : BitVec 64, (sp - 152#64) ↦₆₄ w := by
  have h1 := pointsTo64_of_1_1_4_2_entails (sp - 152#64) b0 b1 v2 v6
  rw [sub_add_eq_sub sp 1#64 152#64 151#64,
      sub_add_eq_sub sp 2#64 152#64 150#64,
      sub_add_eq_sub sp 6#64 152#64 146#64] at h1
  exact h1

namespace FromSessionStateFacts

theorem frame15_fold_16 (sp : BitVec 64) (uc8 : BitVec 16) (ud0 : BitVec 32) (ud4 : BitVec 16) :
    (((sp - 184#64) ↦₁₆ uc8) ∗ memRegion (sp - 182#64) 6 ∗
      ((sp - 176#64) ↦₃₂ ud0) ∗ ((sp - 172#64) ↦₁₆ ud4) ∗
      memRegion (sp - 170#64) 2) ⊢
    ((sp - 184#64) ↦₈ uc8.setWidth 8) ∗ memRegion (sp - 183#64) 15 := by
  rw [pointsTo16_eq_pointsToBytes (sp - 184#64)]
  simp only [unpack16, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, sepConj_assoc]
  have h183 : sp - 184#64 + 1#64 = sp - 183#64 := by bv_lin
  rw [h183, frame15_split sp]
  refine sepConj_mono (Entails.refl _) ?_
  refine sepConj_mono (Entails.sepExists_intro _) (sepConj_mono (Entails.refl _) ?_)
  exact sepConj_mono (Entails.sepExists_intro ud0) (sepConj_mono (Entails.sepExists_intro ud4) (Entails.refl _))

theorem fold_entails {P Q T T' F : SepProp} (hent : T ⊢ T') (hf : P = T ∗ F)
    (h : T' ∗ F ⊢ Q) : P ⊢ Q :=
  Entails.trans (hf ▸ sepConj_mono_left hent) h

theorem finish_otrFrom {prog : Program} {target_pc : BitVec 64}
    {s s0 : State} {P R : SepProp} {A : RustAlloc} {img : Obj.Image}
    (x : OtrFromGhost) (G' : SessionGhost)
    (res' : Except SignalProtocolError (OutgoingTripleRatchet (List (BitVec 8))))
    (st' : SessionState (List (BitVec 8)))
    (hmod1 : x.model.1 = res')
    (hmod2 : x.model.2 = st')
    (_hnopanic : res' ≠ .error .panic)
    (_hagree : x.G.AgreeExceptPq G')
    (hdone : SepWP prog target_pc s
      (sessionStateAt A x.ss G' st' ∗
        otrResultAt A x.ret x.G.pq res' ∗
        ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        stackAt s0.sp smallRootStack ∗ A.pool)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (⌜res' ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
            (⌜x.G.AgreeExceptPq G'⌝ ∗ sessionStateAt A x.ss G' st') ∗
            otrResultAt A x.ret x.G.pq res' ∗
            ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ stackAt s0.sp smallRootStack ∗ A.pool) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf))
    (hent : P ⊢
      sessionStateAt A x.ss G' st' ∗
        otrResultAt A x.ret x.G.pq res' ∗
        ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        stackAt s0.sp smallRootStack ∗ A.pool) :
    SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ (⌜x.model.1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
          (∃∗ G', ⌜x.G.AgreeExceptPq G'⌝ ∗ sessionStateAt A x.ss G' x.model.2) ∗
          otrResultAt A x.ret x.G.pq x.model.1 ∗
          logOff img ∗ stackAt s0.sp smallRootStack ∗ A.pool) ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  apply SepWP.instantiate_otrFrom_post x G'
  dsimp only [logOff]
  rw [hmod1, hmod2]
  exact SepWP.weaken_pre hent hdone

end FromSessionStateFacts

/-! ## Relocatable `[LibsignalPlacement]` 4-case Decomposition for `OTR::from_session_state` -/

def otrFromRawPlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec OtrFromGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ s.readReg64 .x8 = x.ret⌝ ∗
      sessionStateAt A x.ss x.G x.st ∗
      memRegion x.ret 200 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      stackAt s.sp smallRootStack ∗ A.pool
  post := fun x s0 sf =>
    ⌜x.model.1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
      (∃∗ G', ⌜x.G.AgreeExceptPq G'⌝ ∗ sessionStateAt A x.ss G' x.model.2) ∗
      otrResultAt A x.ret x.G.pq x.model.1 ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp smallRootStack ∗ A.pool

abbrev otrFromPlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec OtrFromGhost :=
  withLsRoLoaded lsmpl (withLsCodeLoaded lsmpl (otrFromRawPlacedSpec A))

def otrFromCasePlacedSpec [LibsignalPlacement] (A : RustAlloc) (P : OtrFromGhost → Prop) :
    Spec OtrFromGhost where
  pre := fun x s =>
    ⌜P x ∧ LibsignalCodeLoaded lsmpl s.mem ∧ LibsignalRoLoaded lsmpl s.mem ∧
      s.readReg64 .x0 = x.ss ∧ s.readReg64 .x8 = x.ret⌝ ∗ sessionStateAt A x.ss x.G x.st ∗
      memRegion x.ret 200 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s.sp smallRootStack ∗ A.pool
  post := (otrFromRawPlacedSpec A).post
  onPanic := (otrFromRawPlacedSpec A).onPanic

theorem otrFromCasePlacedSpec_pre_of_pre [LibsignalPlacement] {A : RustAlloc}
    {P : OtrFromGhost → Prop} {x : OtrFromGhost} {s0 : State} {R : SepProp} (hx : P x)
    (hpre : s0.mem ⊨ (otrFromPlacedSpec A).pre x s0 ∗ R) :
    s0.mem ⊨ (otrFromCasePlacedSpec A P).pre x s0 ∗ R := by
  dsimp only [otrFromPlacedSpec, withLsRoLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hro, hpre⟩ := hpre
  obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre
  dsimp only [otrFromRawPlacedSpec, otrFromCasePlacedSpec] at hpre ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  exact ⟨⟨hx, hcl, hro, hpre.1.1, hpre.1.2⟩, hpre.2⟩

theorem subroutine_ok_of_cases4_placed [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {A : RustAlloc} {P₁ P₂ P₃ P₄ : OtrFromGhost → Prop}
    (hcov : ∀ x, P₁ x ∨ P₂ x ∨ P₃ x ∨ P₄ x)
    (h1 : subroutine_ok prog entry (otrFromCasePlacedSpec A P₁))
    (h2 : subroutine_ok prog entry (otrFromCasePlacedSpec A P₂))
    (h3 : subroutine_ok prog entry (otrFromCasePlacedSpec A P₃))
    (h4 : subroutine_ok prog entry (otrFromCasePlacedSpec A P₄)) :
    subroutine_ok prog entry (otrFromPlacedSpec A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  rcases hcov x with hx | hx | hx | hx
  · exact h1.mono_outcome x R s0 hpc hrun (otrFromCasePlacedSpec_pre_of_pre hx hpre) hsp fun _ hout => hout
  · exact h2.mono_outcome x R s0 hpc hrun (otrFromCasePlacedSpec_pre_of_pre hx hpre) hsp fun _ hout => hout
  · exact h3.mono_outcome x R s0 hpc hrun (otrFromCasePlacedSpec_pre_of_pre hx hpre) hsp fun _ hout => hout
  · exact h4.mono_outcome x R s0 hpc hrun (otrFromCasePlacedSpec_pre_of_pre hx hpre) hsp fun _ hout => hout

theorem SepWP.instantiate_otrFrom_placed_post [LibsignalPlacement] {prog : Program}
    {target_pc : BitVec 64} {s s0 : State} {P R : SepProp} {A : RustAlloc}
    (x : OtrFromGhost) (G' : SessionGhost)
    (h : SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ (⌜x.model.1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
          (⌜x.G.AgreeExceptPq G'⌝ ∗ sessionStateAt A x.ss G' x.model.2) ∗
          otrResultAt A x.ret x.G.pq x.model.1 ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp smallRootStack ∗ A.pool) ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)) :
    SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ (⌜x.model.1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
          (∃∗ G', ⌜x.G.AgreeExceptPq G'⌝ ∗ sessionStateAt A x.ss G' x.model.2) ∗
          otrResultAt A x.ret x.G.pq x.model.1 ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp smallRootStack ∗ A.pool) ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) :=
  SepWP.mono h fun _ _ _ _ ⟨h1, h2⟩ =>
    ⟨fun hm => Satisfies.mono
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro G'))))
      (h1 hm), h2⟩

namespace FromSessionStateFacts

theorem finish_otrFrom_placed [LibsignalPlacement] {prog : Program} {target_pc : BitVec 64}
    {s s0 : State} {P R : SepProp} {A : RustAlloc}
    (x : OtrFromGhost) (G' : SessionGhost)
    (res' : Except SignalProtocolError (OutgoingTripleRatchet (List (BitVec 8))))
    (st' : SessionState (List (BitVec 8)))
    (hmod1 : x.model.1 = res')
    (hmod2 : x.model.2 = st')
    (_hnopanic : res' ≠ .error .panic)
    (_hagree : x.G.AgreeExceptPq G')
    (hdone : SepWP prog target_pc s
      (sessionStateAt A x.ss G' st' ∗
        otrResultAt A x.ret x.G.pq res' ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        stackAt s0.sp smallRootStack ∗ A.pool)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (⌜res' ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
            (⌜x.G.AgreeExceptPq G'⌝ ∗ sessionStateAt A x.ss G' st') ∗
            otrResultAt A x.ret x.G.pq res' ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp smallRootStack ∗ A.pool) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf))
    (hent : P ⊢
      sessionStateAt A x.ss G' st' ∗
        otrResultAt A x.ret x.G.pq res' ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        stackAt s0.sp smallRootStack ∗ A.pool) :
    SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ (⌜x.model.1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
          (∃∗ G', ⌜x.G.AgreeExceptPq G'⌝ ∗ sessionStateAt A x.ss G' x.model.2) ∗
          otrResultAt A x.ret x.G.pq x.model.1 ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp smallRootStack ∗ A.pool) ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  apply SepWP.instantiate_otrFrom_placed_post x G'
  rw [hmod1, hmod2]
  exact SepWP.weaken_pre hent hdone

end FromSessionStateFacts

end CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
