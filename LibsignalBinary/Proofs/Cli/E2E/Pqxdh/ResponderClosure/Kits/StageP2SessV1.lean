/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3c
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3d

/-!
# SPQR V1 Bob `SessionState` Packing

Packs the 344-byte SPQR V1 Bob session byte layout (`p2BobSessRegIdsV1`) with its seven
heap-allocated key boxes and `p2BobSpqrVecBuf` into `sessionStateAt A ss G st` at any base address
`ss`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
  CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
  (entails_replace_sub mkBobSenderChainGhost vecGhostAt_of_box)
open CryptoVerification.SpqrV1.Top.InitialState (initialStateValue)

set_option linter.unusedSimpArgs false

/-! ## 1. SPQR V1 `SessionGhost` -/

/-- Ghost layout for a freshly-initialized SPQR V1 Bob `SessionState`
(`receiverChains = []`, `pq = ⟨spqrCap, spqrBufPtr⟩`, `pending = none`, `kyber = none`). -/
def mkBobGhostV1 (locIdPtr remIdPtr rootKeyPtr aliceBasePtr spqrCap spqrBufPtr : BitVec 64)
    (locIdBytes remIdBytes aliceBaseBytes : List (BitVec 8))
    (sg : SenderChainGhost) (f248 f24c : BitVec 32) : SessionGhost :=
  { localIk := ⟨33#64, locIdPtr, locIdBytes⟩
    remoteIk := ⟨33#64, remIdPtr, remIdBytes⟩
    root := ⟨32#64, rootKeyPtr⟩
    chainsCap := 0#64
    chainsPtr := 8#64
    chains := []
    alice := ⟨33#64, aliceBasePtr, aliceBaseBytes⟩
    pq := ⟨spqrCap, spqrBufPtr⟩
    sender := some sg
    pending := none
    kyber := none
    regIds := unpack32 f248 ++ unpack32 f24c }

/-! ## 2. Unpacking `p2BobSessRegIdsV1` & Folding into `sessionStateAt` -/

theorem p2BobSpqrVecBuf_eq_vecU8At (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      p2BobSpqrVecBuf A cap ptr bs =
    vecU8At A v cap ptr bs := by
  unfold vecU8At vecHeader p2BobSpqrVecBuf
  simp only [sepConj_assoc]

theorem p2BobSessRegIdsV1_fold (a p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64)
    (remoteRegId localRegId : BitVec 32) :
    (a ↦₆₄ 33#64) ∗ ((a + 0x8#64) ↦₆₄ p1) ∗ ((a + 0x10#64) ↦₆₄ 33#64) ∗
    ((a + 0x18#64) ↦₆₄ 33#64) ∗ ((a + 0x20#64) ↦₆₄ p2) ∗ ((a + 0x28#64) ↦₆₄ 33#64) ∗
    ((a + 0x30#64) ↦₆₄ 32#64) ∗
    ((a + 0x38#64) ↦ₛ p2BobSessMid280V1 p3 p4 c5 p5 l5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
    ((a + 0x150#64) ↦₃₂ remoteRegId) ∗ ((a + 0x154#64) ↦₃₂ localRegId) =
      (a ↦ₛ p2BobSessRegIdsV1 p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2
        remoteRegId localRegId) := by
  have hfold :
      p2BobSessRegIdsV1 p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2
        remoteRegId localRegId =
      unpack64 33#64 ++ (unpack64 p1 ++ (unpack64 33#64 ++
      (unpack64 33#64 ++ (unpack64 p2 ++ (unpack64 33#64 ++
      (unpack64 32#64 ++
        (p2BobSessMid280V1 p3 p4 c5 p5 l5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 ++
          (unpack32 remoteRegId ++ unpack32 localRegId)))))))) := by
    unfold p2BobSessRegIdsV1 p2BobSessHead56Bv8
    simp only [List.append_assoc]
  rw [hfold,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, p2BobSessMid280V1_length,
      pointsToBytes_append, unpack32_length,
      ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes,
      ← pointsTo32_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem p2BobSessMid280V1_entails_fields (ss rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr spqrLen
    ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) :
    ((ss + 0x38#64) ↦ₛ p2BobSessMid280V1 rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr spqrLen
      ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ⊢
    ((ss + 0x38#64) ↦₆₄ rootKeyBoxPtr) ∗ ((ss + 0x40#64) ↦₆₄ 32#64) ∗
    ((ss + 0x48#64) ↦₆₄ 0#64) ∗ ((ss + 0x50#64) ↦₆₄ 8#64) ∗ ((ss + 0x58#64) ↦₆₄ 0#64) ∗
    ((ss + 0x60#64) ↦₆₄ 33#64) ∗ ((ss + 0x68#64) ↦₆₄ baseKeyBoxPtr) ∗ ((ss + 0x70#64) ↦₆₄ 33#64) ∗
    ((ss + 0x78#64) ↦₆₄ spqrCap) ∗ ((ss + 0x80#64) ↦₆₄ spqrBufPtr) ∗ ((ss + 0x88#64) ↦₆₄ spqrLen) ∗
    Initiator.senderChainFieldsAt ss ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr 0#32 ∗
    ((ss + 0xf4#64) ↦₃₂ pad_f4) ∗
    ((ss + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (ss + 0x100#64) 40 ∗
    ((ss + 0x128#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (ss + 0x130#64) 24 ∗
    ((ss + 0x148#64) ↦₃₂ 4#32) ∗ ((ss + 0x14c#64) ↦₃₂ 0#32) := by
  have h4 : unpack64 4#64 = unpack32 4#32 ++ unpack32 0#32 := by decide
  rw [Initiator.senderChainFieldsAt_eq_pointsToBytes]
  unfold p2BobSessMid280V1; rw [h4]
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length, unpack32_length,
    Initiator.senderChainBytes100_length, BitVec.add_assoc, BitVec.reduceAdd,
    ← pointsTo64_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes, sepConj_assoc]
  have hc40 :
      ((ss + 0x100#64) ↦₆₄ c0) ∗ ((ss + 0x108#64) ↦₆₄ c1) ∗ ((ss + 0x110#64) ↦₆₄ c2) ∗
      ((ss + 0x118#64) ↦₆₄ c3) ∗ ((ss + 0x120#64) ↦₆₄ c4) ⊢ memRegion (ss + 0x100#64) 40 := by
    rw [(ProofLib.memRegion_cells (ss + 0x100#64) 5 (by decide) :
      memRegion (ss + 0x100#64) 40 = cells (ss + 0x100#64) 5)]
    simp only [cells, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_assoc, sepExists_sepConj_left]
    simp only [sepExists_sepConj_right, sepConj_assoc]
    exact Entails.sepExists_right c0 (Entails.sepExists_right c1
      (Entails.sepExists_right c2 (Entails.sepExists_right c3 (Entails.sepExists_right c4
      (Entails.refl _)))))
  have hd24 :
      ((ss + 0x130#64) ↦₆₄ d0) ∗ ((ss + 0x138#64) ↦₆₄ d1) ∗ ((ss + 0x140#64) ↦₆₄ d2) ⊢
      memRegion (ss + 0x130#64) 24 := by
    rw [(ProofLib.memRegion_cells (ss + 0x130#64) 3 (by decide) :
      memRegion (ss + 0x130#64) 24 = cells (ss + 0x130#64) 3)]
    simp only [cells, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_assoc, sepExists_sepConj_left]
    simp only [sepExists_sepConj_right, sepConj_assoc]
    exact Entails.sepExists_right d0 (Entails.sepExists_right d1
      (Entails.sepExists_right d2 (Entails.refl _)))
  refine Entails.trans (entails_replace_sub hc40 (by sep_focus) rfl) ?_
  exact entails_replace_sub hd24 (by sep_focus) (eq_of_sep_emp (by sep_focus))

theorem bobSenderChain_ss_entails_optSenderChainAt {A : RustAlloc}
    (ss ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
    (spkPubBytes spkPrivBytes chainKeyBytes : List (BitVec 8))
    (pad_f4 : BitVec 32) (sc : SenderChain)
    (hrat_pub : ratchetPubBoxPtr ≠ 0#64)
    (hrat_priv : ratchetPrivBoxPtr ≠ 0#64)
    (hck_ptr : chainKeyBoxPtr ≠ 0#64)
    (hspk_pub_len : spkPubBytes.length = 33)
    (hspk_priv_len : spkPrivBytes.length = 32)
    (hspk_deser : PublicKey.deserialize spkPubBytes = .ok sc.ratchetKey.publicKey)
    (hspk_priv_eq : spkPrivBytes = sc.ratchetKey.privateKey.bytes.toList)
    (hspk_clamp : Ratchet.clampScalar sc.ratchetKey.privateKey.bytes =
      sc.ratchetKey.privateKey.bytes)
    (hck_eq : chainKeyBytes = keyToBytes32 sc.chainKey.key)
    (hck_idx : sc.chainKey.index = 0#32) :
    (Initiator.senderChainFieldsAt ss ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr 0#32 ∗
      ((ss + 0xf4#64) ↦₃₂ pad_f4) ∗
      (ratchetPubBoxPtr ↦ₛ spkPubBytes) ∗ A.live ratchetPubBoxPtr 33 1 ∗
      (ratchetPrivBoxPtr ↦ₛ spkPrivBytes) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
      (chainKeyBoxPtr ↦ₛ chainKeyBytes) ∗ A.live chainKeyBoxPtr 32 1) ⊢
    optSenderChainAt A (ss + 0x90#64)
      (some (mkBobSenderChainGhost ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
        spkPubBytes spkPrivBytes)) (some sc) := by
  have hsub0 : ∀ a b : BitVec 64, ss + a + b = ss + (a + b) := fun a b => by bv_omega
  have hsrk := vecGhostAt_of_box (A := A) (ss + 0x90#64) ratchetPubBoxPtr 33#64 33 spkPubBytes
    hrat_pub (by decide) rfl rfl hspk_pub_len (by decide)
  have hpriv := vecGhostAt_of_box (A := A) (ss + 0xa8#64) ratchetPrivBoxPtr 32#64 32 spkPrivBytes
    hrat_priv (by decide) rfl rfl hspk_priv_len (by decide)
  have hck_vec := vecGhostAt_of_box (A := A) (ss + 0xd8#64) chainKeyBoxPtr 32#64 32
    (keyToBytes32 sc.chainKey.key) hck_ptr (by decide) rfl rfl (length_keyToBytes32 _) (by decide)
  have hmk :
      ((ss + 0xc0#64) ↦₆₄ 0#64) ∗ ((ss + 0xc8#64) ↦₆₄ 8#64) ∗ ((ss + 0xd0#64) ↦₆₄ 0#64) ⊢
      vecAt A 104 8 (messageKeyAt A) (ss + 0xc0#64) 0#64 8#64 [] := by
    unfold vecAt vecHeader vecBuf
    simp only [hsub0, BitVec.reduceAdd, List.length_nil, ↓reduceIte]
    rw [← sepConj_emp (((ss + 0xc0#64) ↦₆₄ 0#64) ∗ ((ss + 0xc8#64) ↦₆₄ 8#64) ∗
      ((ss + 0xd0#64) ↦₆₄ 0#64))]
    exact Entails.trans (Entails.of_eq (by ac_rfl))
      (sepConj_mono_right (Entails.pure_right ⟨by decide, by decide, by decide⟩ (Entails.refl _)))
  have hpad := pointsTo32_entails_memRegion (ss + 0xf4#64) pad_f4
  unfold optSenderChainAt optChainKeyAt mkBobSenderChainGhost Initiator.senderChainFieldsAt
  refine Entails.pure_right ⟨hspk_deser, hspk_priv_eq, hspk_clamp, hspk_pub_len⟩ ?_
  rw [hck_eq, ← hck_idx]
  simp only [hsub0, BitVec.reduceAdd] at hsrk hpriv hck_vec ⊢
  refine Entails.trans (entails_replace_sub hsrk (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub hpriv (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub hmk (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub hck_vec (by sep_focus) rfl) ?_
  exact entails_replace_sub hpad (by sep_focus) (eq_of_sep_emp (by unfold vecGhostAt; sep_focus))

theorem p2BobSlotsV1_entails_sessionStateAt {A : RustAlloc}
    (ss locIdPtr remIdPtr rootKeyPtr aliceBasePtr spqrCap spqrBufPtr : BitVec 64)
    (locIdBytes remIdBytes rootKeyBytes aliceBaseBytes pqBytes : List (BitVec 8))
    (sg : SenderChainGhost) (sc : SenderChain) (prevCounter f248 f24c : BitVec 32)
    (st : SessionState (List (BitVec 8))) (remIk : IdentityKey)
    (hnew1 : locIdPtr ≠ 0#64) (hnew2 : remIdPtr ≠ 0#64)
    (hnew3 : rootKeyPtr ≠ 0#64) (hnew4 : aliceBasePtr ≠ 0#64)
    (hloc_len : locIdBytes.length = 33) (hrem_len : remIdBytes.length = 33)
    (halice_len : aliceBaseBytes.length = 33)
    (hloc_deser : PublicKey.deserialize locIdBytes = .ok st.localIdentity.publicKey)
    (hrem_eq : st.remoteIdentity = some remIk)
    (hrem_deser : PublicKey.deserialize remIdBytes = .ok remIk.publicKey)
    (hroot_eq : rootKeyBytes = keyToBytes32 st.rootKey)
    (hrc : st.receiverChains = []) (hpq : pqBytes = st.pqRatchetState)
    (hsc : st.senderChain = some sc) (hpend : st.pendingPreKey = false)
    (hver : st.sessionVersion = 4#32) (hprev : st.previousCounter = prevCounter) :
    ((ss ↦₆₄ 33#64) ∗ ((ss + 0x08#64) ↦₆₄ locIdPtr) ∗ ((ss + 0x10#64) ↦₆₄ 33#64) ∗
      ((ss + 0x18#64) ↦₆₄ 33#64) ∗ ((ss + 0x20#64) ↦₆₄ remIdPtr) ∗ ((ss + 0x28#64) ↦₆₄ 33#64) ∗
      ((ss + 0x30#64) ↦₆₄ 32#64) ∗ ((ss + 0x38#64) ↦₆₄ rootKeyPtr) ∗ ((ss + 0x40#64) ↦₆₄ 32#64) ∗
      ((ss + 0x48#64) ↦₆₄ 0#64) ∗ ((ss + 0x50#64) ↦₆₄ 8#64) ∗ ((ss + 0x58#64) ↦₆₄ 0#64) ∗
      ((ss + 0x60#64) ↦₆₄ 33#64) ∗ ((ss + 0x68#64) ↦₆₄ aliceBasePtr) ∗ ((ss + 0x70#64) ↦₆₄ 33#64) ∗
      ((ss + 0x78#64) ↦₆₄ spqrCap) ∗ ((ss + 0x80#64) ↦₆₄ spqrBufPtr) ∗
      ((ss + 0x88#64) ↦₆₄ BitVec.ofNat 64 pqBytes.length) ∗
      p2BobSpqrVecBuf A spqrCap spqrBufPtr pqBytes ∗
      optSenderChainAt A (ss + 0x90#64) (some sg) (some sc) ∗
      optTailVecAt A 48 (ss + 0xf8#64) none ∗
      optTailVecAt A 32 (ss + 0x128#64) none ∗
      ((ss + 0x148#64) ↦₃₂ 4#32) ∗ ((ss + 0x14c#64) ↦₃₂ prevCounter) ∗
      ((ss + 0x150#64) ↦₃₂ f248) ∗ ((ss + 0x154#64) ↦₃₂ f24c) ∗
      A.live locIdPtr 33 1 ∗ (locIdPtr ↦ₛ locIdBytes) ∗
      A.live remIdPtr 33 1 ∗ (remIdPtr ↦ₛ remIdBytes) ∗
      A.live rootKeyPtr 32 1 ∗ (rootKeyPtr ↦ₛ rootKeyBytes) ∗
      A.live aliceBasePtr 33 1 ∗ (aliceBasePtr ↦ₛ aliceBaseBytes)) ⊢
    sessionStateAt A ss
      (mkBobGhostV1 locIdPtr remIdPtr rootKeyPtr aliceBasePtr spqrCap spqrBufPtr
        locIdBytes remIdBytes aliceBaseBytes sg f248 f24c) st := by
  have hloc := vecGhostAt_of_box (A := A) ss locIdPtr 33#64 33 locIdBytes
    hnew1 (by decide) rfl rfl hloc_len (by decide)
  have hrem := vecGhostAt_of_box (A := A) (ss + 0x18#64) remIdPtr 33#64 33 remIdBytes
    hnew2 (by decide) rfl rfl hrem_len (by decide)
  have h18_8 : ss + 0x18#64 + 8#64 = ss + 0x20#64 := by bv_omega
  have h18_16 : ss + 0x18#64 + 16#64 = ss + 0x28#64 := by bv_omega
  rw [h18_8, h18_16] at hrem
  have hroot :
      ((ss + 0x30#64) ↦₆₄ 32#64) ∗ ((ss + 0x38#64) ↦₆₄ rootKeyPtr) ∗ ((ss + 0x40#64) ↦₆₄ 32#64) ∗
      A.live rootKeyPtr 32 1 ∗ (rootKeyPtr ↦ₛ rootKeyBytes) ⊢
      vecU8At A (ss + 0x30#64) 32#64 rootKeyPtr (keyToBytes32 st.rootKey) := by
    rw [hroot_eq]
    have hr := vecGhostAt_of_box (A := A) (ss + 0x30#64) rootKeyPtr 32#64 32
      (keyToBytes32 st.rootKey) hnew3 (by decide) rfl rfl (length_keyToBytes32 _) (by decide)
    have h1 : ss + 0x30#64 + 8#64 = ss + 0x38#64 := by bv_omega
    have h2 : ss + 0x30#64 + 16#64 = ss + 0x40#64 := by bv_omega
    rw [h1, h2] at hr
    exact hr
  have hchains :
      ((ss + 0x48#64) ↦₆₄ 0#64) ∗ ((ss + 0x50#64) ↦₆₄ 8#64) ∗ ((ss + 0x58#64) ↦₆₄ 0#64) ⊢
      vecAt A 104 8 (chainAt A) (ss + 0x48#64) 0#64 8#64
        (([] : List ChainGhost).zip st.receiverChains) := by
    unfold vecAt vecHeader vecBuf
    have h1 : ss + 0x48#64 + 8#64 = ss + 0x50#64 := by bv_omega
    have h2 : ss + 0x48#64 + 16#64 = ss + 0x58#64 := by bv_omega
    rw [hrc]
    simp only [h1, h2, List.zip_nil_left, List.length_nil, ↓reduceIte]
    rw [← sepConj_emp (((ss + 0x48#64) ↦₆₄ 0#64) ∗ ((ss + 0x50#64) ↦₆₄ 8#64) ∗
      ((ss + 0x58#64) ↦₆₄ 0#64))]
    exact Entails.trans (Entails.of_eq (by ac_rfl))
      (sepConj_mono_right (Entails.pure_right ⟨by decide, by decide, by decide⟩ (Entails.refl _)))
  have halice := vecGhostAt_of_box (A := A) (ss + 0x60#64) aliceBasePtr 33#64 33 aliceBaseBytes
    hnew4 (by decide) rfl rfl halice_len (by decide)
  have h60_8 : ss + 0x60#64 + 8#64 = ss + 0x68#64 := by bv_omega
  have h60_16 : ss + 0x60#64 + 16#64 = ss + 0x70#64 := by bv_omega
  rw [h60_8, h60_16] at halice
  have hpq_hdr :
      ((ss + 0x78#64) ↦₆₄ spqrCap) ∗ ((ss + 0x80#64) ↦₆₄ spqrBufPtr) ∗
      ((ss + 0x88#64) ↦₆₄ BitVec.ofNat 64 pqBytes.length) ∗
      p2BobSpqrVecBuf A spqrCap spqrBufPtr pqBytes ⊢
      vecU8At A (ss + 0x78#64) spqrCap spqrBufPtr st.pqRatchetState := by
    have h1 : ss + 0x78#64 + 8#64 = ss + 0x80#64 := by bv_omega
    have h2 : ss + 0x78#64 + 16#64 = ss + 0x88#64 := by bv_omega
    rw [hpq, ← h1, ← h2]
    exact Entails.of_eq (p2BobSpqrVecBuf_eq_vecU8At _ _ _ _ _)
  have htail :
      ((ss + 0x148#64) ↦₃₂ 4#32) ∗ ((ss + 0x14c#64) ↦₃₂ prevCounter) ∗
      ((ss + 0x150#64) ↦₃₂ f248) ∗ ((ss + 0x154#64) ↦₃₂ f24c) =
      ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗ ((ss + 0x14c#64) ↦₃₂ st.previousCounter) ∗
      ((ss + 0x150#64) ↦ₛ (unpack32 f248 ++ unpack32 f24c)) := by
    have h154 : ss + 0x150#64 + 4#64 = ss + 0x154#64 := by bv_omega
    rw [hver, hprev, pointsToBytes_append, unpack32_length, ← pointsTo32_eq_pointsToBytes,
      ← pointsTo32_eq_pointsToBytes, h154]
  unfold sessionStateAt mkBobGhostV1
  dsimp only
  have hpure :
      PublicKey.deserialize locIdBytes = .ok st.localIdentity.publicKey ∧
      (match st.remoteIdentity with
       | none => remIdBytes = []
       | some ik => PublicKey.deserialize remIdBytes = .ok ik.publicKey) ∧
      ([] : List ChainGhost).length = st.receiverChains.length ∧
      (none : Option TailVecGhost).isSome = st.pendingPreKey ∧
      (unpack32 f248 ++ unpack32 f24c).length = 8 ∧
      locIdBytes.length = 33 ∧
      (st.remoteIdentity.isSome → remIdBytes.length = 33) := by
    refine ⟨hloc_deser, ?_, by simp [hrc], by simp [hpend], by simp, hloc_len, fun _ => hrem_len⟩
    rw [hrem_eq]; exact hrem_deser
  apply Entails.pure_right hpure
  rw [hsc, ← htail]
  refine Entails.trans (entails_replace_sub hloc (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub hrem (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub hroot (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub hchains (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub halice (by sep_focus) rfl) ?_
  exact entails_replace_sub hpq_hdr (by sep_focus) (eq_of_sep_emp (by sep_focus))

theorem p2BobSessRegIdsV1_entails_sessionStateAt {A : RustAlloc}
    (ss localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
      ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
    (pad_f4 remoteRegId localRegId : BitVec 32)
    (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64)
    (locIdBytes remIdBytes rootKeyBytes aliceBaseBytes spkPubBytes spkPrivBytes
      chainKeyBytes pqBytes : List (BitVec 8))
    (sc : SenderChain) (st : SessionState (List (BitVec 8))) (remIk : IdentityKey)
    (hloc_nz : localIkBoxPtr ≠ 0#64) (hrem_nz : remoteIkBoxPtr ≠ 0#64)
    (hroot_nz : rootKeyBoxPtr ≠ 0#64) (halice_nz : baseKeyBoxPtr ≠ 0#64)
    (hrat_pub : ratchetPubBoxPtr ≠ 0#64) (hrat_priv : ratchetPrivBoxPtr ≠ 0#64)
    (hck_ptr : chainKeyBoxPtr ≠ 0#64)
    (hloc_len : locIdBytes.length = 33) (hrem_len : remIdBytes.length = 33)
    (halice_len : aliceBaseBytes.length = 33) (hspk_pub_len : spkPubBytes.length = 33)
    (hspk_priv_len : spkPrivBytes.length = 32)
    (hloc_deser : PublicKey.deserialize locIdBytes = .ok st.localIdentity.publicKey)
    (hrem_eq : st.remoteIdentity = some remIk)
    (hrem_deser : PublicKey.deserialize remIdBytes = .ok remIk.publicKey)
    (hspk_deser : PublicKey.deserialize spkPubBytes = .ok sc.ratchetKey.publicKey)
    (hspk_priv_eq : spkPrivBytes = sc.ratchetKey.privateKey.bytes.toList)
    (hspk_clamp : Ratchet.clampScalar sc.ratchetKey.privateKey.bytes =
      sc.ratchetKey.privateKey.bytes)
    (hroot_eq : rootKeyBytes = keyToBytes32 st.rootKey)
    (hck_eq : chainKeyBytes = keyToBytes32 sc.chainKey.key)
    (hck_idx : sc.chainKey.index = 0#32)
    (hrc : st.receiverChains = []) (hpq : pqBytes = st.pqRatchetState)
    (hsc : st.senderChain = some sc) (hpend : st.pendingPreKey = false)
    (hver : st.sessionVersion = 4#32) (hprev : st.previousCounter = 0#32) :
    ((ss ↦ₛ p2BobSessRegIdsV1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
        spqrCap spqrBufPtr (BitVec.ofNat 64 pqBytes.length) ratchetPubBoxPtr ratchetPrivBoxPtr
        chainKeyBoxPtr pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 remoteRegId localRegId) ∗
      p2BobSpqrVecBuf A spqrCap spqrBufPtr pqBytes ∗
      (localIkBoxPtr ↦ₛ locIdBytes) ∗ A.live localIkBoxPtr 33 1 ∗
      (remoteIkBoxPtr ↦ₛ remIdBytes) ∗ A.live remoteIkBoxPtr 33 1 ∗
      (rootKeyBoxPtr ↦ₛ rootKeyBytes) ∗ A.live rootKeyBoxPtr 32 1 ∗
      (baseKeyBoxPtr ↦ₛ aliceBaseBytes) ∗ A.live baseKeyBoxPtr 33 1 ∗
      (ratchetPubBoxPtr ↦ₛ spkPubBytes) ∗ A.live ratchetPubBoxPtr 33 1 ∗
      (ratchetPrivBoxPtr ↦ₛ spkPrivBytes) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
      (chainKeyBoxPtr ↦ₛ chainKeyBytes) ∗ A.live chainKeyBoxPtr 32 1) ⊢
    sessionStateAt A ss
      (mkBobGhostV1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
        locIdBytes remIdBytes aliceBaseBytes
        (mkBobSenderChainGhost ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
          spkPubBytes spkPrivBytes)
        remoteRegId localRegId) st := by
  rw [← p2BobSessRegIdsV1_fold]
  have hmid := p2BobSessMid280V1_entails_fields ss rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
    (BitVec.ofNat 64 pqBytes.length) ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
    pad_f4 c0 c1 c2 c3 c4 d0 d1 d2
  have hsc_fold := bobSenderChain_ss_entails_optSenderChainAt (A := A) ss ratchetPubBoxPtr
    ratchetPrivBoxPtr chainKeyBoxPtr spkPubBytes spkPrivBytes chainKeyBytes pad_f4 sc
    hrat_pub hrat_priv hck_ptr hspk_pub_len hspk_priv_len hspk_deser hspk_priv_eq
    hspk_clamp hck_eq hck_idx
  have hpend1 :
      ((ss + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (ss + 0x100#64) 40 =
      optTailVecAt A 48 (ss + 0xf8#64) none := by
    unfold optTailVecAt noneCap
    have ha : ss + 0xf8#64 + 8#64 = ss + 0x100#64 := by bv_omega
    rw [ha]
  have hpend2 :
      ((ss + 0x128#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (ss + 0x130#64) 24 =
      optTailVecAt A 32 (ss + 0x128#64) none := by
    unfold optTailVecAt noneCap
    have ha : ss + 0x128#64 + 8#64 = ss + 0x130#64 := by bv_omega
    rw [ha]
  have hslots := p2BobSlotsV1_entails_sessionStateAt (A := A) ss localIkBoxPtr remoteIkBoxPtr
    rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr locIdBytes remIdBytes rootKeyBytes
    aliceBaseBytes pqBytes
    (mkBobSenderChainGhost ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
      spkPubBytes spkPrivBytes)
    sc 0#32 remoteRegId localRegId st remIk
    hloc_nz hrem_nz hroot_nz halice_nz hloc_len hrem_len halice_len
    hloc_deser hrem_eq hrem_deser hroot_eq hrc hpq hsc hpend hver hprev
  refine Entails.trans (entails_replace_sub hmid (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub hsc_fold (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub (Entails.of_eq hpend1) (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub (Entails.of_eq hpend2) (by sep_focus) rfl) ?_
  exact Entails.trans (Entails.of_eq (eq_of_sep_emp (by sep_focus))) hslots

/-! ## 3. Canonical `p2BobInitSessionV1` & Discharged Packing Lemma -/

theorem length_bytesToBv8_encodeEC_of_len32 {bs : SignalPqxdh.Bytes} (h : bs.length = 32) :
    (bytesToBv8 (Model.encodeEC bs)).length = 33 := by
  have hbv : (bytesToBv8 bs).length = 32 := by simpa [bytesToBv8] using h
  change (5#8 :: bytesToBv8 bs).length = 33
  simp [hbv]

theorem deserialize_bytesToBv8_encodeEC_of_len32 {bs : SignalPqxdh.Bytes} (h : bs.length = 32) :
    PublicKey.deserialize (bytesToBv8 (Model.encodeEC bs)) =
      .ok ⟨⟨bytesToBv8 bs, by simpa [bytesToBv8] using h⟩⟩ := by
  have hbv : (bytesToBv8 bs).length = 32 := by simpa [bytesToBv8] using h
  change PublicKey.deserialize (5#8 :: bytesToBv8 bs) = _
  unfold PublicKey.deserialize djbType
  simp [hbv, List.take_of_length_le (Nat.le_of_eq hbv)]

private theorem p2_clampBv8List_vec32_eq (v : List.Vector (BitVec 8) 32) :
    clampBv8List v.toList = (Ratchet.clampScalar v).toList := by
  rcases v with ⟨l, hl⟩
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31,
      _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    first
    | (dsimp [clampBv8List, List.Vector.toList, List.Vector.get,
         Ratchet.clampScalar, List.Vector.set]; rfl)
    | cases hl

private theorem p2_clampScalar_of_clampBv8List {spkPrivBytes : List (BitVec 8)}
    {spkBSk : SignalPqxdh.Bytes} (hlen : spkPrivBytes.length = 32)
    (hclamp : clampBv8List spkPrivBytes = bytesToBv8 spkBSk)
    (hbv : (bytesToBv8 spkBSk).length = 32) :
    Ratchet.clampScalar ⟨bytesToBv8 spkBSk, hbv⟩ = ⟨bytesToBv8 spkBSk, hbv⟩ := by
  have hv : (⟨bytesToBv8 spkBSk, hbv⟩ : List.Vector (BitVec 8) 32) =
      Ratchet.clampScalar ⟨spkPrivBytes, hlen⟩ := by
    apply Subtype.ext
    change bytesToBv8 spkBSk = (Ratchet.clampScalar ⟨spkPrivBytes, hlen⟩).toList
    rw [← hclamp, ← p2_clampBv8List_vec32_eq ⟨spkPrivBytes, hlen⟩]
    rfl
  rw [hv]
  exact Reach.clampScalar_idem ⟨spkPrivBytes, hlen⟩

/-- Canonical SPQR V1 Bob `SessionState` constructed from `AcceptKeysInput` and `drKey`. -/
def p2BobInitSessionV1 (ikBPk spkBPk : SignalPqxdh.Bytes) (inp : AcceptKeysInput)
    (drKey : DRKey) (pq : List (BitVec 8))
    (hik : ikBPk.length = 32) (hrem : inp.hdr.ikAPk.length = 32)
    (hspk_pub : spkBPk.length = 32) (hspk_priv : (bytesToBv8 inp.spkBSk).length = 32) :
    SessionState (List (BitVec 8)) :=
  (SessionState.new 4#8
    ⟨⟨bytesToBv8 ikBPk, by simpa [bytesToBv8] using hik⟩⟩
    ⟨⟨bytesToBv8 inp.hdr.ikAPk, by simpa [bytesToBv8] using hrem⟩⟩
    (HKDF.bytesToKey32 (ofU8 drKey.rootKey))
    pq).setSenderChain
    { publicKey := ⟨⟨bytesToBv8 spkBPk, by simpa [bytesToBv8] using hspk_pub⟩⟩
      privateKey := ⟨⟨bytesToBv8 inp.spkBSk, hspk_priv⟩⟩ }
    ⟨HKDF.bytesToKey32 (ofU8 drKey.chainKey), 0#32⟩

theorem p2BobSessRegIdsV1_entails_bobInitSessionV1 {P : Primitives} {A : RustAlloc}
    {inp : AcceptKeysInput} {ikBPk spkBPk : SignalPqxdh.Bytes}
    {spkPrivBytes : List (BitVec 8)} {drKey : DRKey}
    (hWF : StructuralPrims P) (hacc : Model.acceptKeys P inp = some drKey)
    (hwell : WellSizedAcceptKeysInput inp)
    (hikBPk_len : ikBPk.length = 32) (hspkBPk_len : spkBPk.length = 32)
    (hspk_priv_len : spkPrivBytes.length = 32)
    (hspk_clamp : clampBv8List spkPrivBytes = bytesToBv8 inp.spkBSk)
    (ss localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
      ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
    (pad_f4 remoteRegId localRegId : BitVec 32)
    (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64)
    (pqBytes : List (BitVec 8))
    (hloc_nz : localIkBoxPtr ≠ 0#64) (hrem_nz : remoteIkBoxPtr ≠ 0#64)
    (hroot_nz : rootKeyBoxPtr ≠ 0#64) (halice_nz : baseKeyBoxPtr ≠ 0#64)
    (hrat_pub : ratchetPubBoxPtr ≠ 0#64) (hrat_priv : ratchetPrivBoxPtr ≠ 0#64)
    (hck_ptr : chainKeyBoxPtr ≠ 0#64) :
    have hrem_len32 : inp.hdr.ikAPk.length = 32 := hwell.2.2.2.2.2.2.2.1
    have hspk_bv_len : (bytesToBv8 inp.spkBSk).length = 32 := by
      rw [← hspk_clamp]; exact clampBv8List_length hspk_priv_len
    ((ss ↦ₛ p2BobSessRegIdsV1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
        spqrCap spqrBufPtr (BitVec.ofNat 64 pqBytes.length) ratchetPubBoxPtr ratchetPrivBoxPtr
        chainKeyBoxPtr pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 remoteRegId localRegId) ∗
      p2BobSpqrVecBuf A spqrCap spqrBufPtr pqBytes ∗
      (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
      (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ikAPk)) ∗ A.live remoteIkBoxPtr 33 1 ∗
      (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
      (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC inp.hdr.ekAPk)) ∗ A.live baseKeyBoxPtr 33 1 ∗
      (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗ A.live ratchetPubBoxPtr 33 1 ∗
      (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
      (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1) ⊢
    sessionStateAt A ss
      (mkBobGhostV1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
        (bytesToBv8 (Model.encodeEC ikBPk)) (bytesToBv8 (Model.encodeEC inp.hdr.ikAPk))
        (bytesToBv8 (Model.encodeEC inp.hdr.ekAPk))
        (mkBobSenderChainGhost ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
          (bytesToBv8 (Model.encodeEC spkBPk)) (bytesToBv8 inp.spkBSk))
        remoteRegId localRegId)
      (p2BobInitSessionV1 ikBPk spkBPk inp drKey pqBytes
        hikBPk_len hrem_len32 hspkBPk_len hspk_bv_len) := by
  intro hrem_len32 hspk_bv_len
  have hek_len32 : inp.hdr.ekAPk.length = 32 := hwell.2.2.2.2.2.2.2.2.1
  obtain ⟨_, _, hrk_eq, hck_eq⟩ := P3P4.acceptKeys_rootKey_chainKey_props hWF hacc
  exact p2BobSessRegIdsV1_entails_sessionStateAt ss localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr
    baseKeyBoxPtr spqrCap spqrBufPtr ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
    pad_f4 remoteRegId localRegId c0 c1 c2 c3 c4 d0 d1 d2
    (bytesToBv8 (Model.encodeEC ikBPk)) (bytesToBv8 (Model.encodeEC inp.hdr.ikAPk))
    (bytesToBv8 drKey.rootKey) (bytesToBv8 (Model.encodeEC inp.hdr.ekAPk))
    (bytesToBv8 (Model.encodeEC spkBPk)) (bytesToBv8 inp.spkBSk)
    (bytesToBv8 drKey.chainKey) pqBytes
    { ratchetKey :=
        { publicKey := ⟨⟨bytesToBv8 spkBPk, by simpa [bytesToBv8] using hspkBPk_len⟩⟩
          privateKey := ⟨⟨bytesToBv8 inp.spkBSk, hspk_bv_len⟩⟩ }
      chainKey := ⟨HKDF.bytesToKey32 (ofU8 drKey.chainKey), 0#32⟩ }
    (p2BobInitSessionV1 ikBPk spkBPk inp drKey pqBytes
      hikBPk_len hrem_len32 hspkBPk_len hspk_bv_len)
    ⟨⟨bytesToBv8 inp.hdr.ikAPk, by simpa [bytesToBv8] using hrem_len32⟩⟩
    hloc_nz hrem_nz hroot_nz halice_nz hrat_pub hrat_priv hck_ptr
    (length_bytesToBv8_encodeEC_of_len32 hikBPk_len)
    (length_bytesToBv8_encodeEC_of_len32 hrem_len32)
    (length_bytesToBv8_encodeEC_of_len32 hek_len32)
    (length_bytesToBv8_encodeEC_of_len32 hspkBPk_len)
    hspk_bv_len
    (deserialize_bytesToBv8_encodeEC_of_len32 hikBPk_len)
    rfl
    (deserialize_bytesToBv8_encodeEC_of_len32 hrem_len32)
    (deserialize_bytesToBv8_encodeEC_of_len32 hspkBPk_len)
    rfl
    (p2_clampScalar_of_clampBv8List hspk_priv_len hspk_clamp hspk_bv_len)
    hrk_eq.symm
    hck_eq.symm
    rfl rfl rfl rfl rfl rfl rfl

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
