/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDerive
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAlice
import LibsignalBinary.Proofs.E2E.Pqxdh.TopLevel.SessionInitiatePostCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RunEnvCommon
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ModelBridge

/-!
# Stage 5 `SessionState` Lenses, `SessionRecord` Promotion, and Model Agreement

Separation-logic lenses (`sessionState_unack_lens`, `sessionState_regIds_lens`), `SessionRecord`
promotion and `< 2 ^ 32` serialized length bound (`sessionRecord_promote_accept`), `initDef`
accept-path agreement, and post-store `SessionRecord` unpack (`sessionRecord_unpack_drop`).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection CryptoGames
open CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh.Shared CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

/-! ## Bundle and Handshake Header Equalities -/

theorem bundleEOf_fields {b : BundleV} {be : PreKeyBundleFields} (h : bundleEOf? b = some be) :
    be.regId = b.regId ∧ be.spkId = b.spkId ∧ be.kpkId = b.kpkId ∧
      be.idPub = b.idKey.publicKey.bytes ∧ be.spkPub = b.spk.bytes ∧
      be.opk.map Prod.fst = b.opk.map Prod.fst := by
  dsimp only [bundleEOf?] at h
  split_ifs at h with h1 h2 h3
  cases h
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  cases b.opk <;> rfl

theorem ofU8_toU8 (bs : List (BitVec 8)) : ofU8 (toU8 bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    dsimp only [toU8, ofU8, List.map_cons]
    exact congrArg₂ List.cons (by apply BitVec.eq_of_toNat_eq; cases b; simp) ih

theorem bytesToBv8_toU8 (bs : List (BitVec 8)) :
    Pqxdh.Initiator.bytesToBv8 (toU8 bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    dsimp only [Pqxdh.Initiator.bytesToBv8, toU8, List.map_cons]
    exact congrArg₂ List.cons (by apply BitVec.eq_of_toNat_eq; cases b; simp) ih

private theorem toList_u8Vec_eq_ofU8 {n : Nat} {bs : List UInt8} (h : (ofU8 bs).length = n) :
    (u8Vec n bs).toList = ofU8 bs := by
  dsimp only [u8Vec, fitVec]
  simp [h]

private theorem u8Vec_toU8_vec {n : Nat} (v : List.Vector (BitVec 8) n) :
    u8Vec n (toU8 v.toList) = v := by
  apply List.Vector.eq
  rw [toList_u8Vec_eq_ofU8 (by rw [ofU8_toU8]; exact v.2), ofU8_toU8]

theorem initiateKeys_hdr_props {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {kp : IdentityKeyPair} {be : PreKeyBundleFields} {coins : List (BitVec 8)}
    {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    (hek :
      let ekKP := keyPairOf W.C ⟨(padCoins coins).toList.take 32, by simp; decide⟩
      ekASk = ekKP.privateKey.bytes.toList ∧ ekAPk = ekKP.publicKey.bytes.toList)
    (hkeys : SignalPqxdh.Model.initiateKeys (modelPrims X W)
      (initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)) = some (dk, hdr)) :
    (toU8 ekAPk).length = 32 ∧
      Pqxdh.Initiator.bytesToBv8 (SignalPqxdh.encodeEC (toU8 ekAPk)) =
        (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize ∧
      (0x08#8 :: ofU8 hdr.kemCt).length = 1569 ∧
      kyberKey (u8Vec 1568 hdr.kemCt) = 0x08#8 :: ofU8 hdr.kemCt := by
  dsimp only [SignalPqxdh.Model.initiateKeys] at hkeys
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hkeys
  obtain ⟨_, _, _, _, _, _, ⟨ssKem, kemCt⟩, hkem, _, _, _, _, _, _, _, _, hpair⟩ := hkeys
  injection hpair with hprodTop
  rcases Prod.mk.inj hprodTop with ⟨_, rfl⟩
  dsimp only
  dsimp only [modelPrims, blockLevelPrims, SignalPqxdh.kyberPkLen] at hkem
  have hpkLen : ((initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).bundle.pqspkB.length == 1568) = true := by
    dsimp only [initiateInput]; rw [Pqxdh.Initiator.e2e_vecU8_length]; rfl
  simp only [hpkLen, ↓reduceIte] at hkem
  have hctEq : kemCt = E2E.vecU8 (W.Q.encaps
      (u8Vec 1568 (initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).bundle.pqspkB)
      (u8Vec 32 (initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).kemCoins)).1 := by
    injection hkem with hprod
    exact (Prod.mk.inj hprod).2.symm
  have hofKem : (ofU8 kemCt).length = 1568 := by
    rw [hctEq]
    simp [ofU8, E2E.vecU8]
  let ekSeed : List.Vector (BitVec 8) 32 := ⟨(padCoins coins).toList.take 32, by simp; decide⟩
  let ekKP := keyPairOf W.C ekSeed
  change ekASk = ekKP.privateKey.bytes.toList ∧ ekAPk = ekKP.publicKey.bytes.toList at hek
  obtain ⟨_, hekAPk⟩ := hek
  have hekLen : (toU8 ekAPk).length = 32 := by
    rw [hekAPk]
    simp [toU8]
  have hekEnc : Pqxdh.Initiator.bytesToBv8 (SignalPqxdh.encodeEC (toU8 ekAPk)) = 0x05#8 :: ekAPk := by
    rw [hekAPk]
    have hv : toU8 ekKP.publicKey.bytes.toList = E2E.vecU8 ekKP.publicKey.bytes := by
      simp [toU8, E2E.vecU8]
    exact (congrArg (fun l => Pqxdh.Initiator.bytesToBv8 (SignalPqxdh.encodeEC l)) hv).trans
      (Pqxdh.Initiator.bytesToBv8_encodeEC_vecU8 ekKP.publicKey.bytes)
  have hhdrPk : (u8Vec 32 ((modelPrims X W).x25519Base
      (initiateInput W ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins coins)).ekASk)).toList = ekAPk := by
    rw [toList_u8Vec_eq_ofU8 (by dsimp only [modelPrims, blockLevelPrims]; simp [ofU8, E2E.vecU8])]
    dsimp only [modelPrims, blockLevelPrims, initiateInput, E2E.vecU8]
    rw [ofU8_toU8]
    change (W.C.pubKey (Ratchet.clampScalar (u8Vec 32 (toU8 ekSeed.toList)))).toList = ekAPk
    rw [u8Vec_toU8_vec ekSeed, hekAPk]
    rfl
  refine ⟨hekLen, ?_, by simp [hofKem], ?_⟩
  · rw [hekEnc]
    dsimp only [PublicKey.serialize]
    rw [hhdrPk]
    rfl
  · dsimp only [kyberKey]
    rw [toList_u8Vec_eq_ofU8 hofKem]

/-! ## `SessionState` Field Lenses -/

def pack4LE (b0 b1 b2 b3 : BitVec 8) : BitVec 32 :=
  b0.zeroExtend 32 ||| (b1.zeroExtend 32 <<< 8) |||
    (b2.zeroExtend 32 <<< 16) ||| (b3.zeroExtend 32 <<< 24)

theorem unpack32_pack4LE (b0 b1 b2 b3 : BitVec 8) :
    unpack32 (pack4LE b0 b1 b2 b3) = [b0, b1, b2, b3] := by
  dsimp only [unpack32, pack4LE]
  refine congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_
    (congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ rfl))) <;>
    (ext i hi; interval_cases i <;> simp)

theorem pointsToBytes_4_exists_32 {bs : List (BitVec 8)} (h : bs.length = 4) :
    ∃ w : BitVec 32, ∀ a : BitVec 64, (a ↦ₛ bs) = (a ↦₃₂ w) := by
  match bs, h with
  | [b0, b1, b2, b3], _ =>
    refine ⟨pack4LE b0 b1 b2 b3, fun a => ?_⟩
    rw [pointsTo32_eq_pointsToBytes, unpack32_pack4LE]

theorem leBytes_4_eq_unpack32 (w : BitVec 32) : leBytes 4 w.toNat = unpack32 w := by
  change [BitVec.ofNat 8 (w.toNat / 1), BitVec.ofNat 8 (w.toNat / 256),
          BitVec.ofNat 8 (w.toNat / 65536), BitVec.ofNat 8 (w.toNat / 16777216)] =
    [BitVec.extractLsb' 0 8 w, BitVec.extractLsb' 8 8 w,
     BitVec.extractLsb' 16 8 w, BitVec.extractLsb' 24 8 w]
  congr 1
  · apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb']
  · congr 1
    · apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]
    · congr 1
      · apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]
      · congr 1
        · apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]

theorem leBytes_8_zero_eq_unpack64 : leBytes 8 (0#64 : BitVec 64).toNat = unpack64 0#64 := by
  decide

/-- Decompose `sessionStateAt A p sg ss` at Stage 5 entry (`sg.pending = none`,
`sg.kyber = some kg`) to expose:
- `(p + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64` + `memRegion (p + 0x100#64) 40` for
  `set_unacknowledged_pre_key_message`,
- `(p + 0x128#64) ↦₆₄ cap` (`cap + 1#64 ≠ 0#64`) + `(p + 0x140#64) ↦₃₂ w0` for
  `set_unacknowledged_kyber_pre_key_id`,
and re-fold the updated fields back into `sessionStateAt A p sg₁ ss.setUnacknowledgedPreKeyMessage`. -/
theorem sessionState_unack_lens (A : RustAlloc) (p : BitVec 64)
    (sg : SessionGhost) (ss : SessionState (List (BitVec 8)))
    {kg : TailVecGhost} {pendBytes : List (BitVec 8)}
    (hpend0 : sg.pending = none)
    (hkyb0 : sg.kyber = some kg)
    (hpendLen : pendBytes.length = 33) :
    ∀ R (m : Memory), m ⊨ sessionStateAt A p sg ss ∗ R →
      ∃ (cap : BitVec 64) (w0 w1 : BitVec 32) (Rest : SepProp),
        cap = kg.vec.cap ∧
        cap + 1#64 ≠ 0#64 ∧
        (m ⊨ ((p + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
              memRegion (p + 0x100#64) 40 ∗
              ((p + 0x128#64) ↦₆₄ cap) ∗
              ((p + 0x140#64) ↦₃₂ w0) ∗
              (Rest ∗ R)) ∧
        ∀ (opkTag opkId spkId kpkId padVal : BitVec 32) (dataPtr : BitVec 64),
          dataPtr ≠ 0#64 →
          ((p + 0xf8#64) ↦₆₄ 33#64) ∗ ((p + 0x100#64) ↦₆₄ dataPtr) ∗
          ((p + 0x108#64) ↦₆₄ 33#64) ∗ (dataPtr ↦ₛ pendBytes) ∗ A.live dataPtr 33 1 ∗
          ((p + 0x110#64) ↦₃₂ opkTag) ∗ ((p + 0x114#64) ↦₃₂ opkId) ∗
          ((p + 0x118#64) ↦₆₄ 0#64) ∗ ((p + 0x120#64) ↦₃₂ spkId) ∗
          ((p + 0x124#64) ↦₃₂ padVal) ∗
          ((p + 0x128#64) ↦₆₄ cap) ∗ ((p + 0x140#64) ↦₃₂ kpkId) ∗ Rest ⊢
            let pg : TailVecGhost :=
              { vec := ⟨33#64, dataPtr, pendBytes⟩
                tail := unpack32 opkTag ++ unpack32 opkId ++ unpack64 0#64 ++
                          unpack32 spkId ++ unpack32 padVal }
            let kg' : TailVecGhost :=
              { vec := kg.vec, tail := unpack32 kpkId ++ unpack32 w1 }
            sessionStateAt A p { sg with pending := some pg, kyber := some kg' }
              ss.setUnacknowledgedPreKeyMessage := by
  intro R m hm
  dsimp only [sessionStateAt] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  obtain ⟨hpure, hm⟩ := hm
  rw [hpend0, hkyb0] at hm
  dsimp only [optTailVecAt, LibsignalSessionRepr.vecGhostAt] at hm
  rw [vecU8At_eq_header_sep_buf A (p + 0x128#64) kg.vec.cap kg.vec.ptr kg.vec.bytes] at hm
  unfold vecHeader at hm
  have ha130 : p + 0x128#64 + 8#64 = p + 0x130#64 := by bv_omega
  have ha138 : p + 0x128#64 + 16#64 = p + 0x138#64 := by bv_omega
  have ha140 : p + 0x128#64 + 24#64 = p + 0x140#64 := by bv_omega
  have ha100 : p + 0xf8#64 + 8#64 = p + 0x100#64 := by bv_omega
  have hm_kyb : m ⊨ (⌜kg.tail.length = 8⌝ ∗ vecU8Buf A kg.vec.cap kg.vec.ptr kg.vec.bytes ∗
      ((p + 0x140#64) ↦ₛ kg.tail)) ∗
      (((p + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (p + 0x100#64) 40 ∗
       ((p + 0x128#64) ↦₆₄ kg.vec.cap) ∗ ((p + 0x130#64) ↦₆₄ kg.vec.ptr) ∗
       ((p + 0x138#64) ↦₆₄ BitVec.ofNat 64 kg.vec.bytes.length) ∗
       vecGhostAt A sg.localIk p ∗ vecGhostAt A sg.remoteIk (p + 0x18#64) ∗
       vecU8At A (p + 0x30#64) sg.root.cap sg.root.ptr (keyToBytes32 ss.rootKey) ∗
       vecAt A 104 8 (chainAt A) (p + 0x48#64) sg.chainsCap sg.chainsPtr
         (sg.chains.zip ss.receiverChains) ∗
       vecGhostAt A sg.alice (p + 0x60#64) ∗
       vecU8At A (p + 0x78#64) sg.pq.cap sg.pq.ptr ss.pqRatchetState ∗
       optSenderChainAt A (p + 0x90#64) sg.sender ss.senderChain ∗
       ((p + 0x148#64) ↦₃₂ ss.sessionVersion) ∗
       ((p + 0x14c#64) ↦₃₂ ss.previousCounter) ∗
       ((p + 0x150#64) ↦ₛ sg.regIds) ∗ R) := by
    rw [ha130, ha138, ha140, ha100] at hm
    exact sat_eq (by dsimp only [LibsignalSessionRepr.vecGhostAt]; ac_rfl) hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_kyb
  obtain ⟨htail8, hm_kyb⟩ := hm_kyb
  have hcapLt : kg.vec.cap.toNat < 2 ^ 63 := by
    have hbuf : m ⊨ vecU8Buf A kg.vec.cap kg.vec.ptr kg.vec.bytes ∗
        (((p + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (p + 0x100#64) 40 ∗
         ((p + 0x128#64) ↦₆₄ kg.vec.cap) ∗ ((p + 0x130#64) ↦₆₄ kg.vec.ptr) ∗
         ((p + 0x138#64) ↦₆₄ BitVec.ofNat 64 kg.vec.bytes.length) ∗
         ((p + 0x140#64) ↦ₛ kg.tail) ∗
         vecGhostAt A sg.localIk p ∗ vecGhostAt A sg.remoteIk (p + 0x18#64) ∗
         vecU8At A (p + 0x30#64) sg.root.cap sg.root.ptr (keyToBytes32 ss.rootKey) ∗
         vecAt A 104 8 (chainAt A) (p + 0x48#64) sg.chainsCap sg.chainsPtr
           (sg.chains.zip ss.receiverChains) ∗
         vecGhostAt A sg.alice (p + 0x60#64) ∗
         vecU8At A (p + 0x78#64) sg.pq.cap sg.pq.ptr ss.pqRatchetState ∗
         optSenderChainAt A (p + 0x90#64) sg.sender ss.senderChain ∗
         ((p + 0x148#64) ↦₃₂ ss.sessionVersion) ∗
         ((p + 0x14c#64) ↦₃₂ ss.previousCounter) ∗
         ((p + 0x150#64) ↦ₛ sg.regIds) ∗ R) :=
      sat_eq (by dsimp only [LibsignalSessionRepr.vecGhostAt]; ac_rfl) hm_kyb
    dsimp only [vecU8Buf] at hbuf
    rw [sepConj_assoc, satisfies_pure_sepConj] at hbuf
    exact hbuf.1.2.1
  obtain ⟨w0, hw0⟩ := pointsToBytes_4_exists_32 (bs := kg.tail.take 4) (by simp [htail8])
  obtain ⟨w1, hw1⟩ := pointsToBytes_4_exists_32 (bs := kg.tail.drop 4) (by simp [htail8])
  have htailSplit : ((p + 0x140#64) ↦ₛ kg.tail) =
      ((p + 0x140#64) ↦₃₂ w0) ∗ ((p + 0x144#64) ↦₃₂ w1) := by
    conv_lhs => rw [← List.take_append_drop 4 kg.tail]
    rw [pointsToBytes_append, show (kg.tail.take 4).length = 4 by simp [htail8],
      show p + 0x140#64 + 4#64 = p + 0x144#64 by bv_omega, hw0, hw1]
  rw [htailSplit] at hm_kyb
  let Rest : SepProp :=
    vecU8Buf A kg.vec.cap kg.vec.ptr kg.vec.bytes ∗
    ((p + 0x130#64) ↦₆₄ kg.vec.ptr) ∗
    ((p + 0x138#64) ↦₆₄ BitVec.ofNat 64 kg.vec.bytes.length) ∗
    ((p + 0x144#64) ↦₃₂ w1) ∗
    vecGhostAt A sg.localIk p ∗ vecGhostAt A sg.remoteIk (p + 0x18#64) ∗
    vecU8At A (p + 0x30#64) sg.root.cap sg.root.ptr (keyToBytes32 ss.rootKey) ∗
    vecAt A 104 8 (chainAt A) (p + 0x48#64) sg.chainsCap sg.chainsPtr
      (sg.chains.zip ss.receiverChains) ∗
    vecGhostAt A sg.alice (p + 0x60#64) ∗
    vecU8At A (p + 0x78#64) sg.pq.cap sg.pq.ptr ss.pqRatchetState ∗
    optSenderChainAt A (p + 0x90#64) sg.sender ss.senderChain ∗
    ((p + 0x148#64) ↦₃₂ ss.sessionVersion) ∗
    ((p + 0x14c#64) ↦₃₂ ss.previousCounter) ∗
    ((p + 0x150#64) ↦ₛ sg.regIds)
  refine ⟨kg.vec.cap, w0, w1, Rest, rfl, by bv_omega, ?_, ?_⟩
  · dsimp only [Rest, noneCap, LibsignalSessionRepr.vecGhostAt] at hm_kyb ⊢
    exact sat_eq (by ac_rfl) hm_kyb
  · intro opkTag opkId spkId kpkId padVal dataPtr hdataNonNull
    let pg : TailVecGhost :=
      { vec := ⟨33#64, dataPtr, pendBytes⟩
        tail := unpack32 opkTag ++ unpack32 opkId ++ unpack64 0#64 ++
                  unpack32 spkId ++ unpack32 padVal }
    let kg' : TailVecGhost :=
      { vec := kg.vec, tail := unpack32 kpkId ++ unpack32 w1 }
    change _ ⊢ sessionStateAt A p { sg with pending := some pg, kyber := some kg' }
      ss.setUnacknowledgedPreKeyMessage
    dsimp only [sessionStateAt, SessionState.setUnacknowledgedPreKeyMessage,
      optTailVecAt, Rest]
    have hpure' :
        PublicKey.deserialize sg.localIk.bytes = .ok ss.localIdentity.publicKey ∧
        (match ss.remoteIdentity with
         | none => sg.remoteIk.bytes = []
         | some ik => PublicKey.deserialize sg.remoteIk.bytes = .ok ik.publicKey) ∧
        sg.chains.length = ss.receiverChains.length ∧
        (some pg).isSome = true ∧ sg.regIds.length = 8 ∧
        sg.localIk.bytes.length = 33 ∧
        (ss.remoteIdentity.isSome → sg.remoteIk.bytes.length = 33) :=
      ⟨hpure.1, hpure.2.1, hpure.2.2.1, rfl, hpure.2.2.2.2.1, hpure.2.2.2.2.2.1,
       hpure.2.2.2.2.2.2⟩
    refine Entails.pure_right hpure' ?_
    have hpgLen : pg.tail.length = 48 - 24 := by dsimp only [pg]; simp
    have hkgLen : kg'.tail.length = 32 - 24 := by dsimp only [kg']; simp
    rw [pure_sepConj_of_true hpgLen, pure_sepConj_of_true hkgLen]
    have hpgVec := Pqxdh.TopLevel.vecU8At_of_header_live_pointsToBytes A (p + 0xf8#64) 33#64
      dataPtr pendBytes 33 rfl (by decide) (by decide) hpendLen hdataNonNull
    have ha108 : p + 0xf8#64 + 16#64 = p + 0x108#64 := by bv_omega
    rw [ha100, ha108] at hpgVec
    dsimp only [LibsignalSessionRepr.vecGhostAt]
    rw [vecU8At_eq_header_sep_buf A (p + 0x128#64) kg.vec.cap kg.vec.ptr kg.vec.bytes]
    unfold vecHeader
    rw [ha130, ha138]
    have hpgTail :
        ((p + 0x110#64) ↦₃₂ opkTag) ∗ ((p + 0x114#64) ↦₃₂ opkId) ∗
        ((p + 0x118#64) ↦₆₄ 0#64) ∗ ((p + 0x120#64) ↦₃₂ spkId) ∗
        ((p + 0x124#64) ↦₃₂ padVal) = ((p + 0xf8#64 + 24#64) ↦ₛ pg.tail) := by
      dsimp only [pg]
      have a0 : p + 0xf8#64 + 24#64 = p + 0x110#64 := by bv_omega
      have a1 : p + 0x110#64 + 4#64 = p + 0x114#64 := by bv_omega
      have a2 : p + 0x114#64 + 4#64 = p + 0x118#64 := by bv_omega
      have a3 : p + 0x118#64 + 8#64 = p + 0x120#64 := by bv_omega
      have a4 : p + 0x120#64 + 4#64 = p + 0x124#64 := by bv_omega
      rw [a0, List.append_assoc, List.append_assoc, List.append_assoc,
        pointsToBytes_append, unpack32_length, a1,
        pointsToBytes_append, unpack32_length, a2,
        pointsToBytes_append, unpack64_length, a3,
        pointsToBytes_append, unpack32_length, a4,
        ← pointsTo32_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes,
        ← pointsTo64_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes,
        ← pointsTo32_eq_pointsToBytes]
    have hkgTail :
        ((p + 0x140#64) ↦₃₂ kpkId) ∗ ((p + 0x144#64) ↦₃₂ w1) =
          ((p + 0x128#64 + 24#64) ↦ₛ kg'.tail) := by
      dsimp only [kg']
      have b1 : p + 0x140#64 + 4#64 = p + 0x144#64 := by bv_omega
      rw [ha140, pointsToBytes_append, unpack32_length, b1,
        ← pointsTo32_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes]
    have hstep1 :
        (((p + 0xf8#64) ↦₆₄ 33#64) ∗ ((p + 0x100#64) ↦₆₄ dataPtr) ∗
          ((p + 0x108#64) ↦₆₄ 33#64) ∗ (dataPtr ↦ₛ pendBytes) ∗ A.live dataPtr 33 1 ∗
          ((p + 0x110#64) ↦₃₂ opkTag) ∗ ((p + 0x114#64) ↦₃₂ opkId) ∗
          ((p + 0x118#64) ↦₆₄ 0#64) ∗ ((p + 0x120#64) ↦₃₂ spkId) ∗
          ((p + 0x124#64) ↦₃₂ padVal) ∗
          ((p + 0x128#64) ↦₆₄ kg.vec.cap) ∗ ((p + 0x140#64) ↦₃₂ kpkId) ∗
          (vecU8Buf A kg.vec.cap kg.vec.ptr kg.vec.bytes ∗
           ((p + 0x130#64) ↦₆₄ kg.vec.ptr) ∗
           ((p + 0x138#64) ↦₆₄ BitVec.ofNat 64 kg.vec.bytes.length) ∗
           ((p + 0x144#64) ↦₃₂ w1) ∗
           vecGhostAt A sg.localIk p ∗ vecGhostAt A sg.remoteIk (p + 0x18#64) ∗
           vecU8At A (p + 0x30#64) sg.root.cap sg.root.ptr (keyToBytes32 ss.rootKey) ∗
           vecAt A 104 8 (chainAt A) (p + 0x48#64) sg.chainsCap sg.chainsPtr
             (sg.chains.zip ss.receiverChains) ∗
           vecGhostAt A sg.alice (p + 0x60#64) ∗
           vecU8At A (p + 0x78#64) sg.pq.cap sg.pq.ptr ss.pqRatchetState ∗
           optSenderChainAt A (p + 0x90#64) sg.sender ss.senderChain ∗
           ((p + 0x148#64) ↦₃₂ ss.sessionVersion) ∗
           ((p + 0x14c#64) ↦₃₂ ss.previousCounter) ∗
           ((p + 0x150#64) ↦ₛ sg.regIds))) =
        ((((p + 0xf8#64) ↦₆₄ 33#64) ∗ ((p + 0x100#64) ↦₆₄ dataPtr) ∗
          ((p + 0x108#64) ↦₆₄ 33#64) ∗ (dataPtr ↦ₛ pendBytes) ∗ A.live dataPtr 33 1) ∗
          ((p + 0xf8#64 + 24#64) ↦ₛ pg.tail) ∗
          ((p + 0x128#64 + 24#64) ↦ₛ kg'.tail) ∗
          (((p + 0x128#64) ↦₆₄ kg.vec.cap) ∗
           ((p + 0x130#64) ↦₆₄ kg.vec.ptr) ∗
           ((p + 0x138#64) ↦₆₄ BitVec.ofNat 64 kg.vec.bytes.length) ∗
           vecU8Buf A kg.vec.cap kg.vec.ptr kg.vec.bytes ∗
           vecGhostAt A sg.localIk p ∗ vecGhostAt A sg.remoteIk (p + 0x18#64) ∗
           vecU8At A (p + 0x30#64) sg.root.cap sg.root.ptr (keyToBytes32 ss.rootKey) ∗
           vecAt A 104 8 (chainAt A) (p + 0x48#64) sg.chainsCap sg.chainsPtr
             (sg.chains.zip ss.receiverChains) ∗
           vecGhostAt A sg.alice (p + 0x60#64) ∗
           vecU8At A (p + 0x78#64) sg.pq.cap sg.pq.ptr ss.pqRatchetState ∗
           optSenderChainAt A (p + 0x90#64) sg.sender ss.senderChain ∗
           ((p + 0x148#64) ↦₃₂ ss.sessionVersion) ∗
           ((p + 0x14c#64) ↦₃₂ ss.previousCounter) ∗
           ((p + 0x150#64) ↦ₛ sg.regIds))) := by
      dsimp only [LibsignalSessionRepr.vecGhostAt]
      rw [← hpgTail, ← hkgTail]
      ac_rfl
    dsimp only [LibsignalSessionRepr.vecGhostAt] at hstep1
    rw [hstep1]
    exact Entails.trans
      (sepConj_mono_left hpgVec)
      (entails_ac (by dsimp only [LibsignalSessionRepr.vecGhostAt, pg, kg']; ac_rfl))

/-- Lens updating the 8-byte `regIds` field at `p + 0x150` (`remoteRegId`) and `p + 0x154`
(`localRegId`) of `sessionStateAt A p sg ss`. -/
theorem sessionState_regIds_lens (A : RustAlloc) (p : BitVec 64)
    (sg : SessionGhost) (ss : SessionState (List (BitVec 8))) :
    ∀ R (m : Memory), m ⊨ sessionStateAt A p sg ss ∗ R →
      ∃ (oldRem oldLoc : BitVec 32) (Rest : SepProp),
        (m ⊨ ((p + 0x150#64) ↦₃₂ oldRem) ∗ ((p + 0x154#64) ↦₃₂ oldLoc) ∗ (Rest ∗ R)) ∧
        ∀ (remId locId : BitVec 32),
          ((p + 0x150#64) ↦₃₂ remId) ∗ ((p + 0x154#64) ↦₃₂ locId) ∗ Rest ⊢
            sessionStateAt A p { sg with regIds := unpack32 remId ++ unpack32 locId } ss := by
  intro R m hm
  dsimp only [sessionStateAt] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  obtain ⟨hpure, hm⟩ := hm
  have hlen8 : sg.regIds.length = 8 := hpure.2.2.2.2.1
  obtain ⟨oldRem, hr0⟩ := pointsToBytes_4_exists_32 (bs := sg.regIds.take 4) (by simp [hlen8])
  obtain ⟨oldLoc, hr1⟩ := pointsToBytes_4_exists_32 (bs := sg.regIds.drop 4) (by simp [hlen8])
  have hsplit : ((p + 0x150#64) ↦ₛ sg.regIds) =
      ((p + 0x150#64) ↦₃₂ oldRem) ∗ ((p + 0x154#64) ↦₃₂ oldLoc) := by
    conv_lhs => rw [← List.take_append_drop 4 sg.regIds]
    rw [pointsToBytes_append, show (sg.regIds.take 4).length = 4 by simp [hlen8],
      show p + 0x150#64 + 4#64 = p + 0x154#64 by bv_omega, hr0, hr1]
  let Rest : SepProp :=
    vecGhostAt A sg.localIk p ∗ vecGhostAt A sg.remoteIk (p + 0x18#64) ∗
    vecU8At A (p + 0x30#64) sg.root.cap sg.root.ptr (keyToBytes32 ss.rootKey) ∗
    vecAt A 104 8 (chainAt A) (p + 0x48#64) sg.chainsCap sg.chainsPtr
      (sg.chains.zip ss.receiverChains) ∗
    vecGhostAt A sg.alice (p + 0x60#64) ∗
    vecU8At A (p + 0x78#64) sg.pq.cap sg.pq.ptr ss.pqRatchetState ∗
    optSenderChainAt A (p + 0x90#64) sg.sender ss.senderChain ∗
    optTailVecAt A 48 (p + 0xf8#64) sg.pending ∗
    optTailVecAt A 32 (p + 0x128#64) sg.kyber ∗
    ((p + 0x148#64) ↦₃₂ ss.sessionVersion) ∗
    ((p + 0x14c#64) ↦₃₂ ss.previousCounter)
  refine ⟨oldRem, oldLoc, Rest, ?_, ?_⟩
  · rw [hsplit] at hm
    dsimp only [Rest]
    exact sat_eq (by ac_rfl) hm
  · intro remId locId
    dsimp only [sessionStateAt, Rest]
    have hpure' :
        PublicKey.deserialize sg.localIk.bytes = .ok ss.localIdentity.publicKey ∧
        (match ss.remoteIdentity with
         | none => sg.remoteIk.bytes = []
         | some ik => PublicKey.deserialize sg.remoteIk.bytes = .ok ik.publicKey) ∧
        sg.chains.length = ss.receiverChains.length ∧
        sg.pending.isSome = ss.pendingPreKey ∧
        (unpack32 remId ++ unpack32 locId).length = 8 ∧
        sg.localIk.bytes.length = 33 ∧
        (ss.remoteIdentity.isSome → sg.remoteIk.bytes.length = 33) :=
      ⟨hpure.1, hpure.2.1, hpure.2.2.1, hpure.2.2.2.1, by simp, hpure.2.2.2.2.2.1,
       hpure.2.2.2.2.2.2⟩
    refine Entails.pure_right hpure' ?_
    have hmerge :
        ((p + 0x150#64) ↦₃₂ remId) ∗ ((p + 0x154#64) ↦₃₂ locId) =
          ((p + 0x150#64) ↦ₛ (unpack32 remId ++ unpack32 locId)) := by
      rw [pointsToBytes_append, unpack32_length,
        show p + 0x150#64 + 4#64 = p + 0x154#64 by bv_omega,
        ← pointsTo32_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes]
    exact Entails.trans
      (entails_ac (by rw [← sepConj_assoc, hmerge]; ac_rfl))
      (Entails.refl _)

/-! ## `SessionRecord` Promotion and `initDef` Agreement -/

theorem emptyRecordVecAt_intro (A : RustAlloc) (r : BitVec 64) :
    (r ↦₆₄ 0#64) ∗ ((r + 8#64) ↦₆₄ 8#64) ∗ ((r + 16#64) ↦₆₄ 0#64) ⊢
      vecAt A 24 8 (fun (_ : Unit) _ => emp) r 0#64 8#64 [] := by
  unfold vecAt vecHeader
  dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat]
  refine Entails.trans (Entails.of_eq (sepConj_emp _).symm) ?_
  exact sepConj_mono_right (Pqxdh.TopLevel.vecBuf_empty_0_8_init A 24 (fun (_ : Unit) _ => emp))

/-- Folds the promoted `SessionState` into `sessionRecordAt`, bounds `(Record.encodeRecord ⟨some sess⟩).length < 2 ^ 32`,
and establishes `initDef` agreement on the accepted state. -/
theorem sessionRecord_promote_accept_ext
    {A : RustAlloc} {P : PEParams} {X : UnreachedPqxdhPrimitives}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    {opkId reg : BitVec 32}
    {sg : SessionGhost} {ss : SessionState (List (BitVec 8))}
    {dataPtr : BitVec 64} {padVal w1 : BitVec 32} {kg : TailVecGhost}
    (fsp : BitVec 64)
    (hbe : bundleEOf? x.bundle = some be)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd x.F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd x.F = .ok reg)
    (hopkId : ∀ p, x.bundle.opk = some p → opkId = p.1)
    (hkeys : SignalPqxdh.Model.initiateKeys (modelPrims X P)
      (initiateInput P ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)) = some (dk, hdr))
    (hinitSess : initializeInitiatorSession P.C (pqxdhSpqrSession P)
      ⟨(keyPairOf P.C kp.privateKey.bytes).publicKey⟩ ⟨⟨be.idPub⟩⟩ ⟨be.spkPub⟩
      (HKDF.bytesToKey32 (ofU8 dk.rootKey)) (HKDF.bytesToKey32 (ofU8 dk.chainKey))
      (HKDF.bytesToKey32 (ofU8 dk.pqrKey))
      (HKDF.bytesToKey32 (((padCoins x.coins).toList.drop 160).take 32)) = .ok ss)
    (hpqLen : ss.pqRatchetState.length ≤ 1208)
    (halice : sg.alice.bytes = (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize)
    (hkgBytes : kg.vec.bytes = 0x08#8 :: ofU8 hdr.kemCt)
    (hkemLen : (0x08#8 :: ofU8 hdr.kemCt).length = 1569)
    (hkyberKey : kyberKey (u8Vec 1568 hdr.kemCt) = 0x08#8 :: ofU8 hdr.kemCt) :
    let opkFlag : BitVec 32 := if x.bundle.opk.isSome then 1#32 else 0#32
    let basePk : PublicKey := ⟨u8Vec 32 hdr.ekAPk⟩
    let pg : TailVecGhost :=
      { vec := ⟨33#64, dataPtr, basePk.serialize⟩
        tail := unpack32 opkFlag ++ unpack32 opkId ++ unpack64 0#64 ++
                  unpack32 x.bundle.spkId ++ unpack32 padVal }
    let kg' : TailVecGhost := { vec := kg.vec, tail := unpack32 x.bundle.kpkId ++ unpack32 w1 }
    let sg₂ : SessionGhost :=
      { sg with
        pending := some pg
        kyber := some kg'
        regIds := unpack32 x.bundle.regId ++ unpack32 reg }
    let xOut : RecordExtras :=
      initiatorRecordExtras ⟨kp.privateKey.bytes, reg⟩ be basePk (u8Vec 1568 hdr.kemCt)
    let gs : GhostState (List (BitVec 8)) :=
      ⟨initParty x.peer.val, ss.setUnacknowledgedPreKeyMessage, 0, [0]⟩
    let sess : Session (List (BitVec 8)) := RecordX.sessionOfX (fun _ => xOut) gs
    ((((fsp + 0x128#64) ↦₆₄ 0#64) ∗ ((fsp + 0x130#64) ↦₆₄ 8#64) ∗
      ((fsp + 0x138#64) ↦₆₄ 0#64) ∗
      sessionStateAt A (fsp + 0x140#64) sg₂ ss.setUnacknowledgedPreKeyMessage) ⊢
        sessionRecordAt A (fsp + 0x128#64) ⟨0#64, 8#64, some sg₂⟩ ⟨some sess⟩) ∧
      (Record.encodeRecord ⟨some sess⟩).length < 2 ^ 32 ∧
      initDef X P x.F x.peer.val x.me.val x.bundle x.coins =
        some (some (initAcceptStoresGhost x.F x.peer.val x.bundle.idKey
          (Record.encodeRecord ⟨some sess⟩), ())) := by
  intro opkFlag basePk pg kg' sg₂ xOut gs sess
  obtain ⟨hregB, hspkB, hkpkB, _, _, hopkMap⟩ := bundleEOf_fields hbe
  refine ⟨?_, ?_, ?_⟩
  ·
    dsimp only [sessionRecordAt, sessionStateReprAt]
    have ha140 : fsp + 0x128#64 + 0x18#64 = fsp + 0x140#64 := by bv_omega
    rw [ha140]
    have hsessState : sess.state = ss.setUnacknowledgedPreKeyMessage := rfl
    rw [hsessState]
    have hpendRel : PendingRel (some pg) sess.pendingPreKey := by
      dsimp only [PendingRel, sess, RecordX.sessionOfX, xOut, initiatorRecordExtras, pg]
      refine ⟨Pqxdh.TopLevel.deserialize_serialize_pk_init basePk, ?_, ?_, ?_, by
        dsimp only [PublicKey.serialize]; simp⟩
      · cases hopk : x.bundle.opk with
        | none =>
          have hbeNone : be.opk.map Prod.fst = none := by rw [hopkMap, hopk]; rfl
          rw [hbeNone]
          dsimp only [OptU32Rel, opkFlag]
          rw [hopk]
          simp [unpack32, unpack64]
        | some pr =>
          have hbeSome : be.opk.map Prod.fst = some pr.1 := by rw [hopkMap, hopk]; rfl
          have hid : opkId = pr.1 := hopkId pr hopk
          rw [hbeSome, ← hid]
          dsimp only [OptU32Rel, opkFlag]
          rw [hopk, leBytes_4_eq_unpack32]
          simp [unpack32, unpack64]
      · rw [leBytes_8_zero_eq_unpack64]
        simp [unpack32, unpack64]
      · rw [hspkB, leBytes_4_eq_unpack32]
        simp [unpack32, unpack64]
    have hkybRel : KyberRel (some kg') sess.pendingKyberPreKey := by
      dsimp only [KyberRel, sess, RecordX.sessionOfX, xOut, initiatorRecordExtras, kg']
      refine ⟨hkgBytes.trans hkyberKey.symm, ?_⟩
      rw [hkpkB, leBytes_4_eq_unpack32]
      simp [unpack32]
    have hpureSess :
        PendingRel sg₂.pending sess.pendingPreKey ∧
        KyberRel sg₂.kyber sess.pendingKyberPreKey ∧
        sg₂.alice.bytes = sess.aliceBaseKey ∧
        sg₂.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
        (sg₂.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat := by
      refine ⟨hpendRel, hkybRel, halice, ?_, ?_⟩
      · dsimp only [sg₂, sess, RecordX.sessionOfX, xOut, initiatorRecordExtras]
        rw [hregB, leBytes_4_eq_unpack32]
        simp [unpack32]
      · dsimp only [sg₂, sess, RecordX.sessionOfX, xOut, initiatorRecordExtras]
        rw [leBytes_4_eq_unpack32]
        simp [unpack32]
    rw [pure_sepConj_of_true hpureSess]
    have ha130 : fsp + 0x128#64 + 8#64 = fsp + 0x130#64 := by bv_omega
    have ha138 : fsp + 0x128#64 + 16#64 = fsp + 0x138#64 := by bv_omega
    have hempRec := emptyRecordVecAt_intro A (fsp + 0x128#64)
    rw [ha130, ha138] at hempRec
    exact Entails.trans
      (entails_ac (by ac_rfl :
        (((fsp + 0x128#64) ↦₆₄ 0#64) ∗ ((fsp + 0x130#64) ↦₆₄ 8#64) ∗
          ((fsp + 0x138#64) ↦₆₄ 0#64) ∗
          sessionStateAt A (fsp + 0x140#64) sg₂ ss.setUnacknowledgedPreKeyMessage) =
        (((fsp + 0x128#64) ↦₆₄ 0#64) ∗ ((fsp + 0x130#64) ↦₆₄ 8#64) ∗
          ((fsp + 0x138#64) ↦₆₄ 0#64)) ∗
          sessionStateAt A (fsp + 0x140#64) sg₂ ss.setUnacknowledgedPreKeyMessage))
      (sepConj_mono_left hempRec)
  ·
    dsimp only [initializeInitiatorSession, Bind.bind, Except.bind] at hinitSess
    cases hrc : rootCreateChain P.C (HKDF.bytesToKey32 (ofU8 dk.rootKey)) ⟨be.spkPub⟩
      (KeyPair.generate P.C (HKDF.bytesToKey32 (((padCoins x.coins).toList.drop 160).take 32))).privateKey with
    | error err => simp [hrc] at hinitSess
    | ok pair =>
      simp only [hrc, Pure.pure, Except.pure, Except.ok.injEq] at hinitSess
      subst hinitSess
      have hsessEq : sess = Pqxdh.TopLevel.aliceInitiatedSession
          ⟨(keyPairOf P.C kp.privateKey.bytes).publicKey⟩ ⟨⟨be.idPub⟩⟩ ⟨be.spkPub⟩ basePk
          pair.1 (HKDF.bytesToKey32 (ofU8 dk.chainKey))
          (KeyPair.generate P.C (HKDF.bytesToKey32 (((padCoins x.coins).toList.drop 160).take 32)))
          pair.2 (be.opk.map Prod.fst) be.spkId be.kpkId be.regId reg
          (0x08#8 :: ofU8 hdr.kemCt)
          ((pqxdhSpqrSession P).init .a2b (HKDF.bytesToKey32 (ofU8 dk.pqrKey))) := by
        simp [sess, RecordX.sessionOfX, xOut, initiatorRecordExtras, gs,
          Pqxdh.TopLevel.aliceInitiatedSession, Pqxdh.TopLevel.aliceInitiatedState,
          SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
          SessionState.setUnacknowledgedPreKeyMessage, currentVersion, maxReceiverChains,
          hkyberKey]
      rw [hsessEq]
      exact Pqxdh.TopLevel.encodeRecord_aliceInitiated_length_lt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        hkemLen hpqLen
  ·
    have hkeysReg : SignalPqxdh.Model.initiateKeys (modelPrims X P)
        (initiateInput P ⟨kp.privateKey.bytes, reg⟩ be (padCoins x.coins)) =
        some (dk, hdr) := hkeys
    have hstateEq : initiateState X P (initParty x.peer.val)
        ⟨kp.privateKey.bytes, reg⟩ be (padCoins x.coins) = some (xOut, gs) := by
      simp only [initiateState, hkeysReg, hinitSess]
      rfl
    have hencEq : encodeRecordUnderExtras (fun _ => xOut) gs = Record.encodeRecord ⟨some sess⟩ :=
      Pqxdh.TopLevel.encodeRecordX_initiateExtras_eq _ _ _ _ _
    dsimp only [initDef]
    rw [hbe, htrusted, hkp, hreg]
    dsimp only
    rw [hstateEq]
    dsimp only [initAcceptStoresGhost]
    rw [hencEq]

theorem sessionRecord_promote_accept
    {A : RustAlloc} {W : CliHooks} {X : UnreachedPqxdhPrimitives}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    {opkId reg : BitVec 32}
    {sg : SessionGhost} {ss : SessionState (List (BitVec 8))}
    {dataPtr : BitVec 64} {padVal w1 : BitVec 32} {kg : TailVecGhost}
    (fsp : BitVec 64)
    (hbe : bundleEOf? x.bundle = some be)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd x.F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd x.F = .ok reg)
    (hopkId : ∀ p, x.bundle.opk = some p → opkId = p.1)
    (hkeys : SignalPqxdh.Model.initiateKeys (modelPrims X ⟨W.C, W.Q⟩)
      (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)) = some (dk, hdr))
    (hinitSess : initializeInitiatorSession W.C (pqxdhSpqrSession ⟨W.C, W.Q⟩)
      ⟨(keyPairOf W.C kp.privateKey.bytes).publicKey⟩ ⟨⟨be.idPub⟩⟩ ⟨be.spkPub⟩
      (HKDF.bytesToKey32 (ofU8 dk.rootKey)) (HKDF.bytesToKey32 (ofU8 dk.chainKey))
      (HKDF.bytesToKey32 (ofU8 dk.pqrKey))
      (HKDF.bytesToKey32 (((padCoins x.coins).toList.drop 160).take 32)) = .ok ss)
    (hpqLen : ss.pqRatchetState.length ≤ 1208)
    (halice : sg.alice.bytes = (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize)
    (hkgBytes : kg.vec.bytes = 0x08#8 :: ofU8 hdr.kemCt)
    (hkemLen : (0x08#8 :: ofU8 hdr.kemCt).length = 1569)
    (hkyberKey : kyberKey (u8Vec 1568 hdr.kemCt) = 0x08#8 :: ofU8 hdr.kemCt) :
    let opkFlag : BitVec 32 := if x.bundle.opk.isSome then 1#32 else 0#32
    let basePk : PublicKey := ⟨u8Vec 32 hdr.ekAPk⟩
    let pg : TailVecGhost :=
      { vec := ⟨33#64, dataPtr, basePk.serialize⟩
        tail := unpack32 opkFlag ++ unpack32 opkId ++ unpack64 0#64 ++
                  unpack32 x.bundle.spkId ++ unpack32 padVal }
    let kg' : TailVecGhost := { vec := kg.vec, tail := unpack32 x.bundle.kpkId ++ unpack32 w1 }
    let sg₂ : SessionGhost :=
      { sg with
        pending := some pg
        kyber := some kg'
        regIds := unpack32 x.bundle.regId ++ unpack32 reg }
    let xOut : RecordExtras :=
      initiatorRecordExtras ⟨kp.privateKey.bytes, reg⟩ be basePk (u8Vec 1568 hdr.kemCt)
    let gs : GhostState (List (BitVec 8)) :=
      ⟨initParty x.peer.val, ss.setUnacknowledgedPreKeyMessage, 0, [0]⟩
    let sess : Session (List (BitVec 8)) := RecordX.sessionOfX (fun _ => xOut) gs
    ((((fsp + 0x128#64) ↦₆₄ 0#64) ∗ ((fsp + 0x130#64) ↦₆₄ 8#64) ∗
      ((fsp + 0x138#64) ↦₆₄ 0#64) ∗
      sessionStateAt A (fsp + 0x140#64) sg₂ ss.setUnacknowledgedPreKeyMessage) ⊢
        sessionRecordAt A (fsp + 0x128#64) ⟨0#64, 8#64, some sg₂⟩ ⟨some sess⟩) ∧
      (Record.encodeRecord ⟨some sess⟩).length < 2 ^ 32 ∧
      initDef X ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val x.bundle x.coins =
        some (some (initAcceptStoresGhost x.F x.peer.val x.bundle.idKey
          (Record.encodeRecord ⟨some sess⟩), ())) :=
  sessionRecord_promote_accept_ext (P := ⟨W.C, W.Q⟩) fsp hbe htrusted hkp hreg hopkId
    hkeys hinitSess hpqLen halice hkgBytes hkemLen hkyberKey

/-- Unpack `sessionRecordAt A (fsp + 0x128#64) ⟨0#64, 8#64, some sg₂⟩ ⟨some sess⟩` after
`store_session` for inline cleanup (`+0x1830..+0x18c4`): exposes the 24-byte empty `Vec` header
`(0, 8, 0)` and the first 64-bit word `sg₂.localIk.cap` at `fsp + 0x140#64` with
`sg₂.localIk.cap + 1#64 ≠ 0#64`, together with re-folding back into
`sessionStateAt A (fsp + 0x140#64) sg₂ sess.state` right before `drop_glue<SessionStructure>`. -/
theorem sessionRecord_unpack_drop (A : RustAlloc) (fsp : BitVec 64)
    (sg₂ : SessionGhost) (sess : Session (List (BitVec 8))) :
    ∀ R (m : Memory),
      m ⊨ sessionRecordAt A (fsp + 0x128#64) ⟨0#64, 8#64, some sg₂⟩ ⟨some sess⟩ ∗ R →
      ∃ (cap : BitVec 64) (Rest : SepProp),
        cap + 1#64 ≠ 0#64 ∧
        (m ⊨ ((fsp + 0x128#64) ↦₆₄ 0#64) ∗ ((fsp + 0x130#64) ↦₆₄ 8#64) ∗
              ((fsp + 0x138#64) ↦₆₄ 0#64) ∗ ((fsp + 0x140#64) ↦₆₄ cap) ∗ (Rest ∗ R)) ∧
        (((fsp + 0x140#64) ↦₆₄ cap) ∗ Rest ⊢
          sessionStateAt A (fsp + 0x140#64) sg₂ sess.state) := by
  intro R m hm
  dsimp only [sessionRecordAt, vecAt, vecBuf, sessionStateReprAt] at hm
  unfold vecHeader at hm
  have ha130 : fsp + 0x128#64 + 8#64 = fsp + 0x130#64 := by bv_omega
  have ha138 : fsp + 0x128#64 + 16#64 = fsp + 0x138#64 := by bv_omega
  have ha140 : fsp + 0x128#64 + 0x18#64 = fsp + 0x140#64 := by bv_omega
  have hite :
      (if (0#64 : BitVec 64) = 0 then emp
       else A.live (8#64) ((0#64).toNat * 24) 8 ∗
         arrayAt (fun (_ : Unit) _ => emp) 24 8#64 [] ∗
         memRegion (8#64 + BitVec.ofNat 64 (([] : List Unit).length * 24))
           (((0#64).toNat - ([] : List Unit).length) * 24)) = emp := rfl
  rw [ha130, ha138, ha140, hite] at hm
  have hm1 : m ⊨ ⌜([] : List Unit).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0⌝ ∗
      (⌜PendingRel sg₂.pending sess.pendingPreKey ∧
        KyberRel sg₂.kyber sess.pendingKyberPreKey ∧
        sg₂.alice.bytes = sess.aliceBaseKey ∧
        sg₂.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
        (sg₂.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat⌝ ∗
       ((fsp + 0x128#64) ↦₆₄ 0#64) ∗ ((fsp + 0x130#64) ↦₆₄ 8#64) ∗
       ((fsp + 0x138#64) ↦₆₄ 0#64) ∗
       sessionStateAt A (fsp + 0x140#64) sg₂ sess.state ∗ emp ∗ R) := sat_eq (by ac_rfl) hm
  rw [satisfies_pure_sepConj] at hm1
  have hm2 := hm1.2
  rw [satisfies_pure_sepConj, emp_sepConj] at hm2
  have hm3 := hm2.2
  dsimp only [sessionStateAt, LibsignalSessionRepr.vecGhostAt] at hm3
  rw [vecU8At_eq_header_sep_buf A (fsp + 0x140#64)
        sg₂.localIk.cap sg₂.localIk.ptr sg₂.localIk.bytes] at hm3
  unfold vecHeader at hm3
  have hm4 : m ⊨ ⌜PublicKey.deserialize sg₂.localIk.bytes = .ok sess.state.localIdentity.publicKey ∧
      (match sess.state.remoteIdentity with
       | none => sg₂.remoteIk.bytes = []
       | some ik => PublicKey.deserialize sg₂.remoteIk.bytes = .ok ik.publicKey) ∧
      sg₂.chains.length = sess.state.receiverChains.length ∧
      sg₂.pending.isSome = sess.state.pendingPreKey ∧ sg₂.regIds.length = 8 ∧
      sg₂.localIk.bytes.length = 33 ∧
      (sess.state.remoteIdentity.isSome → sg₂.remoteIk.bytes.length = 33)⌝ ∗
      (vecU8Buf A sg₂.localIk.cap sg₂.localIk.ptr sg₂.localIk.bytes ∗
       ((fsp + 0x128#64) ↦₆₄ 0#64) ∗ ((fsp + 0x130#64) ↦₆₄ 8#64) ∗
       ((fsp + 0x138#64) ↦₆₄ 0#64) ∗ ((fsp + 0x140#64) ↦₆₄ sg₂.localIk.cap) ∗
       (((fsp + 0x140#64 + 8#64) ↦₆₄ sg₂.localIk.ptr) ∗
        ((fsp + 0x140#64 + 16#64) ↦₆₄ BitVec.ofNat 64 sg₂.localIk.bytes.length) ∗
        vecGhostAt A sg₂.remoteIk (fsp + 0x140#64 + 0x18#64) ∗
        vecU8At A (fsp + 0x140#64 + 0x30#64) sg₂.root.cap sg₂.root.ptr
          (keyToBytes32 sess.state.rootKey) ∗
        vecAt A 104 8 (chainAt A) (fsp + 0x140#64 + 0x48#64) sg₂.chainsCap sg₂.chainsPtr
          (sg₂.chains.zip sess.state.receiverChains) ∗
        vecGhostAt A sg₂.alice (fsp + 0x140#64 + 0x60#64) ∗
        vecU8At A (fsp + 0x140#64 + 0x78#64) sg₂.pq.cap sg₂.pq.ptr sess.state.pqRatchetState ∗
        optSenderChainAt A (fsp + 0x140#64 + 0x90#64) sg₂.sender sess.state.senderChain ∗
        optTailVecAt A 48 (fsp + 0x140#64 + 0xf8#64) sg₂.pending ∗
        optTailVecAt A 32 (fsp + 0x140#64 + 0x128#64) sg₂.kyber ∗
        ((fsp + 0x140#64 + 0x148#64) ↦₃₂ sess.state.sessionVersion) ∗
        ((fsp + 0x140#64 + 0x14c#64) ↦₃₂ sess.state.previousCounter) ∗
        ((fsp + 0x140#64 + 0x150#64) ↦ₛ sg₂.regIds)) ∗ R) :=
    sat_eq (by dsimp only [LibsignalSessionRepr.vecGhostAt]; ac_rfl) hm3
  rw [satisfies_pure_sepConj] at hm4
  obtain ⟨hpureSt, hm5⟩ := hm4
  have hcapLt : sg₂.localIk.cap.toNat < 2 ^ 63 := by
    dsimp only [vecU8Buf] at hm5
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm5
    exact hm5.1.2.1
  let Tail : SepProp :=
    vecU8Buf A sg₂.localIk.cap sg₂.localIk.ptr sg₂.localIk.bytes ∗
    ((fsp + 0x140#64 + 8#64) ↦₆₄ sg₂.localIk.ptr) ∗
    ((fsp + 0x140#64 + 16#64) ↦₆₄ BitVec.ofNat 64 sg₂.localIk.bytes.length) ∗
    vecGhostAt A sg₂.remoteIk (fsp + 0x140#64 + 0x18#64) ∗
    vecU8At A (fsp + 0x140#64 + 0x30#64) sg₂.root.cap sg₂.root.ptr
      (keyToBytes32 sess.state.rootKey) ∗
    vecAt A 104 8 (chainAt A) (fsp + 0x140#64 + 0x48#64) sg₂.chainsCap sg₂.chainsPtr
      (sg₂.chains.zip sess.state.receiverChains) ∗
    vecGhostAt A sg₂.alice (fsp + 0x140#64 + 0x60#64) ∗
    vecU8At A (fsp + 0x140#64 + 0x78#64) sg₂.pq.cap sg₂.pq.ptr sess.state.pqRatchetState ∗
    optSenderChainAt A (fsp + 0x140#64 + 0x90#64) sg₂.sender sess.state.senderChain ∗
    optTailVecAt A 48 (fsp + 0x140#64 + 0xf8#64) sg₂.pending ∗
    optTailVecAt A 32 (fsp + 0x140#64 + 0x128#64) sg₂.kyber ∗
    ((fsp + 0x140#64 + 0x148#64) ↦₃₂ sess.state.sessionVersion) ∗
    ((fsp + 0x140#64 + 0x14c#64) ↦₃₂ sess.state.previousCounter) ∗
    ((fsp + 0x140#64 + 0x150#64) ↦ₛ sg₂.regIds)
  refine ⟨sg₂.localIk.cap, Tail, by bv_omega, ?_, ?_⟩
  · dsimp only [Tail]
    exact sat_eq (by ac_rfl) hm5
  · dsimp only [sessionStateAt, LibsignalSessionRepr.vecGhostAt, Tail]
    refine Entails.pure_right hpureSt ?_
    rw [vecU8At_eq_header_sep_buf A (fsp + 0x140#64)
          sg₂.localIk.cap sg₂.localIk.ptr sg₂.localIk.bytes]
    unfold vecHeader
    exact entails_ac (by ac_rfl)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas
