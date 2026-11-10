/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Game.StatementPq
public import Computational.Proofs.SpecLemmas.Game.StatementBinaryHarnessCore
public import Computational.Proofs.LibsignalCli.Entry.CliPqEntryBridges
public import Computational.Proofs.LibsignalCli.Entry.CliPqReachSize
public import Computational.Proofs.LibsignalCli.Entry.CliPqSessionCap
import all Init.Data.String.Defs
import all Init.Data.Repr
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.Crypto
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap
import Mathlib.Algebra.Order.Ring.Star
import ProofLib.SepLogic.WP.StepsCore

@[expose] public section

set_option autoImplicit false

/-!
# PQ CLI handshake and step bridges

Connects `StatementPq` directories, wire encodings, `PqxdhPartyInSpecDomain` invariants, and the
Alice/Bob handshake steps (`cliPqInit`, `acceptKeys`) to `sessionSchemeFixedSpk`.
-/

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.SignalSession
  CryptoVerification.LibsignalCli.Entry

/-! ## Parameter and wire helpers -/

@[simp] theorem paramsIdsWithSpqr_spqrV1SessionB_eq_paramsPqBIds
    (W : PEParams) (idA idB : IdentityKey) :
    paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) idA idB =
      paramsPqBIds W idA idB :=
  rfl

@[simp] theorem cliPqAfter_eq_spec :
    cliPqAfter = cliPqAfterSpec :=
  rfl

theorem bhReadProstVarint_varint_append (n : ℕ) :
    ∀ rest : List (BitVec 8), bhReadProstVarint (Prost.varint n ++ rest) = some (n, rest) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro rest
    rw [Prost.varint]
    split_ifs with hlt
    · simp [bhReadProstVarint, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 256), hlt]
    · have hbnat : (BitVec.ofNat 8 (n % 128 + 128)).toNat = n % 128 + 128 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hge : ¬ (n % 128 + 128 < 128) := by omega
      rw [List.cons_append, bhReadProstVarint]
      dsimp only
      simp only [hbnat, hge, ↓reduceIte,
        ih (n / 128) (Nat.div_lt_self (by omega) (by decide)) rest, Option.map_some,
        Option.some.injEq, Prod.mk.injEq]
      exact ⟨by rw [Nat.add_sub_cancel, Nat.mod_add_div], trivial⟩

@[simp] theorem bhDecodePreKeyMsgE_wireWhisper (body : Bytes) :
    bhDecodePreKeyMsgE (wireWhisper :: body) = none := by
  cases body <;> rfl

/-! ## Directory invariants and step preservation -/

private theorem textBytes_addrE_length_lt (P : Party) :
    (textBytes (partyAddress P).text).length < 2 ^ 31 := by
  cases P <;> decide +kernel

private theorem le32_length_lt (v : BitVec 32) : (le32 v).length < 2 ^ 31 := by
  simp [le32]

private theorem identityKey_serialize_length_lt (k : IdentityKey) :
    k.serialize.length < 2 ^ 31 := by
  simp [IdentityKey.serialize, PublicKey.serialize]

private theorem encodeVarintAux_len_le : ∀ (k : ℕ) (v : BitVec 64),
    (encodeVarintAux k v).length ≤ k
  | 0, _ => by simp [encodeVarintAux]
  | k + 1, v => by
    unfold encodeVarintAux; split_ifs
    · simp
    · simp only [List.length_cons]
      exact Nat.add_le_add_right (encodeVarintAux_len_le k (v >>> 7)) 1

private theorem encodeVarint_len_le (v : BitVec 64) :
    (LibsignalProtoCodec.encodeVarint v).length ≤ 10 :=
  encodeVarintAux_len_le 10 v

private theorem encodeKey_len_le (tag : ℕ) (wt : LibsignalProtoCodec.WireType) :
    (encodeKey tag wt).length ≤ 10 :=
  encodeVarintAux_len_le 10 _

private theorem encodeBytes3_length_le (tag : ℕ) (v : List (BitVec 8)) :
    (RecordCodecs.encodeProto3BytesField tag v).length ≤ 20 + v.length := by
  unfold RecordCodecs.encodeProto3BytesField
  split_ifs with hv
  · simp
  · unfold encodeBytesField
    have h1 := encodeKey_len_le tag .lengthDelimited
    have h2 := encodeVarint_len_le (BitVec.ofNat 64 v.length)
    simp only [List.length_append]
    omega

private theorem idKeyPair_encode_length_lt (C : Crypto) (idPriv : List.Vector (BitVec 8) 32) :
    (RecordCodecs.IdentityKeyPairStructure.encode
      ⟨djbKey (keyPairOf C idPriv).publicKey.bytes, idPriv.toList⟩).length < 2 ^ 31 := by
  unfold RecordCodecs.IdentityKeyPairStructure.encode
  simp only [List.length_append]
  have h1 := encodeBytes3_length_le 1 (djbKey (keyPairOf C idPriv).publicKey.bytes)
  have h2 := encodeBytes3_length_le 2 idPriv.toList
  have hd : (djbKey (keyPairOf C idPriv).publicKey.bytes).length = 33 := by simp [djbKey]
  have hp : idPriv.toList.length = 32 := idPriv.2
  omega

@[simp] theorem lastResortUses_cliPqDirA {S : SignalPqxdh.Setup} {l : Nat} (bi : ModelDriverInstance S l) :
    lastResortUses (cliPqDirA bi) = 0 :=
  rfl

theorem wfPq_cliPqDirA {S : SignalPqxdh.Setup} {l : Nat} (W : PEParams) (bi : ModelDriverInstance S l) :
    PqxdhPartyInSpecDomain W (cliPqDirA bi) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ _ ⟨⟩
  · intro f hf
    have hcap :=
      LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap.encodeDir_nonBaseKeys_length_le_fileCapBytes
        W (cliPqDirA bi) (by rintro _ _ ⟨⟩) f hf
    refine ⟨?_, hcap⟩
    simp only [cliPqDirA, encodeDir, List.map_nil, List.flatten_nil, List.append_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with ((rfl | rfl | rfl) | rfl)
    · exact textBytes_addrE_length_lt .A
    · exact idKeyPair_encode_length_lt W.C bi.meA.idPriv
    · exact le32_length_lt bi.meA.regId
    · exact identityKey_serialize_length_lt _
  · simp [cliPqDirA]
  · simp [cliPqDirA]
  · simp [cliPqDirA]
  · simp [cliPqDirA]

@[simp] theorem lastResortUses_cliPqDirB0 {S : SignalPqxdh.Setup} {l : Nat}
    (bi : ModelDriverInstance S l) (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64) :
    lastResortUses (cliPqxdhDirBobBeforeAccept bi sigs) = 0 :=
  rfl

theorem wfPq_of_pqSteps_cliPqDirA {S : SignalPqxdh.Setup} {l : Nat}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {n : ℕ} {bi : ModelDriverInstance S l} {stₙ : PqParty}
    (hsteps : PqSteps X W n (cliPqDirA bi) stₙ) (hn : n < 2 ^ 25) :
    PqxdhPartyInSpecDomain W stₙ ∧ lastResortUses stₙ ≤ n ∧
      (∀ x g, stₙ.session = some (x, g) →
        g.session.pqRatchetState.length ≤ 286196) ∧
      (∀ x g, stₙ.session = some (x, g) →
        (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31) := by
  obtain ⟨hwf, hlr, hcap⟩ :=
    wfPq_of_pqSteps_r3 (wfPq_cliPqDirA W bi) rfl (lastResortUses_cliPqDirA bi) hsteps hn
  refine ⟨hwf, hlr, fun x g hs => ?_, fun x g hs => ?_⟩
  · have hst : { stₙ with session := some (x, g) } = stₙ := by
      cases stₙ; dsimp only at hs ⊢; rw [hs]
    exact pqLength_le_286196_of_wfPq (hst.symm ▸ hwf)
  · have h := hcap x g hs; unfold sessionCapBytes fileCapBytes at h; omega

/-! ## Alice `cliPqInit` and Bob `acceptKeys` bridges -/

theorem toU8_ofU8_eq (bs : List UInt8) : toU8 (ofU8 bs) = bs := by
  induction bs with
  | nil => rfl
  | cons _ _ ih => simp only [toU8, ofU8, List.map_cons] at *; rw [ih]

theorem ofU8_toU8_eq (bs : List (BitVec 8)) : ofU8 (toU8 bs) = bs := by
  induction bs with
  | nil => rfl
  | cons _ _ ih => simp only [toU8, ofU8, List.map_cons] at *; rw [ih]

theorem fitU8VecStrict_some_iff {n : ℕ} {bs : SignalPqxdh.Bytes}
    {v : List.Vector (BitVec 8) n} :
    fitU8VecStrict n bs = some v ↔ bs.length = n ∧ v = u8Vec n bs := by
  unfold fitU8VecStrict u8Vec
  constructor
  · intro h
    dsimp only at h
    split_ifs at h with hlen
    · injection h with h
      have hbs : bs.length = n := by simpa [ofU8] using hlen
      refine ⟨hbs, ?_⟩
      subst h
      apply Subtype.ext
      simp [fitVec, hlen]
  · rintro ⟨hbs, rfl⟩
    have hlen : (ofU8 bs).length = n := by simp [ofU8, hbs]
    simp only [hlen, ↓reduceDIte]
    congr 1
    apply Subtype.ext
    simp [fitVec, hlen]

theorem vecU8_u8Vec_of_len {n : ℕ} {bs : SignalPqxdh.Bytes} (h : bs.length = n) :
    vecU8 (u8Vec n bs) = bs := by
  have hlen : (ofU8 bs).length = n := by simp [ofU8, h]
  unfold vecU8 u8Vec
  have hfit : (fitVec n (ofU8 bs)).toList = ofU8 bs := by simp [fitVec, hlen]
  rw [hfit, toU8_ofU8_eq]

@[simp] theorem u8Vec_vecU8_eq {n : ℕ} (v : List.Vector (BitVec 8) n) :
    u8Vec n (vecU8 v) = v := by
  apply Subtype.ext
  have hof : ofU8 (vecU8 v) = v.toList := ofU8_toU8_eq v.toList
  simp [u8Vec, fitVec, hof]

theorem bytesToKey32_u8Vec_eq_bhBytesWord {bs : SignalPqxdh.Bytes} (h : bs.length = 32) :
    HKDF.bytesToKey32 (u8Vec 32 bs).toList = bhBytesWord bs := by
  have hlen : (ofU8 bs).length = 32 := by simp [ofU8, h]
  unfold u8Vec bhBytesWord
  have hfit : (fitVec 32 (ofU8 bs)).toList = ofU8 bs := by simp [fitVec, hlen]
  rw [hfit]

@[simp] private theorem u32_toBitVec_eq (x : UInt32) : u32 x.toBitVec = x := by
  unfold u32
  apply UInt32.eq_of_toBitVec_eq
  rfl

private theorem u32_ofNat_toNat_eq (x : UInt32) : u32 (BitVec.ofNat 32 x.toNat) = x := by
  simp [u32_toBitVec_eq]

theorem cliPqInit_eq_initiateState_map {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hspec : CliSpecPqxdh run X W) (dA : PqParty) (hwf : PqxdhPartyInSpecDomain W dA)
    (hparty : dA.party = .A) (hnone : dA.session = none)
    (b : PreKeyBundleFields) (htrust : dA.trusts ⟨⟨b.idPub⟩⟩ = true)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    cliPqInit run W dA b t =
      (initiateState X W .A dA.me b t).map (fun (x, g) => binStateOfUnderExtras (fun _ => x) g) := by
  unfold cliPqInit
  rw [cliPqAfter_eq_spec, (hspec dA hwf).1 b t hnone]
  have hnt : (!dA.trusts ⟨⟨b.idPub⟩⟩) = false := by simp [htrust]
  rw [cliPqAfterSpec_pqObserve_eq W .A (pqInitInputs W dA b t) (pqInitModel X W dA b t)]
  · unfold pqInitModel
    rw [hnt, hparty]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rcases hi : initiateState X W .A dA.me b t with _ | ⟨x, g⟩
    · rfl
    · obtain ⟨_, _, hg_party, hg_ep⟩ := initiateState_aligned_and_epochs hi
      simp only [Option.join_some, Option.map_some, binStateOfUnderExtras, hg_party, hg_ep]
  · intro st' out hmod
    unfold pqInitModel at hmod
    rw [hnt] at hmod
    simp only [Bool.false_eq_true, ↓reduceIte] at hmod
    rcases hi : initiateState X W dA.party dA.me b t with _ | ⟨x, g⟩
    · simp [hi] at hmod
    · rw [hi] at hmod
      simp only [Option.some.injEq, Prod.mk.injEq] at hmod
      rcases hmod with ⟨rfl, rfl⟩
      exact ⟨hparty, x, g, rfl⟩

theorem pqStep_of_initiateState_eq_some {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (dA : PqParty) (hparty : dA.party = .A) (hnone : dA.session = none)
    (b : PreKeyBundleFields) (htrust : dA.trusts ⟨⟨b.idPub⟩⟩ = true)
    (t : List.Vector (BitVec 8) initiateTapeLen) (x : RecordExtras) (g : GhostState Bytes)
    (hi : initiateState X W .A dA.me b t = some (x, g)) :
    PqStep X W dA { dA with peerId := some ⟨⟨b.idPub⟩⟩, session := some (x, g) } ∧
      PqSteps X W 1 dA { dA with peerId := some ⟨⟨b.idPub⟩⟩, session := some (x, g) } := by
  have hnt : (!dA.trusts ⟨⟨b.idPub⟩⟩) = false := by simp [htrust]
  have hmod : pqInitModel X W dA b t =
      some (some ({ dA with peerId := some ⟨⟨b.idPub⟩⟩, session := some (x, g) }, [])) := by
    unfold pqInitModel
    rw [hnt, hparty, hi]
    rfl
  have hstep := PqStep.init b t _ [] hnone hmod
  exact ⟨hstep, PqSteps.single hstep⟩

theorem initiateState_of_initiateKeys_eq_some (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (meA : LocalIdentity) (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen)
    (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr) (spkCoins : BitVec 256)
    (hinit : SignalPqxdh.Model.initiateKeys (modelPrims X W) (initiateInput W meA b t) =
      some (dk, hdr))
    (hspk : ⟨b.spkPub⟩ = (KeyPair.generate W.C spkCoins).publicKey)
    (hnoz : ∀ a b, W.C.X (Ratchet.clampScalar a) (W.C.pubKey (Ratchet.clampScalar b)) ≠
      List.Vector.replicate 32 0#8) :
    let idA : IdentityKey := ⟨(keyPairOf W.C meA.idPriv).publicKey⟩
    let idB : IdentityKey := ⟨⟨b.idPub⟩⟩
    let P_pq := paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) idA idB
    let kInit := initKeysOfSampled spkCoins (bhKeySOf dk (SignalSession.tapeAliceCoins t))
    initiateState X W .A meA b t =
      some (initiatorRecordExtras meA b ⟨u8Vec 32 hdr.ekAPk⟩ (u8Vec 1568 hdr.kemCt),
        P_pq.initA kInit) := by
  dsimp only
  unfold initiateState
  rw [hinit]
  dsimp only
  set idA : IdentityKey := ⟨(keyPairOf W.C meA.idPriv).publicKey⟩
  set idB : IdentityKey := ⟨⟨b.idPub⟩⟩
  set P_pq := paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) idA idB
  set aliceCoins := SignalSession.tapeAliceCoins t
  set kInit := initKeysOfSampled spkCoins (bhKeySOf dk aliceCoins)
  have hinit_sess :
      initializeInitiatorSession W.C (pqxdhSpqrSession W) idA idB ⟨b.spkPub⟩
        (HKDF.bytesToKey32 (ofU8 dk.rootKey)) (HKDF.bytesToKey32 (ofU8 dk.chainKey))
        (HKDF.bytesToKey32 (ofU8 dk.pqrKey)) (HKDF.bytesToKey32 ((t.toList.drop 160).take 32)) =
      initializeInitiatorSession P_pq.C P_pq.spqr P_pq.idA P_pq.idB
        (KeyPair.generate P_pq.C kInit.bobSpkCoins).publicKey
        kInit.rootKey kInit.chainKey kInit.pqrKey kInit.aliceRatchetCoins := by
    have hspk' : ⟨b.spkPub⟩ = (KeyPair.generate P_pq.C kInit.bobSpkCoins).publicKey := hspk
    rw [hspk']
    rfl
  rw [hinit_sess]
  unfold Params.initA
  dsimp only
  have hok : ∃ s,
      initializeInitiatorSession P_pq.C P_pq.spqr P_pq.idA P_pq.idB
        (KeyPair.generate P_pq.C kInit.bobSpkCoins).publicKey
        kInit.rootKey kInit.chainKey kInit.pqrKey kInit.aliceRatchetCoins = .ok s := by
    unfold initializeInitiatorSession rootCreateChain Ratchet.createChain KeyPair.generate
    dsimp only
    rw [CryptoGames.LibsignalSM.Proofs.Correctness.clampScalar_idem]
    have hP_C : P_pq.C = W.C := rfl
    rw [hP_C]
    have hne_vec := hnoz (Ratchet.keyToBytesVec32 kInit.aliceRatchetCoins) (Ratchet.keyToBytesVec32 kInit.bobSpkCoins)
    have hne_list : (W.C.X (Ratchet.clampScalar (Ratchet.keyToBytesVec32 kInit.aliceRatchetCoins))
        (W.C.pubKey (Ratchet.clampScalar (Ratchet.keyToBytesVec32 kInit.bobSpkCoins)))).toList ≠
        List.replicate 32 0#8 := by
      intro heq
      apply hne_vec
      apply Subtype.ext
      simpa [List.Vector.replicate, List.Vector.toList] using heq
    simp only [hne_list, ↓reduceIte]
    exact ⟨_, rfl⟩
  rcases hok with ⟨s, hs⟩
  rw [hs]

/-- Connects `bhRunInitiate` to `cliPqInit` and a `PqStep.init` transition on `P_pq.initA`. -/
theorem cliPqInit_eq_some_binStateOfX {S : SignalPqxdh.Setup}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hspec : CliSpecPqxdh run X W)
    (dA : PqParty) (hwf : PqxdhPartyInSpecDomain W dA)
    (u_init u_resp : Fin S.N_id)
    (secIKA0 spkSk : SignalPqxdh.Bytes)
    (bnd : SignalPqxdh.PreKeyBundleInput)
    (meA : LocalIdentity) (bundleE : PreKeyBundleFields)
    (t_init : List.Vector (BitVec 8) 160) (t_dr : List.Vector (BitVec 8) 32)
    (ss kemCt : SignalPqxdh.Bytes)
    (inst : BHAdapterInstMeta S)
    (hparty : dA.party = .A) (hnone : dA.session = none) (hme_eq : dA.me = meA)
    (hpeer : dA.peerId = some (bhIdKeyOf bnd.ikB))
    (hmeA : mkMeEStrict u_init.val secIKA0 = some meA)
    (hbnd : mkBundleEStrict u_resp.val bnd = some bundleE)
    (hregA : bhInitRegId inst.sid = BitVec.ofNat 32 u_init.val)
    (huresp : inst.u_resp = u_resp)
    (hsig_spk : (modelPrims X W).sigVerify bnd.ikB (SignalPqxdh.encodeEC bnd.spkB) bnd.spkSig = true)
    (hsig_kem : (modelPrims X W).sigVerify bnd.ikB (SignalPqxdh.encodeKEM bnd.pqspkB) bnd.pqspkSig = true)
    (henc : (modelPrims X W).kemEncaps bnd.pqspkB (tapeKemCoins t_init) = some (ss, kemCt))
    (hkemCt_len : kemCt.length = 1568)
    (hspkSk_len : spkSk.length = 32)
    (hspkB : bnd.spkB = (modelPrims X W).x25519Base spkSk)
    (hdh1_noz : (modelPrims X W).x25519 secIKA0 bnd.spkB ≠ List.replicate 32 0)
    (hdh2_noz : (modelPrims X W).x25519 (tapeEkASk t_init) bnd.ikB ≠ List.replicate 32 0)
    (hdh3_noz : (modelPrims X W).x25519 (tapeEkASk t_init) bnd.spkB ≠ List.replicate 32 0)
    (hdh4_noz : SignalPqxdh.dhOptNonZero
      (bnd.opkB?.map (fun (_, opkPk) => (modelPrims X W).x25519 (tapeEkASk t_init) opkPk)) = true)
    (hnoz : ∀ a b, W.C.X (Ratchet.clampScalar a) (W.C.pubKey (Ratchet.clampScalar b)) ≠
      List.Vector.replicate 32 0#8)
    (hhdr : inst.hdr =
      { ikAPk := (modelPrims X W).x25519Base secIKA0
        ekAPk := (modelPrims X W).x25519Base (tapeEkASk t_init)
        spkId := bnd.spkId
        opkId? := bnd.opkB?.map Prod.fst
        pqspkId := bnd.pqspkId
        kemCt := kemCt }) :
    let P := modelPrims X W
    let dk := P.hkdfDerive96 (SignalPqxdh.buildSecrets
      (P.x25519 secIKA0 bnd.spkB)
      (P.x25519 (tapeEkASk t_init) bnd.ikB)
      (P.x25519 (tapeEkASk t_init) bnd.spkB)
      (bnd.opkB?.map (fun (_, opkPk) => P.x25519 (tapeEkASk t_init) opkPk))
      ss)
    let idA : IdentityKey := ⟨(keyPairOf W.C meA.idPriv).publicKey⟩
    let idB : IdentityKey := ⟨⟨bundleE.idPub⟩⟩
    let P_pq := paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) idA idB
    let t := appendInitiateTape t_init t_dr
    let gA0 := P_pq.initA (initKeysOfSampled (bhBytesWord spkSk) (bhKeySOf dk (SignalSession.tapeAliceCoins t)))
    initiateState X W .A meA bundleE t = some (bhInstExtrasA inst, gA0) ∧
      cliPqInit run W dA bundleE t = some (binStateOfUnderExtras (fun _ => bhInstExtrasA inst) gA0) ∧
      PqStep X W dA { dA with session := some (bhInstExtrasA inst, gA0) } ∧
      PqSteps X W 1 dA { dA with session := some (bhInstExtrasA inst, gA0) } := by
  let _ := hkemCt_len
  dsimp only
  set P := modelPrims X W
  set t := appendInitiateTape t_init t_dr
  unfold mkMeEStrict at hmeA
  rcases hfit_ikA : fitU8VecStrict 32 secIKA0 with _ | idPrivA
  · simp [hfit_ikA, bind, Option.bind] at hmeA
  rw [hfit_ikA] at hmeA; simp only [bind, Option.bind, Option.some.injEq] at hmeA
  obtain ⟨_, hidPrivA_eq⟩ := fitU8VecStrict_some_iff.mp hfit_ikA
  unfold mkBundleEStrict at hbnd
  rcases hfit_spk : fitU8VecStrict 32 bnd.spkB with _ | spkPubV
  · simp [hfit_spk, bind, Option.bind] at hbnd
  rcases hfit_ssig : fitU8VecStrict 64 bnd.spkSig with _ | spkSigV
  · simp [hfit_spk, hfit_ssig, bind, Option.bind] at hbnd
  rcases hfit_kpk : fitU8VecStrict 1568 bnd.pqspkB with _ | kpkPubV
  · simp [hfit_spk, hfit_ssig, hfit_kpk, bind, Option.bind] at hbnd
  rcases hfit_ksig : fitU8VecStrict 64 bnd.pqspkSig with _ | kpkSigV
  · simp [hfit_spk, hfit_ssig, hfit_kpk, hfit_ksig, bind, Option.bind] at hbnd
  rcases hfit_idB : fitU8VecStrict 32 bnd.ikB with _ | idPubV
  · simp [hfit_spk, hfit_ssig, hfit_kpk, hfit_ksig, hfit_idB, bind, Option.bind] at hbnd
  obtain ⟨hspk_len, hspkV⟩ := fitU8VecStrict_some_iff.mp hfit_spk
  obtain ⟨hssig_len, hssigV⟩ := fitU8VecStrict_some_iff.mp hfit_ssig
  obtain ⟨hkpk_len, hkpkV⟩ := fitU8VecStrict_some_iff.mp hfit_kpk
  obtain ⟨hksig_len, hksigV⟩ := fitU8VecStrict_some_iff.mp hfit_ksig
  obtain ⟨hidB_len, hidBV⟩ := fitU8VecStrict_some_iff.mp hfit_idB
  have hbnd_fields :
      bundleE.regId = BitVec.ofNat 32 u_resp.val ∧
      bundleE.spkId = BitVec.ofNat 32 bnd.spkId.toNat ∧
      bundleE.spkPub = u8Vec 32 bnd.spkB ∧
      bundleE.spkSig = u8Vec 64 bnd.spkSig ∧
      bundleE.kpkId = BitVec.ofNat 32 bnd.pqspkId.toNat ∧
      bundleE.kpkPub = u8Vec 1568 bnd.pqspkB ∧
      bundleE.kpkSig = u8Vec 64 bnd.pqspkSig ∧
      bundleE.idPub = u8Vec 32 bnd.ikB ∧
      bundleE.opk.map (fun (i, k) => (u32 i, vecU8 k)) = bnd.opkB? ∧
      bundleE.opk.map Prod.fst = bnd.opkB?.map (fun (id, _) => BitVec.ofNat 32 id.toNat) := by
    rw [hfit_spk, hfit_ssig, hfit_kpk, hfit_ksig, hfit_idB] at hbnd
    dsimp only [bind, Option.bind] at hbnd
    cases hopk : bnd.opkB? with
    | none =>
      rw [hopk] at hbnd
      simp only [Option.some.injEq] at hbnd
      subst hbnd
      exact ⟨rfl, rfl, hspkV, hssigV, rfl, hkpkV, hksigV, hidBV, rfl, rfl⟩
    | some pair =>
      rcases pair with ⟨oid, opkBytes⟩
      rw [hopk] at hbnd
      dsimp only at hbnd
      rcases hfit_opk : fitU8VecStrict 32 opkBytes with _ | opkV
      · simp [hfit_opk] at hbnd
      · rw [hfit_opk] at hbnd
        simp only [Option.some.injEq] at hbnd
        obtain ⟨hopk_len, hopkV⟩ := fitU8VecStrict_some_iff.mp hfit_opk
        subst hbnd
        refine ⟨rfl, rfl, hspkV, hssigV, rfl, hkpkV, hksigV, hidBV, ?_, rfl⟩
        simp [hopkV, vecU8_u8Vec_of_len hopk_len]
  have hu32_spk : u32 (BitVec.ofNat 32 bnd.spkId.toNat) = bnd.spkId := u32_ofNat_toNat_eq bnd.spkId
  have hu32_kpk : u32 (BitVec.ofNat 32 bnd.pqspkId.toNat) = bnd.pqspkId := u32_ofNat_toNat_eq bnd.pqspkId
  have hbnd_eq : (initiateInput W meA bundleE t).bundle = bnd := by
    unfold initiateInput
    rcases bnd with ⟨ikB, spkId, spkB, spkSig, opkB?, pqspkId, pqspkB, pqspkSig⟩
    simp only [hbnd_fields.2.1, hbnd_fields.2.2.1, hbnd_fields.2.2.2.1, hbnd_fields.2.2.2.2.1,
      hbnd_fields.2.2.2.2.2.1, hbnd_fields.2.2.2.2.2.2.1, hbnd_fields.2.2.2.2.2.2.2.1,
      hbnd_fields.2.2.2.2.2.2.2.2.1, vecU8_u8Vec_of_len hspk_len, vecU8_u8Vec_of_len hssig_len,
      vecU8_u8Vec_of_len hkpk_len, vecU8_u8Vec_of_len hksig_len, vecU8_u8Vec_of_len hidB_len,
      hu32_spk, hu32_kpk]
  have hek_eq : (initiateInput W meA bundleE t).ekASk = tapeEkASk t_init := by
    rcases t_init with ⟨l1, h1⟩; rcases t_dr with ⟨l2, h2⟩
    dsimp only [initiateInput, tapeEkASk, t, appendInitiateTape, List.Vector.toList]
    rw [List.take_append_of_le_length (by omega)]
  have hkem_eq : (initiateInput W meA bundleE t).kemCoins = tapeKemCoins t_init := by
    dsimp only [initiateInput, tapeKemCoins, initiateKemCoins]
    congr 1
    apply List.Vector.ext; intro i
    simp only [List.Vector.get_ofFn]
    have hget {n : Nat} (v : List.Vector (BitVec 8) n) (k : Fin n) :
        v.get k = v.toList[k.val]'(by rw [List.Vector.toList_length]; exact k.2) := by
      rcases v with ⟨l, rfl⟩; rfl
    rw [hget, hget]
    rcases t_init with ⟨l1, h1⟩; rcases t_dr with ⟨l2, h2⟩
    dsimp only [t, appendInitiateTape, List.Vector.toList]
    exact List.getElem_append_left (by omega)
  have hikA_sk_dh : ∀ pk, P.x25519 (initiateInput W meA bundleE t).ikASk pk = P.x25519 secIKA0 pk := by
    intro pk
    have hme_priv : meA.idPriv = u8Vec 32 secIKA0 := by rw [← hmeA]; exact hidPrivA_eq
    unfold P modelPrims blockLevelPrims initiateInput keyPairOf
    dsimp only
    rw [hme_priv, u8Vec_vecU8_eq, CryptoGames.LibsignalSM.Proofs.Correctness.clampScalar_idem]
  have hikA_pk_eq : (initiateInput W meA bundleE t).ikAPk = P.x25519Base secIKA0 := by
    have hme_priv : meA.idPriv = u8Vec 32 secIKA0 := by rw [← hmeA]; exact hidPrivA_eq
    unfold P modelPrims blockLevelPrims initiateInput keyPairOf
    dsimp only
    rw [hme_priv]
  have htrA : (initiateInput W meA bundleE t).trustedPeer = true := rfl
  set dk := P.hkdfDerive96 (SignalPqxdh.buildSecrets
    (P.x25519 secIKA0 bnd.spkB)
    (P.x25519 (tapeEkASk t_init) bnd.ikB)
    (P.x25519 (tapeEkASk t_init) bnd.spkB)
    (bnd.opkB?.map (fun (_, opkPk) => P.x25519 (tapeEkASk t_init) opkPk))
    ss)
  set idA : IdentityKey := ⟨(keyPairOf W.C meA.idPriv).publicKey⟩
  set idB : IdentityKey := ⟨⟨bundleE.idPub⟩⟩
  set P_pq := paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) idA idB
  set gA0 := P_pq.initA (initKeysOfSampled (bhBytesWord spkSk) (bhKeySOf dk (SignalSession.tapeAliceCoins t)))
  have hdh1_b : (P.x25519 secIKA0 bnd.spkB != List.replicate 32 0) = true := bne_iff_ne.mpr hdh1_noz
  have hdh2_b : (P.x25519 (tapeEkASk t_init) bnd.ikB != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh2_noz
  have hdh3_b : (P.x25519 (tapeEkASk t_init) bnd.spkB != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh3_noz
  have hinitKeys : SignalPqxdh.Model.initiateKeys P (initiateInput W meA bundleE t) =
      some (dk, inst.hdr) := by
    unfold SignalPqxdh.Model.initiateKeys
    rw [htrA, hbnd_eq, hek_eq, hkem_eq, hikA_sk_dh, hikA_pk_eq, hhdr]
    simp only [hsig_spk, hsig_kem, henc, hdh1_b, hdh2_b, hdh3_b, hdh4_noz,
      ↓reduceIte, _root_.guard, bind, Option.bind, pure]
    dsimp only [dk]
  have hspk_kp : ⟨bundleE.spkPub⟩ = (KeyPair.generate W.C (bhBytesWord spkSk)).publicKey := by
    rw [hbnd_fields.2.2.1, hspkB]
    unfold P modelPrims blockLevelPrims
    dsimp only
    rw [u8Vec_vecU8_eq]
    change (keyPairOf W.C (u8Vec 32 spkSk)).publicKey = _
    rw [keyPairOf_eq_keyPair_generate W.C (u8Vec 32 spkSk),
      bytesToKey32_u8Vec_eq_bhBytesWord hspkSk_len]
  have his := initiateState_of_initiateKeys_eq_some X W meA bundleE t dk inst.hdr (bhBytesWord spkSk)
    hinitKeys hspk_kp hnoz
  have hextras : initiatorRecordExtras meA bundleE ⟨u8Vec 32 inst.hdr.ekAPk⟩ (u8Vec 1568 inst.hdr.kemCt) =
      bhInstExtrasA inst := by
    have hme_reg : meA.regId = BitVec.ofNat 32 u_init.val := by rw [← hmeA]
    unfold initiatorRecordExtras bhInstExtrasA
    rw [hme_reg, ← hregA, hbnd_fields.1, ← huresp, hbnd_fields.2.1, hbnd_fields.2.2.2.2.1,
      hbnd_fields.2.2.2.2.2.2.2.2.2, hhdr]
    dsimp only
    cases bnd.opkB? <;> rfl
  rw [hextras] at his
  have hpeer_id : (⟨⟨bundleE.idPub⟩⟩ : IdentityKey) = bhIdKeyOf bnd.ikB := by
    rw [hbnd_fields.2.2.2.2.2.2.2.1]; rfl
  have htrust : dA.trusts ⟨⟨bundleE.idPub⟩⟩ = true := by
    simp [PqParty.trusts, hpeer, hpeer_id]
  let dA1 : PqParty :=
    { dA with peerId := some ⟨⟨bundleE.idPub⟩⟩, session := some (bhInstExtrasA inst, gA0) }
  let dA2 : PqParty := { dA with session := some (bhInstExtrasA inst, gA0) }
  have hdA_upd : dA1 = dA2 := by
    cases dA; dsimp only [dA1, dA2] at hpeer ⊢; rw [hpeer_id, ← hpeer]
  have hcli := cliPqInit_eq_initiateState_map hspec dA hwf hparty hnone bundleE htrust t
  have his_dA : initiateState X W .A dA.me bundleE t = some (bhInstExtrasA inst, gA0) := by
    rw [hme_eq]; exact his
  rw [his_dA] at hcli
  obtain ⟨hstep, hsteps⟩ := pqStep_of_initiateState_eq_some dA hparty hnone bundleE htrust t
    (bhInstExtrasA inst) gA0 his_dA
  change PqStep X W dA dA1 at hstep
  change PqSteps X W 1 dA dA1 at hsteps
  rw [hdA_upd] at hstep hsteps
  exact ⟨his, hcli, hstep, hsteps⟩

/-- Shows `acceptKeys` on strict responder inputs recovers the initiator's derived `DRKey` outside
`cliClause2BadKemBool`. -/
theorem acceptKeys_of_mkKeysEStrict (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (u_resp j_resp : ℕ) (secIKB0 : SignalPqxdh.Bytes)
    (bEntry : SignalPqxdh.SpkBundleEntry) (opkOpt : Option (ℕ × SignalPqxdh.Bytes))
    (meB : LocalIdentity) (keysB : ResponderPreKeySecrets) (m : PreKeyMessageFields) (ss : SignalPqxdh.Bytes)
    (hmeB : mkMeEStrict u_resp secIKB0 = some meB)
    (hkeysB : mkKeysEStrict j_resp bEntry opkOpt = some keysB)
    (hopkId : m.opkId = keysB.opk.map Prod.fst)
    (hcanon : (modelPrims X W).isCanonical (vecU8 m.baseKey) = true)
    (hdh1_noz : (modelPrims X W).x25519 bEntry.spkSk (vecU8 m.idPub) ≠ List.replicate 32 0)
    (hdh2_noz : (modelPrims X W).x25519 secIKB0 (vecU8 m.baseKey) ≠ List.replicate 32 0)
    (hdh3_noz : (modelPrims X W).x25519 bEntry.spkSk (vecU8 m.baseKey) ≠ List.replicate 32 0)
    (hdh4_noz : SignalPqxdh.dhOptNonZero
      (opkOpt.map (fun (_, opkSk) => (modelPrims X W).x25519 opkSk (vecU8 m.baseKey))) = true)
    (hdec : (modelPrims X W).kemDecaps bEntry.pqspkSk (vecU8 m.kyberCt) = some ss) :
    let P := modelPrims X W
    let dk := P.hkdfDerive96 (SignalPqxdh.buildSecrets
      (P.x25519 bEntry.spkSk (vecU8 m.idPub))
      (P.x25519 secIKB0 (vecU8 m.baseKey))
      (P.x25519 bEntry.spkSk (vecU8 m.baseKey))
      (opkOpt.map (fun (_, opkSk) => P.x25519 opkSk (vecU8 m.baseKey)))
      ss)
    SignalPqxdh.Model.acceptKeys P (acceptInput W meB keysB m) = some dk ∧
      HKDF.bytesToKey32 keysB.spkPriv.toList = bhBytesWord bEntry.spkSk := by
  dsimp only
  set P := modelPrims X W
  unfold mkMeEStrict at hmeB
  rcases hfit_ikB : fitU8VecStrict 32 secIKB0 with _ | idPrivB
  · simp [hfit_ikB, bind, Option.bind] at hmeB
  rw [hfit_ikB] at hmeB; simp only [bind, Option.bind, Option.some.injEq] at hmeB
  obtain ⟨_, hidPrivB_eq⟩ := fitU8VecStrict_some_iff.mp hfit_ikB
  unfold mkKeysEStrict at hkeysB
  rcases hfit_spk : fitU8VecStrict 32 bEntry.spkSk with _ | spkPrivV
  · simp [hfit_spk, bind, Option.bind] at hkeysB
  rcases hfit_kpub : fitU8VecStrict 1568 bEntry.pqspkPk with _ | kpkPubV
  · simp [hfit_spk, hfit_kpub, bind, Option.bind] at hkeysB
  rcases hfit_ksec : fitU8VecStrict 3168 bEntry.pqspkSk with _ | kpkSecV
  · simp [hfit_spk, hfit_kpub, hfit_ksec, bind, Option.bind] at hkeysB
  obtain ⟨hspk_len, hspkV⟩ := fitU8VecStrict_some_iff.mp hfit_spk
  obtain ⟨hksec_len, hksecV⟩ := fitU8VecStrict_some_iff.mp hfit_ksec
  have hkeys_fields :
      keysB.spkPriv = u8Vec 32 bEntry.spkSk ∧
      keysB.kpkSec = u8Vec 3168 bEntry.pqspkSk ∧
      (((acceptInput W meB keysB m).hdr.opkId? = none ∧
        (acceptInput W meB keysB m).opkBSk? = none ∧
        opkOpt = none) ∨
       (∃ o oid opkSk skBytes,
        opkOpt = some (o, opkSk) ∧
        (acceptInput W meB keysB m).hdr.opkId? = some oid ∧
        (acceptInput W meB keysB m).opkBSk? = some skBytes ∧
        P.x25519 skBytes (vecU8 m.baseKey) = P.x25519 opkSk (vecU8 m.baseKey))) := by
    rw [hfit_spk, hfit_kpub, hfit_ksec] at hkeysB
    dsimp only [bind, Option.bind] at hkeysB
    cases hopk : opkOpt with
    | none =>
      rw [hopk] at hkeysB
      simp only [Option.some.injEq] at hkeysB
      subst hkeysB
      dsimp only at hopkId
      refine ⟨hspkV, hksecV, Or.inl ⟨?_, rfl, rfl⟩⟩
      unfold acceptInput
      rw [hopkId]
      rfl
    | some pair =>
      rcases pair with ⟨o, opkSk⟩
      rw [hopk] at hkeysB
      dsimp only at hkeysB
      rcases hfit_opk : fitU8VecStrict 32 opkSk with _ | opkV
      · simp [hfit_opk] at hkeysB
      · rw [hfit_opk] at hkeysB
        simp only [Option.some.injEq] at hkeysB
        obtain ⟨_, hopkV⟩ := fitU8VecStrict_some_iff.mp hfit_opk
        subst hkeysB
        dsimp only at hopkId
        refine ⟨hspkV, hksecV, Or.inr ⟨o, u32 (BitVec.ofNat 32 o), opkSk,
          vecU8 (keyPairOf W.C opkV).privateKey.bytes, rfl, ?_, ?_, ?_⟩⟩
        · unfold acceptInput; rw [hopkId]; rfl
        · unfold acceptInput; rw [hopkId]; dsimp only [Option.map]; simp only [↓reduceIte]
        · unfold P modelPrims blockLevelPrims keyPairOf
          dsimp only
          rw [hopkV, u8Vec_vecU8_eq, CryptoGames.LibsignalSM.Proofs.Correctness.clampScalar_idem]
  have hikB_dh : ∀ pk, P.x25519 (acceptInput W meB keysB m).ikBSk pk = P.x25519 secIKB0 pk := by
    intro pk
    have hme_priv : meB.idPriv = u8Vec 32 secIKB0 := by rw [← hmeB]; exact hidPrivB_eq
    unfold P modelPrims blockLevelPrims acceptInput keyPairOf
    dsimp only
    rw [hme_priv, u8Vec_vecU8_eq, CryptoGames.LibsignalSM.Proofs.Correctness.clampScalar_idem]
  have hspk_dh : ∀ pk, P.x25519 (acceptInput W meB keysB m).spkBSk pk = P.x25519 bEntry.spkSk pk := by
    intro pk
    unfold P modelPrims blockLevelPrims acceptInput keyPairOf
    dsimp only
    rw [hkeys_fields.1, u8Vec_vecU8_eq, CryptoGames.LibsignalSM.Proofs.Correctness.clampScalar_idem]
  have hpqspk_eq : (acceptInput W meB keysB m).pqspkBSk = bEntry.pqspkSk := by
    dsimp only [acceptInput]
    rw [hkeys_fields.2.1, vecU8_u8Vec_of_len hksec_len]
  have hhdr_fields :
      (acceptInput W meB keysB m).trustedPeer = true ∧
      (acceptInput W meB keysB m).replayOk = true ∧
      (acceptInput W meB keysB m).hdr.ikAPk = vecU8 m.idPub ∧
      (acceptInput W meB keysB m).hdr.ekAPk = vecU8 m.baseKey ∧
      (acceptInput W meB keysB m).hdr.kemCt = vecU8 m.kyberCt :=
    ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hid_len32 : (vecU8 m.idPub).length = 32 := by simp [vecU8, toU8]
  have hbk_len32 : (vecU8 m.baseKey).length = 32 := by simp [vecU8, toU8]
  have hct_len : (vecU8 m.kyberCt).length = SignalPqxdh.kyberCtLen := by
    simp [vecU8, toU8, SignalPqxdh.kyberCtLen]
  have hdh1_b : (P.x25519 bEntry.spkSk (vecU8 m.idPub) != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh1_noz
  have hdh2_b : (P.x25519 secIKB0 (vecU8 m.baseKey) != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh2_noz
  have hdh3_b : (P.x25519 bEntry.spkSk (vecU8 m.baseKey) != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh3_noz
  refine ⟨?_, ?_⟩
  · unfold SignalPqxdh.Model.acceptKeys
    rw [hhdr_fields.1, hhdr_fields.2.1, hpqspk_eq,
      hhdr_fields.2.2.1, hhdr_fields.2.2.2.1, hhdr_fields.2.2.2.2, hikB_dh, hspk_dh, hspk_dh]
    rcases hkeys_fields.2.2 with ⟨ho1, ho2, ho3⟩ | ⟨o, oid, opkSk, skBytes, ho0, ho1, ho2, ho_dh⟩
    · rw [ho3]
      rw [ho1, ho2]
      simp only [hid_len32, hbk_len32, hct_len, beq_self_eq_true, hcanon, hdh1_b, hdh2_b, hdh3_b,
        SignalPqxdh.dhOptNonZero, hdec, ↓reduceIte, _root_.guard, bind, Option.bind, pure,
        Option.map]
    · rw [ho0] at hdh4_noz ⊢
      rw [ho1, ho2]
      dsimp only [bind, Option.bind, pure, Option.map] at hdh4_noz ⊢
      rw [ho_dh]
      simp only [hid_len32, hbk_len32, hct_len, beq_self_eq_true, hcanon, hdh1_b, hdh2_b, hdh3_b,
        hdh4_noz, hdec, ↓reduceIte, _root_.guard, pure]
  · rw [hkeys_fields.1]
    exact bytesToKey32_u8Vec_eq_bhBytesWord hspk_len

end CryptoVerification.E2E

