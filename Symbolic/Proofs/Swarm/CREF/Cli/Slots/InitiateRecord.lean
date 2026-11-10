/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RecordBridge
public import Symbolic.Proofs.Swarm.CREF.Cli.Slots.InitiateDefs
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.DecCryptoAPure
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.InitiateCrypto
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.InitiateRecordAux
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# CLI `init` Session Record and Post-State Bridge

Connects `initiateState` outputs to `recordBytes (sessionToRecordRecPending (pqSession x g))`,
`AliceInitiatedV1PostPure`, and `InitiatePureOutcome` over the 34-piece coin split
`initiateDrawsOfCoins`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.Cli.Slots
open Symbolic.Swarm.CREF.CliPure

open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
cref_open
open Symbolic.Swarm.CREF.CliPure

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.Refinement (ExternCryptoLawsHold)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E
open CryptoVerification.SignalSession
open Proofs.libsignal.Hooks2 (cryptoOf')
open Proofs.libsignal.RngG.CliPure.DecCrypto (keyToBytes32_bytesToKey32_of_length_eq_32)

private theorem extractLsb'_append_eq_init {W : Nat} (b : BitVec W) (s₂ s₁ n₂ n₁ : Nat)
    (h : s₂ = s₁ + n₁) : b.extractLsb' s₂ n₂ ++ b.extractLsb' s₁ n₁ = b.extractLsb' s₁ (n₂ + n₁) := by
  subst h; ext i hi; simp only [BitVec.getElem_append, BitVec.getElem_extractLsb']
  split <;> [rfl; (congr 1; omega)]

private theorem decodeLe32_comp_le32 (v : BitVec 32) :
    DY.Libsignal.Composed.Refinement.decodeLe32 (DY.Libsignal.Composed.Refinement.le32 v) = v := by
  rw [comp_le32_eq_toLEBytes4]
  simp only [CryptoVerification.LibsignalAesCbc.toLEBytes, List.ofFn_succ, List.ofFn_zero,
    Fin.val_zero, Fin.val_succ, DY.Libsignal.Composed.Refinement.decodeLe32,
    DY.Libsignal.PQXDH.Refinement.bundleU32, Option.getD_some]
  rw [extractLsb'_append_eq_init v 24 16 8 8 rfl, extractLsb'_append_eq_init v 16 8 16 8 rfl,
    extractLsb'_append_eq_init v 8 0 24 8 rfl]
  ext i hi; simp

private theorem slice_mid (pre mid post : HwBytes) {n m : Nat}
    (hn : pre.length = n) (hm : mid.length = m) :
    DY.Libsignal.Composed.Refinement.slice (pre ++ (mid ++ post)) n m = mid := by
  subst hn hm
  unfold DY.Libsignal.Composed.Refinement.slice
  rw [List.drop_left, List.take_left]

private theorem bundlePreKeyIds_bundleBlob_publicBundleOf (bE : PreKeyBundleFields) :
    DY.Libsignal.Composed.Refinement.bundlePreKeyIds (bundleBlob (publicBundleOf bE)) =
      (bE.opk.map Prod.fst, bE.spkId, bE.kpkId) := by
  have hlen_le32 : ∀ v : BitVec 32, (DY.Libsignal.Composed.Refinement.le32 v).length = 4 := by
    intro v; rw [comp_le32_eq_toLEBytes4]; rfl
  have hlen_djb : ∀ v : List.Vector (BitVec 8) 32, (djbKey v).length = 33 := by
    intro v; simp [djbKey]
  have hlen_sig : ∀ v : List.Vector (BitVec 8) 64, v.toList.length = 64 := by
    intro v; exact v.2
  cases hopk : bE.opk with
  | none =>
    have hblob : bundleBlob (publicBundleOf bE) =
        DY.Libsignal.Composed.Refinement.le32 bE.regId ++ (List.replicate 38 0#8 ++
          (DY.Libsignal.Composed.Refinement.le32 bE.spkId ++
            (djbKey bE.spkPub ++ (bE.spkSig.toList ++
              (DY.Libsignal.Composed.Refinement.le32 bE.kpkId ++
                (CryptoVerification.E2E.kyberKey bE.kpkPub ++
                  (bE.kpkSig.toList ++ djbKey bE.idPub))))))) := by
      unfold bundleBlob publicBundleOf; rw [hopk]; simp [List.append_assoc]
    have hb0 : (bundleBlob (publicBundleOf bE))[4]? = some 0#8 := by
      rw [hblob, List.getElem?_append_right (by rw [hlen_le32]), hlen_le32]; rfl
    unfold DY.Libsignal.Composed.Refinement.bundlePreKeyIds
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · unfold DY.Libsignal.PQXDH.Refinement.BundleBlob.opkId
        DY.Libsignal.PQXDH.Refinement.BundleBlob.hasOpkByte
      simp only [hb0, show (some 0#8 == some 1#8) = false by decide, Bool.false_eq_true, ↓reduceIte,
        Option.map_none]
    · unfold DY.Libsignal.PQXDH.Refinement.BundleBlob.spkId
      rw [show bundleBlob (publicBundleOf bE) =
          (DY.Libsignal.Composed.Refinement.le32 bE.regId ++ List.replicate 38 0#8) ++
            (DY.Libsignal.Composed.Refinement.le32 bE.spkId ++
              (djbKey bE.spkPub ++ (bE.spkSig.toList ++
                (DY.Libsignal.Composed.Refinement.le32 bE.kpkId ++
                  (CryptoVerification.E2E.kyberKey bE.kpkPub ++
                    (bE.kpkSig.toList ++ djbKey bE.idPub)))))) by
          rw [hblob]; simp [List.append_assoc],
        slice_mid _ _ _ (by simp [hlen_le32]) (hlen_le32 _), decodeLe32_comp_le32]
    · unfold DY.Libsignal.PQXDH.Refinement.BundleBlob.kpkId
      rw [show bundleBlob (publicBundleOf bE) =
          (DY.Libsignal.Composed.Refinement.le32 bE.regId ++ List.replicate 38 0#8 ++
            DY.Libsignal.Composed.Refinement.le32 bE.spkId ++ djbKey bE.spkPub ++ bE.spkSig.toList) ++
            (DY.Libsignal.Composed.Refinement.le32 bE.kpkId ++
              (CryptoVerification.E2E.kyberKey bE.kpkPub ++
                (bE.kpkSig.toList ++ djbKey bE.idPub))) by
          rw [hblob]; simp [List.append_assoc],
        slice_mid _ _ _ (by simp [hlen_le32, hlen_djb, hlen_sig]) (hlen_le32 _), decodeLe32_comp_le32]
  | some ik =>
    rcases ik with ⟨oid, okey⟩
    have hblob : bundleBlob (publicBundleOf bE) =
        DY.Libsignal.Composed.Refinement.le32 bE.regId ++ (1#8 ::
          (DY.Libsignal.Composed.Refinement.le32 oid ++
            (djbKey okey ++ (DY.Libsignal.Composed.Refinement.le32 bE.spkId ++
              (djbKey bE.spkPub ++ (bE.spkSig.toList ++
                (DY.Libsignal.Composed.Refinement.le32 bE.kpkId ++
                  (CryptoVerification.E2E.kyberKey bE.kpkPub ++
                    (bE.kpkSig.toList ++ djbKey bE.idPub))))))))) := by
      unfold bundleBlob publicBundleOf; rw [hopk]; simp [List.append_assoc]
    have hb1 : (bundleBlob (publicBundleOf bE))[4]? = some 1#8 := by
      rw [hblob, List.getElem?_append_right (by rw [hlen_le32]), hlen_le32]; rfl
    unfold DY.Libsignal.Composed.Refinement.bundlePreKeyIds
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · unfold DY.Libsignal.PQXDH.Refinement.BundleBlob.opkId
        DY.Libsignal.PQXDH.Refinement.BundleBlob.hasOpkByte
      simp only [hb1, beq_self_eq_true, ↓reduceIte, Option.map_some, Option.some.injEq]
      rw [show bundleBlob (publicBundleOf bE) =
          (DY.Libsignal.Composed.Refinement.le32 bE.regId ++ [1#8]) ++
            (DY.Libsignal.Composed.Refinement.le32 oid ++
              (djbKey okey ++ (DY.Libsignal.Composed.Refinement.le32 bE.spkId ++
                (djbKey bE.spkPub ++ (bE.spkSig.toList ++
                  (DY.Libsignal.Composed.Refinement.le32 bE.kpkId ++
                    (CryptoVerification.E2E.kyberKey bE.kpkPub ++
                      (bE.kpkSig.toList ++ djbKey bE.idPub)))))))) by
          rw [hblob]; simp [List.append_assoc],
        slice_mid _ _ _ (by simp [hlen_le32]) (hlen_le32 _), decodeLe32_comp_le32]
    · unfold DY.Libsignal.PQXDH.Refinement.BundleBlob.spkId
      rw [show bundleBlob (publicBundleOf bE) =
          (DY.Libsignal.Composed.Refinement.le32 bE.regId ++ [1#8] ++
            DY.Libsignal.Composed.Refinement.le32 oid ++ djbKey okey) ++
            (DY.Libsignal.Composed.Refinement.le32 bE.spkId ++
              (djbKey bE.spkPub ++ (bE.spkSig.toList ++
                (DY.Libsignal.Composed.Refinement.le32 bE.kpkId ++
                  (CryptoVerification.E2E.kyberKey bE.kpkPub ++
                    (bE.kpkSig.toList ++ djbKey bE.idPub)))))) by
          rw [hblob]; simp [List.append_assoc],
        slice_mid _ _ _ (by simp [hlen_le32, hlen_djb]) (hlen_le32 _), decodeLe32_comp_le32]
    · unfold DY.Libsignal.PQXDH.Refinement.BundleBlob.kpkId
      rw [show bundleBlob (publicBundleOf bE) =
          (DY.Libsignal.Composed.Refinement.le32 bE.regId ++ [1#8] ++
            DY.Libsignal.Composed.Refinement.le32 oid ++ djbKey okey ++
            DY.Libsignal.Composed.Refinement.le32 bE.spkId ++ djbKey bE.spkPub ++ bE.spkSig.toList) ++
            (DY.Libsignal.Composed.Refinement.le32 bE.kpkId ++
              (CryptoVerification.E2E.kyberKey bE.kpkPub ++
                (bE.kpkSig.toList ++ djbKey bE.idPub))) by
          rw [hblob]; simp [List.append_assoc],
        slice_mid _ _ _ (by simp [hlen_le32, hlen_djb, hlen_sig]) (hlen_le32 _), decodeLe32_comp_le32]

theorem initiateState_ok_post {interp : ExternInterpretation} {P : PEParams}
    (hext : ExternContractsHoldCli interp) (hagree : ModelAgree interp P)
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r)
    {st : PqParty} (hal : AlicePqParty interp r st) (hwf_st : PqxdhPartyInSpecDomain P st)
    {X : UnreachedPqxdhPrimitives} {bE : PreKeyBundleFields}
    (hhonDir : HonestBundleDir interp r (publicBundleOf bE))
    (tVec : List.Vector (BitVec 8) initiateTapeLen)
    {x : RecordExtras} {g : GhostState HwBytes}
    (hinit : initiateState X P st.party st.me bE tVec = some (x, g)) :
    let recState := encodeRecordUnderExtras (fun _ => x) g
    let bundle := bundleBlob (publicBundleOf bE)
    let ds := initiateDrawsOfCoins tVec.toList
    recState = DY.Libsignal.Composed.Refinement.recordBytes
      (Symbolic.Swarm.CREF.Cli.sessionToRecordRecPending (Symbolic.Swarm.CREF.Cli.pqSession x g)) ∧
    IniPure.AliceInitiatedV1PostPure interp r bundle ds recState ∧
    InitiatePureOutcome interp r bundle tVec.toList (some recState) ds := by
  intro recState bundle ds
  have hEq : ExternCryptoLawsHold interp := hext.1
  have hhon : HonestBundle interp r bundle := hhonDir.2
  obtain ⟨hspk_eq, hkpk_eq, hid_eq⟩ := honestBundle_publicBundleOf_fields hhon
  have htrust : st.trusts ⟨⟨bE.idPub⟩⟩ = true :=
    (alicePqParty_trusts_iff hal hEq bE).mpr hid_eq
  obtain ⟨_, _, _, hwf'⟩ := wfPq_after_initiateState hagree hEq hwf hal hwf_st htrust hinit
  let st' : PqParty := { st with peerId := some ⟨⟨bE.idPub⟩⟩, session := some (x, g) }
  have hsess' : st'.session = some (x, g) := rfl
  have hrec_pending : recState = DY.Libsignal.Composed.Refinement.recordBytes
      (Symbolic.Swarm.CREF.Cli.sessionToRecordRecPending (Symbolic.Swarm.CREF.Cli.pqSession x g)) :=
    Symbolic.Swarm.CREF.Cli.encodeRecordX_eq_recordBytesPending_of_wfPq hwf' hsess'
  have hcanon := Symbolic.Swarm.CREF.Cli.recordCanonical_Q_of_wfPq hwf' hsess'
  have hinScope := Symbolic.Swarm.CREF.Cli.recordInScopeP_of_wfPq hwf' hsess'
  have hscope := Symbolic.Swarm.CREF.Cli.recordScopeP_of_wfPq hwf' hsess'
  have hlen31 := encodeRecordX_initiateState_lt_2pow31 hinit
  have hlen62 : recState.length < 2 ^ 62 := by dsimp only [recState]; omega
  unfold initiateState at hinit
  rcases hik : SignalPqxdh.Model.initiateKeys (modelPrims X P)
      (initiateInput P st.me bE tVec) with _ | ⟨dk, hdr⟩
  · simp [hik] at hinit
  · rw [hik] at hinit; dsimp only at hinit
    obtain ⟨hbin, hek_out, hkemCt_out, hkdf_eq, hrk_l, hck_l, hpqr_l⟩ :=
      initiateKeys_ok_bridge hagree hEq hwf hal hhon X tVec hik
    unfold initializeInitiatorSession at hinit
    dsimp only [bind, Except.bind, pure, Except.pure] at hinit
    rcases hrc : rootCreateChain P.C (HKDF.bytesToKey32 (ofU8 dk.rootKey)) ⟨bE.spkPub⟩
        (KeyPair.generate P.C (HKDF.bytesToKey32 ((tVec.toList.drop 160).take 32))).privateKey with
      _ | ⟨rk1, ck1⟩
    · simp [hrc] at hinit
    · rw [hrc] at hinit
      simp only [Option.some.injEq, Prod.mk.injEq] at hinit
      rcases hinit with ⟨hx_eq, hg_eq⟩
      let g0 : Ghost := ⟨fun _ _ => [], fun _ => []⟩
      let S0 : OpaqueSymbolSemantics := compSemOf interp r
      let agr0 := aliceLitAgreement r bundle ds
      have hopk0 :
          ((if bundle[4]? = some 1#8 then some (hwLit (slice bundle 10 32)) else none).map
            (gamma interp S0 g0)) =
          if bundle[4]? = some 1#8 then some (slice bundle 10 32) else none := by
        split_ifs
        · exact congrArg some (gamma_hwLit interp S0 g0 (slice bundle 10 32))
        · rfl
      have hdh1 : gamma interp S0 g0 (DY.DiffieHellman.dhPk (hwLit (secretBytes r 1))) =
          pubBytes interp (secretBytes r 1) := by
        rw [TR.gamma_dhPk, gamma_hwLit, pubBytes]
      have hdh2 : gamma interp S0 g0 (DY.DiffieHellman.dhPk (hwLit (secretBytes r 2))) =
          pubBytes interp (secretBytes r 2) := by
        rw [TR.gamma_dhPk, gamma_hwLit, pubBytes]
      obtain ⟨hγ_ct, hγ_rk, hγ_ck, hγ_pqr⟩ :=
        comp_gamma_aliceAgreement interp hEq r g0 bundle ds
          (gamma_hwLit interp S0 g0 (secretBytes r 0))
          (gamma_hwLit interp S0 g0 (ds.getD 0 []))
          hdh1 hdh2
          (gamma_hwLit interp S0 g0 (r.opaqueBytes (setupPublic r 6)))
          hopk0
          (gamma_hwLit interp S0 g0 (entropyBytes ds))
      have hrk_bytes : ofU8 dk.rootKey = gamma interp S0 g0 agr0.2.rk := by
        have := congrArg Prod.fst hkdf_eq
        exact this.trans hγ_rk.symm
      have hck_bytes : ofU8 dk.chainKey = gamma interp S0 g0 agr0.2.ck := by
        have := congrArg (fun p => p.2.1) hkdf_eq
        exact this.trans hγ_ck.symm
      have hpqr_bytes : ofU8 dk.pqrKey = gamma interp S0 g0 agr0.2.pqr := by
        have := congrArg (fun p => p.2.2) hkdf_eq
        exact this.trans hγ_pqr.symm
      have hct_bytes : (u8Vec 1568 hdr.kemCt).toList = gamma interp S0 g0 agr0.1 :=
        hkemCt_out.trans hγ_ct.symm
      have hds33_eq : ds.getD 33 [] = (tVec.toList.drop 160).take 32 :=
        initiateDrawsOfCoins_getD_33 tVec.toList
      have hds33_len : (ds.getD 33 []).length = 32 := by
        rw [hds33_eq]; simp [tVec.toList_length, initiateTapeLen]
      have hkp33_eq : KeyPair.generate P.C (HKDF.bytesToKey32 ((tVec.toList.drop 160).take 32)) =
          keyPairOf P.C (vec32 (ds.getD 33 [])) := by
        rw [← hds33_eq]
        exact keyPair_generate_bytesToKey32_eq_keyPairOf P.C hds33_len
      obtain ⟨hsend_priv, hsend_pub⟩ := keyPairOf_vec32_priv_pub hagree hds33_len
      have hrc' : rootCreateChain (cryptoOf' interp P.C.E P.C.D)
          (HKDF.bytesToKey32 (ofU8 dk.rootKey)) ⟨bE.spkPub⟩
          ⟨Ratchet.clampScalar (vec32 (ds.getD 33 []))⟩ = .ok (rk1, ck1) := by
        rw [← crypto_eq_cryptoOf'_of_modelAgree hagree]
        rw [hkp33_eq] at hrc
        exact hrc
      have heph_cl : (Ratchet.clampScalar (vec32 (ds.getD 33 []))).toList = clamp (ds.getD 33 []) := by
        rw [clampScalar_toList_eq_composedClamp,
            Proofs.libsignal.Hooks2.vec32_toList_of_length_32' _ hds33_len]
      obtain ⟨hck1_idx, hrk1_γ_pq, hck1_γ⟩ :=
        rootCreateChain_eq_gamma_createChain_aliceLit interp hEq r bundle ds
          (ofU8 dk.rootKey) ⟨bE.spkPub⟩ (vec32 (ds.getD 33 [])) rk1 ck1
          hrk_bytes hrk_l hspk_eq heph_cl hrc'
      have hrk1_γ_tr : HMAC.keyToBytes32 rk1 =
          gamma interp S0 g0
            (DY.Libsignal.TripleRatchet.createChain agr0.2.rk
              (DY.DiffieHellman.dhPk (hwLit (secretBytes r 2)))
              (hwLit (ds.getD 33 []))).1 := by
        rw [hrk1_γ_pq, gamma_createChain_fst interp hEq S0 g0,
            IniPure.gamma_tr_createChain_fst interp hEq S0 g0]
      have hpqBytes_eq : (pqxdhSpqrSession P).init .a2b (HKDF.bytesToKey32 (ofU8 dk.pqrKey)) =
          S0.init (gamma interp S0 g0 agr0.2.pqr) [0#8] := by
        rw [hpqr_bytes]
        exact spqrPq_init_a2b_eq_compSemOf hagree r (hpqr_l ▸ hpqr_bytes ▸ rfl)
      have hsess_eq : Symbolic.Swarm.CREF.Cli.pqSession x g =
          aliceInitiatedSessionV1
            ⟨(keyPairOf P.C st.me.idPriv).publicKey⟩ ⟨⟨bE.idPub⟩⟩ ⟨bE.spkPub⟩
            ⟨u8Vec 32 hdr.ekAPk⟩ rk1 (HKDF.bytesToKey32 (ofU8 dk.chainKey))
            (keyPairOf P.C (vec32 (ds.getD 33 []))) ck1 (bE.opk.map Prod.fst)
            bE.spkId bE.kpkId bE.regId r.regIdA
            (DY.Libsignal.Composed.Refinement.kyberKey (gamma interp S0 g0 agr0.1))
            (S0.init (gamma interp S0 g0 agr0.2.pqr) [0#8]) := by
        subst hx_eq hg_eq
        rw [hkp33_eq, hpqBytes_eq]
        have hregA : st.me.regId = r.regIdA := by rw [hal.me_eq]
        have hkyb_eq : CryptoVerification.E2E.kyberKey (u8Vec 1568 hdr.kemCt) =
            DY.Libsignal.Composed.Refinement.kyberKey (gamma interp S0 g0 agr0.1) := by
          unfold CryptoVerification.E2E.kyberKey DY.Libsignal.Composed.Refinement.kyberKey
          rw [hct_bytes]
        unfold Symbolic.Swarm.CREF.Cli.pqSession aliceInitiatedSessionV1 aliceInitiatedStateV1
          initiatorRecordExtras
        simp [SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
          SessionState.setUnacknowledgedPreKeyMessage, currentVersion, maxReceiverChains,
          hregA, hkyb_eq]
      have hour_ser : (⟨(keyPairOf P.C st.me.idPriv).publicKey⟩ : IdentityKey).serialize =
          ecKey (pubBytes interp (secretBytes r 0)) := by
        rw [hal.me_eq]
        simpa [IdentityKey.serialize, PublicKey.serialize, djbKey, djbType] using
          keyPairOf_alice_pubKey_eq hagree hwf
      have htheir_ser : (⟨⟨bE.idPub⟩⟩ : IdentityKey).serialize =
          ecKey (pubBytes interp (secretBytes r 1)) := by
        unfold IdentityKey.serialize PublicKey.serialize djbType ecKey
        rw [hid_eq]; rfl
      have hbase_ser : (⟨u8Vec 32 hdr.ekAPk⟩ : PublicKey).serialize =
          ecKey (pubBytes interp (ds.getD 0 [])) := by
        unfold PublicKey.serialize djbType ecKey
        rw [hek_out]; rfl
      have hspk_ser : (⟨bE.spkPub⟩ : PublicKey).serialize =
          ecKey (pubBytes interp (secretBytes r 2)) := by
        unfold PublicKey.serialize djbType ecKey
        rw [hspk_eq]; rfl
      have hck0_γ : HMAC.keyToBytes32 (HKDF.bytesToKey32 (ofU8 dk.chainKey)) =
          gamma interp S0 g0 agr0.2.ck := by
        rw [keyToBytes32_bytesToKey32_of_length_eq_32 _ hck_l, hck_bytes]
      have hV1 : IniPure.AliceInitiatedV1PostPure interp r bundle ds recState := by
        refine ⟨⟨(keyPairOf P.C st.me.idPriv).publicKey⟩, ⟨⟨bE.idPub⟩⟩, ⟨bE.spkPub⟩,
          ⟨u8Vec 32 hdr.ekAPk⟩, rk1, HKDF.bytesToKey32 (ofU8 dk.chainKey),
          keyPairOf P.C (vec32 (ds.getD 33 [])), ck1, bE.opk.map Prod.fst,
          bE.spkId, bE.kpkId, bE.regId, ?_⟩
        rw [← hsess_eq]
        exact ⟨hcanon, hinScope, hscope, hlen62, hour_ser, htheir_ser, hbase_ser,
          hsend_pub, hck1_idx, hck1_γ, hrk1_γ_tr, hsend_priv, hspk_ser, hck0_γ,
          (bundlePreKeyIds_bundleBlob_publicBundleOf bE).symm⟩
      exact ⟨hrec_pending, hV1, ⟨tVec.toList_length, rfl, hhon, hbin, hV1⟩⟩

end Symbolic.Swarm.CREF.Cli.Slots
