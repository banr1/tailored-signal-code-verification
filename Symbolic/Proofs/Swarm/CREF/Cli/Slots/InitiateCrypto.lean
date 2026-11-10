/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Slots.InitiateDefs
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.InitiateShaHmac
import Symbolic.Proofs.Swarm.CREF.TR.SkippedVarLit

/-!
# CLI `init` Cryptographic Handshake and Honest Bundle Bridge

Connects `SignalPqxdh.Model.initiateKeys` under `ModelAgree`,
`ExternCryptoLawsHold`, `ProtocolSetupWF`, `AlicePqParty`, and `HonestBundle` to
the symbolic handshake byte terms (`IniOkBin`, `kemEncapCtBytes`,
`aliceLitIkmBytes`, and `pqxdhKdfBytes`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.Cli.Slots
open Symbolic.Swarm.CREF.CliPure

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.Refinement (ExternCryptoLawsHold sha256CompressFunction)
open DY.Libsignal.TripleRatchet (x25519LowOrder)
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.E2E
open CryptoVerification.SignalSession
open Symbolic.Swarm.CREF (IniOkBin BundleOpkAccepted entropyBytes kemEncapCtBytes kemEncapSSBytes aliceLitIkmBytes clamp_clamp)
open Symbolic.Swarm.CREF.TR (dhAgreeBytes pqxdhIkmBytes pqxdhKdfBytes)

/-! ## `HonestBundle` slice extraction on `PreKeyBundleFields` -/

private theorem slice_mid {pre mid suf : HwBytes} {off n : Nat}
    (hpre : pre.length = off) (hmid : mid.length = n) :
    slice (pre ++ (mid ++ suf)) off n = mid := by
  unfold slice
  subst hpre hmid
  rw [List.drop_left, List.take_append_of_le_length (Nat.le_refl _),
      List.take_of_length_le (Nat.le_refl _)]

private theorem bE_opk_bytes_len (bE : PreKeyBundleFields) :
    (match bE.opk with
     | some (i, k) => 1#8 :: CryptoVerification.LibsignalAesCbc.toLEBytes 4 i ++ djbKey k
     | none => 0#8 :: List.replicate 37 0#8).length = 38 := by
  cases bE.opk with
  | none => simp
  | some ik =>
    rcases ik with ⟨i, k⟩
    simp [djbKey, CryptoVerification.LibsignalAesCbc.toLEBytes]

theorem bE_bytes_opk_slices (bE : PreKeyBundleFields) :
    (match bE.opk with
     | none => (bundleBlob (publicBundleOf bE))[4]? = some 0#8
     | some (_, k) =>
       (bundleBlob (publicBundleOf bE))[4]? = some 1#8 ∧
       (bundleBlob (publicBundleOf bE))[9]? = some 0x05#8 ∧
       slice (bundleBlob (publicBundleOf bE)) 10 32 = k.toList) := by
  rw [bundleBlob_publicBundleOf]
  unfold PreKeyBundleFields.bytes
  cases hopk : bE.opk with
  | none =>
    simp [CryptoVerification.LibsignalAesCbc.toLEBytes]
  | some ik =>
    rcases ik with ⟨oid, k⟩
    dsimp only
    have h4 : (CryptoVerification.LibsignalAesCbc.toLEBytes 4 bE.regId ++
        (1#8 :: CryptoVerification.LibsignalAesCbc.toLEBytes 4 oid ++ djbKey k) ++
        CryptoVerification.LibsignalAesCbc.toLEBytes 4 bE.spkId ++ djbKey bE.spkPub ++
        bE.spkSig.toList ++ CryptoVerification.LibsignalAesCbc.toLEBytes 4 bE.kpkId ++
        CryptoVerification.E2E.kyberKey bE.kpkPub ++ bE.kpkSig.toList ++ djbKey bE.idPub)[4]? =
        some 1#8 := by
      simp [CryptoVerification.LibsignalAesCbc.toLEBytes, List.append_assoc]
    have h9 : (CryptoVerification.LibsignalAesCbc.toLEBytes 4 bE.regId ++
        (1#8 :: CryptoVerification.LibsignalAesCbc.toLEBytes 4 oid ++ djbKey k) ++
        CryptoVerification.LibsignalAesCbc.toLEBytes 4 bE.spkId ++ djbKey bE.spkPub ++
        bE.spkSig.toList ++ CryptoVerification.LibsignalAesCbc.toLEBytes 4 bE.kpkId ++
        CryptoVerification.E2E.kyberKey bE.kpkPub ++ bE.kpkSig.toList ++ djbKey bE.idPub)[9]? =
        some 0x05#8 := by
      simp [djbKey, CryptoVerification.LibsignalAesCbc.toLEBytes, List.append_assoc]
    refine ⟨h4, h9, ?_⟩
    let pre := CryptoVerification.LibsignalAesCbc.toLEBytes 4 bE.regId ++
      (1#8 :: CryptoVerification.LibsignalAesCbc.toLEBytes 4 oid) ++ [0x05#8]
    let suf := CryptoVerification.LibsignalAesCbc.toLEBytes 4 bE.spkId ++ djbKey bE.spkPub ++
      bE.spkSig.toList ++ CryptoVerification.LibsignalAesCbc.toLEBytes 4 bE.kpkId ++
      CryptoVerification.E2E.kyberKey bE.kpkPub ++ bE.kpkSig.toList ++ djbKey bE.idPub
    have hassoc : CryptoVerification.LibsignalAesCbc.toLEBytes 4 bE.regId ++
        (1#8 :: CryptoVerification.LibsignalAesCbc.toLEBytes 4 oid ++ djbKey k) ++
        CryptoVerification.LibsignalAesCbc.toLEBytes 4 bE.spkId ++ djbKey bE.spkPub ++
        bE.spkSig.toList ++ CryptoVerification.LibsignalAesCbc.toLEBytes 4 bE.kpkId ++
        CryptoVerification.E2E.kyberKey bE.kpkPub ++ bE.kpkSig.toList ++ djbKey bE.idPub =
        pre ++ (k.toList ++ suf) := by
      simp [pre, suf, djbKey, List.append_assoc]
    rw [hassoc]
    exact slice_mid (by simp [pre, CryptoVerification.LibsignalAesCbc.toLEBytes]) (k.toList_length)

theorem honestBundle_publicBundleOf_fields {interp : ExternInterpretation} {r : ProtocolSetup}
    {bE : PreKeyBundleFields} (hhon : HonestBundle interp r (bundleBlob (publicBundleOf bE))) :
    bE.spkPub.toList = pubBytes interp (secretBytes r 2) ∧
    bE.kpkPub.toList = r.opaqueBytes (setupPublic r 6) ∧
    bE.idPub.toList = pubBytes interp (secretBytes r 1) := by
  obtain ⟨hspk, _, hkpk, _, hid⟩ := hhon (bundleBlob_publicBundleOf_length bE)
  rw [bundleBlob_publicBundleOf] at hspk hkpk hid
  let opkB := match bE.opk with
    | some (i, k) => 1#8 :: CryptoVerification.LibsignalAesCbc.toLEBytes 4 i ++ djbKey k
    | none => 0#8 :: List.replicate 37 0#8
  have hopk_len : opkB.length = 38 := bE_opk_bytes_len bE
  have hspk_sl : slice bE.bytes 46 33 = djbKey bE.spkPub := by
    let pre := CryptoVerification.LibsignalAesCbc.toLEBytes 4 bE.regId ++ opkB ++
      CryptoVerification.LibsignalAesCbc.toLEBytes 4 bE.spkId
    let suf := bE.spkSig.toList ++ CryptoVerification.LibsignalAesCbc.toLEBytes 4 bE.kpkId ++
      CryptoVerification.E2E.kyberKey bE.kpkPub ++ bE.kpkSig.toList ++ djbKey bE.idPub
    have heq : bE.bytes = pre ++ (djbKey bE.spkPub ++ suf) := by
      unfold PreKeyBundleFields.bytes
      dsimp only [pre, suf, opkB]
      cases bE.opk <;> simp only [List.cons_append, List.append_assoc]
    rw [heq]
    exact slice_mid (by simp [pre, hopk_len, CryptoVerification.LibsignalAesCbc.toLEBytes])
      (by simp [djbKey])
  have hkpk_sl : slice bE.bytes 147 1569 = CryptoVerification.E2E.kyberKey bE.kpkPub := by
    let pre := CryptoVerification.LibsignalAesCbc.toLEBytes 4 bE.regId ++ opkB ++
      CryptoVerification.LibsignalAesCbc.toLEBytes 4 bE.spkId ++ djbKey bE.spkPub ++
      bE.spkSig.toList ++ CryptoVerification.LibsignalAesCbc.toLEBytes 4 bE.kpkId
    let suf := bE.kpkSig.toList ++ djbKey bE.idPub
    have heq : bE.bytes = pre ++ (CryptoVerification.E2E.kyberKey bE.kpkPub ++ suf) := by
      unfold PreKeyBundleFields.bytes
      dsimp only [pre, suf, opkB]
      cases bE.opk <;> simp only [List.cons_append, List.append_assoc]
    rw [heq]
    exact slice_mid
      (by simp [pre, hopk_len, djbKey, CryptoVerification.LibsignalAesCbc.toLEBytes])
      (by simp [CryptoVerification.E2E.kyberKey])
  have hid_sl : slice bE.bytes 1780 33 = djbKey bE.idPub := by
    let pre := CryptoVerification.LibsignalAesCbc.toLEBytes 4 bE.regId ++ opkB ++
      CryptoVerification.LibsignalAesCbc.toLEBytes 4 bE.spkId ++ djbKey bE.spkPub ++
      bE.spkSig.toList ++ CryptoVerification.LibsignalAesCbc.toLEBytes 4 bE.kpkId ++
      CryptoVerification.E2E.kyberKey bE.kpkPub ++ bE.kpkSig.toList
    have heq : bE.bytes = pre ++ (djbKey bE.idPub ++ []) := by
      unfold PreKeyBundleFields.bytes
      dsimp only [pre, opkB]
      cases bE.opk <;> simp only [List.cons_append, List.append_assoc, List.append_nil]
    rw [heq]
    exact slice_mid
      (by simp [pre, hopk_len, djbKey, CryptoVerification.E2E.kyberKey,
            CryptoVerification.LibsignalAesCbc.toLEBytes])
      (by simp [djbKey])
  dsimp only [DY.Libsignal.PQXDH.Refinement.BundleBlob.spkPub,
    DY.Libsignal.PQXDH.Refinement.BundleBlob.kpkPub,
    DY.Libsignal.PQXDH.Refinement.BundleBlob.ikPub] at hspk hkpk hid
  rw [hspk_sl] at hspk
  rw [hkpk_sl] at hkpk
  rw [hid_sl] at hid
  exact ⟨(List.cons.inj hspk).2, (List.cons.inj hkpk).2, (List.cons.inj hid).2⟩

/-! ## `Model.initiateKeys` bridge to symbolic handshake bytes -/

private theorem option_guard_eq_some {p : Prop} [Decidable p] {u : Unit} :
    (_root_.guard p : Option Unit) = some u ↔ p := by
  cases u
  by_cases hp : p <;> simp [_root_.guard, pure, hp]

private theorem ofU8_modelPrims_x25519 {interp : ExternInterpretation} {P : PEParams}
    (hagree : ModelAgree interp P) (X : UnreachedPqxdhPrimitives)
    {sk pk : SignalPqxdh.Bytes} (hsk : sk.length = 32) (hpk : pk.length = 32) :
    ofU8 ((modelPrims X P).x25519 sk pk) = dhAgreeBytes interp (ofU8 sk) (ofU8 pk) := by
  change ofU8 (vecU8 (P.C.X (Ratchet.clampScalar (u8Vec 32 sk)) (u8Vec 32 pk))) = _
  rw [ofU8_vecU8]
  have hcl : (Ratchet.clampScalar (u8Vec 32 sk)).toList = clamp (ofU8 sk) := by
    rw [clampScalar_toList_eq_composedClamp, u8Vec_toList_of_len hsk]
  have hpkl : (u8Vec 32 pk).toList = ofU8 pk := u8Vec_toList_of_len hpk
  have hag := hagree.2.2.2.1 (Ratchet.clampScalar (u8Vec 32 sk)) (u8Vec 32 pk)
  rw [hcl, hpkl] at hag
  unfold dhAgreeBytes
  rw [hag, Option.getD_some]

theorem initiateKeys_ok_bridge {interp : ExternInterpretation} {P : PEParams}
    (hagree : ModelAgree interp P) (hEq : ExternCryptoLawsHold interp)
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r) {st : PqParty} (hal : AlicePqParty interp r st)
    {bE : PreKeyBundleFields} (hhon : HonestBundle interp r (bundleBlob (publicBundleOf bE)))
    (X : UnreachedPqxdhPrimitives) (tVec : List.Vector (BitVec 8) initiateTapeLen)
    {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    (hinit : SignalPqxdh.Model.initiateKeys (modelPrims X P)
      (initiateInput P st.me bE tVec) = some (dk, hdr)) :
    let bundle := bundleBlob (publicBundleOf bE)
    let ds := initiateDrawsOfCoins tVec.toList
    IniOkBin bundle ds ∧
    (u8Vec 32 hdr.ekAPk).toList = pubBytes interp (ds.getD 0 []) ∧
    (u8Vec 1568 hdr.kemCt).toList =
      kemEncapCtBytes interp (r.opaqueBytes (setupPublic r 6)) (entropyBytes ds) ∧
    (ofU8 dk.rootKey, ofU8 dk.chainKey, ofU8 dk.pqrKey) =
      pqxdhKdfBytes (sha256CompressFunction interp) (aliceLitIkmBytes interp r bundle ds) ∧
    (ofU8 dk.rootKey).length = 32 ∧
    (ofU8 dk.chainKey).length = 32 ∧
    (ofU8 dk.pqrKey).length = 32 := by
  intro bundle ds
  obtain ⟨hspk_eq, hkpk_eq, hid_eq⟩ := honestBundle_publicBundleOf_fields hhon
  have ht_len : tVec.toList.length = 192 := tVec.toList_length
  unfold SignalPqxdh.Model.initiateKeys at hinit
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, option_guard_eq_some] at hinit
  obtain ⟨⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟨ss, kemCt⟩, hkem, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, hopt4, hdr_eq⟩⟩ := hinit
  injection hdr_eq with hdr_pair
  injection hdr_pair with hdk_eq hhdr_eq
  let M := modelPrims X P
  let inp := initiateInput P st.me bE tVec
  have hkem' : M.kemEncaps inp.bundle.pqspkB inp.kemCoins = some (ss, kemCt) := hkem
  have hpkLen : ((vecU8 bE.kpkPub).length == SignalPqxdh.kyberPkLen) = true := by
    simp [vecU8, toU8, SignalPqxdh.kyberPkLen]
  dsimp only [M, modelPrims, blockLevelPrims, inp, initiateInput] at hkem'
  simp only [hpkLen, ↓reduceIte] at hkem'
  change (let (ct, ss) := P.Q.encaps (u8Vec 1568 (vecU8 bE.kpkPub)) (u8Vec 32 (vecU8 (initiateKemCoins tVec)))
    some (vecU8 ss, vecU8 ct)) = some (ss, kemCt) at hkem'
  rw [u8Vec_vecU8, u8Vec_vecU8] at hkem'
  injection hkem' with hss_ct
  injection hss_ct with hss_eq hct_eq
  have henc_ag := hagree.2.2.2.2.2.1 bE.kpkPub (initiateKemCoins tVec)
  have hent_eq : entropyBytes ds = (initiateKemCoins tVec).toList :=
    entropyBytes_initiateDrawsOfCoins tVec
  have hent_len : (entropyBytes ds).length = 32 := by simp [entropyBytes]
  have hct_sym : kemEncapCtBytes interp (r.opaqueBytes (setupPublic r 6)) (entropyBytes ds) =
      (P.Q.encaps bE.kpkPub (initiateKemCoins tVec)).1.toList := by
    unfold kemEncapCtBytes
    simp only [hent_len, ↓reduceIte]
    rw [← hkpk_eq, hent_eq, henc_ag, Option.getD_some,
        List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
  have hss_sym : kemEncapSSBytes interp r (r.opaqueBytes (setupPublic r 6)) (entropyBytes ds) =
      (P.Q.encaps bE.kpkPub (initiateKemCoins tVec)).2.toList := by
    unfold kemEncapSSBytes
    simp only [hent_len, ↓reduceIte]
    rw [← hkpk_eq, hent_eq, henc_ag, Option.getD_some,
        List.drop_left' (by simp)]
  have hkemCt_out : (u8Vec 1568 hdr.kemCt).toList =
      kemEncapCtBytes interp (r.opaqueBytes (setupPublic r 6)) (entropyBytes ds) := by
    rw [← hhdr_eq]; dsimp only
    rw [← hct_eq, u8Vec_vecU8, hct_sym]
  have hek_out : (u8Vec 32 hdr.ekAPk).toList = pubBytes interp (ds.getD 0 []) := by
    rw [← hhdr_eq]; dsimp only
    change (u8Vec 32 (vecU8 (P.C.pubKey
      (Ratchet.clampScalar (u8Vec 32 (toU8 (tVec.toList.take 32))))))).toList = _
    rw [u8Vec_vecU8]
    have hu8_ek : (u8Vec 32 (toU8 (tVec.toList.take 32))).toList = ds.getD 0 [] := by
      rw [u8Vec_toList_of_len (by simp [ht_len]), ofU8_toU8]; rfl
    have hcl_ek : (Ratchet.clampScalar (u8Vec 32 (toU8 (tVec.toList.take 32)))).toList =
        clamp (ds.getD 0 []) := by
      rw [clampScalar_toList_eq_composedClamp, hu8_ek]
    have hpub := hagree.2.2.2.2.1 (Ratchet.clampScalar (u8Vec 32 (toU8 (tVec.toList.take 32))))
    rw [hcl_ek] at hpub
    unfold pubBytes
    rw [hpub, Option.getD_some]
  have hdh1 : ofU8 (M.x25519 inp.ikASk inp.bundle.spkB) =
      dhAgreeBytes interp (secretBytes r 0) (pubBytes interp (secretBytes r 2)) := by
    dsimp only [inp, initiateInput]
    rw [hal.me_eq]
    rw [ofU8_modelPrims_x25519 hagree X (by simp [vecU8]) (by simp [vecU8]),
        ofU8_vecU8, ofU8_vecU8, hspk_eq]
    unfold keyPairOf dhAgreeBytes
    dsimp only
    have hvec0 : (vec32 (secretBytes r 0)).toList = secretBytes r 0 :=
      Proofs.libsignal.Hooks2.vec32_toList_of_length_32' _ (secretBytes_0_length hwf)
    rw [clampScalar_toList_eq_composedClamp, hvec0, clamp_clamp]
  have hdh2 : ofU8 (M.x25519 inp.ekASk inp.bundle.ikB) =
      dhAgreeBytes interp (ds.getD 0 []) (pubBytes interp (secretBytes r 1)) := by
    dsimp only [inp, initiateInput]
    rw [ofU8_modelPrims_x25519 hagree X (by simp [ht_len]) (by simp [vecU8]),
        ofU8_toU8, ofU8_vecU8, hid_eq]
    rfl
  have hdh3 : ofU8 (M.x25519 inp.ekASk inp.bundle.spkB) =
      dhAgreeBytes interp (ds.getD 0 []) (pubBytes interp (secretBytes r 2)) := by
    dsimp only [inp, initiateInput]
    rw [ofU8_modelPrims_x25519 hagree X (by simp [ht_len]) (by simp [vecU8]),
        ofU8_toU8, ofU8_vecU8, hspk_eq]
    rfl
  have hopk_sl := bE_bytes_opk_slices bE
  have hopkB : inp.bundle.opkB? = bE.opk.map fun (i, k) => (u32 i, vecU8 k) := rfl
  have ⟨hopk_acc, hsec_eq⟩ : BundleOpkAccepted bundle ∧
      ofU8 (SignalPqxdh.buildSecrets
        (M.x25519 inp.ikASk inp.bundle.spkB)
        (M.x25519 inp.ekASk inp.bundle.ikB)
        (M.x25519 inp.ekASk inp.bundle.spkB)
        (inp.bundle.opkB?.map fun (_, opkPk) => M.x25519 inp.ekASk opkPk) ss) =
      aliceLitIkmBytes interp r bundle ds := by
    cases hopk : bE.opk with
    | none =>
      rw [hopk] at hopk_sl hopkB
      have hb4_not1 : bundle[4]? ≠ some 1#8 := by rw [hopk_sl]; decide
      refine ⟨Or.inl hopk_sl, ?_⟩
      rw [hopkB]
      unfold SignalPqxdh.buildSecrets aliceLitIkmBytes pqxdhIkmBytes
      simp only [Option.map_none, hb4_not1, ↓reduceIte, ofU8_append, ofU8_f_x25519_eq,
        hdh1, hdh2, hdh3, ← hss_eq, ofU8_vecU8, hss_sym, List.append_assoc]
    | some ik =>
      rcases ik with ⟨oid, okVec⟩
      rw [hopk] at hopk_sl hopkB
      obtain ⟨hb4, hb9, hsl10⟩ := hopk_sl
      have hdh4 : ofU8 (M.x25519 inp.ekASk (vecU8 okVec)) =
          dhAgreeBytes interp (ds.getD 0 []) okVec.toList := by
        dsimp only [inp, initiateInput]
        rw [ofU8_modelPrims_x25519 hagree X (by simp [ht_len]) (by simp [vecU8]),
            ofU8_toU8, ofU8_vecU8]
        rfl
      have hopt4' : SignalPqxdh.dhOptNonZero
          (inp.bundle.opkB?.map fun (_, opkPk) => M.x25519 inp.ekASk opkPk) = true := hopt4
      rw [hopkB] at hopt4'
      simp only [Option.map_some, SignalPqxdh.dhOptNonZero, bne_iff_ne] at hopt4'
      have hdh4_nz : dhAgreeBytes interp (ds.getD 0 []) okVec.toList ≠ List.replicate 32 0#8 := by
        intro hzero
        apply hopt4'
        have := congrArg toU8 (hdh4.trans hzero)
        rw [toU8_ofU8] at this
        simpa [toU8] using this
      have hcl_len : (clamp (ds.getD 0 [])).length = 32 := by
        unfold clamp
        dsimp only [ds]
        rw [initiateDrawsOfCoins_getD_0]
        simp [ht_len]
      have hnot_low_key : DY.X25519.isLowOrderKey (okVec.toList.map BitVec.toNat) = false := by
        cases hlow : DY.X25519.isLowOrderKey (okVec.toList.map BitVec.toNat)
        · rfl
        · exfalso
          exact hdh4_nz ((hEq.x25519_agreement_zero_iff_low_order _ _ hcl_len
            okVec.toList_length).mpr hlow)
      let S0 := compSemOf interp r
      let g0 : DY.Libsignal.Composed.Refinement.Ghost := ⟨fun _ _ => [], fun _ => []⟩
      have hγ_lit : gamma interp S0 g0 (DY.Libsignal.Composed.Refinement.litOf okVec.toList) =
          okVec.toList :=
        Symbolic.Swarm.CREF.gamma_compHwLit interp S0 g0 okVec.toList
      have hnot_low : x25519LowOrder
          (DY.Libsignal.Composed.Refinement.litOf (slice bundle 10 32)) = false := by
        rw [hsl10]
        exact Symbolic.Swarm.CREF.TR.RecvDecStep.SkippedVarLit.x25519LowOrder_false_of_gamma_eq_notLow
          interp S0 g0 hEq rfl (by rw [hγ_lit]; exact hnot_low_key)
      refine ⟨Or.inr ⟨hb4, hb9, hnot_low⟩, ?_⟩
      rw [hopkB]
      unfold SignalPqxdh.buildSecrets aliceLitIkmBytes pqxdhIkmBytes
      dsimp only [bundle]
      simp only [Option.map_some, hb4, ↓reduceIte, hsl10, ofU8_append, ofU8_f_x25519_eq,
        hdh1, hdh2, hdh3, hdh4, ← hss_eq, ofU8_vecU8, hss_sym, List.append_assoc]
  have hbin : IniOkBin bundle ds :=
    ⟨initiateDrawsOfCoins_lengths ht_len, bundleBlob_publicBundleOf_length bE, hopk_acc⟩
  obtain ⟨hkdf_eq, hrk_l, hck_l, hpqr_l⟩ :=
    ofU8_hkdfDerive96_modelPrims X P
      (SignalPqxdh.buildSecrets
        (M.x25519 inp.ikASk inp.bundle.spkB)
        (M.x25519 inp.ekASk inp.bundle.ikB)
        (M.x25519 inp.ekASk inp.bundle.spkB)
        (inp.bundle.opkB?.map fun (_, opkPk) => M.x25519 inp.ekASk opkPk) ss)
  rw [hdk_eq] at hkdf_eq hrk_l hck_l hpqr_l
  rw [hsec_eq, hagree.1] at hkdf_eq
  exact ⟨hbin, hek_out, hkemCt_out, hkdf_eq, hrk_l, hck_l, hpqr_l⟩

end Symbolic.Swarm.CREF.Cli.Slots
