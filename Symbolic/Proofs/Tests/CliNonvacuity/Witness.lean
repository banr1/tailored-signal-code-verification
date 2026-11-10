/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Tests.Nonvacuity.SetupTrace
public import Symbolic.Proofs.Tests.CliNonvacuity.Defs
public import Symbolic.Proofs.Swarm.CREF.Sem
public import Symbolic.Proofs.Tests.CliNonvacuity.WitnessBase
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.ALaCarte.Ordering
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic

/-!
# Provisioning Setup, Plaintexts, and `keySetupTrace` Reachability

Defines uniform output-length lemmas for `myInterp` on `assumedInjective` primitives, the concrete
`ProtocolSetup`, `OpaqueSymbolSemantics`, and 9-byte ASCII plaintexts (`pt0`, `pt1`, `ptReply0`,
`pt2`) shared across the CLI non-vacuity suite, `not_kyberMismatch_myInterp`, and
`cliReachable_keySetupTrace`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.Witness

open DY
open CryptoProofLib.Refinement (ByteString ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement
  (ExternCryptoLawsHold sha256CompressFunction sha256CompressSymbol x25519AgreementSymbol
   x25519PublicKeySymbol x25519TorsionSymbol aesCbcEncryptSymbol aesCbcDecryptSymbol torsionShift)
open DY.Libsignal.PQXDH.Refinement
  (kyberEncapsSymbol kyberDecapsSymbol sha512CompressSymbol toEdwardsSymbol edwardsCompressSymbol
   edwardsNegSymbol torsionFreeSymbol doubleScalarMulSymbol scalarModOrderSymbol
   scalarModOrderWideSymbol mlkem768FromSeedSymbol mlkem768ValidatePkSymbol
   mlkem768Encaps1Symbol mlkem768Encaps2Symbol mlkem768DecapsSymbol libcruxHmacSymbol)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost GhostAndSemMatchSetup MatchesEventsAt MatchesEvents
   ExternInterpretationTotalOnUsedSymbols ReturnsLength ProtocolSetupWF
   PreKeyFields KyberMismatch kyberKey kyberEncapsBytes kyberDecapsBytes
   gamma gamma' concretizeAll concretizeRandom concretizeLit concretizeConcat
   concretizeKemPk concretizeSign node ofByteArray
   setupRandomsAt setupPublic slice randTerm)
open DY.Libsignal.Composed.Refinement.Cli
  (ExternContractsHoldCli HooksMatchInterpretation ModelAgree CliTurn initDirs CliTraces
   runFnToRelation)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.SignalSession (CliRun CliHooks CliSpecPqxdh)
open Symbolic.Tests.Nonvacuity (keySetupTrace)
open Symbolic.Proofs.Tests.CliNonvacuity.Defs
  (CliTraceReachableProof modelRunWF_nil invertsGuarded_of_noInverts)
open Symbolic.Proofs.Tests.Refinement.Cli
  (cliWitnessInterp cliWitnessInterp_total cliWitnessInterp_contracts
   cliWitnessHooks cliWitnessHooks_agree)
open Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers (nvMlKem)
open Symbolic.Proofs.Swarm.WIT.Pure
  (exampleAgreement exampleBasepoint length_exampleAgreement
   exampleInterpretation witnessInterpretation_of_none)
open Symbolic.Swarm.CREF
  (compSemOf b1_setupRandomsAt_eq b1_setupPublic_5 b1_setupPublic_6 b1_setupPublic_7)
open Symbolic.Swarm.CREF.Cli
  (isSpqrOrHmacSymbol interpOfParams interpOfParams_other
   externContractsHoldCli_interpOfParams modelAgree_interpOfParams hmacFnOf_interpOfParams)
open Symbolic.Swarm.TRREF.SpqrSemOf (bytesToVec)

private theorem torsionShift_myBaseInterp (pt : ByteString) (t : Fin 8) :
    torsionShift myBaseInterp pt t = pt := by
  unfold torsionShift
  split
  · rfl
  · have ht : myBaseInterp x25519TorsionSymbol [pt, [BitVec.ofNat 8 t.val]] = none := by
      rw [myBaseInterp_other (by decide)]
      simp only [cliWitnessInterp,
        show x25519TorsionSymbol ≠ aesCbcEncryptSymbol by decide,
        show x25519TorsionSymbol ≠ aesCbcDecryptSymbol by decide, ↓reduceIte]
      rw [witnessInterpretation_of_none (by decide)]
      simp [exampleInterpretation, x25519PublicKeySymbol, x25519AgreementSymbol,
        aesCbcEncryptSymbol, aesCbcDecryptSymbol, x25519TorsionSymbol]
    rw [ht]

private theorem myBaseInterp_contracts : ExternContractsHoldCli myBaseInterp := by
  rcases cliWitnessInterp_contracts with ⟨hce, hcan, _⟩
  have ha : myBaseInterp x25519AgreementSymbol = cliWitnessInterp x25519AgreementSymbol :=
    myBaseInterp_other (by decide)
  have hp : myBaseInterp x25519PublicKeySymbol = cliWitnessInterp x25519PublicKeySymbol :=
    myBaseInterp_other (by decide)
  have hm : myBaseInterp libcruxHmacSymbol = cliWitnessInterp libcruxHmacSymbol :=
    myBaseInterp_other (by decide)
  have hts : ∀ pt t, torsionShift myBaseInterp pt t = torsionShift cliWitnessInterp pt t := by
    intro pt t
    unfold torsionShift
    rw [myBaseInterp_other (by decide)]
  refine ⟨?_, ?_, ?_⟩
  · exact
      { x25519_agreement_commutes := fun a b => by
          simpa only [ha, hp] using hce.x25519_agreement_commutes a b
        x25519_agreement_length := fun s p => by
          simpa only [ha] using hce.x25519_agreement_length s p
        x25519_public_key_length := fun s => by
          simpa only [hp] using hce.x25519_public_key_length s
        x25519_agreement_reads_u_coordinate := fun s p p' hp1 hp2 hu => by
          simpa only [ha] using hce.x25519_agreement_reads_u_coordinate s p p' hp1 hp2 hu
        x25519_agreement_torsion_invariant := fun s p t => by
          simpa only [ha, hts] using hce.x25519_agreement_torsion_invariant s p t
        x25519_agreement_zero_iff_low_order := fun s p hs hp1 => by
          simpa only [ha] using hce.x25519_agreement_zero_iff_low_order s p hs hp1
        x25519_public_key_not_low_order := fun s hs => by
          simpa only [hp] using hce.x25519_public_key_not_low_order s hs
        aes_cbc_decrypt_inverts_encrypt := fun pt k iv => by
          have he : myBaseInterp aesCbcEncryptSymbol [pt, k, iv] =
              some (CryptoGames.LibsignalSession.aesCbcEncrypt xorBlock
                (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) pt) := rfl
          rw [he, Option.getD_some]
          change CryptoGames.LibsignalSession.aesCbcDecrypt xorBlock
              (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv)
              (CryptoGames.LibsignalSession.aesCbcEncrypt xorBlock
                (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) pt) = some pt
          rw [aesCbcEncrypt_eq_byteSpecs, aesCbcDecrypt_eq_byteSpecs]
          exact ByteSpecs.cbcDecRaw_correct xorBlock_involutive _ _
            (⟨pt, rfl⟩ : ByteSpecs.Plain pt.length)
        aes_cbc_encrypt_of_decrypt := fun c k iv p _ _ hdec => by
          change CryptoGames.LibsignalSession.aesCbcDecrypt xorBlock
              (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) c = some p at hdec
          change some (CryptoGames.LibsignalSession.aesCbcEncrypt xorBlock
              (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) p) = some c
          exact congrArg some (aesCbcEncrypt_of_decrypt_xor c p _ _ hdec)
        hmac_tag_length := fun k d tag htag => by
          rw [hm] at htag
          exact hce.hmac_tag_length k d tag htag }
  · intro s
    rw [hp]
    exact hcan s
  · intro s t k _ heq hne
    rw [torsionShift_myBaseInterp] at heq
    exact (hne heq).elim

theorem myInterp_contracts : ExternContractsHoldCli myInterp :=
  externContractsHoldCli_interpOfParams myParams myBaseInterp_contracts

theorem myHooks_agree : HooksMatchInterpretation myInterp myHooks := by
  change ModelAgree (interpOfParams myBaseInterp myParams) myParams
  rw [modelAgree_interpOfParams]
  change HooksMatchInterpretation myBaseInterp myHooks
  rcases cliWitnessHooks_agree with ⟨_, _, _, hx, hpk, _, _, hmont, _⟩
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p k iv _ _
    rfl
  · intro c k iv _ _
    rfl
  · intro a b
    rw [myBaseInterp_other (by decide)]
    exact hx a b
  · intro a
    rw [myBaseInterp_other (by decide)]
    exact hpk a
  · intro pk rand
    rfl
  · intro sk ct
    rfl
  · intro u sign
    rw [myBaseInterp_other (by decide)]
    exact hmont u sign
  · intro pt
    rfl

/-! ## Uniform Output Lengths of `myInterp` on `assumedInjective` Primitives -/

theorem length_myInterp_dhPk (s : ByteString) :
    ((myInterp x25519PublicKeySymbol [s]).getD []).length = 32 := by
  rw [myInterp, interpOfParams_other myBaseInterp myParams x25519PublicKeySymbol [s] (by decide),
    myBaseInterp_other (by decide)]
  exact myBaseInterp_contracts.1.x25519_public_key_length s

theorem length_myInterp_dh (s p : ByteString) :
    ((myInterp x25519AgreementSymbol [s, p]).getD []).length = 32 := by
  rw [myInterp, interpOfParams_other myBaseInterp myParams x25519AgreementSymbol [s, p] (by decide),
    myBaseInterp_other (by decide)]
  exact myBaseInterp_contracts.1.x25519_agreement_length s p

theorem le_length_myInterp_aesEnc (m k iv : ByteString) :
    16 ≤ ((myInterp aesCbcEncryptSymbol [m, k, iv]).getD []).length := by
  rw [myInterp,
    interpOfParams_other myBaseInterp myParams aesCbcEncryptSymbol [m, k, iv] (by decide)]
  change 16 ≤ (CryptoGames.LibsignalSession.aesCbcEncrypt xorBlock
      (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) m).length
  exact le_length_aesCbcEncrypt xorBlock _ _ m

theorem length_myInterp_kyberEncap_take (pk e : ByteString) :
    (((myInterp kyberEncapsSymbol [pk, e]).getD []).take 1568).length = 1568 := by
  rw [myInterp, interpOfParams_other myBaseInterp myParams kyberEncapsSymbol [pk, e] (by decide)]
  change ((myKyberCt pk e ++ myKyberSsFromRand pk e).take 1568).length = 1568
  simp only [List.length_take, List.length_append, length_myKyberCt, length_myKyberSsFromRand]
  omega

theorem length_myInterp_kyberEncap_drop (pk e : ByteString) :
    (((myInterp kyberEncapsSymbol [pk, e]).getD []).drop 1568).length = 32 := by
  rw [myInterp, interpOfParams_other myBaseInterp myParams kyberEncapsSymbol [pk, e] (by decide)]
  change ((myKyberCt pk e ++ myKyberSsFromRand pk e).drop 1568).length = 32
  simp only [List.length_drop, List.length_append, length_myKyberCt, length_myKyberSsFromRand]

/-! ## Provisioning `ProtocolSetup`, `OpaqueSymbolSemantics`, Plaintexts, and `not_kyberMismatch_myInterp` -/

def freshBytes (ts n : Nat) : HwBytes :=
  List.replicate n (BitVec.ofNat 8 (ts % 96 + 1))

theorem freshBytes_byte_le (ts n : Nat) {b : BitVec 8} (hb : b ∈ freshBytes ts n) :
    b.toNat ≤ 96 := by
  rw [freshBytes, List.mem_replicate] at hb
  rcases hb with ⟨_, rfl⟩
  simp only [BitVec.toNat_ofNat]
  omega

theorem not_mem_109_freshBytes (ts n : Nat) : (109#8 : BitVec 8) ∉ freshBytes ts n := by
  intro h
  have hle := freshBytes_byte_le ts n h
  have h109 : (109#8 : BitVec 8).toNat = 109 := rfl
  omega

/-- 9-byte printable ASCII plaintext starting with `'m'` (`109#8`), disjoint in byte values from
all coin draws (`<= 96`) and distinct in length from 8-byte tags, 16-byte blocks, and 32-byte keys. -/
def pt0 : HwBytes := [109#8, 48#8, 48#8, 48#8, 48#8, 48#8, 48#8, 48#8, 49#8]
def pt1 : HwBytes := [109#8, 48#8, 48#8, 48#8, 48#8, 48#8, 48#8, 48#8, 50#8]
def ptReply0 : HwBytes := [109#8, 48#8, 48#8, 48#8, 48#8, 48#8, 48#8, 48#8, 51#8]
def pt2 : HwBytes := [109#8, 48#8, 48#8, 48#8, 48#8, 48#8, 48#8, 48#8, 52#8]

def myKyberPubBytes : HwBytes := List.replicate 1568 0x77#8

def myKyberSecField : HwBytes :=
  List.replicate 1537 0#8 ++ myKyberPubBytes ++ List.replicate 64 0#8

def mkRecords (withOpk : Bool) : ProtocolSetup :=
  let dummy : ProtocolSetup :=
    { alice := "alice", bob := "bob", withOpk := withOpk
      regIdA := 10#32, regIdB := 20#32, spkId := 1#32, kpkId := 2#32, opkId := 3#32
      kyberSecB := myKyberSecField, fresh := freshBytes, opaqueBytes := fun _ => [] }
  let pk6 := setupPublic dummy 6
  { dummy with
    opaqueBytes := fun t => if t = pk6 then myKyberPubBytes else List.replicate 64 0#8 }

private def discrSem : OpaqueSymbolSemantics where
  init := fun _ _ => []
  chainKey := fun _ _ _ => []
  sendState := fun _ _ => []
  sendKey := fun _ _ => []
  sendMsg := fun _ _ => []
  recvState := fun _ _ => []
  recvKey := fun _ _ => []
  kemPk := fun _ => []
  kemDecap := fun _ _ => []
  vk := fun _ => []
  sign := fun _ _ _ => [0#8]

private def discrGhost : Ghost where
  σ := fun _ _ => []
  addr := fun _ => []

unseal DY.Bytes in
private local instance (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeRandom g) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, DY.Libsignal.Composed.Refinement.allFuns,
      Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]
    rfl⟩

unseal DY.Bytes in
private local instance (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeLit (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, DY.Libsignal.Composed.Refinement.allFuns,
      DY.Libsignal.Composed.Refinement.litFuns,
      Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]
    rfl⟩

unseal DY.Bytes in
private local instance (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction concretizeConcat (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, DY.Libsignal.Composed.Refinement.allFuns,
      DY.Libsignal.Composed.Refinement.concatFuns,
      Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]
    rfl⟩

unseal DY.Bytes in
private local instance (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemPk S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, DY.Libsignal.Composed.Refinement.allFuns,
      DY.Libsignal.Composed.Refinement.kemFuns,
      Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]
    rfl⟩

unseal DY.Bytes in
private local instance (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSign S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, DY.Libsignal.Composed.Refinement.allFuns,
      DY.Libsignal.Composed.Refinement.sigFuns,
      Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]
    rfl⟩

private theorem sign_ne_kemPk (sk nonce msg seed : DY.Bytes) :
    DY.Signature.sign sk nonce msg ≠ DY.PQKem.kemPk seed := by
  intro heq
  have hs : gamma cliWitnessInterp discrSem discrGhost (DY.Signature.sign sk nonce msg) = [0#8] := by
    unfold gamma gamma'
    show ((({sk, nonce, msg} : DY.Signature.Sign.SubF DY.Bytes).pack).rec
      (concretizeAll cliWitnessInterp discrSem discrGhost)).bytes = _
    rw [DY.Bytes.rec_eq (concretizeSign discrSem)
      (concretizeAll cliWitnessInterp discrSem discrGhost)]; rfl
  have hk : gamma cliWitnessInterp discrSem discrGhost (DY.PQKem.kemPk seed) = [] := by
    unfold gamma gamma'
    show ((({sk := seed} : DY.PQKem.Pk.SubF DY.Bytes).pack).rec
      (concretizeAll cliWitnessInterp discrSem discrGhost)).bytes = _
    rw [DY.Bytes.rec_eq (concretizeKemPk discrSem)
      (concretizeAll cliWitnessInterp discrSem discrGhost)]; rfl
  rw [heq, hk] at hs
  cases hs

private theorem mkRecords_opaqueBytes (withOpk : Bool) (t : DY.Bytes) :
    (mkRecords withOpk).opaqueBytes t =
      if t = DY.PQKem.kemPk (randTerm 16 64) then myKyberPubBytes
      else List.replicate 64 0#8 := by
  dsimp only [mkRecords]
  rw [b1_setupPublic_6 _ (by show "alice" ≠ "bob"; decide)]

theorem mkRecords_opaqueBytes_6 (withOpk : Bool) :
    (mkRecords withOpk).opaqueBytes (setupPublic (mkRecords withOpk) 6) = myKyberPubBytes := by
  have hNe : (mkRecords withOpk).alice ≠ (mkRecords withOpk).bob := by
    show "alice" ≠ "bob"; decide
  rw [mkRecords_opaqueBytes, b1_setupPublic_6 (mkRecords withOpk) hNe]
  simp only [↓reduceIte]

theorem mkRecords_wf (withOpk : Bool) : ProtocolSetupWF (mkRecords withOpk) := by
  have hNe : (mkRecords withOpk).alice ≠ (mkRecords withOpk).bob := by
    show "alice" ≠ "bob"; decide
  have h5 := b1_setupPublic_5 (mkRecords withOpk) hNe
  have h7 := b1_setupPublic_7 (mkRecords withOpk) hNe
  have o5 : (mkRecords withOpk).opaqueBytes (setupPublic (mkRecords withOpk) 5) =
      List.replicate 64 0#8 := by
    rw [mkRecords_opaqueBytes, h5]
    simp only [sign_ne_kemPk, ↓reduceIte]
  have o6 : (mkRecords withOpk).opaqueBytes (setupPublic (mkRecords withOpk) 6) = myKyberPubBytes :=
    mkRecords_opaqueBytes_6 withOpk
  have o7 : (mkRecords withOpk).opaqueBytes (setupPublic (mkRecords withOpk) 7) =
      List.replicate 64 0#8 := by
    rw [mkRecords_opaqueBytes, h7]
    simp only [sign_ne_kemPk, ↓reduceIte]
  refine ⟨hNe, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p _
    exact List.length_replicate
  · rw [b1_setupRandomsAt_eq (mkRecords withOpk) hNe]
    cases withOpk <;> decide
  · dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSigTerm]; rw [o5]; exact List.length_replicate
  · dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkPubTerm]; rw [o6]; exact List.length_replicate
  · dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkSigTerm]; rw [o7]; exact List.length_replicate
  · show myKyberSecField.length = 3169
    simp only [myKyberSecField, myKyberPubBytes, List.length_append, List.length_replicate]
  · unfold slice
    dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkPubTerm]
    rw [o6, show (mkRecords withOpk).kyberSecB = myKyberSecField from rfl]
    unfold myKyberSecField
    rw [List.append_assoc, List.drop_left' List.length_replicate,
      List.take_left' (by simp only [myKyberPubBytes, List.length_replicate])]

theorem not_kyberMismatch_myInterp (withOpk : Bool) (p : PreKeyFields) :
    ¬ KyberMismatch myInterp (mkRecords withOpk) p := by
  rintro ⟨e, ct, ss, he32, _, henc, hndec⟩
  unfold kyberEncapsBytes DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkPubTerm at henc
  rw [mkRecords_opaqueBytes_6, myInterp,
    interpOfParams_other myBaseInterp myParams kyberEncapsSymbol [myKyberPubBytes, e] (by decide)]
    at henc
  change some ((myKyberCt myKyberPubBytes e ++ myKyberSsFromRand myKyberPubBytes e).take 1568,
      (myKyberCt myKyberPubBytes e ++ myKyberSsFromRand myKyberPubBytes e).drop 1568) =
      some (ct, ss) at henc
  rw [List.take_left' (length_myKyberCt _ _), List.drop_left' (length_myKyberCt _ _)] at henc
  injection henc with hpair
  injection hpair with hct hss
  subst hct hss
  apply hndec
  unfold kyberDecapsBytes
  rw [myInterp,
    interpOfParams_other myBaseInterp myParams kyberDecapsSymbol _ (by decide)]
  change some (myKyberDecapRaw ((mkRecords withOpk).kyberSecB.drop 1)
      (myKyberCt myKyberPubBytes e)) = some (myKyberSsFromRand myKyberPubBytes e)
  apply congrArg some
  unfold myKyberDecapRaw myKyberSsFromRand
  have hr : (((myKyberCt myKyberPubBytes e).drop 1 ++ List.replicate 32 0#8).take 32) =
      (e ++ List.replicate 32 0#8).take 32 := by
    unfold myKyberCt
    have he_take : (e ++ List.replicate 32 0#8).take 32 = e := List.take_left' he32
    simp only [List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero, he_take]
    rw [List.append_assoc, List.append_assoc, List.take_left' he32]
  have hp : ((((mkRecords withOpk).kyberSecB.drop 1).drop 1536 ++ List.replicate 32 0#8).take 32) =
      (myKyberPubBytes ++ List.replicate 32 0#8).take 32 := by
    have hsec : (mkRecords withOpk).kyberSecB = myKyberSecField := rfl
    have hlen1568 : 32 ≤ myKyberPubBytes.length := by
      simp only [myKyberPubBytes, List.length_replicate]; omega
    rw [hsec, List.drop_drop]
    show ((myKyberSecField.drop 1537 ++ List.replicate 32 0#8).take 32) = _
    unfold myKyberSecField
    rw [List.append_assoc, List.drop_left' List.length_replicate,
      List.append_assoc, List.take_append_of_le_length hlen1568,
      List.take_append_of_le_length hlen1568]
  rw [hr, hp]

/-- Expands a 32-byte symbolic `messageEncrypt` SPQR coin slice to the 64-byte repeated-byte coin
slice consumed by SPQR V1 ML-KEM-768 keypair generation on initial sends. -/
def padSendCoins (c : HwBytes) : HwBytes :=
  if c.length = 32 then c ++ c else c

def padCompSemOf (i : ExternInterpretation) (r : ProtocolSetup) : OpaqueSymbolSemantics :=
  let base := compSemOf i r
  { base with
    sendState := fun st c => base.sendState st (padSendCoins c)
    sendKey := fun st c => base.sendKey st (padSendCoins c)
    sendMsg := fun st c => base.sendMsg st (padSendCoins c) }

def mySem (withOpk : Bool) : OpaqueSymbolSemantics :=
  padCompSemOf myInterp (mkRecords withOpk)

private theorem gamma_sign_eq (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (sk nonce msg : DY.Bytes) :
    gamma i S g (DY.Signature.sign sk nonce msg) =
      S.sign (gamma i S g sk) (gamma i S g nonce) (gamma i S g msg) := by
  unfold gamma gamma' DY.Signature.sign
  show ((({ sk := sk, nonce := nonce, msg := msg } : DY.Signature.Sign.SubF DY.Bytes).pack).rec
    (concretizeAll i S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeSign S) (concretizeAll i S g)]
  rfl

private theorem gamma_concat_lit_eq (i : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) (b : ByteArray) (r : DY.Bytes) :
    gamma i S g (DY.Concat.concat (DY.Literal.literalToBytes b) r) =
      ofByteArray b ++ gamma i S g r := by
  unfold gamma gamma' DY.Literal.literalToBytes
  show ((({ lhs := ({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack, rhs := r } :
    DY.Concat.Concat.SubF DY.Bytes).pack).rec (concretizeAll i S g)).bytes = _
  rw [DY.Bytes.rec_eq concretizeConcat (concretizeAll i S g)]
  dsimp only [concretizeConcat, node]
  rw [DY.Bytes.rec_eq concretizeLit (concretizeAll i S g)]
  rfl

private theorem padCompSemOf_ready_of_ne (i : ExternInterpretation) (r : ProtocolSetup)
    (hNe : r.alice ≠ r.bob) (g : Ghost)
    (hσ : ∀ p ∈ setupRandomsAt r, g.σ p.1 p.2 = r.fresh p.1 p.2) :
    GhostAndSemMatchSetup i r (padCompSemOf i r) g := by
  refine ⟨hσ, ?_, fun _ => rfl⟩
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · change gamma i (padCompSemOf i r) g (setupPublic r 5) = r.opaqueBytes (setupPublic r 5)
    conv =>
      lhs
      rw [b1_setupPublic_5 r hNe, gamma_sign_eq]
      unfold DY.Libsignal.PQXDH.encodeEC DY.Libsignal.TripleRatchet.litByte
      rw [gamma_concat_lit_eq]
    have h05 : ofByteArray { data := #[DY.Libsignal.PQXDH.ecKeyType] } = [0x05#8] := rfl
    rw [h05, List.singleton_append]
    rfl
  · change gamma i (padCompSemOf i r) g (setupPublic r 6) = r.opaqueBytes (setupPublic r 6)
    conv => lhs; rw [b1_setupPublic_6 r hNe]
    have h16 : g.σ 16 64 = r.fresh 16 64 := by
      apply hσ (16, 64)
      rw [b1_setupRandomsAt_eq r hNe]
      simp only [List.mem_append, List.mem_cons, true_or, or_true]
    conv =>
      lhs
      unfold gamma gamma' DY.PQKem.kemPk randTerm
      change ((({ sk := ({ timestamp := 16, size := 64 } : DY.Random.Random DY.Bytes).pack } :
        DY.PQKem.Pk.SubF DY.Bytes).pack).rec (concretizeAll i (padCompSemOf i r) g)).bytes
      rw [DY.Bytes.rec_eq (concretizeKemPk (padCompSemOf i r))
        (concretizeAll i (padCompSemOf i r) g)]
      dsimp only [concretizeKemPk, DY.Libsignal.Composed.Refinement.opaqueNode]
      rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll i (padCompSemOf i r) g)]
    change (if g.σ 16 64 = r.fresh 16 64 then r.opaqueBytes (setupPublic r 6)
      else 0xFF#8 :: g.σ 16 64) = r.opaqueBytes (setupPublic r 6)
    simp only [h16, ↓reduceIte]
  · change gamma i (padCompSemOf i r) g (setupPublic r 7) = r.opaqueBytes (setupPublic r 7)
    conv =>
      lhs
      rw [b1_setupPublic_7 r hNe, gamma_sign_eq]
      unfold DY.Libsignal.PQXDH.encodeKEM DY.Libsignal.TripleRatchet.litByte
      rw [gamma_concat_lit_eq]
    have h08 : ofByteArray { data := #[DY.Libsignal.PQXDH.kemKeyType] } = [0x08#8] := rfl
    rw [h08, List.singleton_append]
    rfl

theorem mySem_compat (withOpk : Bool) (g : Ghost)
    (hσ : ∀ p ∈ setupRandomsAt (mkRecords withOpk), g.σ p.1 p.2 = freshBytes p.1 p.2) :
    GhostAndSemMatchSetup myInterp (mkRecords withOpk) (mySem withOpk) g :=
  padCompSemOf_ready_of_ne myInterp (mkRecords withOpk) (mkRecords_wf withOpk).1 g hσ

/-! ## CLI-Level Reachability of `keySetupTrace` -/

theorem cliReachable_keySetupTrace : CliTraceReachableProof keySetupTrace := by
  refine ⟨myInterp, myHooks, mkRecords false, mySem false,
    [], ⟨freshBytes, fun _ => []⟩, [], [],
    (fun _ _ _ => CliTraces.done _),
    (fun _ h => nomatch h),
    ⟨mySem_compat false _ (fun _ _ => rfl),
      ⟨(fun _ h => nomatch h), fun _ => Or.inl rfl, fun _ h => nomatch h⟩,
      modelRunWF_nil (mkRecords false) (mkRecords_wf false),
      MatchesEventsAt.nil (fun _ h => nomatch h)⟩,
    rfl,
    myInterp_total, myInterp_contracts, myHooks_agree, mkRecords_wf false,
    invertsGuarded_of_noInverts rfl,
    by
      unfold DY.Libsignal.Composed.Refinement.Cli.CoinsFresh
        DY.Libsignal.Composed.Refinement.Cli.setupDHSecrets
        DY.Libsignal.Composed.Refinement.secretBytes
      rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq _ (mkRecords_wf false).1]
      decide +kernel,
    ?_⟩
  rintro ⟨evs₁, _, _, _, _, _, heq, _⟩
  cases evs₁ <;> cases heq

end Symbolic.Proofs.Tests.CliNonvacuity.Witness
