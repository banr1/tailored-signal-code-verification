/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeEval
import all DY.ALaCarte.Basic
import all DY.ALaCarte.DecidableEq
import all DY.ALaCarte.Ordering
import all DY.Misc.Instances
import all DY.Bytes.Basic
import all Comparse.Basic
import all Comparse.Formats.Basic
import all Comparse.Formats.Derived
import all DY.Comparse
import all DY.Trace.Basic
import all DY.Trace.Monad
import all DY.Trace.Manipulation
import all DY.Actions.Network
import all DY.Actions.PersistentLocalState
import all DY.Actions.PersistentGlobalState
import all DY.Actions.ProtocolEvent
import all DY.Actions.Random
import all DY.EquationalTheory.Literal
import all DY.EquationalTheory.Concat
import all DY.EquationalTheory.DiffieHellman
import all DY.EquationalTheory.KdfExtract
import all DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.Instance
import Symbolic.Specifications.Model.PQXDH
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import all Init.Data.Array.Attach
import all Init.Data.Array.DecidableEq
import all Init.Data.Repr
import all Init.Data.String.Bootstrap
import all Init.Data.String.Defs
import Symbolic.Proofs.Tests.CliNonvacuity.Table.Checkers
import Symbolic.Proofs.Tests.CliNonvacuity.Table.HsCertTrue

/-!
# Bob Session-Start Non-Collision for `withOpk`

Discharges `¬ BobSessionStartCollidesOrImplicitRejectsOn` for the `withOpk = true` PQXDH + Triple
Ratchet handshake trace via certified table checkers and `decide +kernel`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue

set_option maxRecDepth 200000

open scoped DY.Libsignal.Composed
open DY.DiffieHellman (dhPk)
open DY.PQKem (kemPk)
open DY.Libsignal.PQXDH (errToOption agree pqxdhIkm pqxdhKdf serializedIk)
open DY.Libsignal.TripleRatchet
  (TRState parseTrSignalMsg trMsgKeys computeMac createChain kdfCk consumeMessageKey skippedSeeds
   spqrB2A)
open DY.Libsignal.Composed.Refinement
  (setupPublic setupSecret setupSent setupRandoms
   TrialCtx storedStates storedSecrets plaintextTerms bobTrials trialTerms
   runTrace honestSaltsOf BobSessionStartCollidesOrImplicitRejectsOn)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (ikA ikB spkB pqskB opkB keysOpk dhsAOpk oOpk stA0Opk stA1Opk coins0Opk key0Opk pqm0Opk m0Opk
   t6Opk recv7Opk stB0'Opk)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (rnd encSig encMsg parse_encMsg kemDecap_kemEncap agree_comm createChain_comm dec_ok)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness (myInterp mkRecords mySem)
open Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollision
  (noBobStartCollisionBool not_bobSessionStartCollidesOrImplicitRejectsOn_check)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps
  (msPrefix2 mySem_eq_comp ghostOf visPrefix2Comp
   setupTrace_true_eq runTrace_msPrefix2_true)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeEval
  (p0Fields honestPreKeyRep p0_pkId_true p0_spqrIdx_true
   honestSalts_msPrefix2_true
   zeroKey_ne_spqrSendKey symDec_ne_salt)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.HsTables (hsTrueTable)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.HsCertTrue
  (hsTrue_sound hsTrueGamma gamma_comp_eq_hsTrueGamma)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.Checkers
  (noMemoCollisionHsTableBool noMemoCollisionBool_of_hsTableBool
   noMacForgeryTableBool noMacForgeryBool_of_tableBool)

private def bobCtxTrue : TrialCtx :=
  { peerIk := serializedIk (dhPk ikA)
    myIk := serializedIk (dhPk ikB)
    extra := [keysOpk.rk, keysOpk.ck, keysOpk.pqr, stA0Opk.cks, (kdfCk stA0Opk.cks).1]
    ownSalts := [key0Opk]
    seed? := some (kdfCk stA0Opk.cks).2 }

private theorem bobTrials_true_or_nil (tr : DY.ExecTrace) :
    bobTrials (mkRecords true) tr (p0Fields true) (honestPreKeyRep true)
      (encSig stA0Opk coins0Opk key0Opk m0Opk) = [] ∨
    bobTrials (mkRecords true) tr (p0Fields true) (honestPreKeyRep true)
      (encSig stA0Opk coins0Opk key0Opk m0Opk) = [bobCtxTrue] := by
  unfold bobTrials
    DY.Libsignal.Composed.Refinement.ProtocolSetup.ikAPubTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.ikBPubTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.ikBSecTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSecTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.pqskSecTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.opkSecTerm
  rw [p0_pkId_true, p0_spqrIdx_true]
  have hopk : (mkRecords true).withOpk = true := rfl
  have hopkId : ((3#32 : BitVec 32) == (mkRecords true).opkId) = true := rfl
  dsimp only
  rw [hopk, hopkId]
  simp only [Bool.true_and, ↓reduceIte]
  split
  · exact .inl rfl
  · right
    have hp0 : setupPublic (mkRecords true) 0 = dhPk ikA := by
      unfold setupPublic setupSent; rw [setupTrace_true_eq]; rfl
    have hp2 : setupPublic (mkRecords true) 2 = dhPk ikB := by
      unfold setupPublic setupSent; rw [setupTrace_true_eq]; rfl
    have hs1 : setupSecret (mkRecords true) 1 = ikB := by
      unfold setupSecret setupRandoms; rw [setupTrace_true_eq]; rfl
    have hs2 : setupSecret (mkRecords true) 2 = spkB := by
      unfold setupSecret setupRandoms; rw [setupTrace_true_eq]; rfl
    have hs4 : setupSecret (mkRecords true) 4 = pqskB := by
      unfold setupSecret setupRandoms; rw [setupTrace_true_eq]; rfl
    have hs6 : setupSecret (mkRecords true) 6 = opkB := by
      unfold setupSecret setupRandoms; rw [setupTrace_true_eq]; rfl
    rw [hp0, hp2, hs1, hs2, hs4, hs6]
    have hss : (errToOption (DY.PQKem.kemDecap pqskB (honestPreKeyRep true).ct)).getD
        (DY.PQKem.kemRejKey pqskB (honestPreKeyRep true).ct) =
        (DY.PQKem.kemEncap (kemPk pqskB) (rnd 27 32)).2 := by
      show (errToOption (DY.PQKem.kemDecap pqskB (DY.PQKem.kemEncap (kemPk pqskB) (rnd 27 32)).1)).getD _ = _
      rw [kemDecap_kemEncap]; rfl
    rw [hss]
    have hkeys : pqxdhKdf (pqxdhIkm (agree (dhPk ikA) spkB) (agree (honestPreKeyRep true).ek ikB)
        (agree (honestPreKeyRep true).ek spkB)
        (Option.map (agree (honestPreKeyRep true).ek) (some opkB))
        (DY.PQKem.kemEncap (kemPk pqskB) (rnd 27 32)).2) = keysOpk := by
      show pqxdhKdf (pqxdhIkm (agree (dhPk ikA) spkB) (agree (dhPk (rnd 26 32)) ikB)
        (agree (dhPk (rnd 26 32)) spkB) (some (agree (dhPk (rnd 26 32)) opkB))
        (DY.PQKem.kemEncap (kemPk pqskB) (rnd 27 32)).2) = keysOpk
      rw [agree_comm ikA spkB, agree_comm (rnd 26 32) ikB, agree_comm (rnd 26 32) spkB,
        agree_comm (rnd 26 32) opkB]
      rfl
    rw [hkeys]
    have hc : (createChain keysOpk.rk (encSig stA0Opk coins0Opk key0Opk m0Opk).ratchetKey spkB).2 =
        stA0Opk.cks := by
      show (createChain keysOpk.rk (dhPk dhsAOpk) spkB).2 =
        (createChain keysOpk.rk (dhPk spkB) dhsAOpk).2
      rw [createChain_comm keysOpk.rk dhsAOpk spkB]
    rw [hc]
    have hcnt : (encSig stA0Opk coins0Opk key0Opk m0Opk).counter = 0 := rfl
    have hpqm : (encSig stA0Opk coins0Opk key0Opk m0Opk).pqRatchet = pqm0Opk := rfl
    rw [hcnt, hpqm]
    dsimp only [consumeMessageKey, skippedSeeds, List.append_nil]
    rw [show DY.Spqr.spqrInit keysOpk.pqr spqrB2A = stB0'Opk.spqr from rfl, recv7Opk]
    rfl

private def bobTrialTermsTrue : List DY.Bytes :=
  let seed := (kdfCk stA0Opk.cks).2
  let wire := (encSig stA0Opk coins0Opk key0Opk m0Opk).wire
  let mk0 := trMsgKeys DY.Spqr.zeroKey seed
  let mk1 := trMsgKeys key0Opk seed
  [keysOpk.rk, keysOpk.ck, keysOpk.pqr, stA0Opk.cks, (kdfCk stA0Opk.cks).1,
   mk0.cipherKey, mk0.macKey, mk0.iv,
   computeMac mk0.macKey (serializedIk (dhPk ikA)) (serializedIk (dhPk ikB)) wire,
   mk1.cipherKey, mk1.macKey, mk1.iv,
   computeMac mk1.macKey (serializedIk (dhPk ikA)) (serializedIk (dhPk ikB)) wire,
   m0Opk]

private theorem bobTrialTerms_true_eq :
    ([bobCtxTrue].flatMap (trialTerms [DY.Spqr.zeroKey, key0Opk]
      (encSig stA0Opk coins0Opk key0Opk m0Opk))) = bobTrialTermsTrue := by
  unfold bobCtxTrue trialTerms bobTrialTermsTrue
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [symDec_ne_salt (show DY.Spqr.zeroKey ≠ key0Opk from
      zeroKey_ne_spqrSendKey stA0Opk.spqr coins0Opk),
    dec_ok rfl]
  rfl

private def storedStatesTrue : List (DY.PersistentLocalState.LocalState TRState) :=
  [{ participant := "alice", state := stA0Opk },
   { participant := "alice", state := stA1Opk }]

private theorem storedStates_true_eq :
    storedStates (mkRecords true) t6Opk = storedStatesTrue := by
  unfold storedStates storedStatesTrue; rw [setupTrace_true_eq]; rfl

private def storedSecretsTrue : List DY.Bytes :=
  [DY.Comparse.serialize ({ participant := "alice", state := { kind := .identity, sk := ikA } } :
     DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState),
   DY.Comparse.serialize ({ participant := "bob", state := { kind := .identity, sk := ikB } } :
     DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState),
   DY.Comparse.serialize ({ participant := "bob", state := { kind := .signedPrekey, sk := spkB } } :
     DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState),
   DY.Comparse.serialize ({ participant := "bob", state := { kind := .pqPrekey, sk := pqskB } } :
     DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState),
   DY.Comparse.serialize ({ participant := "bob", state := { kind := .oneTimePrekey, sk := opkB } } :
     DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState)]

private theorem storedSecrets_true_eq : storedSecrets t6Opk = storedSecretsTrue := rfl

private def sendTermsTrue : List DY.Bytes :=
  [oOpk.ek, oOpk.ct, encMsg stA0Opk coins0Opk key0Opk m0Opk]

private theorem sendTerms_true_eq :
    (((visPrefix2Comp true).filter (·.kind == .send)).flatMap (·.terms)) = sendTermsTrue := rfl

private theorem ptTerms_true_eq : plaintextTerms (visPrefix2Comp true) = [m0Opk] := rfl

private theorem hmemo_true_nil :
    noMemoCollisionHsTableBool hsTrueTable hsTrueGamma
      storedStatesTrue sendTermsTrue storedSecretsTrue [m0Opk]
      [(honestPreKeyRep true).ek, (honestPreKeyRep true).ct, (honestPreKeyRep true).msg] = true := by
  decide +kernel

private theorem hmac_true_nil :
    noMacForgeryTableBool hsTrueGamma [DY.Spqr.zeroKey, key0Opk]
      (encSig stA0Opk coins0Opk key0Opk m0Opk) [] = true := by
  decide +kernel

private theorem hmemo_true :
    noMemoCollisionHsTableBool hsTrueTable hsTrueGamma
      storedStatesTrue sendTermsTrue storedSecretsTrue [m0Opk]
      ([(honestPreKeyRep true).ek, (honestPreKeyRep true).ct, (honestPreKeyRep true).msg] ++
        bobTrialTermsTrue) = true := by
  decide +kernel

private theorem hmac_true :
    noMacForgeryTableBool hsTrueGamma [DY.Spqr.zeroKey, key0Opk]
      (encSig stA0Opk coins0Opk key0Opk m0Opk) [bobCtxTrue] = true := by
  decide +kernel

theorem not_bobStartCollides_true :
    ¬ BobSessionStartCollidesOrImplicitRejectsOn myInterp (mkRecords true) (mySem true)
        (ghostOf true) (runTrace (mkRecords true) (msPrefix2 true)) (visPrefix2Comp true)
        (honestSaltsOf (mkRecords true) (msPrefix2 true))
        (p0Fields true) (honestPreKeyRep true) :=
  not_bobSessionStartCollidesOrImplicitRejectsOn_check <| by
    unfold noBobStartCollisionBool
    have hp : parseTrSignalMsg (honestPreKeyRep true).msg =
        some (encSig stA0Opk coins0Opk key0Opk m0Opk) :=
      parse_encMsg stA0Opk coins0Opk key0Opk m0Opk
    rw [runTrace_msPrefix2_true, honestSalts_msPrefix2_true, hp, mySem_eq_comp true]
    dsimp only
    rcases bobTrials_true_or_nil t6Opk with hbt | hbt
    · rw [hbt, List.flatMap_nil, List.append_nil, Bool.and_eq_true]
      exact ⟨noMemoCollisionBool_of_hsTableBool hsTrue_sound gamma_comp_eq_hsTrueGamma
        storedStates_true_eq sendTerms_true_eq storedSecrets_true_eq ptTerms_true_eq hmemo_true_nil,
        noMacForgeryBool_of_tableBool gamma_comp_eq_hsTrueGamma hmac_true_nil⟩
    · rw [hbt, bobTrialTerms_true_eq, Bool.and_eq_true]
      exact ⟨noMemoCollisionBool_of_hsTableBool hsTrue_sound gamma_comp_eq_hsTrueGamma
        storedStates_true_eq sendTerms_true_eq storedSecrets_true_eq ptTerms_true_eq hmemo_true,
        noMacForgeryBool_of_tableBool gamma_comp_eq_hsTrueGamma hmac_true⟩

theorem attackerKnows_torsionVariant_bridge (v : Fin 4) (t : Fin 8) (tr : DY.ExecTrace) (k : DY.Bytes)
    (hak : k.AttackerKnows tr) : (DY.X25519.x25519TorsionVariant k v t).AttackerKnows tr := by
  exact DY.Bytes.AttackerKnows.prove DY.X25519.x25519Variant.attackerKnowledge _ tr ⟨k, v, t, rfl, hak⟩

theorem symEnc_attackerKnowledge_pred (p : DY.Bytes → Prop) (out : DY.Bytes) :
    DY.SymEnc.symEnc.attackerKnowledge.pred p out =
      (∃ key iv msg, out = DY.SymEnc.symEnc key iv msg ∧ p key ∧ p iv ∧ p msg) := by rfl
theorem symDec_attackerKnowledge_pred (p : DY.Bytes → Prop) (out : DY.Bytes) :
    DY.SymEnc.symDec.attackerKnowledge.pred p out =
      (∃ key iv ct, some out = DY.SymEnc.symDec key iv ct ∧ p key ∧ p iv ∧ p ct) := by rfl
theorem trunc8_attackerKnowledge_pred (p : DY.Bytes → Prop) (out : DY.Bytes) :
    DY.Trunc.trunc8.attackerKnowledge.pred p out =
      (∃ inp, out = DY.Trunc.trunc8 inp ∧ p inp) := by rfl
theorem x25519Variant_attackerKnowledge_pred (p : DY.Bytes → Prop) (out : DY.Bytes) :
    DY.X25519.x25519Variant.attackerKnowledge.pred p out =
      (∃ key v t, out = DY.X25519.x25519TorsionVariant key v t ∧ p key) := by rfl
theorem x25519VariantKey_attackerKnowledge_pred (p : DY.Bytes → Prop) (out : DY.Bytes) :
    DY.X25519.normalizeX25519Key.attackerKnowledge.pred p out =
      (∃ x : DY.X25519.Variant.SubF DY.Bytes, p x.pack ∧ out = x.key) := by rfl
theorem kemPk_attackerKnowledge_pred (p : DY.Bytes → Prop) (out : DY.Bytes) :
    DY.PQKem.kemPk.attackerKnowledge.pred p out =
      (∃ sk, out = DY.PQKem.kemPk sk ∧ p sk) := by rfl
theorem kemEncapCipher_attackerKnowledge_pred (p : DY.Bytes → Prop) (out : DY.Bytes) :
    DY.PQKem.kemEncapCipher.attackerKnowledge.pred p out =
      (∃ pk entropy rhs, (out, rhs) = DY.PQKem.kemEncap pk entropy ∧ p pk ∧ p entropy) := by rfl
theorem kemEncapSS_attackerKnowledge_pred (p : DY.Bytes → Prop) (out : DY.Bytes) :
    DY.PQKem.kemEncapSS.attackerKnowledge.pred p out =
      (∃ pk entropy lhs, (lhs, out) = DY.PQKem.kemEncap pk entropy ∧ p pk ∧ p entropy) := by rfl
theorem kemDecap_attackerKnowledge_pred (p : DY.Bytes → Prop) (out : DY.Bytes) :
    DY.PQKem.kemDecap.attackerKnowledge.pred p out =
      (∃ sk cipher, some out = DY.PQKem.kemDecap sk cipher ∧ p sk ∧ p cipher) := by rfl
theorem spqrInit_attackerKnowledge_pred (p : DY.Bytes → Prop) (out : DY.Bytes) :
    DY.Spqr.spqrInit.attackerKnowledge.pred p out =
      (∃ authKey params, out = DY.Spqr.spqrInit authKey params ∧ p authKey ∧ p params) := by rfl
theorem spqrChainKey_attackerKnowledge_pred (p : DY.Bytes → Prop) (out : DY.Bytes) :
    DY.Spqr.spqrChainKey.attackerKnowledge.pred p out =
      (∃ authKey params idx, out = DY.Spqr.spqrChainKey authKey params idx ∧ p authKey ∧ p params ∧ p idx) := by rfl
theorem spqrSendState_attackerKnowledge_pred (p : DY.Bytes → Prop) (out : DY.Bytes) :
    DY.Spqr.spqrSendState.attackerKnowledge.pred p out =
      (∃ st coins, out = (DY.Spqr.spqrSend st coins).1 ∧ p st ∧ p coins) := by rfl
theorem spqrSendKey_attackerKnowledge_pred (p : DY.Bytes → Prop) (out : DY.Bytes) :
    DY.Spqr.spqrSendKey.attackerKnowledge.pred p out =
      (∃ st coins, out = (DY.Spqr.spqrSend st coins).2.1 ∧ p st ∧ p coins) := by rfl
theorem spqrSendMsg_attackerKnowledge_pred (p : DY.Bytes → Prop) (out : DY.Bytes) :
    DY.Spqr.spqrSendMsg.attackerKnowledge.pred p out =
      (∃ st coins, out = (DY.Spqr.spqrSend st coins).2.2 ∧ p st ∧ p coins) := by rfl
theorem spqrRecvState_attackerKnowledge_pred (p : DY.Bytes → Prop) (out : DY.Bytes) :
    DY.Spqr.spqrRecvState.attackerKnowledge.pred p out =
      (∃ st msg idx r, DY.Spqr.spqrRecv st msg idx = some r ∧ out = r.1 ∧ p st ∧ p msg) := by rfl
theorem spqrRecvKey_attackerKnowledge_pred (p : DY.Bytes → Prop) (out : DY.Bytes) :
    DY.Spqr.spqrRecvKey.attackerKnowledge.pred p out =
      (∃ st msg idx r, DY.Spqr.spqrRecv st msg idx = some r ∧ out = r.2 ∧ p st ∧ p msg) := by rfl
theorem spqrStateArg_attackerKnowledge_pred (p : DY.Bytes → Prop) (out : DY.Bytes) :
    DY.Spqr.spqrStateArg.attackerKnowledge.pred p out =
      ((∃ x : DY.Spqr.InitState.SubF DY.Bytes, p x.pack ∧ (out = x.authKey ∨ out = x.params)) ∨
       (∃ x : DY.Spqr.SendState.SubF DY.Bytes, p x.pack ∧ (out = x.st ∨ out = x.coins)) ∨
       (∃ x : DY.Spqr.RecvState.SubF DY.Bytes, p x.pack ∧ (out = x.st ∨ out = x.msg))) := by rfl
theorem trWireMsg_attackerKnowledge_pred (p : DY.Bytes → Prop) (out : DY.Bytes) :
    DY.TrWire.trWireMsg.attackerKnowledge.pred p out =
      (∃ x : DY.TrWire.TrWireMsg.SubF DY.Bytes,
        out = x.pack ∧ p x.senderRatchetKey ∧ p x.ciphertext ∧ p x.pqRatchet) := by rfl
theorem trWireMsgArg_attackerKnowledge_pred (p : DY.Bytes → Prop) (out : DY.Bytes) :
    DY.TrWire.trWireMsgArg.attackerKnowledge.pred p out =
      (∃ x : DY.TrWire.TrWireMsg.SubF DY.Bytes,
        p x.pack ∧ (out = x.senderRatchetKey ∨ out = x.ciphertext ∨ out = x.pqRatchet)) := by rfl

theorem bool_serialize_singleton_head (b : Bool) :
    ∃ ba : ByteArray, ba.size = 1 ∧
      ba = (if b then ⟨#[1]⟩ else ⟨#[0]⟩) ∧
      (_root_.Comparse.NonExtensibleMessageFormat.bool (Bytes := DY.Bytes)).serialize b =
        [DY.Literal.literalToBytes ba] := by
  unfold _root_.Comparse.NonExtensibleMessageFormat.bool
  exact ⟨_, @Subtype.prop ByteArray (fun a => a.size = 1) _, by cases b <;> decide +kernel, rfl⟩

theorem uint32_serialize_singleton_head (x : UInt32) (hx : x = 0 ∨ x = 1 ∨ x = 2) :
    ∃ ba : ByteArray, ba.size = 4 ∧
      (ba = ⟨#[0, 0, 0, 0]⟩ ∨ ba = ⟨#[0, 0, 0, 1]⟩ ∨ ba = ⟨#[1, 0, 0, 0]⟩ ∨
       ba = ⟨#[0, 0, 0, 2]⟩ ∨ ba = ⟨#[2, 0, 0, 0]⟩) ∧
      (_root_.Comparse.NonExtensibleMessageFormat.uint32 (Bytes := DY.Bytes)).serialize x =
        [DY.Literal.literalToBytes ba] := by
  unfold _root_.Comparse.NonExtensibleMessageFormat.uint32
  refine ⟨_, @Subtype.prop ByteArray (fun a => a.size = 4) _, ?_, rfl⟩
  rcases hx with rfl | rfl | rfl <;> decide +kernel

unseal DY.Bytes in
theorem variant_view?_none (k : DY.Bytes) (v : Fin 4) (t : Fin 8) :
    let x := (({ key := k, variation := v, torsion := t } : DY.X25519.Variant.SubF DY.Bytes).pack)
    x.view? DY.Random.Random = none ∧
    x.view? DY.DiffieHellman.DhPk.SubF = none ∧
    x.view? DY.DiffieHellman.Dh.SubF = none ∧
    x.view? DY.KdfExtract.KdfExtract.SubF = none ∧
    x.view? DY.SymEnc.Enc.SubF = none ∧
    x.view? DY.Trunc.Trunc8.SubF = none ∧
    x.view? DY.PQKem.Encap.SubF = none ∧
    x.view? DY.PQKem.SharedSecret.SubF = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

unseal DY.Bytes in
theorem randTerm_zero_view? (ts : Nat) :
    let x := (({ timestamp := ts, size := 0 } : DY.Random.Random DY.Bytes).pack)
    x.view? DY.Random.Random = some { timestamp := ts, size := 0 } ∧
    x.view? DY.DiffieHellman.DhPk.SubF = none ∧
    x.view? DY.DiffieHellman.Dh.SubF = none ∧
    x.view? DY.KdfExtract.KdfExtract.SubF = none ∧
    x.view? DY.SymEnc.Enc.SubF = none ∧
    x.view? DY.Trunc.Trunc8.SubF = none ∧
    x.view? DY.PQKem.Encap.SubF = none ∧
    x.view? DY.PQKem.SharedSecret.SubF = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem dhPk_ne_kdfExtract (x s m : DY.Bytes) :
    DY.DiffieHellman.dhPk x ≠ DY.KdfExtract.kdfExtract s m := by intro h; cases h

theorem dh_pack_ne_kdfExtract (a b s m : DY.Bytes) :
    ({ pk := a, sk := b } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack ≠ DY.KdfExtract.kdfExtract s m := by
  intro h; cases h

theorem trunc8_ne_kdfExtract (a s m : DY.Bytes) :
    DY.Trunc.trunc8 a ≠ DY.KdfExtract.kdfExtract s m := by intro h; cases h

theorem spqrA2B_utf8_size : "A->B".toUTF8.size = 4 := by decide

end Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue
