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
import Symbolic.Proofs.Tests.CliNonvacuity.Table.HsCertFalse
import Symbolic.Proofs.Swarm.CREF.Sem

/-!
# Bob Session-Start Non-Collision for `withoutOpk`

Discharges `¬ BobSessionStartCollidesOrImplicitRejectsOn` for the `withOpk = false` PQXDH + Triple
Ratchet handshake trace via certified table checkers and `decide +kernel`, and provides shared
symbolic tag, serialization, and trace-reduction helpers.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse

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
  (ikA ikB spkB pqskB keys1 dhsA o1 stA0 stA1 coins0 key0 pqm0 m0 t6 recv8 stB0')
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (rnd encSig encMsg parse_encMsg kemDecap_kemEncap agree_comm createChain_comm dec_ok)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness (myInterp mkRecords mySem)
open Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollision
  (noBobStartCollisionBool not_bobSessionStartCollidesOrImplicitRejectsOn_check)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps
  (msPrefix2 mySemComp mySem_eq_comp ghostOf visPrefix2Comp
   setupTrace_false_eq runTrace_msPrefix2_false)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeEval
  (p0Fields honestPreKeyRep p0_pkId_false p0_spqrIdx_false
   honestSalts_msPrefix2_false
   zeroKey_ne_spqrSendKey symDec_ne_salt)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.HsTables (hsFalseTable)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.HsCertFalse
  (hsFalse_sound hsFalseGamma gamma_comp_eq_hsFalseGamma)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.Checkers
  (noMemoCollisionHsTableBool noMemoCollisionBool_of_hsTableBool
   noMacForgeryTableBool noMacForgeryBool_of_tableBool)

private def bobCtxFalse : TrialCtx :=
  { peerIk := serializedIk (dhPk ikA)
    myIk := serializedIk (dhPk ikB)
    extra := [keys1.rk, keys1.ck, keys1.pqr, stA0.cks, (kdfCk stA0.cks).1]
    ownSalts := [key0]
    seed? := some (kdfCk stA0.cks).2 }

private theorem bobTrials_false_or_nil (tr : DY.ExecTrace) :
    bobTrials (mkRecords false) tr (p0Fields false) (honestPreKeyRep false)
      (encSig stA0 coins0 key0 m0) = [] ∨
    bobTrials (mkRecords false) tr (p0Fields false) (honestPreKeyRep false)
      (encSig stA0 coins0 key0 m0) = [bobCtxFalse] := by
  unfold bobTrials
    DY.Libsignal.Composed.Refinement.ProtocolSetup.ikAPubTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.ikBPubTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.ikBSecTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSecTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.pqskSecTerm
  rw [p0_pkId_false, p0_spqrIdx_false]
  dsimp only
  split
  · exact .inl rfl
  · right
    have hp0 : setupPublic (mkRecords false) 0 = dhPk ikA := by
      unfold setupPublic setupSent; rw [setupTrace_false_eq]; rfl
    have hp2 : setupPublic (mkRecords false) 2 = dhPk ikB := by
      unfold setupPublic setupSent; rw [setupTrace_false_eq]; rfl
    have hs1 : setupSecret (mkRecords false) 1 = ikB := by
      unfold setupSecret setupRandoms; rw [setupTrace_false_eq]; rfl
    have hs2 : setupSecret (mkRecords false) 2 = spkB := by
      unfold setupSecret setupRandoms; rw [setupTrace_false_eq]; rfl
    have hs4 : setupSecret (mkRecords false) 4 = pqskB := by
      unfold setupSecret setupRandoms; rw [setupTrace_false_eq]; rfl
    rw [hp0, hp2, hs1, hs2, hs4]
    have hss : (errToOption (DY.PQKem.kemDecap pqskB (honestPreKeyRep false).ct)).getD
        (DY.PQKem.kemRejKey pqskB (honestPreKeyRep false).ct) =
        (DY.PQKem.kemEncap (kemPk pqskB) (rnd 23 32)).2 := by
      show (errToOption (DY.PQKem.kemDecap pqskB (DY.PQKem.kemEncap (kemPk pqskB) (rnd 23 32)).1)).getD _ = _
      rw [kemDecap_kemEncap]; rfl
    rw [hss]
    have hkeys : pqxdhKdf (pqxdhIkm (agree (dhPk ikA) spkB) (agree (honestPreKeyRep false).ek ikB)
        (agree (honestPreKeyRep false).ek spkB)
        (Option.map (agree (honestPreKeyRep false).ek) none)
        (DY.PQKem.kemEncap (kemPk pqskB) (rnd 23 32)).2) = keys1 := by
      show pqxdhKdf (pqxdhIkm (agree (dhPk ikA) spkB) (agree (dhPk (rnd 22 32)) ikB)
        (agree (dhPk (rnd 22 32)) spkB) none (DY.PQKem.kemEncap (kemPk pqskB) (rnd 23 32)).2) = keys1
      rw [agree_comm ikA spkB, agree_comm (rnd 22 32) ikB, agree_comm (rnd 22 32) spkB]
      rfl
    rw [hkeys]
    have hc : (createChain keys1.rk (encSig stA0 coins0 key0 m0).ratchetKey spkB).2 = stA0.cks := by
      show (createChain keys1.rk (dhPk dhsA) spkB).2 = (createChain keys1.rk (dhPk spkB) dhsA).2
      rw [createChain_comm keys1.rk dhsA spkB]
    rw [hc]
    have hcnt : (encSig stA0 coins0 key0 m0).counter = 0 := rfl
    have hpqm : (encSig stA0 coins0 key0 m0).pqRatchet = pqm0 := rfl
    rw [hcnt, hpqm]
    dsimp only [consumeMessageKey, skippedSeeds, List.append_nil]
    rw [show DY.Spqr.spqrInit keys1.pqr spqrB2A = stB0'.spqr from rfl, recv8]
    rfl

private def bobTrialTermsFalse : List DY.Bytes :=
  let seed := (kdfCk stA0.cks).2
  let wire := (encSig stA0 coins0 key0 m0).wire
  let mk0 := trMsgKeys DY.Spqr.zeroKey seed
  let mk1 := trMsgKeys key0 seed
  [keys1.rk, keys1.ck, keys1.pqr, stA0.cks, (kdfCk stA0.cks).1,
   mk0.cipherKey, mk0.macKey, mk0.iv,
   computeMac mk0.macKey (serializedIk (dhPk ikA)) (serializedIk (dhPk ikB)) wire,
   mk1.cipherKey, mk1.macKey, mk1.iv,
   computeMac mk1.macKey (serializedIk (dhPk ikA)) (serializedIk (dhPk ikB)) wire,
   m0]

private theorem bobTrialTerms_false_eq :
    ([bobCtxFalse].flatMap (trialTerms [DY.Spqr.zeroKey, key0] (encSig stA0 coins0 key0 m0))) =
      bobTrialTermsFalse := by
  unfold bobCtxFalse trialTerms bobTrialTermsFalse
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [symDec_ne_salt (show DY.Spqr.zeroKey ≠ key0 from zeroKey_ne_spqrSendKey stA0.spqr coins0),
    dec_ok rfl]
  rfl

private def storedStatesFalse : List (DY.PersistentLocalState.LocalState TRState) :=
  [{ participant := "alice", state := stA0 },
   { participant := "alice", state := stA1 }]

private theorem storedStates_false_eq :
    storedStates (mkRecords false) t6 = storedStatesFalse := by
  unfold storedStates storedStatesFalse; rw [setupTrace_false_eq]; rfl

private def storedSecretsFalse : List DY.Bytes :=
  [DY.Comparse.serialize ({ participant := "alice", state := { kind := .identity, sk := ikA } } :
     DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState),
   DY.Comparse.serialize ({ participant := "bob", state := { kind := .identity, sk := ikB } } :
     DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState),
   DY.Comparse.serialize ({ participant := "bob", state := { kind := .signedPrekey, sk := spkB } } :
     DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState),
   DY.Comparse.serialize ({ participant := "bob", state := { kind := .pqPrekey, sk := pqskB } } :
     DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState)]

private theorem storedSecrets_false_eq : storedSecrets t6 = storedSecretsFalse := rfl

private def sendTermsFalse : List DY.Bytes :=
  [o1.ek, o1.ct, encMsg stA0 coins0 key0 m0]

private theorem sendTerms_false_eq :
    (((visPrefix2Comp false).filter (·.kind == .send)).flatMap (·.terms)) = sendTermsFalse := rfl

private theorem ptTerms_false_eq : plaintextTerms (visPrefix2Comp false) = [m0] := rfl

private theorem hmemo_false_nil :
    noMemoCollisionHsTableBool hsFalseTable hsFalseGamma
      storedStatesFalse sendTermsFalse storedSecretsFalse [m0]
      [(honestPreKeyRep false).ek, (honestPreKeyRep false).ct, (honestPreKeyRep false).msg] = true := by
  decide +kernel

private theorem hmac_false_nil :
    noMacForgeryTableBool hsFalseGamma [DY.Spqr.zeroKey, key0]
      (encSig stA0 coins0 key0 m0) [] = true := by
  decide +kernel

private theorem hmemo_false :
    noMemoCollisionHsTableBool hsFalseTable hsFalseGamma
      storedStatesFalse sendTermsFalse storedSecretsFalse [m0]
      ([(honestPreKeyRep false).ek, (honestPreKeyRep false).ct, (honestPreKeyRep false).msg] ++
        bobTrialTermsFalse) = true := by
  decide +kernel

private theorem hmac_false :
    noMacForgeryTableBool hsFalseGamma [DY.Spqr.zeroKey, key0]
      (encSig stA0 coins0 key0 m0) [bobCtxFalse] = true := by
  decide +kernel

theorem not_bobStartCollides_false :
    ¬ BobSessionStartCollidesOrImplicitRejectsOn myInterp (mkRecords false) (mySem false)
        (ghostOf false) (runTrace (mkRecords false) (msPrefix2 false)) (visPrefix2Comp false)
        (honestSaltsOf (mkRecords false) (msPrefix2 false))
        (p0Fields false) (honestPreKeyRep false) :=
  not_bobSessionStartCollidesOrImplicitRejectsOn_check <| by
    unfold noBobStartCollisionBool
    have hp : parseTrSignalMsg (honestPreKeyRep false).msg = some (encSig stA0 coins0 key0 m0) :=
      parse_encMsg stA0 coins0 key0 m0
    rw [runTrace_msPrefix2_false, honestSalts_msPrefix2_false, hp, mySem_eq_comp false]
    dsimp only
    rcases bobTrials_false_or_nil t6 with hbt | hbt
    · rw [hbt, List.flatMap_nil, List.append_nil, Bool.and_eq_true]
      exact ⟨noMemoCollisionBool_of_hsTableBool hsFalse_sound gamma_comp_eq_hsFalseGamma
        storedStates_false_eq sendTerms_false_eq storedSecrets_false_eq ptTerms_false_eq hmemo_false_nil,
        noMacForgeryBool_of_tableBool gamma_comp_eq_hsFalseGamma hmac_false_nil⟩
    · rw [hbt, bobTrialTerms_false_eq, Bool.and_eq_true]
      exact ⟨noMemoCollisionBool_of_hsTableBool hsFalse_sound gamma_comp_eq_hsFalseGamma
        storedStates_false_eq sendTerms_false_eq storedSecrets_false_eq ptTerms_false_eq hmemo_false,
        noMacForgeryBool_of_tableBool gamma_comp_eq_hsFalseGamma hmac_false⟩

def bytesTag (b : DY.Bytes) : Nat :=
  if (b.view? DY.Random.Random).isSome then 0
  else if (b.view? DY.Literal.Literal.SubF).isSome then 1
  else if (b.view? DY.Concat.Concat.SubF).isSome then 2
  else if (b.view? DY.DiffieHellman.DhPk.SubF).isSome then 3
  else if (b.view? DY.DiffieHellman.Dh.SubF).isSome then 4
  else if (b.view? DY.KdfExtract.KdfExtract.SubF).isSome then 5
  else if (b.view? DY.SymEnc.Enc.SubF).isSome then 6
  else if (b.view? DY.Trunc.Trunc8.SubF).isSome then 7
  else if (b.view? DY.X25519.Variant.SubF).isSome then 9
  else if (b.view? DY.PQKem.Pk.SubF).isSome then 10
  else if (b.view? DY.PQKem.Encap.SubF).isSome then 11
  else if (b.view? DY.PQKem.SharedSecret.SubF).isSome then 12
  else if (b.view? DY.Signature.Vk.SubF).isSome then 13
  else if (b.view? DY.Signature.Sign.SubF).isSome then 14
  else if (b.view? DY.Spqr.InitState.SubF).isSome then 15
  else if (b.view? DY.Spqr.ChainKey.SubF).isSome then 16
  else if (b.view? DY.Spqr.SendState.SubF).isSome then 17
  else if (b.view? DY.Spqr.SendKey.SubF).isSome then 18
  else if (b.view? DY.Spqr.SendMsg.SubF).isSome then 19
  else if (b.view? DY.Spqr.RecvState.SubF).isSome then 20
  else if (b.view? DY.Spqr.RecvKey.SubF).isSome then 21
  else if (b.view? DY.TrWire.TrWireMsg.SubF).isSome then 22
  else if (b.view? DY.PQKem.RejKey.SubF).isSome then 23
  else 24

class SubBytesTag (F : Type → Type) [DY.SubBytesFunctor F] [DY.BytesFunctor.Has F] where
  tag : Nat
  tag_pack : ∀ x : DY.BytesView F, bytesTag x.pack = tag

instance : SubBytesTag DY.Random.Random := ⟨0, fun _ => by rfl⟩
instance : SubBytesTag DY.Literal.Literal.SubF := ⟨1, fun _ => by rfl⟩
instance : SubBytesTag DY.Concat.Concat.SubF := ⟨2, fun _ => by rfl⟩
instance : SubBytesTag DY.DiffieHellman.DhPk.SubF := ⟨3, fun _ => by rfl⟩
instance : SubBytesTag DY.DiffieHellman.Dh.SubF := ⟨4, fun _ => by rfl⟩
instance : SubBytesTag DY.KdfExtract.KdfExtract.SubF := ⟨5, fun _ => by rfl⟩
instance : SubBytesTag DY.SymEnc.Enc.SubF := ⟨6, fun _ => by rfl⟩
instance : SubBytesTag DY.Trunc.Trunc8.SubF := ⟨7, fun _ => by rfl⟩
instance : SubBytesTag DY.X25519.Variant.SubF := ⟨9, fun _ => by rfl⟩
instance : SubBytesTag DY.PQKem.Pk.SubF := ⟨10, fun _ => by rfl⟩
instance : SubBytesTag DY.PQKem.Encap.SubF := ⟨11, fun _ => by rfl⟩
instance : SubBytesTag DY.PQKem.SharedSecret.SubF := ⟨12, fun _ => by rfl⟩
instance : SubBytesTag DY.Signature.Vk.SubF := ⟨13, fun _ => by rfl⟩
instance : SubBytesTag DY.Signature.Sign.SubF := ⟨14, fun _ => by rfl⟩
instance : SubBytesTag DY.Spqr.InitState.SubF := ⟨15, fun _ => by rfl⟩
instance : SubBytesTag DY.Spqr.ChainKey.SubF := ⟨16, fun _ => by rfl⟩
instance : SubBytesTag DY.Spqr.SendState.SubF := ⟨17, fun _ => by rfl⟩
instance : SubBytesTag DY.Spqr.SendKey.SubF := ⟨18, fun _ => by rfl⟩
instance : SubBytesTag DY.Spqr.SendMsg.SubF := ⟨19, fun _ => by rfl⟩
instance : SubBytesTag DY.Spqr.RecvState.SubF := ⟨20, fun _ => by rfl⟩
instance : SubBytesTag DY.Spqr.RecvKey.SubF := ⟨21, fun _ => by rfl⟩
instance : SubBytesTag DY.TrWire.TrWireMsg.SubF := ⟨22, fun _ => by rfl⟩
instance : SubBytesTag DY.PQKem.RejKey.SubF := ⟨23, fun _ => by rfl⟩

@[simp] theorem bytesTag_pack {F : Type → Type} [DY.SubBytesFunctor F] [DY.BytesFunctor.Has F]
    [SubBytesTag F] (x : DY.BytesView F) : bytesTag x.pack = SubBytesTag.tag F :=
  SubBytesTag.tag_pack x

theorem pack_ne_pack {F₁ F₂ : Type → Type}
    [DY.SubBytesFunctor F₁] [DY.BytesFunctor.Has F₁] [SubBytesTag F₁]
    [DY.SubBytesFunctor F₂] [DY.BytesFunctor.Has F₂] [SubBytesTag F₂]
    (x : DY.BytesView F₁) (y : DY.BytesView F₂)
    (hne : SubBytesTag.tag F₁ ≠ SubBytesTag.tag F₂ := by decide) :
    x.pack ≠ y.pack :=
  fun h => hne (by rw [← bytesTag_pack x, ← bytesTag_pack y, h])

theorem view_pack_none {F₁ F₂ : Type → Type}
    [DY.SubBytesFunctor F₁] [DY.BytesFunctor.Has F₁] [SubBytesTag F₁]
    [DY.SubBytesFunctor F₂] [DY.BytesFunctor.Has F₂] [SubBytesTag F₂]
    (x : DY.BytesView F₁)
    (hne : SubBytesTag.tag F₁ ≠ SubBytesTag.tag F₂ := by decide) :
    (x.pack).view? F₂ = none := by
  have hp := DY.Bytes.pack_view? F₂ x.pack
  cases hv : (x.pack).view? F₂ with
  | none => rfl
  | some y => rw [hv] at hp; exact absurd hp.symm (pack_ne_pack x y hne)

@[simp] theorem bytesTag_randTerm (idx sz : Nat) : bytesTag (DY.Libsignal.Composed.Refinement.randTerm idx sz) = 0 := by rfl
@[simp] theorem bytesTag_lit (bs : ByteArray) : bytesTag (DY.Literal.literalToBytes bs) = 1 := by rfl
@[simp] theorem bytesTag_concat (a b : DY.Bytes) : bytesTag (DY.Concat.concat a b) = 2 := by rfl
@[simp] theorem bytesTag_dhPk (sk : DY.Bytes) : bytesTag (DY.DiffieHellman.dhPk sk) = 3 := by rfl
@[simp] theorem bytesTag_kdf (s m : DY.Bytes) : bytesTag (DY.KdfExtract.kdfExtract s m) = 5 := by rfl
@[simp] theorem bytesTag_symEnc (k iv m : DY.Bytes) : bytesTag (DY.SymEnc.symEnc k iv m) = 6 := by rfl
@[simp] theorem bytesTag_trunc8 (a : DY.Bytes) : bytesTag (DY.Trunc.trunc8 a) = 7 := by rfl
@[simp] theorem bytesTag_kemPk (sk : DY.Bytes) : bytesTag (DY.PQKem.kemPk sk) = 10 := by rfl
@[simp] theorem bytesTag_kemEncap_fst (pk e : DY.Bytes) : bytesTag (DY.PQKem.kemEncap pk e).1 = 11 := by rfl
@[simp] theorem bytesTag_kemEncap_snd (pk e : DY.Bytes) : bytesTag (DY.PQKem.kemEncap pk e).2 = 12 := by rfl
@[simp] theorem bytesTag_vk (sk : DY.Bytes) : bytesTag (DY.Signature.vk sk) = 13 := by rfl
@[simp] theorem bytesTag_sign (sk n m : DY.Bytes) : bytesTag (DY.Signature.sign sk n m) = 14 := by rfl
@[simp] theorem bytesTag_spqrInit (a p : DY.Bytes) : bytesTag (DY.Spqr.spqrInit a p) = 15 := by rfl
@[simp] theorem bytesTag_spqrChainKey (a p i : DY.Bytes) : bytesTag (DY.Spqr.spqrChainKey a p i) = 16 := by rfl
@[simp] theorem bytesTag_spqrSendState (st c : DY.Bytes) : bytesTag (DY.Spqr.spqrSend st c).1 = 17 := by rfl
@[simp] theorem bytesTag_spqrSendMsg (st c : DY.Bytes) : bytesTag (DY.Spqr.spqrSend st c).2.2 = 19 := by rfl
@[simp] theorem bytesTag_trWireMsg (v : UInt8) (rk : DY.Bytes) (c pc : UInt32) (ct pq : DY.Bytes)
    (ev : DY.TrWire.EncodingVariation) :
    bytesTag (DY.TrWire.trWireMsg v rk c pc ct pq ev) = 22 := by rfl
@[simp] theorem bytesTag_kemRejKey (sk ct : DY.Bytes) : bytesTag (DY.PQKem.kemRejKey sk ct) = 23 := by rfl

theorem ai_lit_eq (bs : ByteArray) :
    DY.Libsignal.Composed.Refinement.assumedInjective (DY.Literal.literalToBytes bs) = false := by rfl
theorem ai_lit_pack_eq (b : ByteArray) :
    DY.Libsignal.Composed.Refinement.assumedInjective (({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack) = false := by rfl
theorem ai_concat_eq (a c : DY.Bytes) : DY.Libsignal.Composed.Refinement.assumedInjective (DY.Concat.concat a c) = false := by rfl
theorem ai_trWire_eq (ver : UInt8) (rk : DY.Bytes) (c pc : UInt32) (ct pq : DY.Bytes)
    (ev : DY.TrWire.EncodingVariation) :
    DY.Libsignal.Composed.Refinement.assumedInjective (DY.TrWire.trWireMsg ver rk c pc ct pq ev) = false := by rfl
theorem ai_trWire_pack_eq (w : DY.TrWire.TrWireMsg.SubF DY.Bytes) :
    DY.Libsignal.Composed.Refinement.assumedInjective w.pack = false := by rfl
theorem ai_kdfExtract_eq (k m : DY.Bytes) :
    DY.Libsignal.Composed.Refinement.assumedInjective (DY.KdfExtract.kdfExtract k m) = true := by rfl
theorem x25519Key_dhPk_eq (sk : DY.Bytes) :
    DY.X25519.normalizeX25519Key (DY.DiffieHellman.dhPk sk) = DY.DiffieHellman.dhPk sk := by rfl
theorem length_hmac_symbolic_bridge (k m : DY.Bytes) :
    (DY.Libsignal.TripleRatchet.hmac k m).length = 32 := by
  simp only [DY.Libsignal.TripleRatchet.hmac, DY.KdfExtract.kdfExtract]
  simp [DY.Bytes.length.eq, DY.KdfExtract.KdfExtract.SubF.length]
theorem trunc8Length_eq_8 : DY.Trunc.trunc8Length = 8 := by rfl
theorem spqrHeaded_computeMac_bridge (mk ikS ikR wire : DY.Bytes) :
    DY.Libsignal.Composed.Refinement.spqrHeaded (DY.Libsignal.TripleRatchet.computeMac mk ikS ikR wire) = false := by rfl
theorem canonicalVariation_eq :
    DY.TrWire.canonicalVariation =
      ⟨4, [], 0, 0, [.known 1 0 0, .known 2 0 0, .known 3 0 0, .known 4 0 0]⟩ := by rfl

@[simp] theorem concatPrefixes_nil (s : DY.Bytes) : _root_.Comparse.concatPrefixes [] s = s := by rfl
@[simp] theorem concatPrefixes_cons (p : DY.Bytes) (ps : List DY.Bytes) (s : DY.Bytes) :
    _root_.Comparse.concatPrefixes (p :: ps) s = DY.Concat.concat p (_root_.Comparse.concatPrefixes ps s) := by rfl
theorem concatPrefixes_append_eq : ∀ (ps₁ ps₂ : List DY.Bytes) (s : DY.Bytes),
    _root_.Comparse.concatPrefixes ps₁ (_root_.Comparse.concatPrefixes ps₂ s) = _root_.Comparse.concatPrefixes (ps₁ ++ ps₂) s
  | [], _, _ => by rfl
  | p :: ps₁, ps₂, s => congrArg (DY.Concat.concat p) (concatPrefixes_append_eq ps₁ ps₂ s)

theorem bool_serialize_singleton (b : Bool) :
    ∃ ba : ByteArray, ba.size = 1 ∧
      (_root_.Comparse.NonExtensibleMessageFormat.bool (Bytes := DY.Bytes)).serialize b =
        [DY.Literal.literalToBytes ba] := by
  unfold _root_.Comparse.NonExtensibleMessageFormat.bool
  exact ⟨_, @Subtype.prop ByteArray (fun a => a.size = 1) _, rfl⟩
theorem slowNat_serialize_zero :
    (_root_.Comparse.NonExtensibleMessageFormat.slowNat (Bytes := DY.Bytes)).serialize 0 =
      (_root_.Comparse.NonExtensibleMessageFormat.bool (Bytes := DY.Bytes)).serialize false := by rfl
theorem slowNat_serialize_succ (n : Nat) :
    (_root_.Comparse.NonExtensibleMessageFormat.slowNat (Bytes := DY.Bytes)).serialize (n + 1) =
      (_root_.Comparse.NonExtensibleMessageFormat.bool (Bytes := DY.Bytes)).serialize true ++
        (_root_.Comparse.NonExtensibleMessageFormat.slowNat (Bytes := DY.Bytes)).serialize n := by rfl
theorem slowBytes_serialize_eq (b : DY.Bytes) :
    (_root_.Comparse.NonExtensibleMessageFormat.slowBytes (Bytes := DY.Bytes)).serialize b =
      (_root_.Comparse.NonExtensibleMessageFormat.slowNat (Bytes := DY.Bytes)).serialize
        (_root_.Comparse.BytesLike.length b) ++ [b] := by rfl
theorem slowString_serialize_eq (s : String) :
    (_root_.Comparse.NonExtensibleMessageFormat.slowString (Bytes := DY.Bytes)).serialize s =
      (_root_.Comparse.NonExtensibleMessageFormat.slowNat (Bytes := DY.Bytes)).serialize s.utf8ByteSize ++
        [DY.Literal.literalToBytes s.toUTF8] := by rfl
theorem uint32_serialize_singleton (x : UInt32) :
    ∃ b : ByteArray, b.size = 4 ∧
      (_root_.Comparse.NonExtensibleMessageFormat.uint32 (Bytes := DY.Bytes)).serialize x =
        [DY.Literal.literalToBytes b] := by
  unfold _root_.Comparse.NonExtensibleMessageFormat.uint32
  exact ⟨_, @Subtype.prop ByteArray (fun a => a.size = 4) _, rfl⟩
theorem recvChain_serialize_eq (c : DY.Libsignal.TripleRatchet.RecvChain) :
    (DY.Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain)).serialize c =
      _root_.Comparse.NonExtensibleMessageFormat.slowBytes.serialize c.ratchetKey ++
        (_root_.Comparse.NonExtensibleMessageFormat.slowBytes.serialize c.chainKey ++
          (_root_.Comparse.NonExtensibleMessageFormat.uint32.serialize c.index ++
            _root_.Comparse.NonExtensibleMessageFormat.slowNat.serialize c.rIdx)) := by rfl
theorem recvList_serialize_nil :
    (_root_.Comparse.ExtensibleMessageFormat.list
      (DY.Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize [] =
      DY.Literal.literalToBytes .empty := by rfl
theorem recvList_serialize_cons (d : DY.Libsignal.TripleRatchet.RecvChain)
    (cs : List DY.Libsignal.TripleRatchet.RecvChain) :
    (_root_.Comparse.ExtensibleMessageFormat.list
      (DY.Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize (d :: cs) =
      _root_.Comparse.concatPrefixes
        ((DY.Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain)).serialize d)
        ((_root_.Comparse.ExtensibleMessageFormat.list
          (DY.Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize cs) := by rfl
theorem serialize_local_pqxdh_eq_bridge
    (ls : DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState) :
    (DY.Comparse.serialize ls : DY.Bytes) =
      _root_.Comparse.concatPrefixes
        (_root_.Comparse.NonExtensibleMessageFormat.slowString.serialize ls.participant ++
          (_root_.Comparse.NonExtensibleMessageFormat.bool.serialize ls.state.kind.toBits.1 ++
            _root_.Comparse.NonExtensibleMessageFormat.bool.serialize ls.state.kind.toBits.2))
        ls.state.sk := by
  simp only [← concatPrefixes_append_eq]; rfl
theorem serialize_local_tr_eq_bridge
    (ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState) :
    (DY.Comparse.serialize ls : DY.Bytes) =
      _root_.Comparse.concatPrefixes
        (_root_.Comparse.NonExtensibleMessageFormat.slowString.serialize ls.participant ++
          (_root_.Comparse.NonExtensibleMessageFormat.slowString.serialize ls.state.peer ++
            (_root_.Comparse.NonExtensibleMessageFormat.slowBytes.serialize ls.state.myIk ++
              (_root_.Comparse.NonExtensibleMessageFormat.slowBytes.serialize ls.state.peerIk ++
                (_root_.Comparse.NonExtensibleMessageFormat.slowBytes.serialize ls.state.rk ++
                  (_root_.Comparse.NonExtensibleMessageFormat.slowBytes.serialize ls.state.dhs ++
                    (_root_.Comparse.NonExtensibleMessageFormat.slowBytes.serialize ls.state.cks ++
                      (_root_.Comparse.NonExtensibleMessageFormat.uint32.serialize ls.state.ns ++
                        (_root_.Comparse.NonExtensibleMessageFormat.uint32.serialize ls.state.pn ++
                          (_root_.Comparse.NonExtensibleMessageFormat.slowBytes.serialize ls.state.sid ++
                            (_root_.Comparse.NonExtensibleMessageFormat.bool.serialize ls.state.initiator ++
                              (_root_.Comparse.NonExtensibleMessageFormat.slowNat.serialize ls.state.rIdx ++
                                _root_.Comparse.NonExtensibleMessageFormat.slowBytes.serialize ls.state.spqr))))))))))))
        ((_root_.Comparse.ExtensibleMessageFormat.list
          (DY.Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize
          ls.state.recv) := by
  simp only [← concatPrefixes_append_eq]; rfl

theorem alice_utf8_sizes : "alice".utf8ByteSize = 5 ∧ "alice".toUTF8.size = 5 := by decide
theorem bob_utf8_sizes : "bob".utf8ByteSize = 3 ∧ "bob".toUTF8.size = 3 := by decide

theorem ofByteArray_pqxdhLabel_props :
    (DY.Libsignal.Composed.Refinement.ofByteArray "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024".toUTF8).head? = some 0x57#8 ∧
    (DY.Libsignal.Composed.Refinement.ofByteArray "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024".toUTF8).length ≠ 64 :=
  ⟨by decide +kernel, by decide +kernel⟩

theorem ofByteArray_whisperRatchet_props :
    (DY.Libsignal.Composed.Refinement.ofByteArray "WhisperRatchet".toUTF8).head? = some 0x57#8 ∧
    (DY.Libsignal.Composed.Refinement.ofByteArray "WhisperRatchet".toUTF8).length ≠ 64 :=
  ⟨by decide +kernel, by decide +kernel⟩

theorem ofByteArray_whisperMessageKeys_props :
    (DY.Libsignal.Composed.Refinement.ofByteArray "WhisperMessageKeys".toUTF8).head? = some 0x57#8 ∧
    (DY.Libsignal.Composed.Refinement.ofByteArray "WhisperMessageKeys".toUTF8).length ≠ 64 :=
  ⟨by decide +kernel, by decide +kernel⟩

theorem setupPublic_0_bridge (r : DY.Libsignal.Composed.Refinement.ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    DY.Libsignal.Composed.Refinement.setupPublic r 0 =
      DY.DiffieHellman.dhPk (DY.Libsignal.Composed.Refinement.randTerm 0 32) := by
  rw [DY.Libsignal.Composed.Refinement.setupPublic, DY.Libsignal.Composed.Refinement.setupSent,
    Symbolic.Swarm.CREF.b1_setupTrace_eq r hNe]
  cases r.withOpk <;> rfl

theorem setupPublic_1_bridge (r : DY.Libsignal.Composed.Refinement.ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    DY.Libsignal.Composed.Refinement.setupPublic r 1 =
      DY.Signature.vk (DY.Libsignal.Composed.Refinement.randTerm 0 32) := by
  rw [DY.Libsignal.Composed.Refinement.setupPublic, DY.Libsignal.Composed.Refinement.setupSent,
    Symbolic.Swarm.CREF.b1_setupTrace_eq r hNe]
  cases r.withOpk <;> rfl

theorem setupPublic_2_bridge (r : DY.Libsignal.Composed.Refinement.ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    DY.Libsignal.Composed.Refinement.setupPublic r 2 =
      DY.DiffieHellman.dhPk (DY.Libsignal.Composed.Refinement.randTerm 5 32) := by
  rw [DY.Libsignal.Composed.Refinement.setupPublic, DY.Libsignal.Composed.Refinement.setupSent,
    Symbolic.Swarm.CREF.b1_setupTrace_eq r hNe]
  cases r.withOpk <;> rfl

theorem setupPublic_3_bridge (r : DY.Libsignal.Composed.Refinement.ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    DY.Libsignal.Composed.Refinement.setupPublic r 3 =
      DY.Signature.vk (DY.Libsignal.Composed.Refinement.randTerm 5 32) := by
  rw [DY.Libsignal.Composed.Refinement.setupPublic, DY.Libsignal.Composed.Refinement.setupSent,
    Symbolic.Swarm.CREF.b1_setupTrace_eq r hNe]
  cases r.withOpk <;> rfl

theorem setupPublic_4_bridge (r : DY.Libsignal.Composed.Refinement.ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    DY.Libsignal.Composed.Refinement.setupPublic r 4 =
      DY.DiffieHellman.dhPk (DY.Libsignal.Composed.Refinement.randTerm 10 32) := by
  rw [DY.Libsignal.Composed.Refinement.setupPublic, DY.Libsignal.Composed.Refinement.setupSent,
    Symbolic.Swarm.CREF.b1_setupTrace_eq r hNe]
  cases r.withOpk <;> rfl

theorem setupPublic_5_bridge (r : DY.Libsignal.Composed.Refinement.ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    DY.Libsignal.Composed.Refinement.setupPublic r 5 =
      DY.Signature.sign (DY.Libsignal.Composed.Refinement.randTerm 5 32)
        (DY.Libsignal.Composed.Refinement.randTerm 11 64)
        (DY.Libsignal.PQXDH.encodeEC (DY.DiffieHellman.dhPk (DY.Libsignal.Composed.Refinement.randTerm 10 32))) := by
  rw [DY.Libsignal.Composed.Refinement.setupPublic, DY.Libsignal.Composed.Refinement.setupSent,
    Symbolic.Swarm.CREF.b1_setupTrace_eq r hNe]
  cases r.withOpk <;> rfl

theorem setupPublic_6_bridge (r : DY.Libsignal.Composed.Refinement.ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    DY.Libsignal.Composed.Refinement.setupPublic r 6 =
      DY.PQKem.kemPk (DY.Libsignal.Composed.Refinement.randTerm 16 64) :=
  Symbolic.Swarm.CREF.b1_setupPublic_6 r hNe

theorem setupPublic_7_bridge (r : DY.Libsignal.Composed.Refinement.ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    DY.Libsignal.Composed.Refinement.setupPublic r 7 =
      DY.Signature.sign (DY.Libsignal.Composed.Refinement.randTerm 5 32)
        (DY.Libsignal.Composed.Refinement.randTerm 17 64)
        (DY.Libsignal.PQXDH.encodeKEM (DY.PQKem.kemPk (DY.Libsignal.Composed.Refinement.randTerm 16 64))) := by
  rw [DY.Libsignal.Composed.Refinement.setupPublic, DY.Libsignal.Composed.Refinement.setupSent,
    Symbolic.Swarm.CREF.b1_setupTrace_eq r hNe]
  cases r.withOpk <;> rfl

theorem spqrSend_spqrInit_key_eq (a p coins : DY.Bytes) :
    (DY.Spqr.spqrSend (DY.Spqr.spqrInit a p) coins).2.1 =
      DY.Spqr.spqrChainKey a p (DY.Spqr.encodeSpqrIndexTerm 1) := by
  simp [DY.Spqr.spqrSend, DY.Spqr.spqrInit, DY.BytesView.view_pack]
theorem spqrSend_after_send_key_eq (st c c' : DY.Bytes) :
    (DY.Spqr.spqrSend (DY.Spqr.spqrSend st c).1 c').2.1 =
      ({ st := (DY.Spqr.spqrSend st c).1, coins := c' } : DY.Spqr.SendKey.SubF DY.Bytes).pack := by
  rfl
theorem spqrRecv_spqrInit_spqrB2A_eq_bridge {pqr pq st' own : DY.Bytes} {idx : UInt32}
    (h : DY.Spqr.spqrRecv (DY.Spqr.spqrInit pqr DY.Libsignal.TripleRatchet.spqrB2A) pq idx =
      some (st', own)) :
    own = if idx = 0 then DY.Spqr.zeroKey
      else DY.Spqr.spqrChainKey pqr DY.Libsignal.TripleRatchet.spqrA2B (DY.Spqr.encodeSpqrIndexTerm idx) := by
  have hdir : DY.Spqr.spqrParamsDir? DY.Libsignal.TripleRatchet.spqrB2A = some .b2a := by rfl
  simp only [DY.Spqr.spqrRecv, DY.Spqr.spqrInit, DY.BytesView.view_pack, hdir] at h
  split at h
  · contradiction
  · injection h with hpair; injection hpair with _ hown; exact hown.symm

@[simp] theorem length_nil_eq : (DY.Trace.nil : DY.ExecTrace).length = 0 := by rfl
@[simp] theorem length_append_entry_eq {T : Type} [DY.ExecTraceTypes.Has T]
    (tr : DY.ExecTrace) (x : T) : (tr.append x).length = tr.length + 1 := by rfl
theorem not_eventLoggedAt_nil {E : Type} [DY.ExecTraceTypes.Has (DY.ProtocolEvent.ExecEntryT E)]
    {ev : E} {j : Nat} (h : (DY.Trace.nil : DY.ExecTrace).EventLoggedAt ev j) : False := by
  cases h
theorem getMessageSentAt_eq_at? (tr : DY.ExecTrace) (i : Nat) :
    tr.getMessageSentAt i =
      match (tr.at? i : Option DY.Network.ExecEntryT) with
      | some ⟨m⟩ => some m
      | none => none := by
  unfold DY.Trace.getMessageSentAt
  rcases (tr.at? i : Option DY.Network.ExecEntryT) with _ | ⟨m⟩ <;> rfl
theorem eventLoggedAt_eq_at? {E : Type} [DY.ExecTraceTypes.Has (DY.ProtocolEvent.ExecEntryT E)]
    (tr : DY.ExecTrace) (ev : E) (j : Nat) :
    tr.EventLoggedAt ev j = ((tr.at? j : Option (DY.ProtocolEvent.ExecEntryT E)) = some ⟨ev⟩) := by
  rfl
theorem eventLoggedAt_iff_at? (E : Type) [DY.ExecTraceTypes.Has (DY.ProtocolEvent.ExecEntryT E)]
    (tr : DY.ExecTrace) (ev : E) (j : Nat) :
    tr.EventLoggedAt ev j ↔ (tr.at? j : Option (DY.ProtocolEvent.ExecEntryT E)) = some ⟨ev⟩ := by
  rfl
theorem getEventAt_eq_at? (E : Type) [DY.ExecTraceTypes.Has (DY.ProtocolEvent.ExecEntryT E)]
    (tr : DY.ExecTrace) (j : Nat) :
    tr.getEventAt E j =
      match (tr.at? j : Option (DY.ProtocolEvent.ExecEntryT E)) with
      | some ⟨ev⟩ => some ev
      | none => none := by
  unfold DY.Trace.getEventAt
  rcases (tr.at? j : Option (DY.ProtocolEvent.ExecEntryT E)) with _ | ⟨ev⟩ <;> rfl
theorem traceful_run_bind_snd {α β : Type} (x : DY.Traceful α)
    (f : α → DY.Traceful β) (tr : DY.ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).2.val
      | none => (x.run tr).2.val := by
  rw [DY.Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr1⟩
  · rfl
  · rcases (f a).run tr1.val with ⟨_, _⟩; rfl
@[simp] theorem traceful_run_pure_fst {α : Type} (a : α) (tr : DY.ExecTrace) :
    ((pure a : DY.Traceful α).run tr).1 = some a := by rfl
@[simp] theorem traceful_run_pure_snd {α : Type} (a : α) (tr : DY.ExecTrace) :
    ((pure a : DY.Traceful α).run tr).2.val = tr := by rfl
@[simp] theorem traceful_run_failure_fst {α : Type} (tr : DY.ExecTrace) :
    ((failure : DY.Traceful α).run tr).1 = none := by rfl
@[simp] theorem traceful_run_failure_snd {α : Type} (tr : DY.ExecTrace) :
    ((failure : DY.Traceful α).run tr).2.val = tr := by rfl
@[simp] theorem monadLift_err_fst_eq {α : Type} (x : DY.Err α) (tr : DY.ExecTrace) :
    ((liftM x : DY.Traceful α).run tr).1 = DY.Libsignal.PQXDH.errToOption x := by
  cases x <;> rfl
@[simp] theorem monadLift_err_snd_eq {α : Type} (x : DY.Err α) (tr : DY.ExecTrace) :
    ((liftM x : DY.Traceful α).run tr).2.val = tr := by
  cases x <;> rfl
theorem storeLocalState_tr_snd_eq (p : DY.Participant) (st : DY.Libsignal.TripleRatchet.TRState)
    (tr : DY.ExecTrace) :
    ((DY.PersistentLocalState.storeLocalState p st).run tr).2.val =
      tr.append (⟨({ participant := p, state := st } : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState)⟩ :
        DY.PersistentGlobalState.State.ExecEntryT (DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState)) := by
  rfl
theorem storeLocalState_pq_snd_eq (p : DY.Participant) (st : DY.Libsignal.PQXDH.PQXDHState)
    (tr : DY.ExecTrace) :
    ((DY.PersistentLocalState.storeLocalState p st).run tr).2.val =
      tr.append (⟨({ participant := p, state := st } : DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState)⟩ :
        DY.PersistentGlobalState.State.ExecEntryT (DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState)) := by
  rfl
theorem aliceStart_cont_run_snd_eq (tr : DY.ExecTrace) (a b : DY.Participant)
    (o : DY.Libsignal.PQXDH.AliceHandshakeOut) :
    ((do
      let dhsA ← DY.Random.genRand 32
      let (rkA, cksA) := DY.Libsignal.TripleRatchet.createChain o.keys.rk o.spk dhsA
      let stA : DY.Libsignal.TripleRatchet.TRState := {
        peer := b, myIk := DY.Libsignal.PQXDH.serializedIk o.ikA,
        peerIk := DY.Libsignal.PQXDH.serializedIk o.ikB, rk := rkA, dhs := dhsA,
        cks := cksA, ns := 0, pn := 0,
        sid := DY.Concat.concat (DY.DiffieHellman.dhPk dhsA) o.keys.rk,
        initiator := true, rIdx := 1,
        recv := [{ ratchetKey := o.spk, chainKey := o.keys.ck, index := 0, rIdx := 1 }],
        spqr := DY.Spqr.spqrInit o.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B }
      let _ ← DY.Network.sendMessage o.ek
      let _ ← DY.Network.sendMessage o.ct
      let doneIdx ← DY.Libsignal.TripleRatchet.traceLength
      DY.ProtocolEvent.logEvent
        (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys)
      DY.ProtocolEvent.logEvent
        (DY.Libsignal.TripleRatchet.TREvent.InitSession a b (DY.DiffieHellman.dhPk dhsA) o.spk)
      DY.ProtocolEvent.logEvent (DY.Libsignal.Composed.ComposedEvent.HandshakeSession (stA.sessionInfo a) doneIdx)
      DY.PersistentLocalState.storeLocalState a stA).run
      ((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append (⟨32⟩ : DY.Random.ExecEntryT))).2.val =
    let dhsA := DY.Libsignal.Composed.Refinement.randTerm (tr.length + 2) 32
    let (rkA, cksA) := DY.Libsignal.TripleRatchet.createChain o.keys.rk o.spk dhsA
    let stA : DY.Libsignal.TripleRatchet.TRState := {
      peer := b, myIk := DY.Libsignal.PQXDH.serializedIk o.ikA,
      peerIk := DY.Libsignal.PQXDH.serializedIk o.ikB, rk := rkA, dhs := dhsA,
      cks := cksA, ns := 0, pn := 0,
      sid := DY.Concat.concat (DY.DiffieHellman.dhPk dhsA) o.keys.rk,
      initiator := true, rIdx := 1,
      recv := [{ ratchetKey := o.spk, chainKey := o.keys.ck, index := 0, rIdx := 1 }],
      spqr := DY.Spqr.spqrInit o.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B }
    ((((((((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append (⟨32⟩ : DY.Random.ExecEntryT)).append
      (⟨32⟩ : DY.Random.ExecEntryT)).append (⟨o.ek⟩ : DY.Network.ExecEntryT)).append
      (⟨o.ct⟩ : DY.Network.ExecEntryT)).append
      (⟨DY.Libsignal.PQXDH.PQXDHEvent.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys⟩ :
        DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)).append
      (⟨DY.Libsignal.TripleRatchet.TREvent.InitSession a b (DY.DiffieHellman.dhPk dhsA) o.spk⟩ :
        DY.ProtocolEvent.ExecEntryT DY.Libsignal.TripleRatchet.TREvent)).append
      (⟨DY.Libsignal.Composed.ComposedEvent.HandshakeSession (stA.sessionInfo a) (tr.length + 5)⟩ :
        DY.ProtocolEvent.ExecEntryT DY.Libsignal.Composed.ComposedEvent)).append
      (⟨{ participant := a, state := stA }⟩ :
        DY.PersistentGlobalState.State.ExecEntryT
          (DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState)) := by rfl
theorem logEvent_snd_eq {E : Type} [DY.ExecTraceTypes.Has (DY.ProtocolEvent.ExecEntryT E)]
    (ev : E) (tr : DY.ExecTrace) :
    ((DY.ProtocolEvent.logEvent ev).run tr).2.val =
      tr.append (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT E) := by
  rfl
theorem getEntry_run_eq (E : Type) [DY.ExecTraceTypes.Has E] (idx : Nat) (tr : DY.ExecTrace) :
    ((DY.getEntry idx : DY.Traceful E).run tr).1 = (tr.at? idx : Option E) ∧
    ((DY.getEntry idx : DY.Traceful E).run tr).2.val = tr := by exact ⟨rfl, rfl⟩
theorem receiveMessage_fst_eq (idx : Nat) (tr : DY.ExecTrace) :
    ((DY.Network.receiveMessage idx).run tr).1 = tr.getMessageSentAt idx := by
  unfold DY.Network.receiveMessage DY.Trace.getMessageSentAt
  rw [DY.Traceful.run_bind]
  rcases h : ((DY.getEntry idx : DY.Traceful DY.Network.ExecEntryT).run tr) with ⟨_ | ⟨t⟩, tr1⟩
  · have h1 := (getEntry_run_eq DY.Network.ExecEntryT idx tr).1; rw [h] at h1; rw [← h1]
  · have h1 := (getEntry_run_eq DY.Network.ExecEntryT idx tr).1; rw [h] at h1; rw [← h1]; rfl
theorem requireTracePredicate_run_eq (P : DY.ExecTrace → Bool) (tr : DY.ExecTrace) :
    ((DY.Libsignal.PQXDH.guardTrace P).run tr).1 = (if P tr then some () else none) ∧
    ((DY.Libsignal.PQXDH.guardTrace P).run tr).2.val = tr := by
  exact ⟨rfl, rfl⟩
theorem getGlobalState_snd_eq {StateT : Type}
    [DY.ExecTraceTypes.Has (DY.PersistentGlobalState.State.ExecEntryT StateT)]
    (i : Nat) (tr : DY.ExecTrace) :
    (((DY.PersistentGlobalState.getGlobalState i : DY.Traceful StateT)).run tr).2.val = tr := by
  unfold DY.PersistentGlobalState.getGlobalState
  rw [traceful_run_bind_snd, (getEntry_run_eq (DY.PersistentGlobalState.State.ExecEntryT StateT) i tr).2]
  split <;> rfl
theorem getLocalState_snd_eq {StateT : Type}
    [DY.ExecTraceTypes.Has (DY.PersistentLocalState.State.ExecEntryT StateT)]
    (me : DY.Participant) (i : Nat) (tr : DY.ExecTrace) :
    (((DY.PersistentLocalState.getLocalState me i : DY.Traceful StateT)).run tr).2.val = tr := by
  unfold DY.PersistentLocalState.getLocalState
  rw [traceful_run_bind_snd, getGlobalState_snd_eq]
  split
  · rw [traceful_run_bind_snd]
    unfold _root_.guard
    split
    · rw [DY.Traceful.run_pure]; dsimp only; split <;> rfl
    · split <;> rfl
  · rfl
theorem genRand_snd_eq (n : Nat) (tr : DY.ExecTrace) :
    ((DY.Random.genRand n : DY.Traceful DY.Bytes).run tr).2.val =
      tr.append (⟨n⟩ : DY.Random.ExecEntryT) := by rfl

theorem run_sendMessage_bind_snd {α : Type} (msg : DY.Bytes) (f : Nat → DY.Traceful α)
    (tr : DY.ExecTrace) :
    ((DY.Network.sendMessage msg >>= f).run tr).2.val =
      ((f tr.length).run (tr.append (⟨msg⟩ : DY.Network.ExecEntryT))).2.val := by rfl

theorem messageEncrypt_cont_run_snd_eq (tr₂ : DY.ExecTrace) (me : DY.Participant)
    (sIdx : Nat) (stA : DY.Libsignal.TripleRatchet.TRState) (cl : Nat) (pqSalt : DY.Bytes) :
    let m := DY.Libsignal.Composed.Refinement.randTerm tr₂.length 32
    let coins := DY.Libsignal.Composed.Refinement.randTerm (tr₂.length + 1) cl
    let spqr' := (DY.Spqr.spqrSend stA.spqr coins).1
    let key := (DY.Spqr.spqrSend stA.spqr coins).2.1
    let pqMsg := (DY.Spqr.spqrSend stA.spqr coins).2.2
    let trPre := ((tr₂.append (⟨32⟩ : DY.Random.ExecEntryT)).append
      (⟨cl⟩ : DY.Random.ExecEntryT)).append (⟨key⟩ : DY.Network.ExecEntryT)
    let cks' := (DY.Libsignal.TripleRatchet.kdfCk stA.cks).1
    let seed := (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2
    let keys := DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed
    let ct := DY.SymEnc.symEnc keys.cipherKey keys.iv m
    let wire := DY.Libsignal.TripleRatchet.trHonestWireMsg
      (DY.DiffieHellman.dhPk stA.dhs) stA.ns stA.pn ct pqMsg
    let mac := DY.Libsignal.TripleRatchet.computeMac keys.macKey stA.myIk stA.peerIk wire
    let out := DY.Concat.concat wire mac
    let stA' : DY.Libsignal.TripleRatchet.TRState :=
      { stA with cks := cks', ns := stA.ns + 1, spqr := spqr' }
    ((do
      DY.ProtocolEvent.logEvent
        (DY.Libsignal.TripleRatchet.TREvent.Sent me stA.peer (DY.DiffieHellman.dhPk stA.dhs) stA.ns m)
      let _ ← DY.Libsignal.TripleRatchet.logMessageKeyAndStore
        me (stA.sessionInfo me) .sender
        seed pqSalt stA.ns stA.rIdx sIdx stA'
      DY.Network.sendMessage (DY.Concat.concat wire mac)).run trPre).2.val =
    (((trPre.append
      (⟨DY.Libsignal.TripleRatchet.TREvent.Sent me stA.peer (DY.DiffieHellman.dhPk stA.dhs) stA.ns m⟩ :
        DY.ProtocolEvent.ExecEntryT DY.Libsignal.TripleRatchet.TREvent)).append
      (⟨DY.Libsignal.TripleRatchet.TREvent.MessageKey (stA.sessionInfo me) .sender
        seed pqSalt stA.ns stA.rIdx sIdx⟩ :
        DY.ProtocolEvent.ExecEntryT DY.Libsignal.TripleRatchet.TREvent)).append
      (⟨{ participant := me, state := stA' }⟩ :
        DY.PersistentGlobalState.State.ExecEntryT
          (DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState))).append
      (⟨out⟩ : DY.Network.ExecEntryT) := by rfl

end Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
