/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.StoredRk
public import Symbolic.Proofs.Swarm.CREF.TR.G1.CanonRep
public import Symbolic.Proofs.RngG.R3ModelInv
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.R3ChainsWFPresPure
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Actions.Network
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPureA
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.Sem
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Refinement.EncodeWithCovered -- shake: keep
import Symbolic.Proofs.Swarm.CREF.Cli.PureCRel -- shake: keep
import Symbolic.Proofs.SR.RecvSpecWPure -- shake: keep
import Symbolic.Proofs.Refinement.RngFree.SendSpecPure -- shake: keep
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.PinCoinsPure -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.G1.G1RepMacTR -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.Leaks -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.NoTrWireU -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.RecvCol -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.RecvRep -- shake: keep
import Symbolic.Proofs.Swarm.TRREF.B3DefsPure -- shake: keep
import Symbolic.Proofs.Swarm.TRREF.SpqrSemOf -- shake: keep
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Actions.Network

/-!
# Existing-Chain Decrypt Helpers and Ratchet-Key Dispatch Definitions

Proves setup public-key attacker knowledge, receiver-chain well-formedness preservation on the
existing-chain branch, and defines `AuthenticDecryptRepB3St` and `NoRatchetPkDispatchAt`.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR hiding PureBinCanonSession PureRecordRepr SpqrSem at?_append_of_lt getLocalState_fst newRandoms_append_rnd runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc run_bind_fst run_bind_snd
cref_open
cref_open_tr
open DY.Libsignal.TripleRatchet
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.TripleRatchet (SessionInfo RecvChain findRecvChain setRecvChain recvChainFor
  consumeMessageKey computeMac messageVersion)

theorem knows_setupPublic (r₀ : ProtocolSetup) (hNe : r₀.alice ≠ r₀.bob) (ms : List Move) (i : Nat) (hi : i = 0 ∨ i = 2) :
    (setupPublic r₀ i).AttackerKnows (runTraceMoves r₀ ms) := by
  apply setupSent_known
  let f (T : ExecTrace) : List DY.Bytes :=
    (newIndices Trace.nil T).filterMap fun k => T.getMessageSentAt k
  have hnil : f Trace.nil = [] := by
    simp [f, newIndices, Symbolic.DYBridge.DY.Trace.length_eq_1]
  have happ : ∀ {E : Type} [ExecTraceTypes.Has E] (T : ExecTrace) (e : E),
      f (T.append e) = f T ++
        (match ((T.append e).at? T.length : Option Network.ExecEntryT) with
         | none => []
         | some entry => [entry.msg]) := by
    intro E _ T e
    have hidx : newIndices Trace.nil (T.append e) = newIndices Trace.nil T ++ [T.length] := by
      simp [newIndices, Symbolic.DYBridge.DY.Trace.length_eq_1,
        Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        List.range'_concat]
    have hpre : List.filterMap (fun k => (T.append e).getMessageSentAt k) (newIndices Trace.nil T) =
        f T := by
      apply List.filterMap_congr
      intro k hk
      have hlt : k < T.length := by
        simp [newIndices, Symbolic.DYBridge.DY.Trace.length_eq_1, List.mem_range'] at hk
        omega
      simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1,
        Symbolic.Swarm.CREF.TR.at?_append_of_lt T e hlt]
    have hlast := Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1 T.length (T.append e)
    dsimp only [f]
    rw [hidx, List.filterMap_append, hpre]
    cases hproj : ((T.append e).at? T.length : Option Network.ExecEntryT) <;>
      simp [List.filterMap_cons, List.filterMap_nil, hlast, hproj, f]
  have hnet : ∀ (T : ExecTrace) (b : DY.Bytes), f (T.append (b1_NetE b)) = f T ++ [b] := by
    intro T b; rw [happ, Symbolic.Swarm.CREF.TR.at?_append_eq T (b1_NetE b) rfl]
  have hrnd : ∀ (T : ExecTrace) (n : Nat), f (T.append (b1_RndE n)) = f T := by
    intro T n; rw [happ, Symbolic.Swarm.CREF.TR.at?_append_eq_of_proj T (b1_RndE n) rfl none rfl, List.append_nil]
  have hev : ∀ (T : ExecTrace) (ev), f (T.append (b1_EvE ev)) = f T := by
    intro T ev; rw [happ, Symbolic.Swarm.CREF.TR.at?_append_eq_of_proj T (b1_EvE ev) rfl none rfl, List.append_nil]
  have hst : ∀ (T : ExecTrace) (p : DY.Participant) (s), f (T.append (b1_StE p s)) = f T := by
    intro T p s; rw [happ, Symbolic.Swarm.CREF.TR.at?_append_eq_of_proj T (b1_StE p s) rfl none rfl, List.append_nil]
  have hsent : setupSent r₀ = f (if r₀.withOpk then b1_setupTr5 r₀.alice r₀.bob else b1_setupTr4 r₀.alice r₀.bob) := by
    rw [setupSent, b1_setupTrace_eq r₀ hNe]
  rw [setupPublic, hsent]
  rcases hi with rfl | rfl <;> cases r₀.withOpk
  · simp only [↓reduceIte, Bool.false_eq_true, b1_setupTr4, b1_setupTr3, b1_setupTr2, b1_setupTr1,
      hnet, hrnd, hev, hst, hnil, List.nil_append, List.cons_append]
    exact List.mem_cons_self
  · simp only [↓reduceIte, b1_setupTr5, b1_setupTr4, b1_setupTr3, b1_setupTr2, b1_setupTr1,
      hnet, hrnd, hev, hst, hnil, List.nil_append, List.cons_append]
    exact List.mem_cons_self
  · simp only [↓reduceIte, Bool.false_eq_true, b1_setupTr4, b1_setupTr3, b1_setupTr2, b1_setupTr1,
      hnet, hrnd, hev, hst, hnil, List.nil_append, List.cons_append]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · simp only [↓reduceIte, b1_setupTr5, b1_setupTr4, b1_setupTr3, b1_setupTr2, b1_setupTr1,
      hnet, hrnd, hev, hst, hnil, List.nil_append, List.cons_append]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

end Symbolic.Swarm.CREF.CliPure.TR

namespace Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
open Symbolic.Swarm.CREF.TR hiding PureBinCanonSession PureRecordRepr SpqrSem at?_append_of_lt getLocalState_fst newRandoms_append_rnd runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc run_bind_fst run_bind_snd

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (SessionInfo DRState KeyComponent KeyDir RecvChain findRecvChain setRecvChain recvChainFor consumeMessageKey chainKeyAt kdfCk kdfRk maxForwardJumps u32Max computeMac messageVersion createChain x25519LowOrder litByte)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Refinement (sha256CompressFunction x25519PublicKeySymbol aesCbcEncryptSymbol aesCbcDecryptSymbol ExternCryptoLawsHold encodeWith canonicalVariation WireFields FieldItem PbValue readVarint paddedVarint encodeField readVarint_paddedVarint)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.CBC (blockToBytesLE)
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec encodeRecord
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 hiding encodeRecord
open CryptoVerification.SessionModel (chainStepN skippedKeys)
open CryptoVerification.SessionModel.AdvanceAndFrame
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.Refinement
open Proofs.libsignal.RngG Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3
open Proofs.libsignal.SR (AesW   messageDecryptSignalW)
open Symbolic.Swarm.CREF.CliPure.RpkCli (pinCoins)

open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec senderChainToChainRec receiverChainToChainRec)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.FreshSigma (at?_eq_some_of_getLocalState_some)
open Symbolic.Swarm.CREF.TR.Pure
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf saltToBytes spqrIdx1Bytes
  spqrSendOf_of_send_some spqrKeyBytes_saltToBytes)
open Symbolic.Swarm.CREF.TR.G1 (g1_rep_of_recvRepresentations)
open Symbolic.Swarm.CREF.TR.NoTrWireU (NoTrWireU )
open Symbolic.Swarm.CREF.TR.RecvCol (TRRecvAllCollide)
open Symbolic.Swarm.CREF.TR.RecvRep (decrypt_recvRepresentations_nonempty_of_tryFrom)

theorem getElem?_receiverChains_inj_of_nodup
    {rcs : List ReceiverChain} (hnodup : (rcs.map ReceiverChain.senderRatchetKey).Nodup)
    {i j : Nat} {rc₁ rc₂ : ReceiverChain} {pk : PublicKey}
    (h1 : rcs[i]? = some rc₁) (h2 : rcs[j]? = some rc₂) (hk1 : rc₁.senderRatchetKey = pk) (hk2 : rc₂.senderRatchetKey = pk) : i = j := by
  have hi : i < (rcs.map ReceiverChain.senderRatchetKey).length := by rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp h1).1
  have hj : j < (rcs.map ReceiverChain.senderRatchetKey).length := by rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp h2).1
  have hm1 : (rcs.map ReceiverChain.senderRatchetKey)[i]? = some pk := by rw [List.getElem?_map, h1]; exact congrArg some hk1
  have hm2 : (rcs.map ReceiverChain.senderRatchetKey)[j]? = some pk := by rw [List.getElem?_map, h2]; exact congrArg some hk2
  rw [List.getElem?_eq_getElem hi] at hm1; rw [List.getElem?_eq_getElem hj] at hm2
  exact (List.Nodup.getElem_inj_iff hnodup).mp (Option.some.inj (hm1.trans hm2.symm))

theorem nodup_and_lt_of_existing_tr
    {F : ShaCompress} {their : PublicKey} {counter : BitVec 32} {ck ck_adv ck_next : ChainKey} {r_adv r2 : RatchetState}
    {s s' : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    (hFind : (ratchetStateOf s.state).findReceiverChainKey their = .ok (some ck)) (hNotLt : ¬ (counter < ck.index))
    (hAdv : Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) (ratchetStateOf s.state) = (.ok ck_adv, r_adv))
    (hNext : ck_adv.nextChainKey F = .ok ck_next) (hSet : Mut.exec (RatchetState.setReceiverChainKey their ck_next) r_adv = (.ok (), r2))
    (hs' : s'.state.receiverChains = r2.receiverChains) (hwf : RecordChainsWF3 (sessionToRecordRec s)) :
    RecordChainsWF3 (sessionToRecordRec s') := by
  apply recordChainsWF3_of_chainsWFm; rw [hs']
  exact chainsWFm_existing hFind hNotLt hAdv hNext hSet (chainsWFm_of_recordChainsWF3 hwf)

end Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep

namespace Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt
open Symbolic.Swarm.CREF.TR hiding PureBinCanonSession PureRecordRepr SpqrSem at?_append_of_lt getLocalState_fst newRandoms_append_rnd runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc run_bind_fst run_bind_snd

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (SessionInfo DRState KeyComponent KeyDir RecvChain findRecvChain setRecvChain recvChainFor consumeMessageKey chainKeyAt kdfCk kdfRk maxForwardJumps u32Max computeMac messageVersion createChain x25519LowOrder litByte)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Refinement (sha256CompressFunction x25519PublicKeySymbol aesCbcEncryptSymbol aesCbcDecryptSymbol ExternCryptoLawsHold encodeWith canonicalVariation WireFields FieldItem PbValue readVarint paddedVarint encodeField readVarint_paddedVarint)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.CBC (blockToBytesLE)
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec encodeRecord
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 hiding encodeRecord
open CryptoVerification.SessionModel (chainStepN skippedKeys)
open CryptoVerification.SessionModel.AdvanceAndFrame
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.Refinement
open Proofs.libsignal.RngG Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3
open Proofs.libsignal.SR (AesW   messageDecryptSignalW)
open Symbolic.Swarm.CREF.CliPure.RpkCli (pinCoins)

open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec senderChainToChainRec receiverChainToChainRec)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.FreshSigma (at?_eq_some_of_getLocalState_some)
open Symbolic.Swarm.CREF.TR.Pure
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf saltToBytes spqrIdx1Bytes
  spqrSendOf_of_send_some spqrKeyBytes_saltToBytes)
open Symbolic.Swarm.CREF.TR.G1 (g1_rep_of_recvRepresentations)
open Symbolic.Swarm.CREF.TR.NoTrWireU (NoTrWireU )
open Symbolic.Swarm.CREF.TR.RecvCol (TRRecvAllCollide)
open Symbolic.Swarm.CREF.TR.RecvRep (decrypt_recvRepresentations_nonempty_of_tryFrom)
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep

/-- Salt-form authentic decrypt representation at a fixed provenance state `st_prov`. -/
def AuthenticDecryptRepB3St (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : SpqrSem)
    (g : Ghost) (ms₁ : List Move) (_body pt : HwBytes) (_t₀ : DY.Bytes) (msg₀ : TRSignalMsg)
    (st_prov : TRState) (_salt seed : DY.Bytes) : Prop :=
  ∃ (st_s : TRState) (t_c coinsLen : Nat),
    st_s ∈ availableStates r₀ (runTraceMoves r₀ ms₁) ∧
    msg₀.pqRatchet = (DY.Spqr.spqrSend st_s.spqr (randTerm t_c coinsLen)).2.2 ∧
    DY.Spqr.spqrEmptyMsg msg₀.pqRatchet = false ∧
    ∃ (pqSalt ptTerm : DY.Bytes),
      pqSalt.AttackerKnows (runTraceMoves r₀ ms₁) ∧
      msg₀.mac = computeMac (trMsgKeys pqSalt seed).macKey st_prov.peerIk st_prov.myIk msg₀.wire ∧
      DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv msg₀.ciphertext = some ptTerm ∧
      gamma interpretation S g ptTerm = pt

/-- Existing-chain ratchet-key dispatch hypothesis at `(g, ms₁)`. -/
def NoRatchetPkDispatchAt (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : SpqrSem)
    (g : Ghost) (ms₁ : List Move) (_τ₁ : List MachineEvent) : Prop :=
  ∀ (p : Participant) (stateIdx₀ : Nat) (body ptBytes : HwBytes) (m : SignalMessage) (st₀ : TRState)
    (c c' : RecvChain) (t₀ seed k_own : DY.Bytes) (msg₀ : TRSignalMsg),
    ModelRun r₀ ms₁ → (runTraceMoves r₀ ms₁).Reachable reachability →
    SignalMessage.tryFrom protoSignalCodec body = .ok m →
    t₀ ∈ recvRepresentations interpretation r₀ S g ms₁ body → parseTrSignalMsg t₀ = some msg₀ →
    msg₀.version = messageVersion → msg₀.counter = UInt32.ofBitVec m.counter →
    ¬RecvCollision interpretation r₀ S g ms₁ t₀ →
    ¬ReselectCollision interpretation r₀ S g ms₁ t₀ →
    ((PersistentLocalState.getLocalState p stateIdx₀ : Traceful TRState).run (runTraceMoves r₀ ms₁)).1 = some st₀ →
    c ∈ st₀.recv → consumeMessageKey c msg₀.counter = some (seed, c') →
    (msg₀.ratchetKey = c.ratchetKey → recvSeed st₀ msg₀ = some seed) →
    k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms₁) st₀ msg₀ →
    Symbolic.Swarm.CREF.TR.G1.RecvHistInvTR interpretation S g r₀ ms₁ →
    Symbolic.Swarm.CREF.TR.G1.InstallWitnessTR r₀ (runTraceMoves r₀ ms₁) →
    RkKnownOrInit (runTraceMoves r₀ ms₁) c.ratchetKey →
    gamma interpretation S g c.ratchetKey = m.senderRatchetKey.bytes.toList →
    body.drop (body.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₀.wire) →
    st₀.peerIk.AttackerKnows (runTraceMoves r₀ ms₁) → st₀.myIk.AttackerKnows (runTraceMoves r₀ ms₁) →
    interpretation DY.Libsignal.Refinement.aesCbcDecryptSymbol
      [m.ciphertext, gamma interpretation S g (trMsgKeys k_own seed).cipherKey,
       (gamma interpretation S g (trMsgKeys k_own seed).iv).take 16] = some ptBytes →
    ∃ (t₁ : DY.Bytes) (msg₁ : TRSignalMsg),
      t₁ ∈ recvRepresentations interpretation r₀ S g ms₁ body ∧ parseTrSignalMsg t₁ = some msg₁ ∧
      msg₁.version = messageVersion ∧ msg₁.ratchetKey = c.ratchetKey ∧ msg₁.counter = msg₀.counter ∧
      body.drop (body.length - 8) =
        gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₁.wire) ∧
      (seed.AttackerKnows (runTraceMoves r₀ ms₁) ∨ ∃ salt ∈ honestSalts r₀ ms₁,
        AuthenticDecryptRepB3St interpretation r₀ S g ms₁ body ptBytes t₁ msg₁ st₀ salt seed ∧
        gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₁.wire) =
          gamma interpretation S g (computeMac (trMsgKeys salt seed).macKey st₀.peerIk st₀.myIk msg₁.wire) ∧
        interpretation DY.Libsignal.Refinement.aesCbcDecryptSymbol
          [m.ciphertext, gamma interpretation S g (trMsgKeys salt seed).cipherKey,
           (gamma interpretation S g (trMsgKeys salt seed).iv).take 16] = some ptBytes)

end Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt
