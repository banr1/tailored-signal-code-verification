/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecTieSeedEqPure
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2AdapterPure
import Batteries.Data.UInt
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecTieSeedShapePure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvAtFactsPure
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.AcceptCliPure
public import Symbolic.Proofs.Swarm.CREF.Sem
public import Symbolic.Proofs.Swarm.TRREF.B3DefsPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecTieAPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecTieBExclPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.DecCryptoBPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepNoRatchetPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SendRetCoinsCliPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SendRetCoinsCliPureB
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplRep
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import Symbolic.Proofs.Swarm.CREF.TR.SkippedSeedLineage
import Symbolic.Proofs.Swarm.CREF.TR.TrStateRkCkIk
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.Proofs.Swarm.CREF.Xpl.SkippedHit
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Cross-Branch Exclusion for Promote Chain-Step vs Model `decryptSkipped`

Proves `prom_seedEq_core` and `prom_not_decryptSkipped_of_binStep`, ruling out an accepting model
`Move.decryptSkipped` when the implementation takes the existing-chain step branch
(`PromDecSelNoRatchet`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
cref_open_tr

open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (RecvChain findRecvChain consumeMessageKey computeMac)
open DY.Libsignal.Refinement (sha256CompressFunction ExternCryptoLawsHold)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 hiding encodeRecord
open Proofs.libsignal.RngG Proofs.libsignal.Hooks2 Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec)
open Symbolic.Swarm.TRREF
open Symbolic.Swarm.CREF.TR.Pure
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.RecvDecStep Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
open Symbolic.Swarm.CREF.CliPure.TR.SendRetCoins (stateRel_sessionToRecordRec_extract_TR gamma_litOf gamma_trMsgKeys_eq_generateKeys gamma_computeMac_tr)

theorem prom_accBlk_nil_no_rng' (b pt : HwBytes) :
    ∀ e ∈ promAccBlk b [] pt, eventKind e ≠ .rng := by
  intro e he
  simp only [promAccBlk, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> simp [eventKind]

theorem prom_accBlk_rng (b rngBytes pt : HwBytes) :
    ∃ e ∈ promAccBlk b [.rng rngBytes] pt, eventKind e = .rng :=
  ⟨.rng rngBytes, by simp [promAccBlk], rfl⟩

/-- Synthetic `RecvWireGhost` packaging the session `sess` and record bytes `rec` for lemmas that
inspect only `.sess` and `.stateBytes`. -/
def promGhost (rec : HwBytes) (sess : Session (List (BitVec 8))) : RecvWireGhost :=
  { who := 0, aPtr := 0, meBytes := [], stateBytes := rec, sess := sess, wirePtr := 0,
    wireBytes := [], cur := 0, rest := [], tlsInit := none }

private theorem prom_tryFrom_serialized_eq {body : HwBytes} {m : SignalMessage}
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m) : m.serialized = body := by
  simp only [SignalMessage.tryFrom, bind, Except.bind, Pure.pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at htry
  split at htry; · cases htry
  split at htry; · cases htry
  split at htry; · cases htry
  split at htry <;> try cases htry
  split at htry <;> try cases htry
  split at htry <;> try cases htry
  split at htry <;> try cases htry
  split at htry <;> try cases htry
  rfl

section X2
variable {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
  {who : List Participant} {ok : Nat → Bool}
  {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
  {rec b : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
  {sess sess' : Session (List (BitVec 8))}
  {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}

/-- In the existing-chain branch (`PromDecSelNoRatchet`), the model chain `c` at `ci` consumes
`msg.counter`, matches `msg.ratchetKey` under `gamma`, and produces a MAC matching `msg.mac`. -/
theorem prom_seedEq_core
    (hceh : ExternCryptoLawsHold interpretation) (hwf : ProtocolSetupWF r) (hS : S = compSemOf interpretation r)
    (hC : PromAcceptCallBy₂ interpretation r S who ok j e' mid acc rec b sm pf
      sess sess' coins expected pt)
    (hsel : PromDecSelNoRatchet sess pf.inner mid coins)
    (g : Ghost) (ms : List Move)
    (hcompat : GhostAndSemMatchSetup interpretation r S g) (hrun : ModelRun r ms)
    (hat : RecvDecStepAt.RecvAtFacts interpretation r S g ms)
    (p : Participant) (stateIdx : Nat) (st : TRState) (c : RecvChain) (t : DY.Bytes)
    (msg : TRSignalMsg) (ci : Nat) (rc : ReceiverChain) (ck : ChainKey)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run
      (runTraceMoves r ms)).1 = some st)
    (hrel : StateRel interpretation S g st (sessionToRecordRec sess))
    (hnd : ((sessionToRecordRec sess).current.receiverChains.map
      ChainRec.senderRatchetKey).Nodup)
    (hpq : sess.state.pqRatchetState = gamma interpretation S g st.spqr)
    (hks : TRKeyShape interpretation S g st)
    (hc : st.recv[ci]? = some c)
    (hrep : t ∈ recvRepresentations interpretation r S g ms pf.message)
    (hparse : parseTrSignalMsg t = some msg)
    (htry : SignalMessage.tryFrom protoSignalCodec pf.message = .ok pf.inner)
    (hrc : sess.state.receiverChains[ci]? = some rc)
    (hrc_key : rc.senderRatchetKey = pf.inner.senderRatchetKey) (hck : rc.chainKey = some ck) :
    ∃ seed_c c', consumeMessageKey c msg.counter = some (seed_c, c') ∧
      findRecvChain st.recv c.ratchetKey = some c ∧
      gamma interpretation S g c.ratchetKey = gamma interpretation S g msg.ratchetKey ∧
      st ∈ availableStates r (runTraceMoves r ms) ∧
      ({ st := st.spqr, msg := msg.pqRatchet } : DY.Spqr.RecvKey.SubF DY.Bytes).pack ∈
        ownKeys r (runTraceMoves r ms) st msg ∧
      gamma interpretation S g (computeMac (trMsgKeys
          ({ st := st.spqr, msg := msg.pqRatchet } : DY.Spqr.RecvKey.SubF DY.Bytes).pack seed_c).macKey
          st.peerIk st.myIk msg.wire) =
        gamma interpretation S g msg.mac := by
  have hnodup_rc : (sess.state.receiverChains.map ReceiverChain.senderRatchetKey).Nodup := by
    have hmap : (sessionToRecordRec sess).current.receiverChains.map
          ChainRec.senderRatchetKey =
        (sess.state.receiverChains.map ReceiverChain.senderRatchetKey).map
          PublicKey.serialize := by
      dsimp only [sessionToRecordRec, sessionToSessionRec]; rw [List.map_map, List.map_map]; rfl
    exact List.Nodup.of_map PublicKey.serialize (hmap ▸ hnd)
  obtain ⟨remIk, ck', ck_adv, ck_next, r_adv, r2, mkGen, newPqrState, pqrKey, st', _hmid, _hcoins,
      hRem, hFind, hNotLt, hJump, hAdv, hNext, hSet, hMkGen, hrecv_spqr, hMac, _hDec, _hSt', _hsess',
      _hstate⟩ :=
    prom_adapter_noRatchet_out hC.out hnodup_rc hsel
  have hst_avail : st ∈ availableStates r (runTraceMoves r ms) :=
    Symbolic.Swarm.CREF.TR.RecvHistStep2.mem_availableStates_of_at? r ms
      (Symbolic.Swarm.CREF.TR.FreshSigma.at?_eq_some_of_getLocalState_some hst)
  have hRkLens : ∀ c ∈ st.recv, (gamma interpretation S g c.ratchetKey).length = 32 :=
    hat.lens st hst_avail
  have hst_rci : TrStateRkCkIk r st := trStateRkCkIk_of_getLocalState hrun hst
  have hCkLens : ∀ c ∈ st.recv, (gamma interpretation S g c.chainKey).length = 32 :=
    hst_rci.recv_ck_len interpretation S g hwf hcompat
  have hNodupSym : (st.recv.map RecvChain.ratchetKey).Nodup :=
    nodup_ratchetKey_of_stateRel_tr hrel hnd
  obtain ⟨ci₀, ch, c₀, mks', seed, c', hch0, hc0, hfind₀, hsrk0, htheir, _hck, _hch_ck,
      hcons₀_bv, hSeedEq, hCntEq, _hc'_rk, _hc'_rIdx, _hR2Eq, _hRel_c, _hMks'⟩ :=
    stateRel_and_consumeMessageKey_of_existing_tr interpretation S g hrel hNodupSym hCkLens
      (SendRetCoins.gamma_litOf interpretation S g newPqrState) hFind hNotLt hJump hAdv hNext hSet
  have hc₀_mem : c₀ ∈ st.recv := List.mem_of_getElem? hc0
  have hc_mem : c ∈ st.recv := List.mem_of_getElem? hc
  obtain ⟨hwire_t, hmac_t, _hhd_t, hfld⟩ := hrep.2.2.2 msg hparse
  obtain ⟨_hct_m, hrk_m, _hpq_m, hctr_m, _hver_m⟩ := hfld pf.inner htry
  have hγ_c₀ : gamma interpretation S g c₀.ratchetKey = pf.inner.senderRatchetKey.bytes.toList := by
    rw [htheir]; simp [vec32, hRkLens c₀ hc₀_mem]
  obtain ⟨c₁, hc₁, _hidx₁, hγ_c₁⟩ := a2b_modelChain_of_binChain hrel hrc hck
  have hc₁_eq : c = c₁ := Option.some.inj (hc.symm.trans hc₁)
  subst hc₁_eq
  have hcc : c₀ = c :=
    a2b_recvChain_eq_of_gamma hrel hnd hc₀_mem hc_mem (by rw [hγ_c₀, hγ_c₁, hrc_key])
  subst hcc
  have hctr_eq : UInt32.ofBitVec pf.inner.counter = msg.counter := UInt32.ext hctr_m.symm
  have hcons : consumeMessageKey c₀ msg.counter = some (seed, c') := by
    rw [← hctr_eq]; exact hcons₀_bv
  let k_own : DY.Bytes := ({ st := st.spqr, msg := msg.pqRatchet } : DY.Spqr.RecvKey.SubF DY.Bytes).pack
  have hk_own : k_own ∈ ownKeys r (runTraceMoves r ms) st msg := by
    unfold ownKeys; exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hst_avail, beq_self_eq_true _⟩)
  have hk_own_gam :=
    (spqrRecv_step_gamma_state_and_key interpretation hceh r S hS g ms pf.message st
      (promGhost rec sess) t msg pf.inner newPqrState pqrKey hpq hrep hparse htry hrecv_spqr).2
  have hmkGen_eq : mkGen = ⟨gamma interpretation S g seed, pf.inner.counter⟩ := by
    rw [hMkGen]; change ck_adv.messageKeys (sha256CompressFunction interpretation) = _
    rcases h : ck_adv.messageKeys (sha256CompressFunction interpretation) with ⟨sd, ct⟩
    rw [h] at hSeedEq hCntEq; dsimp only at hSeedEq hCntEq; subst hSeedEq hCntEq; rfl
  obtain ⟨_hck_mk, hmk_mk, _hiv_mk, _⟩ :=
    gamma_trMsgKeys_eq_generateKeys interpretation S g k_own seed pf.inner.counter pqrKey hk_own_gam
  obtain ⟨_hrk_sess, _hcks_sess, _hdhs_sess, hloc_ser, ⟨rem0, hrem0, hrem_ser⟩, _hrc_sess⟩ :=
    stateRel_sessionToRecordRec_extract_TR interpretation S g st sess hrel
  rw [hRem] at hrem0; injection hrem0 with hrem_eq; subst hrem_eq
  have hpeer_ser : remIk.serialize = gamma interpretation S g st.peerIk :=
    hrem_ser.trans hks.peerIk_ser
  have hmy_ser : sess.state.localIdentity.serialize = gamma interpretation S g st.myIk :=
    hloc_ser.trans hks.myIk_ser
  have hm_ser : pf.inner.serialized = pf.message := prom_tryFrom_serialized_eq htry
  have hMacBytes : pf.message.drop (pf.message.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st.peerIk st.myIk msg.wire) := by
    have hmac_ver : pf.inner.verifyMac (cryptoOf' interpretation).F remIk sess.state.localIdentity
        (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey = true :=
      ((Proofs.libsignal.RngG.CliPure.DecCrypto.verifyMacWithAddresses_eq_true_iff _ _ _ _ _ _).mp hMac).1
    unfold SignalMessage.verifyMac macLength at hmac_ver; dsimp only at hmac_ver
    have hmac_eq := (beq_iff_eq.mp hmac_ver).symm; rw [hm_ser] at hmac_eq; rw [hmac_eq]
    have hkey_mk : keyToBytes32 ((mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey) =
        gamma interpretation S g (trMsgKeys k_own seed).macKey := by rw [hmkGen_eq]; exact hmk_mk
    exact gamma_computeMac_tr interpretation S g (trMsgKeys k_own seed).macKey st.peerIk st.myIk
      msg.wire remIk sess.state.localIdentity
      ((mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey)
      hkey_mk hpeer_ser hmy_ser (pf.message.take (pf.message.length - 8)) hwire_t.symm
  exact ⟨seed, c', hcons, hfind₀, hγ_c₀.trans hrk_m.symm, hst_avail, hk_own,
    hMacBytes.symm.trans hmac_t.symm⟩

theorem prom_modelRun_pre {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms₀ pre post : List Move} {m : Move}
    {acc blk : List MachineEvent}
    (hB : XplBlock interpretation r₀ S who g ms₀ (pre ++ m :: post) acc blk) :
    ModelRun r₀ (ms₀ ++ pre) := by
  have hreach : (runTraceMoves r₀ (ms₀ ++ pre)).Reachable reachability := by
    have h := hB.run.2.2.1.2.2 (ms₀ ++ pre).length
    rwa [← List.append_assoc, List.take_left] at h
  have h := hB.run
  rw [← List.append_assoc] at h
  exact modelRun_prefix_of_reachable h hreach

/-- Rules out an accepting model `Move.decryptSkipped` when the implementation takes the
existing-chain step branch (`PromDecSelNoRatchet`). -/
theorem prom_not_decryptSkipped_of_binStep
    (hceh : ExternCryptoLawsHold interpretation) (hwf : ProtocolSetupWF r) (hS : S = compSemOf interpretation r)
    (hC : PromAcceptCallBy₂ interpretation r S who ok j e' mid acc rec b sm pf
      sess sess' coins expected pt)
    (hsel : PromDecSelNoRatchet sess pf.inner mid coins)
    (g : Ghost) (ms₀ pre post : List Move) (blk : List MachineEvent)
    (p : Participant) (stateIdx msgIdx skIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (wrapped : Bool)
    (hB : XplBlock interpretation r S who g ms₀
      (pre ++ .decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped :: post) acc blk)
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect
      ((Move.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped).next
        (runMoves pre (runTraceMoves r ms₀)).1) post)
    (hacc : ∃ e ∈ blk, eventKind e = .accept)
    (hnocol : ∀ t, rcvMoveTerm (runTraceMoves r (ms₀ ++ pre))
        (.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped) = some t →
      ¬ RecvCollision interpretation r S g (ms₀ ++ pre) t)
    (hcurR : RcvCurrentRead interpretation r S g (ms₀ ++ pre) pf.message
      (.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped))
    (Z : PureTRSlots) (hrr : PureTRRecordStateInv interpretation r S Z g (ms₀ ++ pre)
      (fun q => if q = p then some rec else none))
    (hrole : RoleSnapshots r (runTraceMoves r (ms₀ ++ pre)))
    (hat : RecvDecStepAt.RecvAtFacts interpretation r S g (ms₀ ++ pre))
    (hX : A2bCrossSeedExcl interpretation r S g (ms₀ ++ pre) acc)
    (hA : A2bSeedShapeEqRes interpretation r S g (ms₀ ++ pre) acc)
    (hRk : A2bSeedRkAliasRes interpretation r S g (ms₀ ++ pre) acc) : False := by
  have hmatch := a2b_block_vis hB hpre hpost
  have hacc_vis : ∃ v ∈ (Move.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped).vis
      (runTraceMoves r (ms₀ ++ pre)), v.kind = .accept := by
    obtain ⟨e, he, hk⟩ := hacc
    obtain ⟨v, hv, hev⟩ := Symbolic.Swarm.CREF.xpl_forall₂_mem_left hmatch e he
    exact ⟨v, hv, hev.1.symm.trans hk⟩
  obtain ⟨st, t, msg, seed_s, rIdx_s, srcIdx, spqr', key, pqSalt, ptTerm, hst, hmsg, hparse, hver,
      hsk, _hunused, _hspqr, _hpqSalt, hmac_eq, _hdec, _hpt, hfind_s⟩ :=
    skippedHit_of_decryptSkipped hacc_vis
  have hrep : t ∈ recvRepresentations interpretation r S g (ms₀ ++ pre) pf.message := hcurR.2 t hmsg
  have hnc : ¬ RecvCollision interpretation r S g (ms₀ ++ pre) t := hnocol t hmsg
  obtain ⟨hp_mem, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀, _hsk_pre₀, _hcanon₀, hks₀,
      hnd₀⟩ := hrr p rec (by simp)
  have hidx₀ : stateIdx = stateIdx₀ := a2b_currentSnapshot_unique_of_role hrole hst hst₀ hcurR.1 hcur₀
  cases hidx₀
  have hst_eq : st = st₀ := Option.some.inj (hst.symm.trans hst₀)
  cases hst_eq
  have hcan : Symbolic.Swarm.CREF.TR.Pure.slots_RecordCanonical_Q Symbolic.Swarm.CREF.TR.Pure.slots_NonEmptyV1Q rec (promGhost rec sess).sess := hC.out.hcan_in
  obtain ⟨hnorm_eq, hrel_sess, hpq_sess, _, _, _, _⟩ :=
    pqRatchetState_eq_gamma_pending interpretation S g rec rec₀ st st (promGhost rec sess) hrecBytes₀
      hrel₀ hcan rfl
  have hrel_sess' : StateRel interpretation S g st (sessionToRecordRec sess) := hrel_sess
  have hpq_sess' : sess.state.pqRatchetState = gamma interpretation S g st.spqr := hpq_sess
  have hrc_rec₀ : rec₀.current.receiverChains = (sessionToRecordRec sess).current.receiverChains :=
    congrArg (fun r => r.current.receiverChains) hnorm_eq
  have hnd_sess : ((sessionToRecordRec sess).current.receiverChains.map
      ChainRec.senderRatchetKey).Nodup := hrc_rec₀ ▸ hnd₀.1
  have hsel' := hsel
  obtain ⟨ci, rc, ck, _hmid, _hcoins, hrc, hrc_key, hck, hle⟩ := hsel'
  have htry : SignalMessage.tryFrom protoSignalCodec pf.message = .ok pf.inner :=
    parsePreKeyWire_inner_tryFrom hC.out.hpf
  obtain ⟨c₀, hc₀, hidx_eq, _hrk₀⟩ := a2b_modelChain_of_binChain hrel_sess' hrc hck
  obtain ⟨_hwire_t, _hmac_t, _hhd_t, hfld⟩ := hrep.2.2.2 msg hparse
  obtain ⟨_hct_m, _hrk_m, _hpq_m, hctr_m, _hver_m⟩ := hfld pf.inner htry
  have hctr_eq : UInt32.ofBitVec pf.inner.counter = msg.counter := UInt32.ext hctr_m.symm
  have hle' : c₀.index ≤ msg.counter := by
    rw [← hctr_eq]; show c₀.index.toBitVec ≤ pf.inner.counter; rw [hidx_eq]; exact hle
  have hc₀_mem : c₀ ∈ st.recv := List.mem_of_getElem? hc₀
  have hrun : ModelRun r (ms₀ ++ pre) := prom_modelRun_pre hB
  have hcompat : GhostAndSemMatchSetup interpretation r S g := hB.1.1
  obtain ⟨seed_c, c', hcons, _hfind, hγrk, hst_avail, hk_own, hmacγ⟩ :=
    prom_seedEq_core hceh hwf hS hC hsel g (ms₀ ++ pre) hcompat hrun hat p stateIdx st c₀ t msg ci
      rc ck hst hrel_sess' hnd_sess hpq_sess' hks₀ hc₀ hrep hparse htry hrc hrc_key hck
  have hseq : seed_s = seed_c := by
    by_cases hγ : gamma interpretation S g seed_c = gamma interpretation S g seed_s
    · exact a2b_seedEq_of_shapeRes interpretation r S g (ms₀ ++ pre) acc hrun hA hRk p stateIdx st
        c₀ c' t msg skIdx rIdx_s srcIdx seed_s seed_c pqSalt pf.message _ hst hcurR.1 hrel_sess'
        hnd_sess hver hc₀_mem hrep hparse hnc hsk hmac_eq hγrk hcons hγ
    · exact (hnc (hX t ⟨msg, hparse, hver, seed_s, a2b_mem_skippedSeedsFor hsk, pqSalt, st,
        hst_avail, hfind_s, hmac_eq,
        st, hst_avail, c₀, hc₀_mem, seed_c, c', hγrk, hcons, hγ, _, hk_own, hmacγ⟩)).elim
  have hsklin : SkippedSeedNeChainSeed r (ms₀ ++ pre) := skippedSeed_ne_chainSeed hrun
  have hr : rIdx_s = c₀.rIdx :=
    hsklin p stateIdx st c₀ msg.counter seed_c c' skIdx msg.ratchetKey msg.counter seed_s rIdx_s
      srcIdx hst hc₀_mem hcons hsk hseq
  have hlog : (runTraceMoves r (ms₀ ++ pre)).EventLoggedAt
      (TREvent.SkippedKeyStored (st.sessionInfo p) msg.ratchetKey msg.counter seed_s c₀.rIdx srcIdx) skIdx := by
    rw [← hr, Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]; exact hsk
  have hlt : msg.counter < c₀.index :=
    ((hat.fresh p stateIdx st hp_mem hst hcurR.1).1.1 c₀ hc₀_mem).2 _ _ _ _ _ hlog
  exact UInt32.not_lt.mpr hle' hlt

end X2

end Symbolic.Swarm.CREF.CliPure
