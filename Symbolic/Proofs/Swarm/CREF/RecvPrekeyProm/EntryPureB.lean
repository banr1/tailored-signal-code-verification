/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.VersionPure
import DY.ALaCarte.Basic
import DY.Bytes.Basic
import DY.EquationalTheory.KdfExtract
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecTieSeedShapePure
public import Symbolic.Proofs.Swarm.CREF.Sem
public import Symbolic.Proofs.Swarm.CREF.TR.RecvFresh
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.OpkSent
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.A2bSameOriginPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.IkShapeSrcPure
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.By2HypsPure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.EntryPureA
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HistOpkPureA
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.NoRatchetPure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.RatchetDHPure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.PromXplAssemblyPure
import Symbolic.Proofs.Swarm.CREF.TR.G1.SkippedPkLineage
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.By2Pure -- shake: keep
import Symbolic.Proofs.Swarm.CREF.RecvWire.By2SupplyA -- shake: keep
public import Symbolic.Proofs.Swarm.CREF.TR.RecvCol -- shake: keep
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# `PromExplainOK`, `PromRcvDecTieAt`, and Skipped/Chain Seed Aliasing Exclusion

Assembles `prom_explainOK_of_noDraw_and_ver`, reduces `PromNewRecByOK₂` to pointwise
`PromRcvDecTieAt`, and proves `prom_a2b_hrkAlias` ruling out seed aliasing between a stored skipped
key and a receiver-chain message key without `RecvCollision`.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Symbolic.Swarm.CREF.CliPure

cref_open
cref_open_tr
open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (SessionInfo RecvChain findRecvChain consumeMessageKey chainKeyAt
  kdfCk kdfRk computeMac createChain x25519LowOrder)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH hiding kdfRk createChain x25519LowOrder
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record
open Symbolic.Swarm.TRREF
open Symbolic.Swarm.CREF.TR.Pure
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.RecvDec hiding StEntry TREntry TRRecvAllCollide
open Symbolic.Swarm.CREF.TR.RecvDecStep
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding StEntry TREntry
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt
open Symbolic.Swarm.CREF.TR.G1
open Proofs.libsignal.RngG Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3

/-- Discharges `PromExplainOK` from `PromNoDrawOK` and `PromVersionOK`. -/
theorem prom_explainOK_of_noDraw_and_ver
    (interpretation : ExternInterpretation) {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    (hext : DY.Libsignal.Composed.Refinement.Cli.ExternContractsHoldCli interpretation)
    (hwf : ProtocolSetupWF r)
    (hSeq : S = compSemOf interpretation r)
    (hND : PromNoDrawOK interpretation r S who ok)
    (hVer : PromVersionOK interpretation r S who ok) :
    PromExplainOK interpretation r S who ok :=
  prom_explainOK_of_rawKnBranches hND
    (promRawCtxSupply_proved interpretation hext hwf)
    (prom_rawKnBranch_skipped interpretation hext hwf hSeq hVer)
    (prom_rawKnBranch_noRatchet interpretation hext hwf hSeq hVer)
    (prom_rawKnBranch_ratchetDH interpretation hext hwf (ikShape_of_extern hext r) hSeq hVer)

/-! ## `PromNewRecByOK₂` reduction and `A2bSeedRkAliasRes` -/

/-- Pointwise post-decrypt `PureTRRecordStateInv` and `TRNsBound` obligation on `blk` with `CleanBy`
hypotheses threaded in scope. -/
abbrev PromRcvDecTieAt
    (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool)
    (p : Participant) (rec newSt : HwBytes) (sent : List HwBytes)
    (acc blk : List MachineEvent) (body : HwBytes) : Prop :=
  ∀ g ms₀ pre m post,
    CleanBy interpretation r S who ok g (ms₀ ++ (pre ++ m :: post)) (acc ++ blk) →
    CleanBy interpretation r S who ok g ms₀ acc →
    XplBlock interpretation r S who g ms₀ (pre ++ m :: post) acc blk →
    MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre →
    DecryptBy p m →
    MovesFrom InvisibleNoEffect (m.next (runMoves pre (runTraceMoves r ms₀)).1) post →
    CHistBy interpretation r S g ms₀ →
    (∀ t, rcvMoveTerm (runTraceMoves r (ms₀ ++ pre)) m = some t →
      ¬ RecvCollision interpretation r S g (ms₀ ++ pre) t) →
    RcvCurrentRead interpretation r S g (ms₀ ++ pre) body m →
    PureCRecRel interpretation r S g (ms₀ ++ pre) p rec →
    TR.TRNsBound r (ms₀ ++ pre) sent →
    TR.PureTRRecordStateInv interpretation r S (pureTrSlots r) g (ms₀ ++ pre ++ [m])
        (fun q => if q = p then some newSt else none) ∧
      TR.TRNsBound r (ms₀ ++ pre ++ [m]) sent

theorem prom_newRecBy₂_of_tieAt
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
    {rec b : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))}
    {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hC : PromAcceptCallBy₂ interpretation r S who ok j e' mid acc rec b sm pf
      sess sess' coins expected pt)
    (htieAt : PromRcvDecTieAt interpretation r S who ok r.bob rec sm.state e'.sent acc
      (promAccBlk b mid pt) pf.message) :
    PromNewRecBy₂ interpretation r S who ok r.bob rec sm.state e'.sent acc
      (promAccBlk b mid pt) := by
  intro g ms₀ δ hc hB h1 hch₀ hrr₀ hns₀
  obtain ⟨pre, m, post, rfl, hpre, hstep, hpost⟩ := h1
  have hc₀ : CleanBy interpretation r S who ok g ms₀ acc :=
    clean_prefix (matchedPrefix_length_eq hB.pre) hc
  have hne_st := (prom_sm_recordBytes hC.out).2
  have hcur := prom_currentRead_of_not_dirtyAt₂ interpretation hC.out.hpf hc hB hpre hpost hC.hmid
  have hq := a2b_quietPre hpre
  obtain ⟨hrsi, hns'⟩ := htieAt g ms₀ pre m post hc hc₀ hB hpre
    (hstep.2.2 (prom_accBlk_has_accept b mid pt)) hpost hch₀
    (fun _t ht => prom_not_recvCollision_of_not_dirtyAt₂ interpretation hC.out.hpf hc hB hpre hC.hmid ht)
    hcur (Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_pureCRecRel hq hrr₀) (Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_trNsBound hq hns₀)
  have hq' := a2b_quietPost hpost
  exact ⟨hne_st, Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_pureCRecRel hq' (Or.inl hrsi), Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_trNsBound hq' hns'⟩

/-- Lifts per-call `PromRcvDecTieAt` to `PromNewRecByOK₂`. -/
theorem prom_newRecByOK₂_of_tieAt
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    (htieAt :
      ∀ (j : Nat) (e' : PromTurn) (mid acc : List MachineEvent)
        (rec b : HwBytes) (sm : StateAndMessage) (pf : PreKeyFields)
        (sess sess' : Session (List (BitVec 8)))
        (coins : BitVec 256) (expected : Option (List (BitVec 8))) (pt : List (BitVec 8)),
        PromAcceptCallBy₂ interpretation r S who ok j e' mid acc rec b sm pf
          sess sess' coins expected pt →
        ¬ CollisionAt interpretation r S who ok (acc ++ promAccBlk b mid pt) →
        ¬ CollisionAtBy interpretation r S who ok (acc ++ promAccBlk b mid pt) →
        PromRcvDecTieAt interpretation r S who ok r.bob rec sm.state e'.sent acc
          (promAccBlk b mid pt) pf.message) :
    PromNewRecByOK₂ interpretation r S who ok := by
  intro j e' mid acc rec b sm pf sess sess' coins expected pt hC hcol
  exact prom_newRecBy₂_of_tieAt hC
    (htieAt j e' mid acc rec b sm pf sess sess' coins expected pt hC hcol hcol)

section RkAliasSupply

open DY.Libsignal.TripleRatchet (KeyDir)
open DY.Libsignal.PQXDH (PQXDHEvent PQXDHState)
open Symbolic.Swarm.COMPOSED.CompTrace

local notation "Preserves" => Symbolic.Swarm.COMPOSED.CompTrace.Preserves

private theorem prom_a2b_trRecvFreshAll_of_quietExt {r₀ : ProtocolSetup} {ms ms' : List Move}
    (hq : Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.QuietExt (runTraceMoves r₀ ms) (runTraceMoves r₀ ms'))
    (h : TR.TRRecvFreshAll r₀ ms) : TR.TRRecvFreshAll r₀ ms' := by
  intro q stateIdx st hqab hget hcur
  rw [Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_getLocalState hq] at hget
  rw [Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_isCurrentSnapshot hq] at hcur
  obtain ⟨hc, hs⟩ := h q stateIdx st hqab hget hcur
  exact ⟨TR.trRecvCountersFresh_of_imp
      (fun _ _ _ _ _ _ hl => (Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_eventLoggedAt hq _ _).mp hl)
      (fun _ _ _ _ _ _ hl => (Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_eventLoggedAt hq _ _).mp hl) hc,
    TR.trSkippedRIdxChainRel_of_imp
      (fun _ _ _ _ _ _ hl => (Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_eventLoggedAt hq _ _).mp hl) hs⟩

private theorem prom_a2b_roleSnapshots_of_quietPre {r₀ : ProtocolSetup} {ms₀ pre : List Move}
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r₀ ms₀) pre)
    (hrole : RoleSnapshots r₀ (runTraceMoves r₀ ms₀)) :
    RoleSnapshots r₀ (runTraceMoves r₀ (ms₀ ++ pre)) := by
  rw [TR.runTrace_append]
  exact roleSnapshots_of_movesFrom_invisibleNoEffect hpre hrole

private theorem prom_a2b_modelRun_pre {interpretation : ExternInterpretation}
    {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
    {g : Ghost} {ms₀ pre post : List Move} {m : Move} {acc blk : List MachineEvent}
    (hB : XplBlock interpretation r₀ S who g ms₀ (pre ++ m :: post) acc blk) :
    ModelRun r₀ (ms₀ ++ pre) := by
  have hreach : (runTraceMoves r₀ (ms₀ ++ pre)).Reachable Composed.reachability := by
    have h := hB.run.2.2.1.2.2 (ms₀ ++ pre).length
    rwa [← List.append_assoc, List.take_left] at h
  have h := hB.run
  rw [← List.append_assoc] at h
  exact modelRun_prefix_of_reachable h hreach

private theorem prom_a2b_rkAlias_rIdx_ne
    {r : ProtocolSetup} {ms : List Move}
    {q : Participant} {skIdx rIdx_s srcIdx : Nat}
    {st : TRState} {c : RecvChain} {msg : TRSignalMsg} {seed_s : DY.Bytes}
    (hskRel : TR.TRSkippedRIdxChainRel (runTraceMoves r ms) q st)
    (hc : c ∈ st.recv)
    (hfind : findRecvChain st.recv msg.ratchetKey = none)
    (hsk : ((runTraceMoves r ms).at? skIdx : Option TREntry) =
      some ⟨TREvent.SkippedKeyStored (st.sessionInfo q) msg.ratchetKey msg.counter seed_s rIdx_s srcIdx⟩) :
    rIdx_s ≠ c.rIdx := by
  intro hrIdx_eq
  have hpk_eq : msg.ratchetKey = c.ratchetKey :=
    hskRel.2 c hc msg.ratchetKey msg.counter seed_s srcIdx skIdx
      (hrIdx_eq ▸ (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mpr hsk)
  have hfind' : st.recv.find? (·.ratchetKey == msg.ratchetKey) = none := hfind
  rw [List.find?_eq_none] at hfind'
  exact hfind' c hc (by simp [hpk_eq])

private theorem prom_a2b_rkAlias_false_of_shape_eq
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move}
    {q : Participant} {stateIdx skIdx rIdx_s srcIdx : Nat}
    {st : TRState} {c c' : RecvChain} {msg : TRSignalMsg} {seed_s seed_c : DY.Bytes}
    (hreach : ReachableTrace (runTraceMoves r ms))
    (hskRel : TR.TRSkippedRIdxChainRel (runTraceMoves r ms) q st)
    (hst : ((PersistentLocalState.getLocalState q stateIdx : Traceful TRState).run (runTraceMoves r ms)).1 = some st)
    (hc : c ∈ st.recv)
    (hfind : findRecvChain st.recv msg.ratchetKey = none)
    (hcons : consumeMessageKey c msg.counter = some (seed_c, c'))
    (hsk : ((runTraceMoves r ms).at? skIdx : Option TREntry) =
      some ⟨TREvent.SkippedKeyStored (st.sessionInfo q) msg.ratchetKey msg.counter seed_s rIdx_s srcIdx⟩)
    (hshape : (gamma' interpretation S g seed_c).shape = (gamma' interpretation S g seed_s).shape) :
    False := by
  have hInv := Symbolic.Swarm.COMPOSED.CompRatchet.compScheduleInv_reachable hreach
  have hst_at : Symbolic.Swarm.COMPOSED.CompTrace.TRStateStoredAt q st stateIdx (runTraceMoves r ms) :=
    getLocalState_some_iff_trStateStoredAt.mp hst
  obtain ⟨_, _, _, ⟨doneIdx_c, ikm_c, dh₁_c, hs_c, _, _, hrecv_c⟩, _⟩ :=
    hInv.stateOK q st stateIdx hst_at
  have hc_sched := hrecv_c c hc
  have hc_pos : 1 ≤ c.rIdx := hc_sched.1
  obtain ⟨_, _, _, _, _, ck₀_c, hroot_c, _hck_c, hseed_c, _⟩ :=
    Symbolic.Swarm.COMPOSED.CompRatchet.consumeMessageKey_compSchedule hc_sched hcons
  obtain ⟨hs_pos, _, doneIdx_s, ikm_s, dh₁_s, ck₀_s, hs_s, hroot_s, hseed_s⟩ :=
    hInv.eventOK (TREvent.SkippedKeyStored (st.sessionInfo q) msg.ratchetKey msg.counter seed_s rIdx_s srcIdx)
      ⟨skIdx, (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mpr hsk⟩
  obtain ⟨rfl, rfl⟩ := compSessionAt_same_sinfo_eq hs_c hs_s
  have hsh_ck₀ :
      (gamma' interpretation S g ck₀_c).shape = (gamma' interpretation S g ck₀_s).shape :=
    shape_chainKeyAt_inj' interpretation S g msg.counter.toNat
      (shape_kdfCk_snd_inj' interpretation S g (by rwa [← hseed_c, ← hseed_s]))
  have hm_eq : c.rIdx - 1 = rIdx_s - 1 :=
    compChainRootFrom1_depth_eq_of_shape_eq interpretation S g hroot_c hroot_s hsh_ck₀
  have hrIdx_eq : rIdx_s = c.rIdx := by omega
  exact prom_a2b_rkAlias_rIdx_ne hskRel hc hfind hsk hrIdx_eq

private def SpkOwnerBob (r : ProtocolSetup) (tr : ExecTrace) : Prop :=
  ∀ b pk i, tr.EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.SignedPrekeyPublished b pk) i →
    b = r.bob

private theorem spkOwnerBob_append_other {r : ProtocolSetup} {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {e : E}
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none)
    (h : SpkOwnerBob r tr) : SpkOwnerBob r (tr.append e) :=
  fun b pk i hev => h b pk i (Symbolic.Swarm.COMPOSED.CompTrace.eventLoggedAt_append_other hnone hev)

private theorem spkOwnerBob_pres_logPQ {r : ProtocolSetup} (ev : DY.Libsignal.PQXDH.PQXDHEvent)
    (hev : ∀ b pk, ev = .SignedPrekeyPublished b pk → b = r.bob) :
    Symbolic.Swarm.COMPOSED.CompTrace.Preserves (SpkOwnerBob r) (ProtocolEvent.logEvent ev) := by
  intro tr h b pk i hl
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1] at hl
  rcases Symbolic.Swarm.COMPOSED.CompTrace.eventLoggedAt_append_same hl with ⟨_, hl'⟩ | ⟨_, heq⟩
  · exact h b pk i hl'
  · exact hev b pk heq

private theorem spk_pres_sendMessage {r : ProtocolSetup} (m : DY.Bytes) :
    Preserves (SpkOwnerBob r) (Network.sendMessage m) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1]
  erw [Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact spkOwnerBob_append_other (e := COMPOSED.CompTrace.NetE m) rfl h
private theorem spk_pres_genRand {r : ProtocolSetup} (n : Nat) :
    Preserves (SpkOwnerBob r) (Random.genRand n) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1]
  exact spkOwnerBob_append_other (e := COMPOSED.CompTrace.RndE n) rfl h
private theorem spk_pres_logTR {r : ProtocolSetup} (ev : TREvent) :
    Preserves (SpkOwnerBob r) (ProtocolEvent.logEvent ev) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1]
  exact spkOwnerBob_append_other (e := TREvE ev) rfl h
private theorem spk_pres_logC {r : ProtocolSetup} (ev : ComposedEvent) :
    Preserves (SpkOwnerBob r) (ProtocolEvent.logEvent ev) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1]
  exact spkOwnerBob_append_other (e := CEvE ev) rfl h
private theorem spk_pres_storeTR {r : ProtocolSetup} (p : Participant) (st : TRState) :
    Preserves (SpkOwnerBob r) (PersistentLocalState.storeLocalState p st) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1]
  erw [Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact spkOwnerBob_append_other (e := TRStE p st) rfl h
private theorem spk_pres_storePQ {r : ProtocolSetup} (p : Participant) (st : PQXDHState) :
    Preserves (SpkOwnerBob r) (PersistentLocalState.storeLocalState p st) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.run_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1]
  erw [Symbolic.DYBridge.DY.Traceful.run_eq_1]
  exact spkOwnerBob_append_other (e := PQStE p st) rfl h

private theorem spk_pres_prodCasesOn {r : ProtocolSetup} {α β γ : Type} (p : α × β)
    (f : α → β → Traceful γ) (hf : ∀ a b, Preserves (SpkOwnerBob r) (f a b)) :
    Preserves (SpkOwnerBob r) (Prod.casesOn p f) := by rcases p with ⟨a, b⟩; exact hf a b

private theorem spk_pres_optionCasesOn {r : ProtocolSetup} {α β : Type} (o : Option α)
    (noneCase : Traceful β) (someCase : α → Traceful β)
    (hn : Preserves (SpkOwnerBob r) noneCase) (hs : ∀ a, Preserves (SpkOwnerBob r) (someCase a)) :
    Preserves (SpkOwnerBob r) (Option.casesOn o noneCase someCase) := by
  rcases o with _ | a; exact hn; exact hs a

private theorem spk_pres_getKey {r : ProtocolSetup} (p : Participant) (h : Nat) (kind : DY.Libsignal.PQXDH.KeyKind) :
    Preserves (SpkOwnerBob r) (DY.Libsignal.PQXDH.getKey p h kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  exact Preserves.bind (Preserves.getLocalState_pq p h) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

private theorem spk_pres_lookupIdentity {r : ProtocolSetup} (p : Participant) (h : Nat) :
    Preserves (SpkOwnerBob r) (DY.Libsignal.PQXDH.lookupIdentity p h) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine Preserves.bind (Preserves.getEntry h) fun _ => ?_
  split <;> [exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _; exact Preserves.failure]

private theorem spk_pres_dhRatchetStep {r : ProtocolSetup} (st : TRState) (pk : DY.Bytes) :
    Preserves (SpkOwnerBob r) (DY.Libsignal.TripleRatchet.dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.bind (spk_pres_genRand 32) fun _ => Preserves.pure _

private theorem spk_pres_ensureReceiverChain {r : ProtocolSetup} (st : TRState) (pk : DY.Bytes) :
    Preserves (SpkOwnerBob r) (DY.Libsignal.TripleRatchet.ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split <;> [exact Preserves.pure _; exact Preserves.bind (spk_pres_dhRatchetStep st pk) fun _ => Preserves.pure _; exact Preserves.failure]

private theorem spk_pres_logSkippedKeys {r : ProtocolSetup} (s : SessionInfo) (pk : DY.Bytes)
    (rIdx src : Nat) (ck : DY.Bytes) (n : UInt32) (k : Nat) :
    Preserves (SpkOwnerBob r) (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k) := by
  induction k generalizing ck n with
  | zero => unfold DY.Libsignal.TripleRatchet.logSkippedKeys; exact Preserves.pure _
  | succ k ih => unfold DY.Libsignal.TripleRatchet.logSkippedKeys; exact Preserves.bind (spk_pres_logTR _) fun _ => ih _ _

private theorem spk_pres_logMessageKeyAndStore {r : ProtocolSetup} (me : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx par : Nat) (st : TRState) :
    Preserves (SpkOwnerBob r)
      (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n rIdx par st) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  exact Preserves.bind (spk_pres_logTR _) fun _ => spk_pres_storeTR me st

local macro "spk_tac" : tactic => `(tactic| repeat (first
  | with_reducible apply Preserves.bind | with_reducible apply spk_pres_prodCasesOn
  | with_reducible apply spk_pres_optionCasesOn
  | with_reducible apply Preserves.pure | with_reducible apply Preserves.failure
  | with_reducible apply spk_pres_genRand | with_reducible apply spk_pres_storeTR
  | with_reducible apply spk_pres_storePQ
  | with_reducible apply spk_pres_sendMessage | with_reducible apply Preserves.getLocalState_tr
  | with_reducible apply Preserves.getLocalState_pq | with_reducible apply spk_pres_getKey
  | with_reducible apply spk_pres_lookupIdentity | with_reducible apply Preserves.receiveMessage
  | with_reducible apply Preserves.getEntry | with_reducible apply Preserves.receiveSignalMsg
  | with_reducible apply Preserves.verifyMacAndDecrypt | with_reducible apply spk_pres_dhRatchetStep
  | with_reducible apply spk_pres_ensureReceiverChain | with_reducible apply spk_pres_logSkippedKeys
  | with_reducible apply Preserves.guardP | with_reducible apply Preserves.monadLiftErr
  | with_reducible apply Preserves.guardTrace | with_reducible apply Preserves.requireTracePredicate
  | with_reducible apply Preserves.traceLength | with_reducible apply spk_pres_logMessageKeyAndStore
  | with_reducible apply spk_pres_logTR | with_reducible apply spk_pres_logC
  | ((with_reducible apply spkOwnerBob_pres_logPQ); (intro _ _ h; cases h; try rfl))
  | split | with_reducible intro))

private theorem spk_pres_aliceHandshake {r : ProtocolSetup} (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    Preserves (SpkOwnerBob r) (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake; spk_tac

private theorem spk_pres_bobHandshake {r : ProtocolSetup} (b a : Participant)
    (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA ekIdx ctIdx : Nat) :
    Preserves (SpkOwnerBob r) (DY.Libsignal.PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx) := by
  unfold DY.Libsignal.PQXDH.bobHandshake; spk_tac

private theorem spk_pres_aliceStart {r : ProtocolSetup} (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : DY.Libsignal.PQXDH.BundleHandles) :
    Preserves (SpkOwnerBob r) (DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB h) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine Preserves.bind (spk_pres_aliceHandshake a b idStateIdx regIdxB h) fun _ => ?_; spk_tac

private theorem spk_pres_bobStart {r : ProtocolSetup} (b a : Participant)
    (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA : Nat)
    (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves (SpkOwnerBob r) (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine Preserves.bind (spk_pres_bobHandshake b a kh regIdxA mh.ek mh.ct) fun o => ?_
  refine Preserves.bind (Preserves.receiveSignalMsg _) fun msg => ?_
  dsimp only
  refine Preserves.bind (spk_pres_ensureReceiverChain _ _) fun ⟨st, c, ratcheted⟩ => ?_
  dsimp only
  rcases consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
  · dsimp only; exact Preserves.failure
  dsimp only
  rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
  · dsimp only; exact Preserves.failure
  dsimp only
  refine Preserves.bind (spk_pres_sendMessage _) fun _ => ?_
  refine Preserves.bind (Preserves.receiveMessage _) fun pqSalt => ?_
  refine Preserves.bind (Preserves.verifyMacAndDecrypt _ _ _ _) fun m => ?_
  rcases o.opk with _ | opk
  · dsimp only
    try refine Preserves.bind (Preserves.pure _) fun _ => ?_
    refine Preserves.bind Preserves.traceLength fun _ => ?_
    refine Preserves.bind (spkOwnerBob_pres_logPQ _ fun _ _ h => nomatch h) fun _ => ?_
    cases ratcheted <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> spk_tac
  · dsimp only
    first
    | refine Preserves.bind
        (Preserves.bind (Preserves.requireTracePredicate _) fun _ =>
          spkOwnerBob_pres_logPQ _ fun _ _ h => nomatch h) fun _ => ?_
    | (refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
       refine Preserves.bind (spkOwnerBob_pres_logPQ _ fun _ _ h => nomatch h) fun _ => ?_)
    refine Preserves.bind Preserves.traceLength fun _ => ?_
    refine Preserves.bind (spkOwnerBob_pres_logPQ _ fun _ _ h => nomatch h) fun _ => ?_
    cases ratcheted <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> spk_tac

private theorem spk_pres_registerIdentity {r : ProtocolSetup} (p : Participant) :
    Preserves (SpkOwnerBob r) (DY.Libsignal.PQXDH.registerIdentity p) := by
  unfold DY.Libsignal.PQXDH.registerIdentity; spk_tac

private theorem spk_pres_genSignedPrekey {r : ProtocolSetup} (idStateIdx : Nat) :
    Preserves (SpkOwnerBob r) (DY.Libsignal.PQXDH.genSignedPrekey r.bob idStateIdx) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey; spk_tac

private theorem spk_pres_genPQPrekey {r : ProtocolSetup} (p : Participant) (idStateIdx : Nat) :
    Preserves (SpkOwnerBob r) (DY.Libsignal.PQXDH.genPQPrekey p idStateIdx) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey; spk_tac

private theorem spk_pres_genOneTimePrekey {r : ProtocolSetup} (p : Participant) :
    Preserves (SpkOwnerBob r) (DY.Libsignal.PQXDH.genOneTimePrekey p) := by
  unfold DY.Libsignal.PQXDH.genOneTimePrekey; spk_tac

private theorem spkOwnerBob_setupTrace (r : ProtocolSetup) : SpkOwnerBob r (setupTrace r) := by
  have hnil : SpkOwnerBob r Trace.nil := fun _ _ _ h => by
    simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, DY.Trace.at?,
      Symbolic.DYBridge.DY.Trace.nil_length_not_lt, ↓reduceDIte, reduceCtorEq] at h
  have hpres : Preserves (SpkOwnerBob r) (ProtocolSetup.setupMove r).act := by
    dsimp only [ProtocolSetup.setupMove, Move.act]
    unfold setupAct
    refine Preserves.bind (spk_pres_registerIdentity r.alice) fun _ => ?_
    refine Preserves.bind (spk_pres_registerIdentity r.bob) fun hB => ?_
    refine Preserves.bind (spk_pres_genSignedPrekey hB) fun _ => ?_
    refine Preserves.bind (spk_pres_genPQPrekey r.bob hB) fun _ => ?_
    cases r.withOpk
    · exact Preserves.pure _
    · exact Preserves.bind (spk_pres_genOneTimePrekey r.bob) fun _ => Preserves.pure _
  exact hpres Trace.nil hnil

private theorem spk_pres_messageEncrypt {r : ProtocolSetup} (me : Participant)
    (stateIdx coinsLen pqIdx : Nat) :
    Preserves (SpkOwnerBob r)
      (DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt; spk_tac

private theorem spk_pres_messageDecrypt {r : ProtocolSetup} (me : Participant)
    (stateIdx msgIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves (SpkOwnerBob r)
      (DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  refine Preserves.bind (Preserves.getLocalState_tr me stateIdx) fun st => ?_
  refine Preserves.bind (Preserves.receiveSignalMsg msgIdx) fun msg => ?_
  refine Preserves.bind (spk_pres_ensureReceiverChain st msg.ratchetKey) fun ⟨st, c, ratcheted⟩ => ?_
  dsimp only
  rcases consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
  · dsimp only; exact Preserves.failure
  dsimp only
  rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
  · dsimp only; exact Preserves.failure
  dsimp only
  cases ratcheted <;> spk_tac

private theorem spk_pres_messageDecryptSkipped {r : ProtocolSetup} (me : Participant)
    (stateIdx msgIdx skIdx pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves (SpkOwnerBob r)
      (DY.Libsignal.TripleRatchet.messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  refine Preserves.bind (Preserves.getLocalState_tr me stateIdx) fun st => ?_
  refine Preserves.bind (Preserves.receiveSignalMsg msgIdx) fun msg => ?_
  refine Preserves.bind (Preserves.getEntry skIdx) fun (e : ProtocolEvent.ExecEntryT TREvent) => ?_
  cases e.ev with
  | SkippedKeyStored s pk n seed rIdx sourceStateIdx =>
    dsimp only
    refine Preserves.bind (Preserves.guardP _) fun _ => ?_
    refine Preserves.bind (Preserves.guardTrace _) fun _ => ?_
    rcases Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
    · dsimp only; exact Preserves.failure
    dsimp only
    spk_tac
  | _ => dsimp only; exact Preserves.failure

private theorem spkOwnerBob_move_next {r : ProtocolSetup} (m : Move) (hsetup : m.isSetup = false) :
    Preserves (SpkOwnerBob r) m.act := by
  cases m with
  | setup _ _ _ => cases hsetup
  | aliceStart a b idStateIdx regIdxB bh shown =>
    dsimp only [Move.act]; exact Preserves.bind (spk_pres_aliceStart a b idStateIdx regIdxB bh) fun _ => Preserves.pure _
  | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown =>
    dsimp only [Move.act]; exact Preserves.bind (spk_pres_bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) fun _ => Preserves.pure _
  | encrypt me stateIdx coinsLen pqIdx wrap =>
    dsimp only [Move.act]; exact Preserves.bind (spk_pres_messageEncrypt me stateIdx coinsLen pqIdx) fun _ => Preserves.pure _
  | encryptAbort me stateIdx =>
    dsimp only [Move.act]; unfold DY.Libsignal.TripleRatchet.messageEncryptAbort; spk_tac
  | encryptFail me stateIdx coinsLen =>
    dsimp only [Move.act]
    exact Preserves.bind Preserves.traceLength fun n =>
      Preserves.bind (spk_pres_messageEncrypt me stateIdx coinsLen (n + 3)) fun _ => Preserves.pure _
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped =>
    dsimp only [Move.act]
    exact Preserves.bind (spk_pres_messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) fun _ => Preserves.pure _
  | decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped =>
    dsimp only [Move.act]
    exact Preserves.bind (spk_pres_messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx) fun _ => Preserves.pure _
  | reject draws => dsimp only [Move.act]; exact Preserves.pure _
  | compromiseIK p stateIdx => dsimp only [Move.act]; unfold DY.Libsignal.PQXDH.compromiseIK; spk_tac
  | compromiseSPK p stateIdx => dsimp only [Move.act]; unfold DY.Libsignal.PQXDH.compromiseSPK; spk_tac
  | compromisePQSPK p stateIdx => dsimp only [Move.act]; unfold DY.Libsignal.PQXDH.compromisePQSPK; spk_tac
  | compromiseOPK p stateIdx => dsimp only [Move.act]; unfold DY.Libsignal.PQXDH.compromiseOPK; spk_tac
  | exposeKey me stateIdx k => dsimp only [Move.act]; unfold DY.Libsignal.TripleRatchet.exposeKey; spk_tac
  | exposeSpqr me stateIdx => dsimp only [Move.act]; unfold DY.Libsignal.TripleRatchet.exposeSpqr; spk_tac
  | exposeSkipped skIdx => dsimp only [Move.act]; unfold DY.Libsignal.TripleRatchet.exposeSkipped; spk_tac
  | attackerSend msg => dsimp only [Move.act]; spk_tac
  | brkDH => dsimp only [Move.act]; unfold DY.Libsignal.PQXDH.breakDH; spk_tac
  | brkKEM => dsimp only [Move.act]; unfold DY.Libsignal.PQXDH.breakKEM; spk_tac

private theorem spkOwnerBob_runMoves {r : ProtocolSetup} :
    ∀ (ms : List Move) (tr : ExecTrace),
      (∀ m ∈ ms, m.isSetup = false) → SpkOwnerBob r tr → SpkOwnerBob r (runMoves ms tr).1
  | [], _, _, htr => htr
  | m :: ms, tr, hms, htr =>
    spkOwnerBob_runMoves ms (m.next tr) (fun m' hm' => hms m' (List.mem_cons_of_mem m hm'))
      (spkOwnerBob_move_next m (hms m List.mem_cons_self) tr htr)

private theorem spkOwnerBob_runTrace {r : ProtocolSetup} {ms : List Move}
    (hms : ∀ m ∈ ms, m.isSetup = false) : SpkOwnerBob r (runTraceMoves r ms) :=
  spkOwnerBob_runMoves ms (setupTrace r) hms (spkOwnerBob_setupTrace r)

private theorem prom_a2b_owner_alice_or_bob
    {r : ProtocolSetup} {ms : List Move} {q : Participant} {stateIdx : Nat} {st : TRState}
    (hrole : RoleSnapshots r (runTraceMoves r ms))
    (hrun : ModelRun r ms)
    (hst : ((PersistentLocalState.getLocalState q stateIdx : Traceful TRState).run (runTraceMoves r ms)).1 = some st) :
    q = r.alice ∨ q = r.bob := by
  have hat := Symbolic.Swarm.CREF.TR.FreshSigma.at?_eq_some_of_getLocalState_some hst
  have hr : st.initiator = decide (q = r.alice) := hrole q st stateIdx hat
  have hreach : ReachableTrace (runTraceMoves r ms) := hrun.2.2.1.1
  have hInv := Symbolic.Swarm.COMPOSED.CompRatchet.compScheduleInv_reachable hreach
  have hst_at : Symbolic.Swarm.COMPOSED.CompTrace.TRStateStoredAt q st stateIdx (runTraceMoves r ms) :=
    getLocalState_some_iff_trStateStoredAt.mp hst
  obtain ⟨_, _, _, ⟨doneIdx_c, ikm_c, dh₁_c, hs_c, _, _, _⟩, _⟩ :=
    hInv.stateOK q st stateIdx hst_at
  have hrole_c := hs_c.2.2
  cases hinit : st.initiator with
  | true =>
    exact Or.inl (of_decide_eq_true (hr.symm.trans hinit))
  | false =>
    change (st.sessionInfo q).initiator = false at hinit
    simp only [hinit, Bool.false_eq_true, ↓reduceIte] at hrole_c
    obtain ⟨b, a, t_spk, ikB, ikA, spkSk, pqsk, opk, ek, ct, dh4, e,
      _hspk, _hr64, _hne, hevB, hme, _⟩ := hrole_c
    obtain ⟨_, sS, _, _, _, _, _, ⟨t, _, _, _, hpub⟩, _⟩ :=
      (Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable (runTraceMoves r ms) hreach).bobDone
        b a _ _ _ _ _ _ _ _ doneIdx_c hevB
    exact Or.inr (hme.trans (spkOwnerBob_runTrace hrun.2.1 b _ (t + 2) hpub))

theorem prom_a2b_hrkAlias
    {interpretation : ExternInterpretation}
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) {who : List Participant}
    (g : Ghost) (ms₀ pre : List Move) (m : Move) (post : List Move)
    (acc blk : List MachineEvent)
    (hB : XplBlock interpretation r S who g ms₀ (pre ++ m :: post) acc blk)
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hch₀ : CHistBy interpretation r S g ms₀)
    (hfresh₀ : TR.TRRecvFreshAll r ms₀) :
    TR.RecvDecStep.A2bSeedRkAliasRes interpretation r S g (ms₀ ++ pre) acc := by
  intro q stateIdx st c c' t msg skIdx rIdx_s srcIdx seed_s seed_c pqSalt body_in
    hst hcur hc hfind hrep hparse hver hnc hsk hmac_eq hγrk hcons hγ
  have hq := a2b_quietPre hpre
  have hrole : RoleSnapshots r (runTraceMoves r (ms₀ ++ pre)) :=
    prom_a2b_roleSnapshots_of_quietPre hpre hch₀.2
  have hfresh : TR.TRRecvFreshAll r (ms₀ ++ pre) :=
    prom_a2b_trRecvFreshAll_of_quietExt hq hfresh₀
  have hrun : ModelRun r (ms₀ ++ pre) := prom_a2b_modelRun_pre hB
  have hreach : ReachableTrace (runTraceMoves r (ms₀ ++ pre)) := hrun.2.2.1.1
  have hq_ab : q = r.alice ∨ q = r.bob := prom_a2b_owner_alice_or_bob hrole hrun hst
  obtain ⟨_hcf, hskRel⟩ := hfresh q stateIdx st hq_ab hst hcur
  by_cases hshape :
      (gamma' interpretation S g seed_c).shape = (gamma' interpretation S g seed_s).shape
  · exact False.elim (prom_a2b_rkAlias_false_of_shape_eq hreach hskRel hst hc hfind hcons hsk hshape)
  · have hst_avail : st ∈ availableStates r (runTraceMoves r (ms₀ ++ pre)) :=
      Symbolic.Swarm.CREF.TR.RecvHistStep2.mem_availableStates_of_at? r (ms₀ ++ pre)
        (Symbolic.Swarm.CREF.TR.FreshSigma.at?_eq_some_of_getLocalState_some hst)
    obtain ⟨ks, ms_, hs_form⟩ := TR.RecvDecStep.a2b_skippedSeed_hmac hreach hsk
    obtain ⟨kc, mc, hc_form⟩ := TR.RecvDecStep.a2b_consume_seed_hmac hcons
    refine False.elim (hnc ?_)
    unfold RecvCollision
    simp only [hparse]
    refine Or.inl ?_
    unfold MemoCollisionOn
    dsimp only
    have ht_cat : t = DY.Concat.concat msg.wire msg.mac :=
      TR.G1.parseTrSignalMsg_eq_concat hparse
    have hs_t : (seed_s, (gamma' interpretation S g seed_s).shape, gamma interpretation S g seed_s) ∈
        (gamma' interpretation S g t).memo := by
      rw [ht_cat]
      refine TR.G1.memo_rhs_subset_memo_concat interpretation S g _ _ ?_
      rw [hmac_eq]
      exact TR.RecvDecStep.a2b_memo_mem_computeMac_seed interpretation S g _ _ _ _ _
        (TR.RecvDecStep.a2b_self_memo_of_hmac interpretation S g hs_form)
    have hc_rt : computeMac (trMsgKeys DY.Spqr.zeroKey seed_c).macKey st.peerIk st.myIk msg.wire ∈
        (whisperTrials interpretation r S g (runTraceMoves r (ms₀ ++ pre)) msg).flatMap
          (trialTerms (honestSalts r (ms₀ ++ pre)) msg) :=
      Symbolic.Swarm.CREF.Stage1Trials.computeMac_mem_whisperTrialTerms_of_byteChain
        hver hst_avail hc hγrk hcons (List.mem_cons_self ..)
    have hc_new : (seed_c, (gamma' interpretation S g seed_c).shape, gamma interpretation S g seed_c) ∈
        (t :: (whisperTrials interpretation r S g (runTraceMoves r (ms₀ ++ pre)) msg).flatMap
          (trialTerms (honestSalts r (ms₀ ++ pre)) msg)).flatMap
          (fun u => (gamma' interpretation S g u).memo) :=
      List.mem_flatMap.mpr ⟨_, List.mem_cons_of_mem _ hc_rt,
        TR.RecvDecStep.a2b_memo_mem_computeMac_seed interpretation S g _ _ _ _ _
          (TR.RecvDecStep.a2b_self_memo_of_hmac interpretation S g hc_form)⟩
    have hs_npt : seed_s ∉ plaintextTerms (runVis r (ms₀ ++ pre)) := by
      have h := TR.G1.not_mem_ptAtoms_of_view_random_isNone r (ms₀ ++ pre) [] (fun _ h => absurd h List.not_mem_nil)
        seed_s (by
          subst hs_form
          dsimp only [hmac, DY.KdfExtract.kdfExtract, DY.KdfExtract.CanKdfExtract.kdfExtract]
          rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _]
          rfl)
      rwa [List.append_nil] at h
    have hc_npt : seed_c ∉ plaintextTerms (runVis r (ms₀ ++ pre)) := by
      have h := TR.G1.not_mem_ptAtoms_of_view_random_isNone r (ms₀ ++ pre) [] (fun _ h => absurd h List.not_mem_nil)
        seed_c (by
          subst hc_form
          dsimp only [hmac, DY.KdfExtract.kdfExtract, DY.KdfExtract.CanKdfExtract.kdfExtract]
          rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _]
          rfl)
      rwa [List.append_nil] at h
    refine ⟨_, List.mem_flatMap.mpr ⟨t, List.mem_cons_self .., hs_t⟩, _, List.mem_append_right _ hc_new,
      fun h => hshape h.symm, Or.inl (by
        subst hs_form
        dsimp only [assumedInjective, hmac, DY.KdfExtract.kdfExtract, DY.KdfExtract.CanKdfExtract.kdfExtract]
        rw [DY.BytesView.view_pack (SubF := DY.KdfExtract.KdfExtract.SubF)]
        simp), ?_, ?_, hγ.symm⟩
    · intro h; rw [List.append_nil] at h; exact absurd h hs_npt
    · intro h; rw [List.append_nil] at h; exact absurd h hc_npt

end RkAliasSupply

end Symbolic.Swarm.CREF.CliPure
