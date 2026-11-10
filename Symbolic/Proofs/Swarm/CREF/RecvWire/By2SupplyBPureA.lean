/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.ALaCarte.Basic
import DY.Bytes.Basic
import DY.EquationalTheory.KdfExtract
import DY.Actions.ProtocolEvent
public import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecTieSeedShapePure
public import Symbolic.Proofs.Swarm.CREF.TR.G1.MacKdfSafeTR
public import Symbolic.Proofs.Swarm.CREF.TR.RecvFresh
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvWire.A2bSameOriginPure
import Symbolic.Proofs.Swarm.CREF.TR.G1.G1Rep
import Symbolic.Proofs.Swarm.CREF.TR.G1.SkippedPkLineage
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.RecvWire.RcvByPure -- shake: keep
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Ratchet-Key Alias Shape-Split Lemmas for Whisper Receive

Proves `a2b_rkAlias_false_of_shape_eq` (excluding equal-shape seeds on a ratchet-key alias via
`TRSkippedRIdxChainRel` and `CompScheduleInv`) and `a2b_rkAliasShapeNeExcl` (reducing
unequal-shape seeds on a ratchet-key alias to `RecvCollision` via `whisperTrials`).
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure hiding StEntry TREntry
open Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (RecvChain findRecvChain consumeMessageKey computeMac messageVersion
  hmac)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record CryptoVerification.E2E.RecordX
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec encodeRecord
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 hiding encodeRecord
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.TR.G1
open Symbolic.Swarm.CREF.TR.RecvDecStep Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep

variable {interpretation : ExternInterpretation}

theorem a2b_trRecvFreshAll_of_quietExt {r₀ : ProtocolSetup} {ms ms' : List Move}
    (hq : PureXplQuiet.QuietExt (runTraceMoves r₀ ms) (runTraceMoves r₀ ms'))
    (h : TR.TRRecvFreshAll r₀ ms) : TR.TRRecvFreshAll r₀ ms' := by
  intro q stateIdx st hqab hget hcur
  rw [PureXplQuiet.quiet_getLocalState hq] at hget
  rw [PureXplQuiet.quiet_isCurrentSnapshot hq] at hcur
  obtain ⟨hc, hs⟩ := h q stateIdx st hqab hget hcur
  exact ⟨TR.trRecvCountersFresh_of_imp
      (fun _ _ _ _ _ _ hl => (PureXplQuiet.quiet_eventLoggedAt hq _ _).mp hl)
      (fun _ _ _ _ _ _ hl => (PureXplQuiet.quiet_eventLoggedAt hq _ _).mp hl) hc,
    TR.trSkippedRIdxChainRel_of_imp
      (fun _ _ _ _ _ _ hl => (PureXplQuiet.quiet_eventLoggedAt hq _ _).mp hl) hs⟩

theorem a2b_roleSnapshots_of_quietPre {r₀ : ProtocolSetup} {ms₀ pre : List Move}
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r₀ ms₀) pre)
    (hrole : RoleSnapshots r₀ (runTraceMoves r₀ ms₀)) :
    RoleSnapshots r₀ (runTraceMoves r₀ (ms₀ ++ pre)) := by
  rw [TR.runTrace_append]
  exact roleSnapshots_of_movesFrom_invisibleNoEffect hpre hrole

theorem a2b_modelRun_pre {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
    {g : Ghost} {ms₀ pre post : List Move} {m : Move} {acc blk : List MachineEvent}
    (hB : XplBlock interpretation r₀ S who g ms₀ (pre ++ m :: post) acc blk) :
    ModelRun r₀ (ms₀ ++ pre) := by
  have hreach : (runTraceMoves r₀ (ms₀ ++ pre)).Reachable reachability := by
    have h := hB.run.2.2.1.2.2 (ms₀ ++ pre).length
    rwa [← List.append_assoc, List.take_left] at h
  have h := hB.run
  rw [← List.append_assoc] at h
  exact modelRun_prefix_of_reachable h hreach

theorem a2b_rkAlias_rIdx_ne
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

theorem a2b_rkAlias_false_of_shape_eq
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move}
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
  exact a2b_rkAlias_rIdx_ne hskRel hc hfind hsk hrIdx_eq

/-- Ratchet-key alias configuration where the cached skipped seed `seed_s` and chain seed
`seed_c` evaluate to the same bytes with unequal shapes. -/
def A2bRkAliasShapeNe (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms : List Move) (t : DY.Bytes) : Prop :=
  let tr := runTraceMoves r ms
  ∃ msg, parseTrSignalMsg t = some msg ∧
    msg.version = messageVersion ∧
    ∃ seed_s ∈ skippedSeedsFor tr msg, (∃ ks ms_, seed_s = hmac ks ms_) ∧ ∃ pqSalt st,
      st ∈ availableStates r tr ∧
      msg.mac = computeMac (trMsgKeys pqSalt seed_s).macKey st.peerIk st.myIk msg.wire ∧
      ∃ c ∈ st.toDRState.recv, ∃ seed_c c',
        findRecvChain st.recv msg.ratchetKey = none ∧
        gamma interpretation S g c.ratchetKey = gamma interpretation S g msg.ratchetKey ∧
        consumeMessageKey c msg.counter = some (seed_c, c') ∧
        gamma interpretation S g seed_c = gamma interpretation S g seed_s ∧
        (gamma' interpretation S g seed_c).shape ≠ (gamma' interpretation S g seed_s).shape

def A2bRkAliasShapeNeExcl (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms : List Move) (acc : List MachineEvent) : Prop :=
  ∀ t, A2bRkAliasShapeNe interpretation r S g ms t → RecvCollision interpretation r S g ms t

theorem a2b_rkAliasShapeNeExcl
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move) (acc : List MachineEvent) :
    A2bRkAliasShapeNeExcl interpretation r S g ms acc := by
  intro t ⟨msg, hparse, hver, seed_s, _hmem_s, ⟨ks, ms_, hs_form⟩, pqSalt, st, hst_av, hmac_eq,
    c, hc, seed_c, c', _hfind, hγrk, hcons, hγ, hsh⟩
  obtain ⟨kc, mc, hc_form⟩ := TR.RecvDecStepTiePure.a2b_consume_seed_hmac hcons
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
    exact TR.RecvDecStepTiePure.a2b_memo_mem_computeMac_seed interpretation S g _ _ _ _ _
      (TR.RecvDecStepTiePure.a2b_self_memo_of_hmac interpretation S g hs_form)
  have hc_rt : computeMac (trMsgKeys DY.Spqr.zeroKey seed_c).macKey st.peerIk st.myIk msg.wire ∈
      (whisperTrials interpretation r S g (runTraceMoves r ms) msg).flatMap
        (trialTerms (honestSalts r ms) msg) :=
    Symbolic.Swarm.CREF.Stage1Trials.computeMac_mem_whisperTrialTerms_of_byteChain
      hver hst_av hc hγrk hcons (List.mem_cons_self ..)
  have hc_new : (seed_c, (gamma' interpretation S g seed_c).shape, gamma interpretation S g seed_c) ∈
      (t :: (whisperTrials interpretation r S g (runTraceMoves r ms) msg).flatMap
        (trialTerms (honestSalts r ms) msg)).flatMap
        (fun u => (gamma' interpretation S g u).memo) :=
    List.mem_flatMap.mpr ⟨_, List.mem_cons_of_mem _ hc_rt,
      TR.RecvDecStepTiePure.a2b_memo_mem_computeMac_seed interpretation S g _ _ _ _ _
        (TR.RecvDecStepTiePure.a2b_self_memo_of_hmac interpretation S g hc_form)⟩
  have hs_npt : seed_s ∉ plaintextTerms (runVis r ms) := by
    have h := TR.G1.not_mem_ptAtoms_of_view_random_isNone r ms [] (fun _ h => absurd h List.not_mem_nil)
      seed_s (by
        subst hs_form
        dsimp only [hmac, DY.KdfExtract.kdfExtract, DY.KdfExtract.CanKdfExtract.kdfExtract]
        rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random _]
        rfl)
    rwa [List.append_nil] at h
  have hc_npt : seed_c ∉ plaintextTerms (runVis r ms) := by
    have h := TR.G1.not_mem_ptAtoms_of_view_random_isNone r ms [] (fun _ h => absurd h List.not_mem_nil)
      seed_c (by
        subst hc_form
        dsimp only [hmac, DY.KdfExtract.kdfExtract, DY.KdfExtract.CanKdfExtract.kdfExtract]
        rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random _]
        rfl)
    rwa [List.append_nil] at h
  refine ⟨_, List.mem_flatMap.mpr ⟨t, List.mem_cons_self .., hs_t⟩, _, List.mem_append_right _ hc_new,
    fun h => hsh h.symm, Or.inl (by
      subst hs_form
      dsimp only [assumedInjective, hmac, DY.KdfExtract.kdfExtract, DY.KdfExtract.CanKdfExtract.kdfExtract]
      rw [DY.BytesView.view_pack (SubF := DY.KdfExtract.KdfExtract.SubF)]
      simp), ?_, ?_, hγ.symm⟩
  · intro h; rw [List.append_nil] at h; exact absurd h hs_npt
  · intro h; rw [List.append_nil] at h; exact absurd h hc_npt

end Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
