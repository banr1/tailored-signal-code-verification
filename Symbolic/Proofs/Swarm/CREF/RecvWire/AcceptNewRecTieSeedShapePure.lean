/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecBasePure
public import Symbolic.Proofs.Swarm.CREF.TR.G1.WireShapeInj
import DY.Bytes.Basic
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
import DY.EquationalTheory.KdfExtract
import Symbolic.Proofs.Swarm.COMPOSED.CompSchedule
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SendRetCoinsCliPureB
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import Symbolic.Proofs.Swarm.CREF.TR.G1.CanonLocal
import Symbolic.Proofs.Swarm.CREF.TR.G1.G1Rep
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.TRView
import Symbolic.Proofs.Swarm.CREF.TR.Leaks -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.StoredRk -- shake: keep
import Symbolic.DYBridge.DY.Bytes.Basic
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
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract

/-!
# Byte-Equal Seed Decomposition for Whisper Receive

Decomposes term equality `seed_s = seed_c` between a cached skipped seed and a receiver-chain
seed with equal byte evaluations into same-shape seed equality (`A2bSeedShapeEqRes`),
ratchet-key aliasing (`A2bSeedRkAliasRes`), and cross-seed MAC exclusion (`A2bCrossSeedExcl`),
discharging distinct-shape hits via `RecvCollision`.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false
set_option linter.unusedVariables false

namespace Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure
open Symbolic.Swarm.CREF.TR hiding HsKeysOk TRStateStoredAt at?_append_of_lt at?_append_self gamma_concat gamma_dhPk getLocalState_fst mem_availableStates_of_trStateStoredAt newRandoms_append_rnd runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc run_bind_fst run_bind_snd
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding SpqrSem StEntry TREntry

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (SessionInfo RecvChain findRecvChain recvChainFor consumeMessageKey
  computeMac messageVersion hmac)
open DY.Libsignal.TripleRatchet
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.TR.G1 Symbolic.Swarm.CREF.TR.G1.Spine

theorem a2b_memo_mem_trunc8 (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (x : DY.Bytes)
    {e : DY.Bytes × DY.Bytes × HwBytes} (he : e ∈ (gamma' i S g x).memo) :
    e ∈ (gamma' i S g (DY.Trunc.trunc8 x)).memo := by
  unfold gamma' at he ⊢
  rw [show DY.Trunc.trunc8 x = ({ input := x } : DY.Trunc.Trunc8.SubF DY.Bytes).pack from rfl,
    DY.Bytes.rec_eq concretizeTrunc (concretizeAll i S g)]
  simp [concretizeTrunc, node, he]

theorem a2b_memo_mem_computeMac_seed (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (salt seed ik1 ik2 w : DY.Bytes) {e : DY.Bytes × DY.Bytes × HwBytes}
    (he : e ∈ (gamma' i S g seed).memo) :
    e ∈ (gamma' i S g (computeMac (trMsgKeys salt seed).macKey ik1 ik2 w)).memo := by
  unfold computeMac
  refine a2b_memo_mem_trunc8 i S g _ (memo_mem_of_hmac_left i S g _ _ ?_)
  dsimp only [trMsgKeys, DY.Libsignal.TripleRatchet.hkdfBlock2]
  exact memo_mem_of_hmac_left i S g _ _ (memo_mem_of_hmac_right i S g _ _ he)

theorem a2b_self_memo_of_hmac (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) {u k m : DY.Bytes}
    (hu : u = hmac k m) :
    (u, (gamma' i S g u).shape, gamma i S g u) ∈ (gamma' i S g u).memo := by
  subst hu; exact self_mem_memo_hmac i S g k m

/-- Two `hmac`-headed seeds `seed_s` (in `msg.mac`) and `seed_c = recvSeed st msg` (for an
available `st`) with equal byte evaluations and distinct shapes trigger `RecvCollision`. -/
theorem a2b_recvCollision_of_seed_shape_ne
    (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) (acc : List MachineEvent) (t : DY.Bytes) (msg : TRSignalMsg)
    (st : TRState) (hst : st ∈ availableStates r₀ (runTraceMoves r₀ ms))
    (seed_s seed_c pqSalt ik1 ik2 ks ms_ kc mc : DY.Bytes)
    (hparse : parseTrSignalMsg t = some msg)
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed_s).macKey ik1 ik2 msg.wire)
    (hseed_c : recvSeed st msg = some seed_c)
    (hs_form : seed_s = hmac ks ms_) (hc_form : seed_c = hmac kc mc)
    (hγ : gamma interpretation S g seed_c = gamma interpretation S g seed_s)
    (hsh : (gamma' interpretation S g seed_c).shape ≠ (gamma' interpretation S g seed_s).shape) :
    RecvCollision interpretation r₀ S g ms t := by
  unfold RecvCollision
  simp only [hparse]
  refine Or.inl ?_
  unfold MemoCollisionOn
  dsimp only
  have ht_cat : t = Concat.concat msg.wire msg.mac := parseTrSignalMsg_eq_concat hparse
  have hs_t : (seed_s, (gamma' interpretation S g seed_s).shape, gamma interpretation S g seed_s) ∈
      (gamma' interpretation S g t).memo := by
    rw [ht_cat]
    refine memo_rhs_subset_memo_concat interpretation S g _ _ ?_
    rw [hmac_eq]
    exact a2b_memo_mem_computeMac_seed interpretation S g _ _ _ _ _
      (a2b_self_memo_of_hmac interpretation S g hs_form)
  have hc_rt : computeMac (trMsgKeys DY.Spqr.zeroKey seed_c).macKey st.peerIk st.myIk msg.wire ∈
      (whisperTrials interpretation r₀ S g (runTraceMoves r₀ ms) msg).flatMap
        (trialTerms (honestSalts r₀ ms) msg) :=
    computeMac_mem_whisperTrialTerms hst (List.mem_cons_self ..) hseed_c
  have hc_new : (seed_c, (gamma' interpretation S g seed_c).shape, gamma interpretation S g seed_c) ∈
      (t :: (whisperTrials interpretation r₀ S g (runTraceMoves r₀ ms) msg).flatMap
        (trialTerms (honestSalts r₀ ms) msg)).flatMap
        (fun u => (gamma' interpretation S g u).memo) :=
    List.mem_flatMap.mpr ⟨_, List.mem_cons_of_mem _ hc_rt,
      a2b_memo_mem_computeMac_seed interpretation S g _ _ _ _ _
        (a2b_self_memo_of_hmac interpretation S g hc_form)⟩
  have hs_npt : seed_s ∉ plaintextTerms (runVis r₀ ms) := by
    have h := not_mem_ptAtoms_of_view_random_isNone r₀ ms [] (fun _ h => absurd h List.not_mem_nil)
      seed_s (by
        subst hs_form
        dsimp only [hmac, DY.KdfExtract.kdfExtract, DY.KdfExtract.CanKdfExtract.kdfExtract]
        rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random _]
        rfl)
    rwa [List.append_nil] at h
  have hc_npt : seed_c ∉ plaintextTerms (runVis r₀ ms) := by
    have h := not_mem_ptAtoms_of_view_random_isNone r₀ ms [] (fun _ h => absurd h List.not_mem_nil)
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

theorem a2b_consume_seed_hmac {c c' : RecvChain} {n : UInt32} {seed : DY.Bytes}
    (h : consumeMessageKey c n = some (seed, c')) : ∃ k m, seed = hmac k m := by
  unfold consumeMessageKey at h
  split_ifs at h
  injection h with h
  injection h with h
  exact ⟨_, _, h.symm⟩

theorem a2b_skippedSeed_hmac {tr : ExecTrace} (hreach : tr.Reachable reachability)
    {skIdx rIdx_s srcIdx : Nat} {s : SessionInfo} {pk seed_s : DY.Bytes} {ctr : UInt32}
    (hsk : (tr.at? skIdx : Option TREntry) =
      some ⟨TREvent.SkippedKeyStored s pk ctr seed_s rIdx_s srcIdx⟩) :
    ∃ k m, seed_s = hmac k m := by
  obtain ⟨_, _, _, _, _, ck₀_s, _, _, hseed_s⟩ :=
    (Symbolic.Swarm.COMPOSED.CompRatchet.compScheduleInv_reachable hreach).eventOK
      (TREvent.SkippedKeyStored s pk ctr seed_s rIdx_s srcIdx)
      ⟨skIdx, (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mpr hsk⟩
  exact ⟨_, _, hseed_s⟩

theorem a2b_recvSeed_of_find {st : TRState} {msg : TRSignalMsg} {c c' : RecvChain}
    {seed : DY.Bytes} (hver : msg.version = messageVersion)
    (hfind : findRecvChain st.recv msg.ratchetKey = some c)
    (hcons : consumeMessageKey c msg.counter = some (seed, c')) :
    recvSeed st msg = some seed := by
  have hf : findRecvChain st.toDRState.recv msg.ratchetKey = some c := hfind
  unfold recvSeed recvChainFor
  simp only [hver, hf, hcons, Option.map_some, ↓reduceIte]

/-- Term equality of a cached skipped seed `seed_s` and a chain seed `seed_c` when `c` is the
term-keyed `findRecvChain` hit and both seeds have equal byte evaluations and equal shapes. -/
def A2bSeedShapeEqRes (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) (acc : List MachineEvent) : Prop :=
  ∀ (p : Participant) (stateIdx : Nat) (st : TRState) (c c' : RecvChain) (t : DY.Bytes)
    (msg : TRSignalMsg) (skIdx rIdx_s srcIdx : Nat) (seed_s seed_c pqSalt : DY.Bytes)
    (body : HwBytes),
    ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run (runTraceMoves r₀ ms)).1 =
      some st →
    isCurrentSnapshot (runTraceMoves r₀ ms) stateIdx = true →
    c ∈ st.recv →
    findRecvChain st.recv msg.ratchetKey = some c →
    t ∈ recvRepresentations interpretation r₀ S g ms body →
    parseTrSignalMsg t = some msg →
    msg.version = messageVersion →
    ¬ RecvCollision interpretation r₀ S g ms t →
    ((runTraceMoves r₀ ms).at? skIdx : Option TREntry) =
      some ⟨TREvent.SkippedKeyStored (st.sessionInfo p) msg.ratchetKey msg.counter seed_s rIdx_s srcIdx⟩ →
    msg.mac = computeMac (trMsgKeys pqSalt seed_s).macKey st.peerIk st.myIk msg.wire →
    consumeMessageKey c msg.counter = some (seed_c, c') →
    gamma interpretation S g seed_c = gamma interpretation S g seed_s →
    (gamma' interpretation S g seed_c).shape = (gamma' interpretation S g seed_s).shape →
    seed_s = seed_c

/-- Term equality of `seed_s` and `seed_c` when no receive chain is keyed by the term
`msg.ratchetKey` yet `c ∈ st.recv` has a byte-equal ratchet key. -/
def A2bSeedRkAliasRes (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) (acc : List MachineEvent) : Prop :=
  ∀ (p : Participant) (stateIdx : Nat) (st : TRState) (c c' : RecvChain) (t : DY.Bytes)
    (msg : TRSignalMsg) (skIdx rIdx_s srcIdx : Nat) (seed_s seed_c pqSalt : DY.Bytes)
    (body : HwBytes),
    ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run (runTraceMoves r₀ ms)).1 =
      some st →
    isCurrentSnapshot (runTraceMoves r₀ ms) stateIdx = true →
    c ∈ st.recv →
    findRecvChain st.recv msg.ratchetKey = none →
    t ∈ recvRepresentations interpretation r₀ S g ms body →
    parseTrSignalMsg t = some msg →
    msg.version = messageVersion →
    ¬ RecvCollision interpretation r₀ S g ms t →
    ((runTraceMoves r₀ ms).at? skIdx : Option TREntry) =
      some ⟨TREvent.SkippedKeyStored (st.sessionInfo p) msg.ratchetKey msg.counter seed_s rIdx_s srcIdx⟩ →
    msg.mac = computeMac (trMsgKeys pqSalt seed_s).macKey st.peerIk st.myIk msg.wire →
    gamma interpretation S g c.ratchetKey = gamma interpretation S g msg.ratchetKey →
    consumeMessageKey c msg.counter = some (seed_c, c') →
    gamma interpretation S g seed_c = gamma interpretation S g seed_s →
    seed_s = seed_c

/-- Byte-equal seeds `seed_s` and `seed_c` are term-equal given `A2bSeedShapeEqRes` and
`A2bSeedRkAliasRes`. -/
theorem a2b_seedEq_of_shapeRes
    (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) (acc : List MachineEvent) (hrun : ModelRun r₀ ms)
    (hA : A2bSeedShapeEqRes interpretation r₀ S g ms acc)
    (hB : A2bSeedRkAliasRes interpretation r₀ S g ms acc)
    (p : Participant) (stateIdx : Nat) (st : TRState) (c c' : RecvChain) (t : DY.Bytes)
    (msg : TRSignalMsg) (skIdx rIdx_s srcIdx : Nat) (seed_s seed_c pqSalt : DY.Bytes)
    (body : HwBytes) (rec : RecordRec)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms)).1 = some st)
    (hcur : isCurrentSnapshot (runTraceMoves r₀ ms) stateIdx = true)
    (hrel : StateRel interpretation S g st rec)
    (hnd : (rec.current.receiverChains.map ChainRec.senderRatchetKey).Nodup)
    (hver : msg.version = messageVersion)
    (hc : c ∈ st.recv)
    (hrep : t ∈ recvRepresentations interpretation r₀ S g ms body)
    (hparse : parseTrSignalMsg t = some msg)
    (hnc : ¬ RecvCollision interpretation r₀ S g ms t)
    (hsk : ((runTraceMoves r₀ ms).at? skIdx : Option TREntry) =
      some ⟨TREvent.SkippedKeyStored (st.sessionInfo p) msg.ratchetKey msg.counter seed_s rIdx_s srcIdx⟩)
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed_s).macKey st.peerIk st.myIk msg.wire)
    (hγrk : gamma interpretation S g c.ratchetKey = gamma interpretation S g msg.ratchetKey)
    (hcons : consumeMessageKey c msg.counter = some (seed_c, c'))
    (hγ : gamma interpretation S g seed_c = gamma interpretation S g seed_s) :
    seed_s = seed_c := by
  cases hf : findRecvChain st.recv msg.ratchetKey with
  | none =>
    exact hB p stateIdx st c c' t msg skIdx rIdx_s srcIdx seed_s seed_c pqSalt body hst hcur hc hf
      hrep hparse hver hnc hsk hmac_eq hγrk hcons hγ
  | some c₀ =>
    have hf' : st.recv.find? (·.ratchetKey == msg.ratchetKey) = some c₀ := hf
    have hc₀ : c₀ ∈ st.recv := List.mem_of_find?_eq_some hf'
    have hk₀ : c₀.ratchetKey = msg.ratchetKey := by simpa using List.find?_some hf'
    have hcc : c₀ = c :=
      List.inj_on_of_nodup_map (RecvHistStep.recvRk_nodup_of_stateRel hrel hnd) hc₀ hc
        (show gamma interpretation S g c₀.ratchetKey = gamma interpretation S g c.ratchetKey by
          rw [hk₀, hγrk])
    rw [hcc] at hf
    by_cases hsh :
        (gamma' interpretation S g seed_c).shape = (gamma' interpretation S g seed_s).shape
    · exact hA p stateIdx st c c' t msg skIdx rIdx_s srcIdx seed_s seed_c pqSalt body hst hcur hc hf
        hrep hparse hver hnc hsk hmac_eq hcons hγ hsh
    · exfalso
      obtain ⟨ks, ms_, hs_form⟩ := a2b_skippedSeed_hmac hrun.2.2.1.1 hsk
      obtain ⟨kc, mc, hc_form⟩ := a2b_consume_seed_hmac hcons
      have hst_avail : st ∈ availableStates r₀ (runTraceMoves r₀ ms) :=
        Symbolic.Swarm.CREF.TR.RecvHistStep2.mem_availableStates_of_at? r₀ ms
          (Symbolic.Swarm.CREF.TR.FreshSigma.at?_eq_some_of_getLocalState_some hst)
      exact hnc (a2b_recvCollision_of_seed_shape_ne interpretation r₀ S g ms acc t msg st hst_avail
        seed_s seed_c pqSalt st.peerIk st.myIk ks ms_ kc mc hparse hmac_eq
        (a2b_recvSeed_of_find hver hf hcons) hs_form hc_form hγ hsh)

/-- Cached `SkippedKeyStored` seeds on `tr` matching `msg.ratchetKey` and `msg.counter`. -/
def skippedSeedsFor (tr : ExecTrace) (msg : TRSignalMsg) : List DY.Bytes :=
  (List.range tr.length).filterMap fun i =>
    match tr.getEventAt TREvent i with
    | some (.SkippedKeyStored _ pk n seed _ _) =>
      if pk = msg.ratchetKey ∧ n = msg.counter then some seed else none
    | _ => none

/-- Cross-seed MAC guess where the receive chain is found by ratchet-key bytes. -/
def A2bCrossSeedMacGuess (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms : List Move) (t : DY.Bytes) : Prop :=
  let tr := runTraceMoves r ms
  ∃ msg, parseTrSignalMsg t = some msg ∧ msg.version = messageVersion ∧
    ∃ seed ∈ skippedSeedsFor tr msg, ∃ (salt : DY.Bytes) (st₀ : TRState),
      st₀ ∈ availableStates r tr ∧
      (findRecvChain st₀.toDRState.recv msg.ratchetKey).isSome = true ∧
      msg.mac = computeMac (trMsgKeys salt seed).macKey st₀.peerIk st₀.myIk msg.wire ∧
    ∃ st ∈ availableStates r tr, ∃ c ∈ st.toDRState.recv, ∃ seed' c',
      gamma interpretation S g c.ratchetKey = gamma interpretation S g msg.ratchetKey ∧
      consumeMessageKey c msg.counter = some (seed', c') ∧
      gamma interpretation S g seed' ≠ gamma interpretation S g seed ∧
    ∃ k ∈ ownKeys r tr st msg,
      gamma interpretation S g (computeMac (trMsgKeys k seed').macKey st.peerIk st.myIk msg.wire) =
        gamma interpretation S g msg.mac

/-- Every cross-seed MAC guess triggers `RecvCollision`. -/
def A2bCrossSeedExcl (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) (acc : List MachineEvent) : Prop :=
  ∀ t, A2bCrossSeedMacGuess interpretation r₀ S g ms t → RecvCollision interpretation r₀ S g ms t

theorem a2b_mem_skippedSeedsFor {tr : ExecTrace} {skIdx : Nat} {s : SessionInfo}
    {msg : TRSignalMsg} {seed : DY.Bytes} {rIdx srcIdx : Nat}
    (hsk : (tr.at? skIdx : Option TREntry) =
      some ⟨TREvent.SkippedKeyStored s msg.ratchetKey msg.counter seed rIdx srcIdx⟩) :
    seed ∈ skippedSeedsFor tr msg := by
  have hlt : skIdx < tr.length := by
    by_contra h
    rw [at?_ge_length tr (Nat.le_of_not_lt h)] at hsk
    cases hsk
  unfold skippedSeedsFor
  refine List.mem_filterMap.mpr ⟨skIdx, List.mem_range.mpr hlt, ?_⟩
  simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hsk]

end Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure
