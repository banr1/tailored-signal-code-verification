/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.PrefixRedHalted -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.PrefixRedHaltedEval -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.CompositionHaltedWitness -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidCodec -- proof-setup: allow-public-import
public import Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.M3Interfaces -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.PqxdhSimTypes -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1Sync.TopInSync
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Msg
import Computational.Proofs.E2E.Dsl.ClampsLossless
import Computational.Proofs.E2E.Dsl.KindRedHaltedEval
import Computational.Proofs.ReductionDsl.Soundness

/-!
# Halted Multi-Session Two-Stage Prefix Reduction Instantiation

Instantiates `PrefixRedHalted` and `PrefixRedHaltedEval` with `kemFailSessionTracker` and
validated subprogram bundles (`ValidHaltedPrefixSubprograms`, `ValidHaltedPrefixSubprogramsInst`),
proving `GRed2Bounded`, per-instance Stage-2 query bounds, and full two-stage `ProbComp`
equivalence (`prefixEval_eq_of_valid`).
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.PrefixRedHaltedInst

open scoped BigOperators
open OracleComp OracleSpec
open _root_.ReductionDsl (Env Expr Comp Mid Ty TwoStageCostedReduction bits
  e2eSessionTargetIface prefixCtxT keyIndQT keyIndQenc keyIndRenc sidT sidV smQT smQenc
  smRT GhostStT atomicE2EOps)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.SM (GameState MakesAtMostQueries RecvResult)
open CryptoGames.LibsignalSession (Crypto GhostState IdentityKey PublicKey ShaCompress)
open CryptoVerification.LibsignalSpqrV1 (MlKem coinBytes)
open CryptoVerification.SpqrV1Sync.SendTotal (BOkTight)
open CryptoVerification.E2E (BHE2EDrvState BHE2ESmResp BHModelInst BHPrefixCtx BHTargetQuery
  BHTargetResp Bytes GRed2Bounded ModelDriverInstanceMeta SampledSessionKey bhClassifyTarget
  bhDrvKiQueryOk bhE2EDrvInstClean bhE2ECostBudget bhE2EInstIkACorr bhE2EMirror bhE2EStepLocalSm
  bhIdKeyOf bhIsBobRecvSMQuery bhLiftP bhNoOpkRespPromoted bhPackSmResp
  bhShallowCheckExtSm bhShallowCommitExtSm bhShallowFinishPrefix bhShallowStepPostLocal
  bhShallowStepPreNonCtl bhTargetGameSpec bhTargetQenc bhTargetRdec configRefuseEarlyBobCorr
  e2eTargetGameCodec paramsIdsWithSpqr sessionSchemeFixedSpk
  stageOneAsProbComp)
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge (KemFailSessionTrack
  initKemFailSessionTrack initKemFailTrack stepKemFailDeliver stepKemFailSend)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixCore (SessionHaltTracker
  bhE2ELocalStartSessionTracked bhE2EStepLocalSmSessionTracked
  bhPrefixRedWithSessionTracked gameRSessionTracked)
open Computational.Proofs.E2E.Dsl.M3Interfaces (DrvMetaAligned DrvMirrorBounded DrvQueryBounded
  DrvSessionsBounded KeyIndReachBounded bhExtSmStep bhFilterSmQuery bhPromoteSlotK
  drvMetaAligned_mirror)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (pqxdhKeyIndImpl1KeyReal_preserves_setupBounded)
open Computational.Proofs.E2E.Dsl.PrefixRedHalted (HaltedPrefixSubprograms bhPrefixHandlePostWithHalted
  bhPrefixHandlePreWithHalted bhPrefixRedWithHalted bhShallowStepPostLocalHalted
  bhShallowStepPreCtlHalted bhShallowStepPreNonCtlHalted drvHaltedEnc drvHaltedTy
  gRed2Bounded_atomic_of_bounds haltedPrefixEndpointCost haltedPrefixSizeBound
  prefixHandlePostHalted prefixHandlePostHalted_eval_ctl prefixHandlePostHalted_eval_ki
  prefixHandlePostHalted_eval_sm prefixHandlePreHalted prefixHandlePreHalted_eval_ctl
  prefixHandlePreHalted_eval_ki prefixHandlePreHalted_eval_sm prefixKiStepHaltedC
  prefixKiStepHaltedC_cost prefixRedHalted prefixRedHalted_makesAtMostQueries
  prefixRedHalted_size_le_budget prefixRedHalted_stage1Queries
  prefixRedHalted_totalQueries_le)
open Computational.Proofs.E2E.Dsl.PrefixRedHaltedEval (StepBudgetOk StepNextInv TargetAdvBounded
  TwoStageAtomicSimSpec atomicGameRespEnc atomicPrefixCtxEnc mapPreEnc packAtomicSmRespEnc
  twoStage_stage12_comp_eq)
open Computational.Proofs.E2E.Dsl.CompositionHaltedWitness (HaltedPausedInv HaltedSimInv
  HaltedTargetAdvPerInstanceBounded ValidSimTrackInv bhPrefixRedWithHalted_eq_bhPrefixRedWithSessionTracked
  commitExtSm_preserves e2eFreshScanInnerFactor e2ePerStepWeightedFactor kemFailSessionTracker
  localStartSessionTracked_preserves promoteSlotK_paused_preserves
  stepLocalSmSessionTracked_preserves totalCost_le_bhE2ECostBudget_of_step_endpoint)

/-! ## Tracker reachability invariant -/

/-- Reachability and length invariant on `KemFailSessionTrack F Bytes` after at most `qBound`
Double Ratchet steps. -/
structure KemBridgeTrackInvLocal (F : ShaCompress) (_K : MlKem) (qBound : ℕ)
    (st : KemFailSessionTrack F Bytes) : Prop where
  sentB_len : st.1.sentB.length ≤ qBound
  wires_len : st.2.length ≤ qBound
  bOk : ∀ Q : Party, BOkTight (st.1.st Q)
  sentB_deser : ∀ mc ∈ st.1.sentB,
    CryptoVerification.LibsignalSpqrV1.Message.deserialize
      CryptoVerification.LibsignalSpqrV1.spqrPolyApi mc.1.epoch
      (_root_.ReductionDsl.spqrMsgPayloadSuffix mc.1) = .ok mc.1

theorem ValidSimTrackInv.of_iff {τ : Type} {ℓ : ℕ}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ}
    {Inv₁ Inv₂ : ℕ → τ → Prop}
    (h1 : ValidSimTrackInv T Inv₁)
    (hiff : ∀ q st, Inv₁ q st ↔ Inv₂ q st) :
    ValidSimTrackInv T Inv₂ where
  init q kS := (hiff q _).mp (h1.init q kS)
  mono hle h := (hiff _ _).mp (h1.mono hle ((hiff _ _).mpr h))
  onSend := by
    intro q gs P coins st h
    have hp := h1.onSend gs P coins ((hiff q st).mpr h)
    exact ⟨(hiff (q + 1) _).mp hp.1, fun ct => (hiff (q + 1) _).mp (hp.2 ct)⟩
  onDeliver := by
    intro q gs Q w res st h
    exact (hiff q _).mp (h1.onDeliver gs Q w res ((hiff q st).mpr h))

theorem kemBridgeTrackInvLocal_mono {F : ShaCompress} {K : MlKem} {q₁ q₂ : ℕ}
    {st : KemFailSessionTrack F Bytes} (hq : q₁ ≤ q₂)
    (h : KemBridgeTrackInvLocal F K q₁ st) :
    KemBridgeTrackInvLocal F K q₂ st :=
  ⟨h.sentB_len.trans hq, h.wires_len.trans hq, h.bOk, h.sentB_deser⟩

theorem kemBridgeTrackInvLocal_init (F : ShaCompress) (K : MlKem) (qBound : ℕ)
    (pqrKey : BitVec 256) :
    KemBridgeTrackInvLocal F K qBound (initKemFailSessionTrack F Bytes pqrKey) := by
  refine ⟨Nat.zero_le qBound, Nat.zero_le qBound, ?_, ?_⟩
  · intro Q
    have hlen : (keyToBytes32 pqrKey).length = 32 := by simp [keyToBytes32]
    cases Q with
    | A =>
      obtain ⟨stA, hinitA, hbokA, -⟩ :=
        CryptoVerification.SpqrV1Sync.SendTotal.st_bInit_tight F (dir := .a2b) hlen
      change Except.ok ((initKemFailTrack F pqrKey).st .A) = Except.ok stA at hinitA
      cases hinitA; exact hbokA
    | B =>
      obtain ⟨stB, hinitB, hbokB, -⟩ :=
        CryptoVerification.SpqrV1Sync.SendTotal.st_bInit_tight F (dir := .b2a) hlen
      change CryptoVerification.LibsignalSpqrV1.States.init_b
        CryptoVerification.LibsignalSpqrV1.spqrPolyApi
        (CryptoVerification.LibsignalSpqrV1.spqrAuthApi F)
        (keyToBytes32 pqrKey) = Except.ok stB at hinitB
      simp only [CryptoVerification.LibsignalSpqrV1.States.init_b,
        CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived.new,
        CryptoVerification.LibsignalSpqrV1.HEADER_SIZE,
        CryptoVerification.LibsignalSpqrV1.AUTHENTICATOR_MACSIZE,
        CryptoVerification.LibsignalSpqrV1.spqrPolyApi,
        CryptoVerification.SpqrV1Sync.InSync.decoderNew_eq 96 (by decide),
        Except.mapError] at hinitB
      change Except.ok ((initKemFailTrack F pqrKey).st .B) = Except.ok stB at hinitB
      cases hinitB; exact hbokB
  · intro _ hmc; cases hmc

theorem kemBridgeTrackInvLocal_stepDeliver {F : ShaCompress} {K : MlKem} {L : ℕ}
    {st : KemFailSessionTrack F Bytes} (Q : Party) (j : ℕ)
    (hInv : KemBridgeTrackInvLocal F K L st) :
    KemBridgeTrackInvLocal F K L (stepKemFailDeliver F K st.1 Q j, st.2) := by
  unfold stepKemFailDeliver
  cases st.1.sentB[j]? with
  | none => exact hInv
  | some mc =>
    rcases mc with ⟨m, _⟩; dsimp only
    cases hrecv : (st.1.st Q).recv K m with
    | error _ => exact hInv
    | ok out =>
      rcases out with ⟨_, st'⟩
      have hbok' : ∀ Q' : Party, BOkTight (Function.update st.1.st Q st' Q') := by
        intro Q'
        by_cases hQ : Q' = Q
        · subst hQ; rw [Function.update_self]
          cases hek : CryptoVerification.SpqrV1Sync.SendTotal.isEkSide (st.1.st Q') with
          | true =>
            exact CryptoVerification.SpqrV1Sync.SendTotal.st_bRecvEk_tight F K hek (hInv.bOk Q') hrecv
          | false =>
            exact CryptoVerification.SpqrV1Sync.SendTotal.st_bRecvCt_tight F K hek (hInv.bOk Q') hrecv
        · rw [Function.update_of_ne hQ]; exact hInv.bOk Q'
      dsimp only
      split_ifs
      · cases st.1.c <;> exact ⟨hInv.sentB_len, hInv.wires_len, hbok', hInv.sentB_deser⟩
      · exact ⟨hInv.sentB_len, hInv.wires_len, hbok', hInv.sentB_deser⟩

theorem kemBridgeTrackInvLocal_stepSend {F : ShaCompress} {K : MlKem} {q : ℕ}
    {st : KemFailSessionTrack F Bytes} (Q : Party) (r : BitVec 512)
    (hInv : KemBridgeTrackInvLocal F K q st) :
    let tr' := stepKemFailSend F K st.1 Q r
    KemBridgeTrackInvLocal F K (q + 1) ({ st.1 with cand := tr'.cand }, st.2) ∧
      ∀ ct : Bytes, KemBridgeTrackInvLocal F K (q + 1) (tr', (ct, Q) :: st.2) := by
  refine ⟨⟨Nat.le_trans hInv.sentB_len (Nat.le_succ q),
    Nat.le_trans hInv.wires_len (Nat.le_succ q), hInv.bOk, hInv.sentB_deser⟩, fun ct => ?_⟩
  have hwires' : ((ct, Q) :: st.2).length ≤ q + 1 := Nat.succ_le_succ hInv.wires_len
  unfold stepKemFailSend; dsimp only
  cases hsend : (st.1.st Q).send K (coinBytes r) with
  | error _ =>
    exact ⟨Nat.le_trans hInv.sentB_len (Nat.le_succ q), hwires', hInv.bOk, hInv.sentB_deser⟩
  | ok p =>
    rcases p with ⟨⟨m, key, st'⟩, tape'⟩; dsimp only
    refine ⟨?_, hwires', ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton]
      exact Nat.add_le_add_right hInv.sentB_len 1
    · intro Q'; dsimp only
      by_cases hQ : Q' = Q
      · subst hQ; rw [Function.update_self]
        exact CryptoVerification.SpqrV1Sync.SendTotal.st_bSendClosed_tight F K (hInv.bOk Q') hsend
      · rw [Function.update_of_ne hQ]; exact hInv.bOk Q'
    · intro mc hmc
      rw [List.mem_append, List.mem_singleton] at hmc
      rcases hmc with hmc | rfl
      · exact hInv.sentB_deser mc hmc
      · dsimp only
        obtain ⟨-, -, hp, -⟩ :=
          CryptoVerification.SpqrV1Sync.TopSync.send_facts F K (st.1.st Q) st'
            (coinBytes r) tape' m key hsend
        obtain ⟨-, hsfx⟩ :=
          Computational.Proofs.E2E.Dsl.ClampsLossless.spqrMsgPayloadSuffix_lossless m
        have hsfxEq : _root_.ReductionDsl.spqrMsgPayloadSuffix m =
            (CryptoVerification.LibsignalSpqrV1.MessageType.from_payload m.payload).toU8 ::
              CryptoVerification.SpqrV1Sync.Codec.payloadBytes m.payload := by
          change CryptoVerification.E2E.Costed.spqrMsgPayloadSuffix m = _
          rw [hsfx]; rcases m with ⟨_, pay⟩
          unfold Computational.Proofs.E2E.Dsl.ClampsLossless.spqrMsgPayloadSuffixRaw
            CryptoVerification.SpqrV1Sync.Codec.payloadBytes
          cases pay <;> rfl
        rw [hsfxEq]
        have hdes := CryptoVerification.SpqrV1Sync.Codec.deserialize_payload
          CryptoVerification.LibsignalSpqrV1.spqrPolyApi
          CryptoVerification.SpqrV1Sync.Codec.spqrPolyApi_mkChunk m.epoch m.payload hp
        cases m; exact hdes

theorem kemBridgeTrackInvLocal_validSimTrackInv {ℓ : ℕ} (F : ShaCompress) (K : MlKem) :
    ValidSimTrackInv (kemFailSessionTracker (ℓ := ℓ) F K) (KemBridgeTrackInvLocal F K) where
  init q kS := kemBridgeTrackInvLocal_init F K q kS.2.2
  mono hle h := kemBridgeTrackInvLocal_mono hle h
  onSend := by
    intro _ _ P coins _ h
    exact kemBridgeTrackInvLocal_stepSend P coins h
  onDeliver := by
    intro _ _ Q w res st h
    dsimp only [kemFailSessionTracker]
    cases res with
    | none => exact h
    | some rr =>
      cases rr with
      | rejected => exact h
      | accepted _ _ _ =>
        cases List.findIdx? (fun wp : Bytes × Party => wp.1 == w && wp.2 == Q.other) st.2.reverse with
        | none => exact h
        | some j => exact kemBridgeTrackInvLocal_stepDeliver Q j h

/-! ## Local `KeyInd` invariant preservation -/

theorem kiStep_preserves {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {TrackInv : ℕ → τ → Prop}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {b : SignalPqxdh.QueryBudget} {qStart qDR qKiDone qStartDone qDrDone : ℕ}
    {σH : BHE2EDrvState S ℓ × List τ}
    (hInv : HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone qDrDone σH)
    (hKiNext : qKiDone + 1 ≤ b.q_total)
    (kq : SignalPqxdh.KeyIndQuery S)
    {out : BHTargetResp ℓ × BHE2EDrvState S ℓ}
    (hout : out ∈ support
      (bhShallowStepPreNonCtl P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K qep decT encT
        σH.1 (.inl (.inl kq)))) :
    HaltedSimInv TrackInv C K b qStart qDR (qKiDone + 1) qStartDone qDrDone (out.2, σH.2) ∧
      (∀ k, HaltedPausedInv k σH → HaltedPausedInv k (out.2, σH.2)) := by
  rcases σH with ⟨σ, tracks⟩
  dsimp only [bhShallowStepPreNonCtl] at hout
  have hpure : out ∈ support (pure (.inl (.inl .noneResp), σ) :
      ProbComp (BHTargetResp ℓ × BHE2EDrvState S ℓ)) →
      HaltedSimInv TrackInv C K b qStart qDR (qKiDone + 1) qStartDone qDrDone (out.2, tracks) ∧
        (∀ k, HaltedPausedInv k (σ, tracks) → HaltedPausedInv k (out.2, tracks)) := by
    simp only [support_pure, Set.mem_singleton_iff]
    rintro rfl
    exact ⟨{
      ki_le := hKiNext
      start_le := hInv.start_le
      dr_le := hInv.dr_le
      mirror := hInv.mirror.mono (Nat.le_succ _) (Nat.le_succ _) (Nat.le_succ _)
        (Nat.le_succ _) (Nat.le_succ _) (le_refl _)
      metaAligned := hInv.metaAligned
      sessions := hInv.sessions
      kiReach := hInv.kiReach.mono (Nat.le_succ _)
      tracks_len := hInv.tracks_len
      tracks_inv := hInv.tracks_inv
    }, fun _ hk => hk⟩
  split_ifs at hout with hok hprom
  · exact hpure hout
  · exact hpure hout
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    rcases hout with ⟨⟨kr, st'⟩, hstep, rfl⟩
    have ⟨hSet', hAdvLe, _⟩ :=
      pqxdhKeyIndImpl1KeyReal_preserves_setupBounded kq hInv.kiReach.setup hstep
    have hKi' : KeyIndReachBounded S (qKiDone + 1) st' :=
      ⟨hSet', hAdvLe.trans (Nat.add_le_add_right hInv.kiReach.advKeys_le 1)⟩
    have hMirSt : DrvQueryBounded qKiDone qStartDone { σ with st := st' } :=
      ⟨hInv.mirror.prins_le, hInv.mirror.bundles_le, hInv.mirror.opks_le,
       hInv.mirror.sends_le, hInv.mirror.corrPrins_le, hInv.mirror.insts_le,
       hInv.mirror.instMeta_le, hInv.mirror.revSpks_le⟩
    have hMir' : DrvQueryBounded (qKiDone + 1) qStartDone (bhE2EMirror { σ with st := st' } kq kr) :=
      DrvMirrorBounded.mirror hMirSt kq kr
    have hInstsEq : (bhE2EMirror { σ with st := st' } kq kr).insts = σ.insts := by
      cases kq <;> cases kr <;> rfl
    have hStEq : (bhE2EMirror { σ with st := st' } kq kr).st = st' := by
      cases kq <;> cases kr <;> rfl
    refine ⟨{
      ki_le := hKiNext
      start_le := hInv.start_le
      dr_le := hInv.dr_le
      mirror := hMir'
      metaAligned := drvMetaAligned_mirror hInv.metaAligned kq kr
      sessions := fun d hd gs0 hgs0 => by
        rw [hInstsEq] at hd
        exact hInv.sessions d hd gs0 hgs0
      kiReach := hStEq ▸ hKi'
      tracks_len := by dsimp only; rw [hInstsEq]; exact hInv.tracks_len
      tracks_inv := hInv.tracks_inv
    }, fun k ⟨hkLt, hkNone⟩ => ⟨by dsimp only; rw [hInstsEq]; exact hkLt, fun d hd => by
        dsimp only at hd; rw [hInstsEq] at hd; exact hkNone d hd⟩⟩

/-! ## Verified subprogram bundles and boundedness -/

@[expose] def haltedPrefixTightStepCost
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) : ℕ :=
  max (max (subs.kiStepCost b)
      (subs.localStartHaltedCost b qStart + subs.promoteSlotKCost qStart))
    (max (subs.extSmStepCost b qStart)
      (subs.haltedStepLocalSmCost b qStart qDR qep)) +
    2 * min qStart (min b.q_total S.N_send_tot) + 184

private theorem prefixHandlePreHalted_cost_le_tight
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) {k : ℕ}
    (hk_inst : k ≤ min qStart (min b.q_total S.N_send_tot)) :
    (prefixHandlePreHalted subs b qStart qDR qep k).cost + 64 ≤
      haltedPrefixTightStepCost subs b qStart qDR qep := by
  have hbits : bits k ≤ min qStart (min b.q_total S.N_send_tot) + 1 :=
    le_trans (CryptoVerification.E2E.Costed.bits_le_self_add_one k) (Nat.add_le_add_right hk_inst 1)
  have hki := prefixKiStepHaltedC_cost subs b
    (Γ := [keyIndQT (ℓ := ℓ) (Pt := Pt) S,
      Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
      drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]) .v2 .v0
  have hloc := subs.localStartHaltedC_cost b qStart true
    (Γ := [sidT (ℓ := ℓ) (Pt := Pt) S,
      Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
      drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]) .v2 .v0
  have hprom := subs.promoteSlotKC_cost qStart
    (Γ := [Ty.prod (.opt .nat) (drvHaltedTy subs), sidT (ℓ := ℓ) (Pt := Pt) S,
      Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
      drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q])
    (.nat k) (.fst .v0) (.fst (.snd .v0))
  have hsm := subs.haltedStepLocalSmC_cost b qStart qDR qep
    (Γ := [Ty.prod .nat (smQT (ℓ := ℓ) (Pt := Pt)), drvHaltedTy subs,
      (e2eTargetGameCodec S ℓ Pt).Q]) .v1 (.fst .v0) (.snd .v0)
  dsimp only [prefixHandlePreHalted, haltedPrefixTightStepCost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2] at *
  omega

private theorem prefixHandlePostHalted_cost_le_tight
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) {k : ℕ}
    (hk_inst : k ≤ min qStart (min b.q_total S.N_send_tot)) :
    (prefixHandlePostHalted subs b qStart qDR qep k).cost + 64 ≤
      haltedPrefixTightStepCost subs b qStart qDR qep := by
  have hbits : bits k ≤ min qStart (min b.q_total S.N_send_tot) + 1 :=
    le_trans (CryptoVerification.E2E.Costed.bits_le_self_add_one k) (Nat.add_le_add_right hk_inst 1)
  have hki := prefixKiStepHaltedC_cost subs b
    (Γ := [keyIndQT (ℓ := ℓ) (Pt := Pt) S,
      Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
      drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]) .v2 .v0
  have hloc := subs.localStartHaltedC_cost b qStart false
    (Γ := [sidT (ℓ := ℓ) (Pt := Pt) S,
      Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
      drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]) .v2 .v0
  have hext := subs.extSmStepC_cost b qStart
    (Γ := [Ty.prod .nat (smQT (ℓ := ℓ) (Pt := Pt)), drvHaltedTy subs,
      (e2eTargetGameCodec S ℓ Pt).Q]) (.nat k) (.fst .v1) (.snd .v0)
  have hsm := subs.haltedStepLocalSmC_cost b qStart qDR qep
    (Γ := [Ty.prod .nat (smQT (ℓ := ℓ) (Pt := Pt)), drvHaltedTy subs,
      (e2eTargetGameCodec S ℓ Pt).Q]) .v1 (.fst .v0) (.snd .v0)
  dsimp only [prefixHandlePostHalted, haltedPrefixTightStepCost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2] at *
  omega

theorem prefixRedHalted_totalCost_le_tight
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep qTot : ℕ) {k : ℕ}
    (hk_inst : k ≤ min qStart (min b.q_total S.N_send_tot)) :
    (prefixRedHalted subs b qStart qDR qep k).totalCost qTot ≤
      haltedPrefixEndpointCost subs b qStart +
        qTot * haltedPrefixTightStepCost subs b qStart qDR qep := by
  have hempty := subs.emptyDrvStateE_cost (Γ := [.unit]) (.bool false)
  have hch := subs.defaultPrefixCtxE_cost (Γ := [drvHaltedTy subs, .bool])
  have hres := subs.drvSetBitE_cost (Γ := [drvHaltedTy subs, .opt .nat, .bool]) (.fst .v0) .v2
  have hfin := subs.finishPrefixC_cost b qStart
    (Γ := [drvHaltedTy subs, .bool, .bool]) (.fst .v0) .v1 .v2
  have hpre := prefixHandlePreHalted_cost_le_tight subs b qStart qDR qep hk_inst
  have hpost := prefixHandlePostHalted_cost_le_tight subs b qStart qDR qep hk_inst
  have hcc : (e2eTargetGameCodec S ℓ Pt).codecCost ≤ 64 := by
    dsimp [e2eTargetGameCodec, _root_.ReductionDsl.e2eGameCodec]; omega
  have hstep :
      max 1 (max (prefixHandlePreHalted subs b qStart qDR qep k).cost
          (prefixHandlePostHalted subs b qStart qDR qep k).cost +
          (e2eTargetGameCodec S ℓ Pt).codecCost) ≤
        haltedPrefixTightStepCost subs b qStart qDR qep := by
    have hpos : 1 ≤ haltedPrefixTightStepCost subs b qStart qDR qep := by
      unfold haltedPrefixTightStepCost; omega
    omega
  have hmul :
      qTot * max 1 (max (prefixHandlePreHalted subs b qStart qDR qep k).cost
          (prefixHandlePostHalted subs b qStart qDR qep k).cost +
          (e2eTargetGameCodec S ℓ Pt).codecCost) ≤
        qTot * haltedPrefixTightStepCost subs b qStart qDR qep :=
    Nat.mul_le_mul_left qTot hstep
  rw [TwoStageCostedReduction.totalCost]
  have hu : (e2eSessionTargetIface ℓ Pt).uCost = 1 := rfl
  rw [hu]
  dsimp only [prefixRedHalted, haltedPrefixEndpointCost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2] at hempty hch hres hfin hmul ⊢
  omega

/-- Evaluation and budget bounds for a `HaltedPrefixSubprograms` bundle against tracker `T`. -/
structure ValidHaltedPrefixSubprograms
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey SessH)
    (TrackInv : ℕ → SessH → Prop)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) : Prop where
  track_valid : ValidSimTrackInv T TrackInv
  endpointCost_le :
    haltedPrefixEndpointCost subs b qStart ≤
      2 ^ 10 * e2ePerStepWeightedFactor S b qStart qInst qep ℓ +
        2 ^ 13 * min qStart (min b.q_total S.N_send_tot) * e2eFreshScanInnerFactor S b
  stepCost_le :
    haltedPrefixTightStepCost subs b qStart qInst qep ≤
      2 ^ 10 * e2ePerStepWeightedFactor S b qStart qInst qep ℓ
  sizeBound_le :
    ∀ qDR : ℕ, ∃ C₀ C₁, C₀ ≤ 2 ^ 22 ∧ C₁ ≤ 2 ^ 11 ∧
      haltedPrefixSizeBound subs b qStart qInst qep ≤
        C₀ + C₁ * bits (bhE2ECostBudget S b qStart qDR qInst qep ℓ)
  kiStepC_eval :
    SignalPqxdh.WellFormedPrimitivesδ P →
    ∀ {qDR qKiDone qStartDone qDrDone : ℕ} {σH : BHE2EDrvState S ℓ × List SessH},
      HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone qDrDone σH →
      qKiDone + 1 ≤ b.q_total →
      ∀ {Γ} (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ subs.drvTy)
        (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
        (ρ : Env Γ) (kq : SignalPqxdh.KeyIndQuery S),
        σE.eval ρ = subs.drvEnc σH.1 →
        kqE.eval ρ = keyIndQenc kq →
        (subs.kiStepC b σE kqE).eval ρ =
          (e2eSessionTargetIface ℓ Pt).liftP
            ((fun out => (atomicGameRespEnc out.1, subs.drvEnc out.2)) <$>
              bhShallowStepPreNonCtl P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
                C K qep decT encT σH.1 (.inl (.inl kq)))
  localStartHaltedC_eval :
    SignalPqxdh.WellFormedPrimitivesδ P →
    ∀ (bm : Bool) {qDR qKiDone qStartDone qDrDone : ℕ} {σH : BHE2EDrvState S ℓ × List SessH},
      HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone qDrDone σH →
      qStartDone + 1 ≤ qStart →
      ∀ {Γ} (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvHaltedTy subs))
        (sidE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S))
        (ρ : Env Γ) (sid : SignalPqxdh.SessionId S),
        σHE.eval ρ = drvHaltedEnc subs σH →
        sidE.eval ρ = sidV sid →
        (subs.localStartHaltedC b qStart bm σHE sidE).eval ρ =
          (e2eSessionTargetIface ℓ Pt).liftP
            ((fun out => (out.1, drvHaltedEnc subs out.2)) <$>
              bhE2ELocalStartSessionTracked T.init (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
                C K (some bm) σH sid)
  promoteSlotKC_eval :
    ∀ {qDR qKiDone qStartDone qDrDone : ℕ} {σH : BHE2EDrvState S ℓ × List SessH},
      HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone qDrDone σH →
      ∀ {Γ} (kE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
        (idxOptE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.opt .nat))
        (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ subs.drvTy)
        (ρ : Env Γ) (k : ℕ) (idx? : Option ℕ),
        k < qStart →
        kE.eval ρ = k →
        idxOptE.eval ρ = idx? →
        σE.eval ρ = subs.drvEnc σH.1 →
        (subs.promoteSlotKC qStart kE idxOptE σE).eval ρ =
          match bhPromoteSlotK k idx? σH.1 with
          | .inl ans => pure (.inl (ans.1, subs.drvEnc ans.2))
          | .inr (ctx, p, σ_p) => pure (.inr (atomicPrefixCtxEnc ctx, (p, subs.drvEnc σ_p)))
  extSmStepC_eval :
    ∀ {qDR qKiDone qStartDone qDrDone k : ℕ} {σH : BHE2EDrvState S ℓ × List SessH},
      HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone qDrDone σH →
      HaltedPausedInv k σH →
      qDrDone + 1 ≤ qDR →
      ∀ {Γ} (kE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
        (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ subs.drvTy)
        (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt)))
        (ρ : Env Γ)
        (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain),
        k < qStart →
        kE.eval ρ = k →
        σE.eval ρ = subs.drvEnc σH.1 →
        sqE.eval ρ = smQenc sq →
        (subs.extSmStepC b qStart kE σE sqE).eval ρ =
          ((fun out => (packAtomicSmRespEnc out.1, subs.drvEnc out.2)) <$>
            bhExtSmStep k σH.1 sq)
  haltedStepLocalSmC_eval :
    ∀ {qDR qKiDone qStartDone qDrDone : ℕ} {σH : BHE2EDrvState S ℓ × List SessH},
      HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone qDrDone σH →
      qDrDone + 1 ≤ qDR →
      ∀ {Γ} (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvHaltedTy subs))
        (idxE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
        (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt)))
        (ρ : Env Γ) (i : ℕ)
        (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain),
        σHE.eval ρ = drvHaltedEnc subs σH →
        idxE.eval ρ = i →
        sqE.eval ρ = smQenc sq →
        (subs.haltedStepLocalSmC b qStart qInst qep σHE idxE sqE).eval ρ =
          (e2eSessionTargetIface ℓ Pt).liftP
            ((fun out => (packAtomicSmRespEnc out.1, drvHaltedEnc subs out.2)) <$>
              bhE2EStepLocalSmSessionTracked T C K qep decT encT σH i sq)
  finishPrefixC_eval :
    SignalPqxdh.WellFormedPrimitivesδ P →
    ∀ {qDR qKiDone qStartDone qDrDone : ℕ} {σH : BHE2EDrvState S ℓ × List SessH},
      HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone qDrDone σH →
      ∀ {Γ} (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ subs.drvTy)
        (bOutE flipE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool)
        (ρ : Env Γ) (bOut flip : Bool),
        σE.eval ρ = subs.drvEnc σH.1 →
        bOutE.eval ρ = bOut →
        flipE.eval ρ = flip →
        (subs.finishPrefixC b qStart σE bOutE flipE).eval ρ =
          (e2eSessionTargetIface ℓ Pt).liftP
            (bhShallowFinishPrefix P σH.1 bOut flip)

theorem prefixRedHalted_gRed2Bounded_of_bounds
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    {b : SignalPqxdh.QueryBudget} {qStart qDR qInst qep k : ℕ}
    (hEnd : haltedPrefixEndpointCost subs b qStart ≤
      2 ^ 10 * e2ePerStepWeightedFactor S b qStart qInst qep ℓ +
        2 ^ 13 * min qStart (min b.q_total S.N_send_tot) * e2eFreshScanInnerFactor S b)
    (hStep : haltedPrefixTightStepCost subs b qStart qInst qep ≤
      2 ^ 10 * e2ePerStepWeightedFactor S b qStart qInst qep ℓ)
    (hSize : ∀ qDR' : ℕ, ∃ C₀ C₁, C₀ ≤ 2 ^ 22 ∧ C₁ ≤ 2 ^ 11 ∧
      haltedPrefixSizeBound subs b qStart qInst qep ≤
        C₀ + C₁ * bits (bhE2ECostBudget S b qStart qDR' qInst qep ℓ))
    (hk : k < qStart) (hk_inst : k ≤ min qStart (min b.q_total S.N_send_tot)) :
    let qTot := b.q_total + qStart + qDR
    GRed2Bounded (prefixRedHalted subs b qStart qInst qep k)
      (fun _ => 1) (fun _ => 0) qTot qTot (bhE2ECostBudget S b qStart qDR qInst qep ℓ) false := by
  dsimp only; rcases hSize qDR with ⟨C₀, C₁, hC₀, hC₁, hSz⟩
  exact gRed2Bounded_atomic_of_bounds (prefixRedHalted subs b qStart qInst qep k)
    (b.q_total + qStart + qDR) (b.q_total + qStart + qDR)
    (bhE2ECostBudget S b qStart qDR qInst qep ℓ) false
    (le_trans (prefixRedHalted_totalCost_le_tight subs b qStart qInst qep
        (b.q_total + qStart + qDR) hk_inst)
      (totalCost_le_bhE2ECostBudget_of_step_endpoint S b qStart qDR qInst qep ℓ
        (b.q_total + qStart + qDR) _ _ (le_refl _) hEnd hStep))
    (prefixRedHalted_size_le_budget subs b qStart qInst qep
      (bhE2ECostBudget S b qStart qDR qInst qep ℓ) C₀ C₁ hk hC₀ hC₁ hSz)
    (prefixRedHalted_stage1Queries subs b qStart qInst qep k)
    (prefixRedHalted_totalQueries_le subs b qStart qInst qep k (b.q_total + qStart + qDR))

theorem prefixRedHalted_gRed2Bounded_of_valid
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    {subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey SessH}
    {TrackInv : ℕ → SessH → Prop} {b : SignalPqxdh.QueryBudget} {qStart qDR qInst qep k : ℕ}
    (hValid : ValidHaltedPrefixSubprograms subs T TrackInv b qStart qInst qep)
    (hk : k < qStart) (hk_inst : k ≤ min qStart (min b.q_total S.N_send_tot)) :
    let qTot := b.q_total + qStart + qDR
    GRed2Bounded (prefixRedHalted subs b qStart qInst qep k)
      (fun _ => 1) (fun _ => 0) qTot qTot (bhE2ECostBudget S b qStart qDR qInst qep ℓ) false :=
  prefixRedHalted_gRed2Bounded_of_bounds subs
    hValid.endpointCost_le hValid.stepCost_le hValid.sizeBound_le hk hk_inst

/-- Per-instance clamped evaluation and budget bounds for a `HaltedPrefixSubprograms` bundle. -/
structure ValidHaltedPrefixSubprogramsInst
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey SessH)
    (TrackInv : ℕ → SessH → Prop) (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) : Prop where
  track_valid : ValidSimTrackInv T TrackInv
  endpointCost_le : haltedPrefixEndpointCost subs b qStart ≤
    2 ^ 10 * e2ePerStepWeightedFactor S b qStart qInst qep ℓ +
      2 ^ 13 * min qStart (min b.q_total S.N_send_tot) * e2eFreshScanInnerFactor S b
  stepCost_le : haltedPrefixTightStepCost subs b qStart qInst qep ≤
    2 ^ 10 * e2ePerStepWeightedFactor S b qStart qInst qep ℓ
  sizeBound_le : ∀ qDR : ℕ, ∃ C₀ C₁, C₀ ≤ 2 ^ 22 ∧ C₁ ≤ 2 ^ 11 ∧
    haltedPrefixSizeBound subs b qStart qInst qep ≤
      C₀ + C₁ * bits (bhE2ECostBudget S b qStart qDR qInst qep ℓ)
  kiStepC_eval : SignalPqxdh.WellFormedPrimitivesδ P → ∀ {σH : BHE2EDrvState S ℓ × List SessH},
    σH.1.prins.length ≤ b.q_total →
    σH.1.instMeta.length ≤ min qStart (min b.q_total S.N_send_tot) →
    PqxdhSimTypes.stListBounded S b.q_total σH.1.st →
    ∀ {Γ} (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ subs.drvTy)
      (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
      (ρ : Env Γ) (kq : SignalPqxdh.KeyIndQuery S),
      σE.eval ρ = subs.drvEnc σH.1 → kqE.eval ρ = keyIndQenc kq →
      (subs.kiStepC b σE kqE).eval ρ = (e2eSessionTargetIface ℓ Pt).liftP
        ((fun out => (atomicGameRespEnc out.1, subs.drvEnc out.2)) <$>
          bhShallowStepPreNonCtl P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
            C K qep decT encT σH.1 (.inl (.inl kq)))
  localStartHaltedC_eval : ∀ (bm : Bool) {σH : BHE2EDrvState S ℓ × List SessH},
    DrvMirrorBounded b.q_total (min b.q_total S.N_spk_tot) b.q_total b.q_total b.q_total
      (min qStart (min b.q_total S.N_send_tot)) σH.1 →
    PqxdhSimTypes.stListBounded S b.q_total σH.1.st →
    σH.2.length ≤ min qStart (min b.q_total S.N_send_tot) →
    ∀ {Γ} (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvHaltedTy subs))
      (sidE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S))
      (ρ : Env Γ) (sid : SignalPqxdh.SessionId S),
      σHE.eval ρ = drvHaltedEnc subs σH → sidE.eval ρ = sidV sid →
      (subs.localStartHaltedC b qStart bm σHE sidE).eval ρ = (e2eSessionTargetIface ℓ Pt).liftP
        ((fun out => (out.1, drvHaltedEnc subs out.2)) <$>
          bhE2ELocalStartSessionTracked T.init (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
            C K (some bm) σH sid)
  promoteSlotKC_eval : ∀ {σH : BHE2EDrvState S ℓ × List SessH},
    σH.1.insts.length ≤ min qStart (min b.q_total S.N_send_tot) →
    ∀ {Γ} (kE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
      (idxOptE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.opt .nat))
      (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ subs.drvTy) (ρ : Env Γ) (k : ℕ) (idx? : Option ℕ),
      k < min qStart (min b.q_total S.N_send_tot) →
      kE.eval ρ = k → idxOptE.eval ρ = idx? → σE.eval ρ = subs.drvEnc σH.1 →
      (subs.promoteSlotKC qStart kE idxOptE σE).eval ρ =
        match bhPromoteSlotK k idx? σH.1 with
        | .inl ans => pure (.inl (ans.1, subs.drvEnc ans.2))
        | .inr (ctx, p, σ_p) => pure (.inr (atomicPrefixCtxEnc ctx, (p, subs.drvEnc σ_p)))
  extSmStepC_eval : ∀ {k : ℕ} {σH : BHE2EDrvState S ℓ × List SessH},
    DrvQueryBounded b.q_total (min qStart (min b.q_total S.N_send_tot)) σH.1 →
    DrvMetaAligned σH.1 → HaltedPausedInv k σH →
    ∀ {Γ} (kE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
      (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ subs.drvTy)
      (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ)
      (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain),
      k < min qStart (min b.q_total S.N_send_tot) →
      kE.eval ρ = k → σE.eval ρ = subs.drvEnc σH.1 → sqE.eval ρ = smQenc sq →
      (subs.extSmStepC b qStart kE σE sqE).eval ρ =
        ((fun out => (packAtomicSmRespEnc out.1, subs.drvEnc out.2)) <$> bhExtSmStep k σH.1 sq)
  haltedStepLocalSmC_eval : ∀ {σH : BHE2EDrvState S ℓ × List SessH},
    σH.1.insts.length ≤ min qStart (min b.q_total S.N_send_tot) → DrvMetaAligned σH.1 →
    σH.1.corrPrins.length ≤ b.q_total → σH.1.revealedSpks.length ≤ b.q_total →
    σH.1.prins.length ≤ b.q_total → DrvSessionsBounded C K qInst σH.1 →
    (∀ d ∈ σH.1.insts, ∀ gs ∈ d.gs,
      Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp.SmEpochBounded qInst gs) →
    σH.2.length ≤ min qStart (min b.q_total S.N_send_tot) → (∀ st ∈ σH.2, TrackInv qInst st) →
    ∀ {Γ} (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvHaltedTy subs))
      (idxE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
      (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt)))
      (ρ : Env Γ) (i : ℕ)
      (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain),
      σHE.eval ρ = drvHaltedEnc subs σH → idxE.eval ρ = i → sqE.eval ρ = smQenc sq →
      (subs.haltedStepLocalSmC b qStart qInst qep σHE idxE sqE).eval ρ =
        (e2eSessionTargetIface ℓ Pt).liftP
          ((fun out => (packAtomicSmRespEnc out.1, drvHaltedEnc subs out.2)) <$>
            bhE2EStepLocalSmSessionTracked T C K qep decT encT σH i sq)
  finishPrefixC_eval : SignalPqxdh.WellFormedPrimitivesδ P → ∀ {σH : BHE2EDrvState S ℓ × List SessH},
    σH.1.insts.length ≤ min qStart (min b.q_total S.N_send_tot) →
    (σH.1.st.sessions.filter (·.tested)).length ≤ min qStart (min b.q_total S.N_send_tot) →
    (∀ r ∈ σH.1.st.respSessions, r.tested = false) →
    PqxdhSimTypes.stListBounded S b.q_total σH.1.st →
    ∀ {Γ} (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ subs.drvTy)
      (bOutE flipE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool)
      (ρ : Env Γ) (bOut flip : Bool),
      σE.eval ρ = subs.drvEnc σH.1 → bOutE.eval ρ = bOut → flipE.eval ρ = flip →
      (subs.finishPrefixC b qStart σE bOutE flipE).eval ρ =
        (e2eSessionTargetIface ℓ Pt).liftP (bhShallowFinishPrefix P σH.1 bOut flip)

theorem prefixRedHalted_gRed2Bounded_of_valid_inst
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    {subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey SessH}
    {TrackInv : ℕ → SessH → Prop} {b : SignalPqxdh.QueryBudget} {qStart qDR qInst qep k : ℕ}
    (hValid : ValidHaltedPrefixSubprogramsInst subs T TrackInv b qStart qInst qep)
    (hk : k < qStart) (hk_inst : k ≤ min qStart (min b.q_total S.N_send_tot)) :
    let qTot := b.q_total + qStart + qDR
    GRed2Bounded (prefixRedHalted subs b qStart qInst qep k)
      (fun _ => 1) (fun _ => 0) qTot qTot (bhE2ECostBudget S b qStart qDR qInst qep ℓ) false :=
  prefixRedHalted_gRed2Bounded_of_bounds subs
    hValid.endpointCost_le hValid.stepCost_le hValid.sizeBound_le hk hk_inst

theorem prefixRedHalted_makesAtMostQueries_of_inst
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep qTot k qsK : ℕ)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hInst : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun i => i == k) q = true)
      qsK)
    (o : (prefixCtxT (ℓ := ℓ) (Pt := Pt)).denote ×
      Mid (bhTargetGameSpec S ℓ (BitVec 512)) Bool
        (Option ℕ) (drvHaltedTy subs).denote (prefixCtxT (ℓ := ℓ) (Pt := Pt)).denote)
    (ho : o ∈ support (stageOneAsProbComp
      ((prefixRedHalted subs b qStart qDR qep k).eval1 (fun _ => B_A) () qTot false)))
    (flip : Bool) :
    MakesAtMostQueries
      ((prefixRedHalted subs b qStart qDR qep k).eval2 o.2 flip qTot false) qsK :=
  prefixRedHalted_makesAtMostQueries subs b qStart qDR qep qTot k qsK B_A hInst o ho flip

/-! ## Two-stage simulation equivalence -/

private theorem atomicLiftP_pure {ℓ : ℕ} {Pt α : Type} (x : α) :
    (e2eSessionTargetIface ℓ Pt).liftP (pure x) = pure x := by
  simp

private theorem atomicLiftP_bind {ℓ : ℕ} {Pt α β : Type} (p : ProbComp α) (f : α → ProbComp β) :
    (e2eSessionTargetIface ℓ Pt).liftP (p >>= f) =
      ((e2eSessionTargetIface ℓ Pt).liftP p >>= fun a => (e2eSessionTargetIface ℓ Pt).liftP (f a)) := by
  simp [PrefixRedHaltedEval.atomicSessionTargetIface_liftP_eq_bhLiftP, bhLiftP]

private theorem atomicLiftP_map {ℓ : ℕ} {Pt α β : Type} (f : α → β) (p : ProbComp α) :
    (e2eSessionTargetIface ℓ Pt).liftP (f <$> p) =
      f <$> (e2eSessionTargetIface ℓ Pt).liftP p := by
  simp [PrefixRedHaltedEval.atomicSessionTargetIface_liftP_eq_bhLiftP, bhLiftP]

private theorem prefixKiStepHaltedC_eval_eq
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    {subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey SessH}
    {TrackInv : ℕ → SessH → Prop}
    {b : SignalPqxdh.QueryBudget} {qStart qDR qInst qep : ℕ}
    (hValid : ValidHaltedPrefixSubprograms subs T TrackInv b qStart qInst qep)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {qKiDone qStartDone qDrDone : ℕ} {σH : BHE2EDrvState S ℓ × List SessH}
    (hInv : HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone qDrDone σH)
    (hKiNext : qKiDone + 1 ≤ b.q_total)
    {Γ : List (_root_.ReductionDsl.Ty (_root_.ReductionDsl.atomicSig ℓ Pt))}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvHaltedTy subs))
    (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
    (ρ : Env Γ) (kq : SignalPqxdh.KeyIndQuery S)
    (hσH : σHE.eval ρ = drvHaltedEnc subs σH)
    (hkq : kqE.eval ρ = keyIndQenc kq) :
    (prefixKiStepHaltedC subs b σHE kqE).eval ρ =
      (e2eSessionTargetIface ℓ Pt).liftP
        ((fun out => (atomicGameRespEnc out.1, drvHaltedEnc subs (out.2, σH.2))) <$>
          bhShallowStepPreNonCtl P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
            C K qep decT encT σH.1 (.inl (.inl kq))) := by
  dsimp only [prefixKiStepHaltedC, Comp.eval]
  rw [pure_bind]
  let ρ1 : Env (_root_.ReductionDsl.Ty.prod (drvHaltedTy subs) (keyIndQT (ℓ := ℓ) (Pt := Pt) S) :: Γ) :=
    .cons ((Expr.pair σHE kqE).eval ρ) ρ
  have h1 : (subs.kiStepC b (.fst (.fst .v0)) (.snd .v0)).eval ρ1 = _ :=
    hValid.kiStepC_eval hP hInv hKiNext (.fst (.fst .v0)) (.snd .v0) ρ1 kq
      (by simp [ρ1, Expr.eval, Expr.v0, hσH, drvHaltedEnc])
      (by simp [ρ1, Expr.eval, Expr.v0, hkq])
  change ((subs.kiStepC b (.fst (.fst .v0)) (.snd .v0)).eval ρ1 >>= _) = _
  rw [h1, atomicLiftP_map, bind_map_left, atomicLiftP_map]
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  exact bind_congr fun ⟨_, _⟩ => by simp [Expr.eval, Expr.v0, Expr.v1, hσH, drvHaltedEnc]

private theorem bhFilterSmQuery_isBobRecv {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {d : BHModelInst S ℓ} {im : ModelDriverInstanceMeta S}
    {sq sq' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain}
    (hf : bhFilterSmQuery d im sq = some sq') :
    bhIsBobRecvSMQuery sq' = bhIsBobRecvSMQuery sq := by
  unfold bhFilterSmQuery at hf
  rcases sq with (((qTr | qCh) | ⟨pDl, cDl⟩) | ⟨pIj, cIj⟩) | qCr
  · simp only [Option.some.injEq] at hf; subst hf; rfl
  · simp only [Option.some.injEq] at hf; subst hf; rfl
  · cases pDl
    · dsimp only at hf; split_ifs at hf; simp only [Option.some.injEq] at hf; subst hf; rfl
    · dsimp only at hf; split_ifs at hf
      · cases hdec : CryptoVerification.E2E.bhDecodePreKeyMsgE cDl <;> rw [hdec] at hf
        · cases hf
        · dsimp only at hf; split_ifs at hf; simp only [Option.some.injEq] at hf; subst hf; rfl
      · cases hdec : CryptoVerification.E2E.bhDecodePreKeyMsgE cDl <;> rw [hdec] at hf
        · simp only [Option.some.injEq] at hf; subst hf; rfl
        · dsimp only at hf; split_ifs at hf; simp only [Option.some.injEq] at hf; subst hf; rfl
  · cases pIj
    · dsimp only at hf; split_ifs at hf; simp only [Option.some.injEq] at hf; subst hf; rfl
    · dsimp only at hf; split_ifs at hf
      · cases hdec : CryptoVerification.E2E.bhDecodePreKeyMsgE cIj <;> rw [hdec] at hf
        · simp only [Option.some.injEq] at hf; subst hf; rfl
        · dsimp only at hf; split_ifs at hf; simp only [Option.some.injEq] at hf; subst hf; rfl
  · simp only [Option.some.injEq] at hf; subst hf; rfl

private theorem checkExtSm_eq_of_filter {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {k : ℕ} {σ : BHE2EDrvState S ℓ}
    {d : BHModelInst S ℓ} {im : ModelDriverInstanceMeta S}
    (hcl : (!bhE2EDrvInstClean σ k) = false)
    (hd : σ.insts[k]? = some d)
    (him : σ.instMeta[k]? = some im)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (hcorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = false) :
    bhShallowCheckExtSm k σ k sq =
      match bhFilterSmQuery d im sq with
      | none => .inl (.inr (none, none, none))
      | some sq' => .inr sq' := by
  dsimp only [bhShallowCheckExtSm]
  have hneq : (k != k) = false := by simp
  rw [hneq, Bool.false_or, hcl]
  simp only [Bool.false_eq_true, ↓reduceIte, hd, him, hcorr]
  unfold bhFilterSmQuery
  rcases sq with (((qTr | qCh) | ⟨pDl, cDl⟩) | ⟨pIj, cIj⟩) | qCr
  · rfl
  · rfl
  · cases pDl
    · dsimp only; split_ifs <;> rfl
    · cases im.bobAccepted
      · dsimp only [Bool.not_false, ↓reduceIte]
        rcases CryptoVerification.E2E.bhDecodePreKeyMsgE cDl with _ | _
        · rfl
        · dsimp only; split_ifs <;> rfl
      · dsimp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rcases CryptoVerification.E2E.bhDecodePreKeyMsgE cDl with _ | _
        · rfl
        · dsimp only; split_ifs <;> rfl
  · cases pIj
    · dsimp only; split_ifs <;> rfl
    · cases im.bobAccepted
      · rfl
      · dsimp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rcases CryptoVerification.E2E.bhDecodePreKeyMsgE cIj with _ | _
        · rfl
        · dsimp only; split_ifs <;> rfl
  · rfl

@[expose] def prefixRedHalted_twoStageSimSpec
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    {subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey SessH}
    {TrackInv : ℕ → SessH → Prop}
    {b : SignalPqxdh.QueryBudget} {qStart qDR qInst qep k : ℕ}
    (hValid : ValidHaltedPrefixSubprograms subs T TrackInv b qStart qInst qep)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (hk : k < qStart) :
    TwoStageAtomicSimSpec S Pt ℓ (atomicE2EOps ℓ P C K decT encT) b qStart qDR
      (BHE2EDrvState S ℓ × List SessH) (Option ℕ) where
  R := prefixRedHalted subs b qStart qInst qep k
  R_ref := bhPrefixRedWithHalted S ℓ P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
    C K qep decT encT
    (fun bm σH sid =>
      bhE2ELocalStartSessionTracked T.init (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
        C K (some bm) σH sid)
    (bhE2EStepLocalSmSessionTracked T C K qep decT encT) k
  drvEnc := drvHaltedEnc subs
  πEnc := id
  σ0 := ({}, [])
  Inv := HaltedSimInv TrackInv C K b qStart qDR
  PausedInv := HaltedPausedInv k
  qenc_eq _ := rfl
  rdec_eq _ _ := rfl
  stage1_queries_zero := prefixRedHalted_stage1Queries subs b qStart qInst qep k
  init_inv := HaltedSimInv.empty TrackInv C K b qStart qDR false
  init_costed := by
    dsimp only [prefixRedHalted, Comp.eval, Expr.eval, drvHaltedEnc]
    rw [subs.emptyDrvStateE_eval]
    rfl
  init_ref := rfl
  chDone_eq _ _ := by
    dsimp only [prefixRedHalted, bhPrefixRedWithHalted, Comp.eval]
    rw [subs.defaultPrefixCtxE_eval]
    rfl
  resume_eq {_ _ _ σ_p} _ _ p flip := by
    dsimp only [prefixRedHalted, bhPrefixRedWithHalted, Comp.eval, Expr.eval]
    rw [subs.drvSetBitE_eval (.fst .v0) .v2 _ σ_p.1 (by simp [Expr.eval, Expr.v0, drvHaltedEnc])]
    rfl
  resume_inv {_ _ _ σ_p} hInv hPaused p flip rs hrs := by
    dsimp only [bhPrefixRedWithHalted] at hrs
    simp only [support_pure, Set.mem_singleton_iff] at hrs
    subst hrs
    exact ⟨hInv.setBit flip, hPaused⟩
  stepPre_eq {qKiDone qStartDone qDrDone σH} hInv t hBud := by
    rcases t with (kq | cq) | ⟨i, sq⟩
    · dsimp only [prefixRedHalted, bhPrefixRedWithHalted, e2eTargetGameCodec]
      rw [prefixHandlePreHalted_eval_ki]
      dsimp only [bhPrefixHandlePreWithHalted, bhShallowStepPreNonCtlHalted, bhTargetQenc]
      let ρ_ki : Env [keyIndQT (ℓ := ℓ) (Pt := Pt) S,
          _root_.ReductionDsl.Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
          drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q] :=
        .cons (keyIndQenc kq) (.cons (.inl (keyIndQenc kq))
          (.cons (drvHaltedEnc subs σH) (.cons (.inl (.inl (keyIndQenc kq))) .nil)))
      rw [prefixKiStepHaltedC_eval_eq hValid hP hInv hBud .v2 .v0 ρ_ki kq rfl rfl]
      rw [atomicLiftP_map, bind_map_left]
      simp only [PrefixRedHaltedEval.atomicSessionTargetIface_liftP_eq_bhLiftP,
        bhLiftP, simulateQ_bind, simulateQ_pure, map_bind, map_pure, bind_assoc, pure_bind,
        mapPreEnc]
    · rcases cq with ⟨sid⟩
      dsimp only [prefixRedHalted, bhPrefixRedWithHalted, e2eTargetGameCodec]
      rw [prefixHandlePreHalted_eval_ctl]
      dsimp only [bhPrefixHandlePreWithHalted, bhShallowStepPreCtlHalted, bhTargetQenc]
      let ρ_ctl : Env [sidT (ℓ := ℓ) (Pt := Pt) S,
          _root_.ReductionDsl.Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
          drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q] :=
        .cons (sidV sid) (.cons (.inr (sidV sid))
          (.cons (drvHaltedEnc subs σH) (.cons (.inl (.inr (sidV sid))) .nil)))
      rw [hValid.localStartHaltedC_eval hP true hInv hBud .v2 .v0 ρ_ctl sid rfl rfl]
      rw [atomicLiftP_map, bind_map_left]
      simp only [PrefixRedHaltedEval.atomicSessionTargetIface_liftP_eq_bhLiftP,
        bhLiftP, simulateQ_bind, map_bind, bind_assoc]
      refine bind_congr_of_forall_mem_support _ fun ⟨idx?, σH'⟩ hmem => ?_
      have hOut := PrefixRedHaltedEval.mem_support_of_atomicSessionLiftP (Pt := Pt) _ hmem
      obtain ⟨hInv', -⟩ := localStartSessionTracked_preserves hValid.track_valid P C K (some true)
        hInv hBud sid hOut
      let ρ_pr : Env [_root_.ReductionDsl.Ty.prod (.opt .nat) (drvHaltedTy subs),
          sidT (ℓ := ℓ) (Pt := Pt) S,
          _root_.ReductionDsl.Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
          drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q] :=
        .cons (idx?, drvHaltedEnc subs σH') ρ_ctl
      rw [hValid.promoteSlotKC_eval hInv' (.nat k) (.fst .v0) (.fst (.snd .v0))
        ρ_pr k idx? hk rfl rfl (by simp [ρ_pr, Expr.eval, Expr.v0, drvHaltedEnc])]
      rcases σH' with ⟨σ', logs'⟩
      dsimp only [bhPromoteSlotK]
      split_ifs with hlt
      · simp [mapPreEnc, drvHaltedEnc, simulateQ_pure]
        cases σ'.insts[k]? <;> rfl
      · simp [mapPreEnc, atomicGameRespEnc, drvHaltedEnc, simulateQ_pure]
    · dsimp only [prefixRedHalted, bhPrefixRedWithHalted, e2eTargetGameCodec]
      rw [prefixHandlePreHalted_eval_sm]
      dsimp only [bhPrefixHandlePreWithHalted, bhShallowStepPreNonCtlHalted, bhTargetQenc]
      let ρ_sm : Env [_root_.ReductionDsl.Ty.prod .nat (smQT (ℓ := ℓ) (Pt := Pt)),
          drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q] :=
        .cons (i, smQenc sq) (.cons (drvHaltedEnc subs σH) (.cons (.inr (i, smQenc sq)) .nil))
      rw [hValid.haltedStepLocalSmC_eval hInv hBud .v1 (.fst .v0) (.snd .v0) ρ_sm i sq rfl rfl rfl]
      rw [atomicLiftP_map, bind_map_left]
      simp only [PrefixRedHaltedEval.atomicSessionTargetIface_liftP_eq_bhLiftP,
        bhLiftP, simulateQ_bind, simulateQ_pure, map_bind, map_pure, bind_assoc, pure_bind,
        mapPreEnc, atomicGameRespEnc]
  stepPre_inv {qKiDone qStartDone qDrDone σH} hInv t hBud res hres := by
    dsimp only [bhPrefixRedWithHalted] at hres
    rcases t with (kq | cq) | ⟨i, sq⟩
    · dsimp only [bhPrefixHandlePreWithHalted, bhShallowStepPreNonCtlHalted, bhTargetQenc] at hres
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hres
      rcases hres with ⟨⟨r, σH1⟩, h1, rfl⟩
      have h1p := KindRedHaltedEval.mem_support_of_bhLiftP _ h1
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h1p
      rcases h1p with ⟨⟨r', σ'⟩, hki, hpair⟩
      cases hpair
      exact (kiStep_preserves P C K qep decT encT hInv hBud kq hki).1
    · rcases cq with ⟨sid⟩
      dsimp only [bhPrefixHandlePreWithHalted, bhShallowStepPreCtlHalted, bhTargetQenc] at hres
      simp only [mem_support_bind_iff] at hres
      rcases hres with ⟨ctlOut, hctl, hres⟩
      have hctlP := KindRedHaltedEval.mem_support_of_bhLiftP _ hctl
      simp only [mem_support_bind_iff] at hctlP
      rcases hctlP with ⟨⟨idx?, ⟨σ', logs'⟩⟩, hst, hif⟩
      obtain ⟨hInv', -⟩ := localStartSessionTracked_preserves hValid.track_valid P C K (some true)
        hInv hBud sid hst
      split_ifs at hif with hlt
      · simp only [support_pure, Set.mem_singleton_iff] at hif
        subst hif
        simp only [support_pure, Set.mem_singleton_iff] at hres
        subst hres
        obtain ⟨hInvP, hPausedP⟩ := promoteSlotK_paused_preserves hInv' hlt
        exact ⟨⟨.startDR sid, rfl⟩, hInvP, hPausedP⟩
      · simp only [support_pure, Set.mem_singleton_iff] at hif
        subst hif
        simp only [support_pure, Set.mem_singleton_iff] at hres
        subst hres
        exact hInv'
    · dsimp only [bhPrefixHandlePreWithHalted, bhShallowStepPreNonCtlHalted, bhTargetQenc] at hres
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hres
      rcases hres with ⟨⟨r, σH1⟩, h1, rfl⟩
      have h1p := KindRedHaltedEval.mem_support_of_bhLiftP _ h1
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h1p
      rcases h1p with ⟨⟨sr, σH'⟩, hsm, hpair⟩
      cases hpair
      exact (stepLocalSmSessionTracked_preserves hValid.track_valid C K qep decT encT
        hInv hBud i sq hsm).1
  stepPost_eq {qKiDone qStartDone qDrDone σH} hInv hPaused t hBud := by
    rcases t with (kq | cq) | ⟨i, sq⟩
    · dsimp only [prefixRedHalted, bhPrefixRedWithHalted, e2eTargetGameCodec]
      rw [prefixHandlePostHalted_eval_ki]
      dsimp only [bhPrefixHandlePostWithHalted, bhShallowStepPostLocalHalted, bhTargetQenc]
      let ρ_ki : Env [keyIndQT (ℓ := ℓ) (Pt := Pt) S,
          _root_.ReductionDsl.Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
          drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q] :=
        .cons (keyIndQenc kq) (.cons (.inl (keyIndQenc kq))
          (.cons (drvHaltedEnc subs σH) (.cons (.inl (.inl (keyIndQenc kq))) .nil)))
      rw [prefixKiStepHaltedC_eval_eq hValid hP hInv hBud .v2 .v0 ρ_ki kq rfl rfl]
      rw [atomicLiftP_map]
      simp only [PrefixRedHaltedEval.atomicSessionTargetIface_liftP_eq_bhLiftP,
        bhLiftP, simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp, Function.comp_def,
        bind_assoc, pure_bind, bhShallowStepPostLocal, bhShallowStepPreNonCtl, Prod.map]
    · rcases cq with ⟨sid⟩
      dsimp only [prefixRedHalted, bhPrefixRedWithHalted, e2eTargetGameCodec]
      rw [prefixHandlePostHalted_eval_ctl]
      dsimp only [bhPrefixHandlePostWithHalted, bhShallowStepPostLocalHalted, bhTargetQenc]
      let ρ_ctl : Env [sidT (ℓ := ℓ) (Pt := Pt) S,
          _root_.ReductionDsl.Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
          drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q] :=
        .cons (sidV sid) (.cons (.inr (sidV sid))
          (.cons (drvHaltedEnc subs σH) (.cons (.inl (.inr (sidV sid))) .nil)))
      rw [hValid.localStartHaltedC_eval hP false hInv hBud .v2 .v0 ρ_ctl sid rfl rfl]
      rw [atomicLiftP_map, bind_map_left]
      simp only [PrefixRedHaltedEval.atomicSessionTargetIface_liftP_eq_bhLiftP,
        bhLiftP, simulateQ_bind, simulateQ_pure, map_bind, map_pure,
        Prod.map, atomicGameRespEnc]
    · dsimp only [prefixRedHalted, bhPrefixRedWithHalted, e2eTargetGameCodec]
      rw [prefixHandlePostHalted_eval_sm]
      dsimp only [bhPrefixHandlePostWithHalted, bhTargetQenc]
      let ρ_sm : Env [_root_.ReductionDsl.Ty.prod .nat (smQT (ℓ := ℓ) (Pt := Pt)),
          drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q] :=
        .cons (i, smQenc sq) (.cons (drvHaltedEnc subs σH) (.cons (.inr (i, smQenc sq)) .nil))
      rcases σH with ⟨σ, tracks⟩
      by_cases hik : i = k
      · subst hik
        rw [decide_eq_true rfl]; simp only [↓reduceIte]
        rw [hValid.extSmStepC_eval hInv hPaused hBud (.nat i) (.fst .v1) (.snd .v0)
          ρ_sm sq hk rfl (by simp [ρ_sm, Expr.eval, Expr.v1, drvHaltedEnc]) rfl]
        simp only [bind_map_left]
        set d := σ.insts[i]'hPaused.1
        have hd : σ.insts[i]? = some d := List.getElem?_eq_getElem hPaused.1
        have hmeta_lt : i < σ.instMeta.length := by
          have hlen : σ.instMeta.length = σ.insts.length := hInv.metaAligned
          have hi_lt : i < σ.insts.length := hPaused.1
          omega
        set im := σ.instMeta[i]'hmeta_lt
        have him : σ.instMeta[i]? = some im := List.getElem?_eq_getElem hmeta_lt
        have hd_gs : d.gs = none := hPaused.2 d hd
        by_cases hcl : (!bhE2EDrvInstClean σ i) = true
        · have hchk : bhShallowCheckExtSm i σ i sq = .inl (.inr (none, none, none)) := by
            dsimp only [bhShallowCheckExtSm]; rw [hcl]; simp
          rw [hchk]
          dsimp only [bhShallowStepPostLocalHalted, bhE2EStepLocalSmSessionTracked, bhExtSmStep]
          rw [hcl]
          simp [bhLiftP, simulateQ_pure, Prod.map, atomicGameRespEnc, drvHaltedEnc]
        · have hclF : (!bhE2EDrvInstClean σ i) = false := Bool.eq_false_iff.mpr hcl
          by_cases hcorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = true
          · have hchk : bhShallowCheckExtSm i σ i sq = .inl (.inr (none, none, none)) := by
              dsimp only [bhShallowCheckExtSm]
              have hneq : (i != i) = false := by simp
              rw [hneq, Bool.false_or, hclF]; simp [hd, him, hcorr]
            rw [hchk]
            dsimp only [bhShallowStepPostLocalHalted, bhE2EStepLocalSmSessionTracked, bhExtSmStep]
            rw [hclF]
            simp [hd, him, hcorr, bhLiftP, simulateQ_pure, Prod.map, atomicGameRespEnc, drvHaltedEnc]
          · have hcorrF : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = false :=
              Bool.eq_false_iff.mpr hcorr
            cases hf : bhFilterSmQuery d im sq with
            | none =>
              have hchk : bhShallowCheckExtSm i σ i sq = .inl (.inr (none, none, none)) := by
                rw [checkExtSm_eq_of_filter hclF hd him sq hcorrF, hf]
              rw [hchk]
              dsimp only [bhShallowStepPostLocalHalted, bhE2EStepLocalSmSessionTracked, bhExtSmStep]
              rw [hclF]
              simp [hd, him, hcorrF, hf, hd_gs, bhLiftP, simulateQ_pure, Prod.map,
                atomicGameRespEnc, drvHaltedEnc]
            | some sq' =>
              have hchk : bhShallowCheckExtSm i σ i sq = .inr sq' := by
                rw [checkExtSm_eq_of_filter hclF hd him sq hcorrF, hf]
              rw [hchk]
              have hcorrF' :
                  (!im.bobAccepted && bhIsBobRecvSMQuery sq' && bhE2EInstIkACorr σ d) = false := by
                rwa [bhFilterSmQuery_isBobRecv hf]
              dsimp only [bhExtSmStep, bhShallowCommitExtSm]
              rw [hclF]
              simp only [Bool.false_eq_true, ↓reduceIte, hd, him, hcorrF, hf,
                map_bind, map_pure, bind_assoc, pure_bind]
              refine bind_congr fun r => ?_
              have hunp : CryptoVerification.E2E.bhUnpackSmResp sq' (bhPackSmResp sq' r) = r := by
                rcases sq' with (((_ | _) | _) | _) | _ <;> rfl
              simp [hcorrF', hunp, Prod.map, atomicGameRespEnc, drvHaltedEnc]
      · rw [decide_eq_false hik]; simp only [Bool.false_eq_true, ↓reduceIte]
        have hchk : bhShallowCheckExtSm k σ i sq = .inl (.inr (none, none, none)) := by
          dsimp only [bhShallowCheckExtSm]
          have hneB : (i != k) = true := bne_iff_ne.mpr hik
          rw [hneB]; simp
        rw [hchk]
        rw [hValid.haltedStepLocalSmC_eval hInv hBud .v1 (.fst .v0) (.snd .v0) ρ_sm i sq rfl rfl rfl]
        rw [atomicLiftP_map, bind_map_left]
        dsimp only [bhShallowStepPostLocalHalted]
        simp only [PrefixRedHaltedEval.atomicSessionTargetIface_liftP_eq_bhLiftP,
          bhLiftP, simulateQ_bind, simulateQ_pure, map_bind, map_pure,
          Prod.map, atomicGameRespEnc]
  stepPost_inv {qKiDone qStartDone qDrDone σH} hInv hPaused t hBud p hp := by
    dsimp only [bhPrefixRedWithHalted] at hp
    rcases t with (kq | cq) | ⟨i, sq⟩
    · dsimp only [bhPrefixHandlePostWithHalted, bhShallowStepPostLocalHalted, bhTargetQenc] at hp
      have hp' := KindRedHaltedEval.mem_support_of_bhLiftP _ hp
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp'
      rcases hp' with ⟨⟨r', σ'⟩, hki, rfl⟩
      have hki' : (r', σ') ∈ support
          (bhShallowStepPreNonCtl P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
            C K qep decT encT σH.1 (.inl (.inl kq))) := hki
      obtain ⟨hInv', hPau'⟩ := kiStep_preserves P C K qep decT encT hInv hBud kq hki'
      exact ⟨hPau' k hPaused, hInv'⟩
    · rcases cq with ⟨sid⟩
      dsimp only [bhPrefixHandlePostWithHalted, bhShallowStepPostLocalHalted, bhTargetQenc] at hp
      have hp' := KindRedHaltedEval.mem_support_of_bhLiftP _ hp
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp'
      rcases hp' with ⟨⟨idx?, σH1⟩, hst, rfl⟩
      obtain ⟨hInv', hPau'⟩ := localStartSessionTracked_preserves hValid.track_valid P C K
        (some false) hInv hBud sid hst
      exact ⟨hPau' k hPaused, hInv'⟩
    · dsimp only [bhPrefixHandlePostWithHalted, bhTargetQenc] at hp
      cases hchk : bhShallowCheckExtSm k σH.1 i sq with
      | inl _ =>
        rw [hchk] at hp
        have hp' := KindRedHaltedEval.mem_support_of_bhLiftP _ hp
        dsimp only [bhShallowStepPostLocalHalted] at hp'
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp'
        rcases hp' with ⟨⟨sr, σH'⟩, hsm, rfl⟩
        obtain ⟨hInv', hPau'⟩ := stepLocalSmSessionTracked_preserves hValid.track_valid
          C K qep decT encT hInv hBud i sq hsm
        exact ⟨hPau' k hPaused, hInv'⟩
      | inr sq' =>
        rw [hchk] at hp
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
        rcases hp with ⟨r, -, rfl⟩
        obtain ⟨hInv', hPau'⟩ := commitExtSm_preserves hValid.track_valid hInv hPaused hBud
          sq' (bhPackSmResp sq' r)
        exact ⟨hPau', hInv'⟩
  finish_eq {_ _ _ σ_out} hInv b_out flip := by
    dsimp only [prefixRedHalted, bhPrefixRedWithHalted]
    let ρ_f : Env [drvHaltedTy subs, .bool, .bool] :=
      .cons (drvHaltedEnc subs σ_out) (.cons b_out (.cons flip .nil))
    rw [hValid.finishPrefixC_eval hP hInv (.fst .v0) .v1 .v2 ρ_f b_out flip
      (by simp [ρ_f, Expr.eval, Expr.v0, drvHaltedEnc]) rfl rfl]
    rfl

/-- Full Stage-1 and Stage-2 `ProbComp` equality between `prefixRedHalted` and
`bhPrefixRedWithSessionTracked`. -/
theorem prefixEval_eq_of_valid
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    {subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey SessH}
    {TrackInv : ℕ → SessH → Prop}
    {b : SignalPqxdh.QueryBudget} {qStart qInst qep k : ℕ} {qs : ℕ → ℕ}
    (hValid : ValidHaltedPrefixSubprograms subs T TrackInv b qStart qInst qep)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : HaltedTargetAdvPerInstanceBounded B_A b qStart qs)
    (hk : k < qStart)
    {β : Type}
    (game2 : IdentityKey → IdentityKey → BitVec 256 →
      OracleComp
        (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool →
      ProbComp β)
    (flip : Bool) :
    let qDR := ∑ j ∈ Finset.range qStart, qs j
    let qTot := b.q_total + qStart + qDR
    let R := prefixRedHalted subs b qStart qInst qep k
    let R_sh := bhPrefixRedWithSessionTracked T P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
      C K qep decT encT k
    (stageOneAsProbComp (R.eval1 (fun _ => B_A) () qTot false) >>= fun o =>
      game2 o.1.1 o.1.2.1 o.1.2.2 (R.eval2 o.2 flip qTot false)) =
    (stageOneAsProbComp (R_sh.eval1 (fun _ => B_A) () qTot false) >>= fun o =>
      game2 o.1.idA o.1.idB o.1.spkCoins (R_sh.eval2 o.2 flip qTot false)) := by
  dsimp only
  set qDR := ∑ j ∈ Finset.range qStart, qs j
  set qTot := b.q_total + qStart + qDR
  have hSim := twoStage_stage12_comp_eq
    (prefixRedHalted_twoStageSimSpec (qDR := qDR) hValid hP hk)
    B_A hB.toTwoStageTargetBounded game2 qTot qTot false flip
  dsimp only [prefixRedHalted_twoStageSimSpec] at hSim
  rwa [bhPrefixRedWithHalted_eq_bhPrefixRedWithSessionTracked] at hSim

end Computational.Proofs.E2E.Dsl.PrefixRedHaltedInst
