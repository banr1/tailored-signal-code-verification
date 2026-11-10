/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.CliPqAdapterCoupling
import Computational.Proofs.E2E.BhKindCouplingV1
import Computational.Proofs.LibsignalCli.CliPqHandshakeStepCore
import Computational.Proofs.LibsignalCli.CliPqKeyIndStepCore
import Computational.Proofs.ReductionDsl.SM.GameCosted
import Computational.Specifications.Pqxdh.Security.HeadlineDelta
import ProofLib.SepLogic.WP.StateNorm
import VCVio.EvalDist.Monad.Basic

@[expose] public section

/-!
# The `startDR` step of the CLI-to-model adapter coupling

Proves `cliStartStepBridgeProp_holds`, coupling `cliDrvStart` and `cliComposedAdapterImplWith` on a
`.startDR sid` control query and establishing `CliAdapterInstRel` for newly promoted instances.
-/

set_option autoImplicit false
set_option linter.constructorNameAsVariable false
set_option linter.unusedSimpArgs false

open scoped ENNReal BigOperators
open ReductionDsl OracleComp OracleSpec MeasureTheory

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.SignalSession
  CryptoVerification.LibsignalCli.Entry

/-! ## Adapter `startDR` unfolding and guard agreement -/

private theorem cliE2EDrvImplWith_run_startDR {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (sid : SignalPqxdh.SessionId S) (σ_e2e : BHE2EDrvState S ℓ) :
    (cliE2EDrvImplWith P ki C K qep decT encT (.inr (.inl (.inr (.startDR sid))))).run σ_e2e =
      compositionLocalStart ki C K (some σ_e2e.b) σ_e2e sid := by
  unfold cliE2EDrvImplWith
  simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, StateT.run_set,
    StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind, Prod.mk.eta, bind_pure]

private theorem bhAdapterHandle_impl_run_startDR_cli {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (_decT : PublicKey → Option Pt) (_encT : Pt → PublicKey)
    (sid : SignalPqxdh.SessionId S) (σ_ad : CliAdapterState S) :
    ((bhShallowAdapterImpl S ℓ (BitVec 512) (.inr (.inl (.inr (.startDR sid))))).run σ_ad) =
      ((liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query
          (.inr (.inl (.inr (.startDR sid))))) :
          OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) (Option ℕ)) >>= fun idx? =>
        match idx? with
        | none => pure (none, σ_ad)
        | some idx =>
          match (bhShallowStepMirrorGuard (.inr (σ_ad.2.2, sid))).2 with
          | none => pure (some idx, σ_ad)
          | some inst =>
            pure (some idx, ((fun j => if j = idx then some inst else σ_ad.1 j), σ_ad.2))) := by
  dsimp [bhShallowAdapterImpl, bhShallowAdapterGameStep, bhShallowQueryTarget]
  congr 1; funext idx?
  cases idx? with
  | none => rfl
  | some idx =>
    dsimp only
    rcases (bhShallowStepMirrorGuard (.inr (σ_ad.2.2, sid))).2 with _ | inst <;> rfl

private def adapterStartDRRun {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (_decT : PublicKey → Option Pt)
    (_encT : Pt → PublicKey) (sid : SignalPqxdh.SessionId S)
    (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ) :
    ProbComp ((Option ℕ × CliAdapterState S) × BHE2EDrvState S ℓ) := do
  let (idx?, σ_e2e') ← compositionLocalStart ki C K (some σ_e2e.b) σ_e2e sid
  match idx? with
  | none => return ((none, σ_ad), σ_e2e')
  | some idx =>
    match (bhShallowStepMirrorGuard (.inr (σ_ad.2.2, sid))).2 with
    | none => return ((some idx, σ_ad), σ_e2e')
    | some inst =>
      return ((some idx, ((fun j => if j = idx then some inst else σ_ad.1 j), σ_ad.2)), σ_e2e')

private theorem cliComposedAdapterImplWith_startDR_run {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ) (decT : PublicKey → Option Pt)
    (encT : Pt → PublicKey) (sid : SignalPqxdh.SessionId S)
    (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ) :
    (((cliComposedAdapterImplWith P ki C K qep decT encT (.inl (.inr (.startDR sid)))).run
        σ_ad).run σ_e2e) =
      adapterStartDRRun (ℓ := ℓ) ki C K decT encT sid σ_ad σ_e2e := by
  unfold adapterStartDRRun
  change (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
    ((bhShallowAdapterImpl S ℓ (BitVec 512) (.inr (.inl (.inr (.startDR sid))))).run
      σ_ad)).run σ_e2e = _
  rw [bhAdapterHandle_impl_run_startDR_cli decT encT]; simp only [simulateQ_bind, StateT.run_bind]; congr 1
  · simp only [simulateQ_query, OracleSpec.query_def]; dsimp [OracleQuery.cont, OracleQuery.input]
    rw [id_map, cliE2EDrvImplWith_run_startDR]
  · funext ⟨idx?, σ_e2e'⟩; cases idx? with
    | none => simp [simulateQ_pure, StateT.run_pure]
    | some idx =>
      dsimp only
      rcases (bhShallowStepMirrorGuard (.inr (σ_ad.2.2, sid))).2 with _ | inst <;>
        simp [simulateQ_pure, StateT.run_pure]

/-- Under `CliAdapterDrvRel`, the CLI promotion guard `bhDrvGuard` agrees with `bhE2EGuard`. -/
theorem bhDrvGuard_eq_bhE2EGuard_of_cliRel {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (sid : SignalPqxdh.SessionId S) : bhDrvGuard ds_cli sid = bhE2EGuard σ_e2e sid := by
  unfold bhDrvGuard bhE2EGuard
  have hElem : ∀ (i : ℕ) (bi : ModelDriverInstance S ℓ) (d : BHModelInst S ℓ),
      ds_cli.bhInsts[i]? = some bi → σ_e2e.insts[i]? = some d →
      bi.sid = d.sid ∧ bi.hdr = d.hdr := fun i bi d hbi hd => by
    have hi_cli : i < ds_cli.bhInsts.length := by
      by_contra hge; rw [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hbi; cases hbi
    have hi_e2e : i < σ_e2e.insts.length := hRel.insts_len_eq ▸ hi_cli
    obtain ⟨_, _, hInst⟩ := hRel.insts_rel i hi_cli hi_e2e
      (hRel.meta_cli_len_eq.symm ▸ hi_cli) (hRel.meta_e2e_len_eq.symm ▸ hi_e2e)
    have hbi_eq : ds_cli.bhInsts[i] = bi := Option.some.inj ((List.getElem?_eq_getElem hi_cli).symm.trans hbi)
    have hd_eq : σ_e2e.insts[i] = d := Option.some.inj ((List.getElem?_eq_getElem hi_e2e).symm.trans hd)
    exact ⟨hbi_eq ▸ hd_eq ▸ hInst.sid_eq.1, hbi_eq ▸ hd_eq ▸ hInst.hdr_eq.1⟩
  have hSidAny : ds_cli.bhInsts.any (fun bi => bi.sid == sid) = σ_e2e.insts.any (fun d => d.sid == sid) :=
    cli_list_any_eq_of_getElem?_rel ds_cli.bhInsts σ_e2e.insts hRel.insts_len_eq
      (fun i bi d hbi hd => by rw [(hElem i bi d hbi hd).1])
  rw [hSidAny, congrArg ModelDriverBase.sends hRel.base_e2e_eq]
  cases σ_e2e.insts.any (fun d => d.sid == sid)
  · dsimp only [Bool.false_eq_true, ↓reduceIte]
    cases σ_e2e.sends.find? (fun (s, _, _) => s == sid) with
    | none => rfl
    | some sh =>
      rcases sh with ⟨s0, bnd, hdr⟩; dsimp only
      have hEkAny : ds_cli.bhInsts.any (fun bi => bi.hdr.ekAPk == hdr.ekAPk) =
          σ_e2e.insts.any (fun d => d.hdr.ekAPk == hdr.ekAPk) :=
        cli_list_any_eq_of_getElem?_rel ds_cli.bhInsts σ_e2e.insts hRel.insts_len_eq
          (fun i bi d hbi hd => by rw [(hElem i bi d hbi hd).2])
      rw [hEkAny, congrArg ModelDriverBase.bundles hRel.base_e2e_eq,
        congrArg ModelDriverBase.prins hRel.base_e2e_eq, hRel.base_e2e_eq, hRel.corrPrins_eq]
  · rfl

theorem stepMirrorGuard_of_bhDrvGuard_eq_some {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (_decT : PublicKey → Option Pt) (_encT : Pt → PublicKey)
    (ds_cli : ModelDriverState S ℓ) (drv : ModelDriverBase S) (sid : SignalPqxdh.SessionId S)
    (hdr : SignalPqxdh.HandshakeHdr) (bnd : SignalPqxdh.PreKeyBundleInput)
    (u_resp : Fin S.N_id) (j_resp : Fin S.N_recv) (hDrv : drv = ds_cli.toModelDriverBase)
    (hGuard : bhDrvGuard ds_cli sid = some (hdr, bnd, (u_resp, j_resp))) :
    (bhShallowStepMirrorGuard (.inr (drv, sid))).2 =
      some { sid := sid, u_resp := u_resp, hdr := hdr, idB := bnd.ikB,
             bobRemoteRegId := bhInitRegId sid } := by
  subst hDrv; unfold bhDrvGuard at hGuard; dsimp only [bhShallowStepMirrorGuard]
  split_ifs at hGuard with hSid
  cases hSends : ds_cli.sends.find? (fun (s, _, _) => s == sid) with
  | none => simp [hSends] at hGuard
  | some sh =>
    rcases sh with ⟨s0, bnd0, hdr0⟩; rw [hSends] at hGuard; dsimp only at hGuard ⊢
    split_ifs at hGuard with hEk
    cases hBnd : ds_cli.bundles.find? (fun ((_, j), (spkB, pqspkB)) =>
        spkB == bnd0.spkB && pqspkB == bnd0.pqspkB &&
        hdr0.spkId == UInt32.ofNat j.val && hdr0.pqspkId == UInt32.ofNat j.val) with
    | none => simp [hBnd] at hGuard
    | some bp =>
      rcases bp with ⟨⟨u0, j0⟩, pkPair⟩; rw [hBnd] at hGuard; dsimp only at hGuard ⊢
      split_ifs at hGuard with hOk
      simp only [Option.some.injEq, Prod.mk.injEq] at hGuard
      rcases hGuard with ⟨rfl, rfl, rfl, rfl⟩
      have hOk1 : (ds_cli.prins.any (fun (u', pk) => u' == u0 && pk == bnd0.ikB) &&
          bhBaseOpkOk ds_cli.toModelDriverBase u0 j0 bnd0) = true :=
        (Bool.and_eq_true _ _).mp hOk |>.1
      simp [hOk1]

theorem bhDrvGuard_eq_some_facts {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {ds : ModelDriverState S ℓ} {sid : SignalPqxdh.SessionId S} {hdr : SignalPqxdh.HandshakeHdr}
    {bnd : SignalPqxdh.PreKeyBundleInput} {u_resp : Fin S.N_id} {j_resp : Fin S.N_recv}
    (hGuard : bhDrvGuard ds sid = some (hdr, bnd, (u_resp, j_resp))) :
    (sid, bnd, hdr) ∈ ds.sends ∧ ((u_resp, j_resp), (bnd.spkB, bnd.pqspkB)) ∈ ds.bundles ∧
    hdr.spkId = UInt32.ofNat j_resp.val ∧ hdr.pqspkId = UInt32.ofNat j_resp.val ∧
    (u_resp, bnd.ikB) ∈ ds.prins ∧ bhBaseOpkOk ds.toModelDriverBase u_resp j_resp bnd = true := by
  unfold bhDrvGuard at hGuard; split_ifs at hGuard with hSid
  cases hSends : ds.sends.find? (fun (s, _, _) => s == sid) with
  | none => simp [hSends] at hGuard
  | some sh =>
    rcases sh with ⟨s0, bnd0, hdr0⟩; rw [hSends] at hGuard; dsimp only at hGuard
    split_ifs at hGuard with hEk
    cases hBnd : ds.bundles.find? (fun ((_, j), (spkB, pqspkB)) =>
        spkB == bnd0.spkB && pqspkB == bnd0.pqspkB &&
        hdr0.spkId == UInt32.ofNat j.val && hdr0.pqspkId == UInt32.ofNat j.val) with
    | none => simp [hBnd] at hGuard
    | some bp =>
      rcases bp with ⟨⟨u0, j0⟩, ⟨spk0, pqspk0⟩⟩; rw [hBnd] at hGuard; dsimp only at hGuard
      split_ifs at hGuard with hOk
      simp only [Option.some.injEq, Prod.mk.injEq] at hGuard
      rcases hGuard with ⟨rfl, rfl, rfl, rfl⟩
      have hs_mem := List.mem_of_find?_eq_some hSends
      have hs_eq : s0 = sid := by have hp := List.find?_some hSends; simpa using hp
      subst s0
      have hb_mem := List.mem_of_find?_eq_some hBnd
      have hb_pred := List.find?_some hBnd
      simp only [Bool.and_eq_true, beq_iff_eq] at hb_pred
      rcases hb_pred with ⟨⟨⟨rfl, rfl⟩, hspkId⟩, hpqspkId⟩
      simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at hOk
      rcases hOk with ⟨⟨⟨⟨u', pk'⟩, hprin_mem, rfl, rfl⟩, hopkOk⟩, _⟩
      exact ⟨hs_mem, hb_mem, hspkId, hpqspkId, hprin_mem, hopkOk⟩

/-! ## `testSession` and `revealSpkSk` coupling -/

theorem forall2_cliSpkBundles_map_reveal_right
    {spks₁ spks₂ : List ((ℕ × ℕ) × SignalPqxdh.SpkBundleEntry)}
    (h : List.Forall₂ CliSpkBundleRel spks₁ spks₂) (target : ℕ × ℕ) :
    List.Forall₂ CliSpkBundleRel spks₁
      (spks₂.map (fun (idx, b) => if idx == target then (idx, { b with revealed := true }) else (idx, b))) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hhead _ ih =>
    rcases hhead with ⟨hidx, h1, h2, h3, h4, h5, h6⟩
    refine List.Forall₂.cons (by dsimp only; split_ifs <;> exact ⟨hidx, h1, h2, h3, h4, h5, h6⟩) ih

theorem revealSpkSk_unilateral_rel {S : SignalPqxdh.Setup} (P : SignalPqxdh.Primitives)
    {st_cli st_e2e : SignalPqxdh.KeyIndState S} (hSt : CliKeyIndStateRel P st_cli st_e2e)
    (u_resp : Fin S.N_id) (j_resp : Fin S.N_recv) :
    ∃ (kr2 : SignalPqxdh.KeyIndResponse) (st2_e2e : SignalPqxdh.KeyIndState S),
      ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P (.revealSpkSk u_resp j_resp)).run st_e2e) =
        pure (kr2, st2_e2e) ∧ CliKeyIndStateRel P st_cli st2_e2e := by
  change ∃ kr2 st2_e2e, ((SignalPqxdh.pqxdhKeyIndImpl false S P (.revealSpkSk u_resp j_resp)).run st_e2e) =
    pure (kr2, st2_e2e) ∧ CliKeyIndStateRel P st_cli st2_e2e
  unfold SignalPqxdh.pqxdhKeyIndImpl; dsimp only
  cases hFind : st_e2e.spkBundles.find? (fun (idx, _) => idx == (u_resp.val, j_resp.val)) with
  | none => exact ⟨.noneResp, st_e2e, by simp [hFind], hSt⟩
  | some p =>
    rcases p with ⟨idx0, bEntry⟩
    refine ⟨.spkSkResp bEntry.spkSk,
      { st_e2e with spkBundles := st_e2e.spkBundles.map (fun (idx, b) =>
          if idx == (u_resp.val, j_resp.val) then (idx, { b with revealed := true }) else (idx, b)) },
      by simp [hFind, StateT.run_bind, StateT.run_set, StateT.run_pure], {
        secb_cli := hSt.secb_cli, secb_e2e := hSt.secb_e2e, principals_eq := hSt.principals_eq
        spkBundles_rel := forall2_cliSpkBundles_map_reveal_right hSt.spkBundles_rel (u_resp.val, j_resp.val)
        opkEntries_eq := hSt.opkEntries_eq, sessions_eq := hSt.sessions_eq
        respSessions_eq := hSt.respSessions_eq, usedRecvOPK_eq := hSt.usedRecvOPK_eq
        usedRecvNoOPK_eq := hSt.usedRecvNoOPK_eq, usedKyberTriples_eq := hSt.usedKyberTriples_eq
        roCache_eq := hSt.roCache_eq, advKeys_eq := hSt.advKeys_eq, resp_not_tested := hSt.resp_not_tested
        tested_spkRevealed := fun s hs htest =>
          let ⟨hRev1, hRev2⟩ := hSt.tested_spkRevealed s hs htest
          ⟨hRev1, isSpkRevealed_map_reveal_of_true_cli P st_e2e.spkBundles (u_resp.val, j_resp.val)
            s.peerSpkPk hRev2⟩ }⟩

/-- Preservation of `CliAdapterKeyIndInv` across `testSession sid` + `revealSpkSk u_resp j_resp`
and appending a promoted instance (leaving `toModelDriverBase` and `initTapes` unchanged). -/
theorem cliAdapterKeyIndInv_of_test_and_revealSpk {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {W : PEParams} {st_cli : SignalPqxdh.KeyIndState S}
    {ds_cli ds_cli' : ModelDriverState S ℓ} (hInv : CliAdapterKeyIndInv S P W st_cli ds_cli)
    (sid : SignalPqxdh.SessionId S) (target : ℕ × ℕ)
    (hBase : ds_cli'.toModelDriverBase = ds_cli.toModelDriverBase) (hTapes : ds_cli'.initTapes = ds_cli.initTapes) :
    let st2_cli : SignalPqxdh.KeyIndState S :=
      { st_cli with
        sessions := st_cli.sessions.map (fun s => if s.sid == sid then { s with tested := true } else s),
        spkBundles := st_cli.spkBundles.map (fun (idx, b) =>
          if idx == target then (idx, { b with revealed := true }) else (idx, b)) }
    CliAdapterKeyIndInv S P W st2_cli ds_cli' := by
  intro st2_cli
  have hPrins : ds_cli'.prins = ds_cli.prins := congrArg ModelDriverBase.prins hBase
  have hBundles : ds_cli'.bundles = ds_cli.bundles := congrArg ModelDriverBase.bundles hBase
  have hOpks : ds_cli'.opks = ds_cli.opks := congrArg ModelDriverBase.opks hBase
  have hSends : ds_cli'.sends = ds_cli.sends := congrArg ModelDriverBase.sends hBase
  have hSpkBwd : ∀ idx b', (idx, b') ∈ st2_cli.spkBundles →
      ∃ b, (idx, b) ∈ st_cli.spkBundles ∧ b'.spkSk = b.spkSk ∧ b'.spkPk = b.spkPk ∧
        b'.pqspkPk = b.pqspkPk ∧ b'.pqspkSk = b.pqspkSk ∧
        b'.spkSig = b.spkSig ∧ b'.pqspkSig = b.pqspkSig := by
    intro idx b' hmem; dsimp only [st2_cli] at hmem; rw [List.mem_map] at hmem
    rcases hmem with ⟨⟨idx0, b⟩, hb_mem, heq⟩; dsimp only at heq
    split_ifs at heq <;> {
      rcases Prod.mk.inj heq with ⟨rfl, rfl⟩; exact ⟨b, hb_mem, rfl, rfl, rfl, rfl, rfl, rfl⟩ }
  have hSpkFwd : ∀ idx b, (idx, b) ∈ st_cli.spkBundles →
      ∃ b', (idx, b') ∈ st2_cli.spkBundles ∧ b.spkPk = b'.spkPk ∧ b.pqspkPk = b'.pqspkPk := by
    intro idx b hb_mem
    refine ⟨if idx == target then { b with revealed := true } else b, ?_, ?_⟩
    · dsimp only [st2_cli]
      have hm := List.mem_map_of_mem
        (f := fun (i, x) => if i == target then (i, { x with revealed := true }) else (i, x))
        hb_mem
      dsimp only at hm; split_ifs at hm ⊢ <;> exact hm
    · split_ifs <;> exact ⟨rfl, rfl⟩
  have hSessBwd : ∀ s' ∈ st2_cli.sessions,
      ∃ s ∈ st_cli.sessions, s'.sid = s.sid ∧ s'.peerSpkPk = s.peerSpkPk ∧
        s'.drKeyReal = s.drKeyReal ∧ s'.drKeyRand = s.drKeyRand ∧ s'.hdr = s.hdr := by
    intro s' hmem; dsimp only [st2_cli] at hmem; rw [List.mem_map] at hmem
    rcases hmem with ⟨s, hs_mem, heq⟩
    split_ifs at heq <;> { subst heq; exact ⟨s, hs_mem, rfl, rfl, rfl, rfl, rfl⟩ }
  have hSessFwd : ∀ s ∈ st_cli.sessions,
      ∃ s' ∈ st2_cli.sessions, s'.sid = s.sid ∧ s'.peerSpkPk = s.peerSpkPk ∧ s'.hdr = s.hdr := by
    intro s hs_mem
    refine ⟨if s.sid == sid then { s with tested := true } else s, List.mem_map_of_mem hs_mem, ?_⟩
    split_ifs <;> exact ⟨rfl, rfl, rfl⟩
  exact {
    prins_wf := hInv.prins_wf, prins_uniq := hInv.prins_uniq
    spk_wf := fun idx b' hmem => by
      obtain ⟨b, hb_mem, h1, h2, h3, h4, h5, h6⟩ := hSpkBwd idx b' hmem
      have hw := hInv.spk_wf idx b hb_mem; rw [h1, h2, h3, h4, h5, h6]; exact hw
    spk_uniq := fun idx₁ idx₂ b₁' b₂' hm1 hm2 hidx => by
      obtain ⟨b₁, hb1, e11, e12, e13, e14, e15, e16⟩ := hSpkBwd idx₁ b₁' hm1
      obtain ⟨b₂, hb2, e21, e22, e23, e24, e25, e26⟩ := hSpkBwd idx₂ b₂' hm2
      obtain ⟨u1, u2, u3, u4, u5, u6⟩ := hInv.spk_uniq idx₁ idx₂ b₁ b₂ hb1 hb2 hidx
      exact ⟨e11.trans (u1.trans e21.symm), e12.trans (u2.trans e22.symm),
             e13.trans (u3.trans e23.symm), e14.trans (u4.trans e24.symm),
             e15.trans (u5.trans e25.symm), e16.trans (u6.trans e26.symm)⟩
    opk_wf := hInv.opk_wf, opk_uniq := hInv.opk_uniq
    ds_prins := fun u ik hmem => hInv.ds_prins u ik (hPrins ▸ hmem)
    prins_ds := fun idx e hmem => let ⟨u, hu⟩ := hInv.prins_ds idx e hmem; ⟨u, hPrins.symm ▸ hu⟩
    ds_bundles := fun slot spkB pqspkB hmem => by
      obtain ⟨e, b, he, hb, hspk, hpqspk⟩ := hInv.ds_bundles slot spkB pqspkB (hBundles ▸ hmem)
      obtain ⟨b', hb', hspk', hpqspk'⟩ := hSpkFwd _ b hb
      exact ⟨e, b', he, hb', hspk.trans hspk', hpqspk.trans hpqspk'⟩
    ds_opks := fun slot opkPk hmem => hInv.ds_opks slot opkPk (hOpks ▸ hmem)
    sessions_wf := fun s' hmem => by
      obtain ⟨s, hs, _, _, hdr1, hdr2, _⟩ := hSessBwd s' hmem
      have hw := hInv.sessions_wf s hs; rw [hdr1, hdr2]; exact hw
    sessions_uniq := fun s₁' s₂' hm1 hm2 hsid => by
      obtain ⟨s₁, hs1, id1, sp1, dr1, _, hd1⟩ := hSessBwd s₁' hm1
      obtain ⟨s₂, hs2, id2, sp2, dr2, _, hd2⟩ := hSessBwd s₂' hm2
      obtain ⟨u1, u2, u3⟩ := hInv.sessions_uniq s₁ s₂ hs1 hs2 (id1.symm.trans (hsid.trans id2))
      exact ⟨sp1.trans (u1.trans sp2.symm), dr1.trans (u2.trans dr2.symm),
             hd1.trans (u3.trans hd2.symm)⟩
    roCache_nil := hInv.roCache_nil, respSessions_wf := hInv.respSessions_wf
    initTapes_wf := fun sid0 u_init bnd0 t_init hmem => by
      obtain ⟨⟨s, hs, hsid0⟩, hprin, hinitP, hssig, hpsig⟩ :=
        hInv.initTapes_wf sid0 u_init bnd0 t_init (hTapes ▸ hmem)
      obtain ⟨s', hs', hsid', _, _⟩ := hSessFwd s hs
      exact ⟨⟨s', hs', hsid'.trans hsid0⟩, hprin, hinitP, hssig, hpsig⟩
    initTapes_uniq := fun sid0 u₁ b₁ t₁ u₂ b₂ t₂ hm1 hm2 =>
      hInv.initTapes_uniq sid0 u₁ b₁ t₁ u₂ b₂ t₂ (hTapes ▸ hm1) (hTapes ▸ hm2)
    sends_wf := fun sid0 bnd0 hdr0 hmem => by
      obtain ⟨⟨s, hs, hsid0, hpspk, hhdr0⟩, hinitT, hspkId, hpqspkId, hopkId,
        hssig, hpsig, hikL, hekL, hkemL, hsigV, hDer⟩ :=
        hInv.sends_wf sid0 bnd0 hdr0 (hSends ▸ hmem)
      obtain ⟨s', hs', hsid', hpspk', hhdr'⟩ := hSessFwd s hs
      refine ⟨⟨s', hs', hsid'.trans hsid0, hpspk'.trans hpspk, hhdr'.trans hhdr0⟩,
        ?_, hspkId, hpqspkId, hopkId, hssig, hpsig, hikL, hekL, hkemL, hsigV, ?_⟩
      · rcases hinitT with ⟨u_init, t_init, uEntry, ht_mem, hu_mem, hik_eq⟩
        exact ⟨u_init, t_init, uEntry, hTapes.symm ▸ ht_mem, hu_mem, hik_eq⟩
      · intro sid' u_init bnd' t_init sEntry' uIdx uEntry ht_mem hsid_eq hs'_mem hs'_sid hu_mem hu_eq
        obtain ⟨sEntry, hs_mem, hse_sid, _, hse_dr, _, _⟩ := hSessBwd sEntry' hs'_mem
        obtain ⟨ss, henc, hek, hdr_eq⟩ := hDer sid' u_init bnd' t_init sEntry uIdx uEntry
          (hTapes ▸ ht_mem) hsid_eq hs_mem (hse_sid.symm.trans hs'_sid) hu_mem hu_eq
        exact ⟨ss, henc, hek, hse_dr.trans hdr_eq⟩ }

/-- Joint execution of `testSession sid` and `revealSpkSk u_resp j_resp` when `bhDrvGuard` succeeds
and `isKeyIndSessionTestable st_cli sid = true`. -/
theorem testSession_and_revealSpk_of_guard_some {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {W : PEParams} {st_cli st_e2e : SignalPqxdh.KeyIndState S}
    {ds_cli : ModelDriverState S ℓ} (hSt : CliKeyIndStateRel P st_cli st_e2e)
    (hInv : CliAdapterKeyIndInv S P W st_cli ds_cli) {sid : SignalPqxdh.SessionId S}
    {hdr : SignalPqxdh.HandshakeHdr} {bnd : SignalPqxdh.PreKeyBundleInput}
    {u_resp : Fin S.N_id} {j_resp : Fin S.N_recv}
    (hGuard : bhDrvGuard ds_cli sid = some (hdr, bnd, (u_resp, j_resp)))
    (hFresh : SignalPqxdh.isKeyIndSessionTestable st_cli sid = true) :
    ∃ (sFound : SignalPqxdh.KeyIndInitiatorEntry S) (respSpk0 : SignalPqxdh.SpkBundleEntry),
      let st1_cli : SignalPqxdh.KeyIndState S :=
        { st_cli with sessions := st_cli.sessions.map (fun s => if s.sid == sid then { s with tested := true } else s) }
      let st1_e2e : SignalPqxdh.KeyIndState S :=
        { st_e2e with sessions := st_e2e.sessions.map (fun s => if s.sid == sid then { s with tested := true } else s) }
      let st2_cli : SignalPqxdh.KeyIndState S :=
        { st1_cli with spkBundles := st_cli.spkBundles.map (fun (idx, b) =>
            if idx == (u_resp.val, j_resp.val) then (idx, { b with revealed := true }) else (idx, b)) }
      let st2_e2e : SignalPqxdh.KeyIndState S :=
        { st1_e2e with spkBundles := st_e2e.spkBundles.map (fun (idx, b) =>
            if idx == (u_resp.val, j_resp.val) then (idx, { b with revealed := true }) else (idx, b)) }
      sFound ∈ st_cli.sessions ∧ sFound.sid = sid ∧ sFound.peerSpkPk = bnd.spkB ∧
      sFound.hdr = hdr ∧ ((u_resp.val, j_resp.val), respSpk0) ∈ st_cli.spkBundles ∧
      st_cli.spkBundles.find? (fun (idx, _) => idx == (u_resp.val, j_resp.val)) =
        some ((u_resp.val, j_resp.val), respSpk0) ∧
      respSpk0.spkPk = bnd.spkB ∧ respSpk0.pqspkPk = bnd.pqspkB ∧
      ((SignalPqxdh.pqxdhKeyIndImpl false S P (.testSession sid)).run st_cli) =
        pure (.drKeyResp sFound.drKeyReal, st1_cli) ∧
      ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P (.testSession sid)).run st_e2e) =
        pure (.drKeyResp sFound.drKeyReal, st1_e2e) ∧
      ((SignalPqxdh.pqxdhKeyIndImpl false S P (.revealSpkSk u_resp j_resp)).run st1_cli) =
        pure (.spkSkResp respSpk0.spkSk, st2_cli) ∧
      ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P (.revealSpkSk u_resp j_resp)).run st1_e2e) =
        pure (.spkSkResp respSpk0.spkSk, st2_e2e) ∧
      CliKeyIndStateRel P st2_cli st2_e2e := by
  obtain ⟨hSendsMem, hBundlesMem, _, _, _, _⟩ := bhDrvGuard_eq_some_facts hGuard
  obtain ⟨⟨sEntry, hsEntry_mem, hsEntry_sid, hsEntry_spk, hsEntry_hdr⟩, _⟩ :=
    hInv.sends_wf sid bnd hdr hSendsMem
  obtain ⟨_, bResp, _, hbResp_mem, hbResp_spk, hbResp_pqspk⟩ :=
    hInv.ds_bundles (u_resp, j_resp) bnd.spkB bnd.pqspkB hBundlesMem
  cases hFindS : st_cli.sessions.find? (fun e => e.sid == sid) with
  | none =>
    have hf := (List.find?_eq_none.mp hFindS) sEntry hsEntry_mem; simp [hsEntry_sid] at hf
  | some sFound =>
    have hsFound_mem := List.mem_of_find?_eq_some hFindS
    have hsFound_sid : sFound.sid = sid := by have hp := List.find?_some hFindS; simpa using hp
    obtain ⟨hsFound_spk_eq, _, hsFound_hdr_eq⟩ :=
      hInv.sessions_uniq sFound sEntry hsFound_mem hsEntry_mem (hsFound_sid.trans hsEntry_sid.symm)
    cases hFindB : st_cli.spkBundles.find? (fun (idx, _) => idx == (u_resp.val, j_resp.val)) with
    | none =>
      have hf := (List.find?_eq_none.mp hFindB) ((u_resp.val, j_resp.val), bResp) hbResp_mem
      simp at hf
    | some bp =>
      rcases bp with ⟨idxFound, respSpk0⟩
      have hresp_mem0 := List.mem_of_find?_eq_some hFindB
      have hidx_eq : idxFound = (u_resp.val, j_resp.val) := by
        have hp := List.find?_some hFindB; simpa using hp
      subst hidx_eq
      obtain ⟨_, hresp_spk_eq, hresp_pqspk_eq, _, _, _⟩ :=
        hInv.spk_uniq _ _ respSpk0 bResp hresp_mem0 hbResp_mem rfl
      refine ⟨sFound, respSpk0, ?_⟩; dsimp only
      have hFresh_e2e : SignalPqxdh.isKeyIndSessionTestable st_e2e sid = true := by
        rw [eq_cliReplaceSpkBundles_of_cliKeyIndStateRel hSt,
          isFreshKeyIndSession_cliReplaceSpkBundles]; exact hFresh
      have hFindS_e2e : st_e2e.sessions.find? (fun e => e.sid == sid) = some sFound := by
        rw [← hSt.sessions_eq, hFindS]
      have hFindB_e2e_ex : ∃ respSpk_e2e,
          st_e2e.spkBundles.find? (fun (idx, _) => idx == (u_resp.val, j_resp.val)) =
            some ((u_resp.val, j_resp.val), respSpk_e2e) ∧
          CliSpkBundleRel ((u_resp.val, j_resp.val), respSpk0)
            ((u_resp.val, j_resp.val), respSpk_e2e) := by
        rcases find_cliSpkBundles_rel_of_forall2 hSt.spkBundles_rel (u_resp.val, j_resp.val) with
          ⟨hnone1, _⟩ | ⟨⟨idx₁, b₁⟩, ⟨idx₂, respSpk_e2e⟩, hsome1, hsome2, hRelB⟩
        · have h1 : st_cli.spkBundles.find? (fun x => x.1 == (u_resp.val, j_resp.val)) =
              some ((u_resp.val, j_resp.val), respSpk0) := hFindB
          rw [hnone1] at h1; cases h1
        · have h1 : st_cli.spkBundles.find? (fun x => x.1 == (u_resp.val, j_resp.val)) =
              some ((u_resp.val, j_resp.val), respSpk0) := hFindB
          rw [hsome1] at h1; simp only [Option.some.injEq, Prod.mk.injEq] at h1
          rcases h1 with ⟨rfl, rfl⟩
          have hidx₂ : idx₂ = (u_resp.val, j_resp.val) := hRelB.1.symm
          subst hidx₂; exact ⟨respSpk_e2e, hsome2, hRelB⟩
      rcases hFindB_e2e_ex with ⟨respSpk_e2e, hFindB_e2e, hRelB⟩
      refine ⟨hsFound_mem, hsFound_sid, hsFound_spk_eq.trans hsEntry_spk,
        hsFound_hdr_eq.trans hsEntry_hdr, hresp_mem0, rfl,
        hresp_spk_eq.trans hbResp_spk.symm, hresp_pqspk_eq.trans hbResp_pqspk.symm,
        ?_, ?_, ?_, ?_, ?_⟩
      · unfold SignalPqxdh.pqxdhKeyIndImpl
        simp [hFresh, hFindS, hSt.secb_cli, StateT.run_bind, StateT.run_set, StateT.run_pure]
      · change ((SignalPqxdh.pqxdhKeyIndImpl false S P (.testSession sid)).run st_e2e) = _
        unfold SignalPqxdh.pqxdhKeyIndImpl
        simp [hFresh_e2e, hFindS_e2e, hSt.secb_e2e, StateT.run_bind, StateT.run_set, StateT.run_pure]
      · unfold SignalPqxdh.pqxdhKeyIndImpl
        simp [hFindB, StateT.run_bind, StateT.run_set, StateT.run_pure]
      · change ((SignalPqxdh.pqxdhKeyIndImpl false S P (.revealSpkSk u_resp j_resp)).run _) = _
        unfold SignalPqxdh.pqxdhKeyIndImpl; rw [hRelB.2.1]
        simp [hFindB_e2e, StateT.run_bind, StateT.run_set, StateT.run_pure]
      · refine {
          secb_cli := hSt.secb_cli, secb_e2e := hSt.secb_e2e, principals_eq := hSt.principals_eq
          spkBundles_rel := forall2_cliSpkBundles_map_reveal hSt.spkBundles_rel (u_resp.val, j_resp.val)
          opkEntries_eq := hSt.opkEntries_eq, sessions_eq := by dsimp only; rw [hSt.sessions_eq]
          respSessions_eq := hSt.respSessions_eq, usedRecvOPK_eq := hSt.usedRecvOPK_eq
          usedRecvNoOPK_eq := hSt.usedRecvNoOPK_eq, usedKyberTriples_eq := hSt.usedKyberTriples_eq
          roCache_eq := hSt.roCache_eq, advKeys_eq := hSt.advKeys_eq
          tested_spkRevealed := fun s' hs' htest' => ?_, resp_not_tested := hSt.resp_not_tested }
        dsimp only at hs' ⊢; rw [List.mem_map] at hs'
        rcases hs' with ⟨s, hs_mem, hs_eq⟩
        by_cases hsid_b : (s.sid == sid) = true
        · simp only [hsid_b, ↓reduceIte] at hs_eq; subst hs_eq
          have hsid_s : s.sid = sid := beq_iff_eq.mp hsid_b
          obtain ⟨hs_spk, _, _⟩ :=
            hInv.sessions_uniq s sFound hs_mem hsFound_mem (hsid_s.trans hsFound_sid.symm)
          have hpk_eq : s.peerSpkPk = respSpk0.spkPk :=
            hs_spk.trans ((hsFound_spk_eq.trans hsEntry_spk).trans
              (hresp_spk_eq.trans hbResp_spk.symm).symm)
          refine ⟨?_, ?_⟩
          · unfold SignalPqxdh.isSpkRevealed; rw [List.any_eq_true]
            refine ⟨((u_resp.val, j_resp.val), { respSpk0 with revealed := true }), ?_, by simp [hpk_eq]⟩
            rw [List.mem_map]; exact ⟨((u_resp.val, j_resp.val), respSpk0), hresp_mem0, by simp⟩
          · unfold SignalPqxdh.isSpkRevealed; rw [List.any_eq_true]
            have he2e_mem := List.mem_of_find?_eq_some hFindB_e2e
            simp only [CliSpkBundleRel] at hRelB
            refine ⟨((u_resp.val, j_resp.val), { respSpk_e2e with revealed := true }), ?_,
              by simp [hpk_eq, hRelB]⟩
            rw [List.mem_map]; exact ⟨((u_resp.val, j_resp.val), respSpk_e2e), he2e_mem, by simp⟩
        · have hsid_f : (s.sid == sid) = false := Bool.eq_false_iff.mpr hsid_b
          simp only [hsid_f, Bool.false_eq_true, ↓reduceIte] at hs_eq; subst hs_eq
          obtain ⟨hRev1, hRev2⟩ := hSt.tested_spkRevealed s hs_mem htest'
          exact ⟨isSpkRevealed_map_reveal_of_true_cli P st_cli.spkBundles
              (u_resp.val, j_resp.val) s.peerSpkPk hRev1,
            isSpkRevealed_map_reveal_of_true_cli P st_e2e.spkBundles
              (u_resp.val, j_resp.val) s.peerSpkPk hRev2⟩

/-! ## Instance promotion and `CliStartStepBridgeProp` -/

private theorem find?_map_update_key_cli {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (target : α) (f : β → β) :
    (l.map (fun (idx, b) => if idx == target then (idx, f b) else (idx, b))).find?
      (fun (idx, _) => idx == target) =
    (l.find? (fun (idx, _) => idx == target)).map (fun (idx, b) => (idx, f b)) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨idx, b⟩; simp only [List.map_cons, List.find?_cons]
    cases h : (idx == target) <;> simp [h, ih]

private theorem fitU8VecStrict_of_length_cli {n : ℕ} {bs : SignalPqxdh.Bytes} (h : bs.length = n) :
    fitU8VecStrict n bs = some (u8Vec n bs) := fitU8VecStrict_some_iff.mpr ⟨h, rfl⟩

private theorem mkMeEStrict_of_length_cli (u : ℕ) {secIKA0 : SignalPqxdh.Bytes}
    (h : secIKA0.length = 32) :
    mkMeEStrict u secIKA0 = some { regId := BitVec.ofNat 32 u, idPriv := u8Vec 32 secIKA0 } := by
  unfold mkMeEStrict; rw [fitU8VecStrict_of_length_cli h]; rfl

private theorem mkKeysEStrict_of_lengths_cli (j : ℕ) (bEntry : SignalPqxdh.SpkBundleEntry)
    (opk? : Option (ℕ × SignalPqxdh.Bytes)) (hspk : bEntry.spkSk.length = 32)
    (hpqpk : bEntry.pqspkPk.length = 1568) (hpqsk : bEntry.pqspkSk.length = 3168)
    (hopk : ∀ o sk, opk? = some (o, sk) → sk.length = 32) :
    mkKeysEStrict j bEntry opk? =
      some { spkId := BitVec.ofNat 32 j, spkPriv := u8Vec 32 bEntry.spkSk
             opk := opk?.map (fun (o, sk) => (BitVec.ofNat 32 o, u8Vec 32 sk))
             kpkId := BitVec.ofNat 32 j, kpkPub := u8Vec 1568 bEntry.pqspkPk
             kpkSec := u8Vec 3168 bEntry.pqspkSk } := by
  unfold mkKeysEStrict
  rw [fitU8VecStrict_of_length_cli hspk, fitU8VecStrict_of_length_cli hpqpk,
      fitU8VecStrict_of_length_cli hpqsk]
  dsimp only [bind, Option.bind]
  cases hopk? : opk? with
  | none => rfl
  | some p =>
    rcases p with ⟨o, sk⟩; dsimp only [Option.map]
    rw [fitU8VecStrict_of_length_cli (hopk o sk hopk?)]

private theorem mkBundleEStrict_of_lengths_cli (u : ℕ) (bnd : SignalPqxdh.PreKeyBundleInput)
    (hspk : bnd.spkB.length = 32) (hspksig : bnd.spkSig.length = 64)
    (hpqpk : bnd.pqspkB.length = 1568) (hpqsig : bnd.pqspkSig.length = 64)
    (hik : bnd.ikB.length = 32) (hopk : ∀ id pk, bnd.opkB? = some (id, pk) → pk.length = 32) :
    mkBundleEStrict u bnd =
      some { regId := BitVec.ofNat 32 u
             opk := bnd.opkB?.map (fun (id, pk) => (BitVec.ofNat 32 id.toNat, u8Vec 32 pk))
             spkId := BitVec.ofNat 32 bnd.spkId.toNat, spkPub := u8Vec 32 bnd.spkB
             spkSig := u8Vec 64 bnd.spkSig, kpkId := BitVec.ofNat 32 bnd.pqspkId.toNat
             kpkPub := u8Vec 1568 bnd.pqspkB, kpkSig := u8Vec 64 bnd.pqspkSig
             idPub := u8Vec 32 bnd.ikB } := by
  unfold mkBundleEStrict
  rw [fitU8VecStrict_of_length_cli hspk, fitU8VecStrict_of_length_cli hspksig,
      fitU8VecStrict_of_length_cli hpqpk, fitU8VecStrict_of_length_cli hpqsig,
      fitU8VecStrict_of_length_cli hik]
  dsimp only [bind, Option.bind]
  cases hopk? : bnd.opkB? with
  | none => rfl
  | some p =>
    rcases p with ⟨id, pk⟩; dsimp only [Option.map]
    rw [fitU8VecStrict_of_length_cli (hopk id pk hopk?)]

private theorem tapeAliceCoins_appendInitiateTape
    (t_init : List.Vector (BitVec 8) 160) (t_dr : List.Vector (BitVec 8) 32) :
    SignalSession.tapeAliceCoins (appendInitiateTape t_init t_dr) = cliTape32AliceCoins t_dr := by
  rcases t_init with ⟨l1, h1⟩; rcases t_dr with ⟨l2, h2⟩
  change HKDF.bytesToKey32 (((l1 ++ l2).drop 160).take 32) = HKDF.bytesToKey32 l2
  rw [← h1, List.drop_left, List.take_of_length_le (by omega)]

private theorem bitvec_ofNat_uint32_ofNat_toNat (n : ℕ) :
    BitVec.ofNat 32 (UInt32.ofNat n).toNat = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq; simp [UInt32.toNat_ofNat]

private theorem keyPairOf_u8Vec_eq_keyPair_generate (C : Crypto) {bs : SignalPqxdh.Bytes}
    (h : bs.length = 32) :
    keyPairOf C (u8Vec 32 bs) = KeyPair.generate C (bhBytesWord bs) := by
  have hkv : Ratchet.keyToBytesVec32 (bhBytesWord bs) = u8Vec 32 bs := by
    have hlen : (ofU8 bs).length = 32 := by simp [ofU8, h]
    apply Subtype.ext
    exact (keyToBytes32_bytesToKey32 (ofU8 bs) hlen).trans (by simp [u8Vec, fitVec, hlen])
  dsimp only [keyPairOf, KeyPair.generate]; rw [hkv]

private theorem x25519_base_ne_zero_any (P : SignalPqxdh.Primitives)
    (hWF : SignalPqxdh.WellFormedPrimitivesδ P) (a b : SignalPqxdh.Bytes) :
    P.x25519 a (P.x25519Base b) ≠ List.replicate 32 0 := by
  rw [← hWF.x25519_clamp, ← hWF.x25519Base_clamp]
  exact hWF.x25519_base_ne_zero (SignalPqxdh.clampScalar25519 a) (SignalPqxdh.clampScalar25519 b)
    (SignalPqxdh.clampScalar25519_length a) (SignalPqxdh.clampScalar25519_length b)

private theorem x25519_clamp_pubKey_ne_zero (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W))
    (a b : List.Vector (BitVec 8) 32) :
    W.C.X (Ratchet.clampScalar a) (W.C.pubKey (Ratchet.clampScalar b)) ≠
      List.Vector.replicate 32 0#8 := by
  intro heq
  have hne := x25519_base_ne_zero_any
    (modelPrims X W) hP.toWellFormedPrimitivesδ (vecU8 a) (vecU8 b)
  dsimp only [modelPrims, blockLevelPrims] at hne
  rw [u8Vec_vecU8_eq, u8Vec_vecU8_eq, u8Vec_vecU8_eq, heq] at hne
  exact hne (by simp [vecU8, toU8, List.Vector.replicate, List.Vector.toList])

private theorem cliAdapterStepCoupled_of_tape32 {S : SignalPqxdh.Setup} {ℓ : ℕ} {α : Type}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {b : Bool} {qStart' : ℕ} {qs_rem' : ℕ → ℕ}
    (c_cli : ProbComp ((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S))
    (c_ad : ProbComp ((α × CliAdapterState S) × BHE2EDrvState S ℓ))
    (f_cli : List.Vector (BitVec 8) 32 → (α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S)
    (f_ad : BitVec 256 → (α × CliAdapterState S) × BHE2EDrvState S ℓ)
    (h_cli : c_cli = do
      let t_dr ← ($ᵗ List.Vector (BitVec 8) 32 : ProbComp (List.Vector (BitVec 8) 32))
      return f_cli t_dr)
    (h_ad : c_ad = do
      let ac ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      return f_ad ac)
    (hInv : ∀ t_dr : List.Vector (BitVec 8) 32,
      let ac := cliTape32AliceCoins t_dr
      (f_cli t_dr).1.1 = (f_ad ac).1.1 ∧
      CliAdapterDrvRel S ℓ X W b qStart' qs_rem'
        (f_cli t_dr).2 (f_cli t_dr).1.2 (f_ad ac).1.2 (f_ad ac).2) :
    cliAdapterStepCoupled X W b qStart' qs_rem' c_cli c_ad := by
  refine ⟨($ᵗ List.Vector (BitVec 8) 32 : ProbComp (List.Vector (BitVec 8) 32)) >>= fun t_dr =>
      pure (f_cli t_dr, f_ad (cliTape32AliceCoins t_dr)), ?_, ?_, ?_⟩
  · have hMap : (Prod.fst <$> (($ᵗ List.Vector (BitVec 8) 32 : ProbComp (List.Vector (BitVec 8) 32)) >>=
        fun t_dr => pure (f_cli t_dr, f_ad (cliTape32AliceCoins t_dr)))) =
      (($ᵗ List.Vector (BitVec 8) 32 : ProbComp (List.Vector (BitVec 8) 32)) >>=
        fun t_dr => pure (f_cli t_dr)) := by simp [map_eq_bind_pure_comp, bind_assoc]
    rw [hMap, h_cli]
  · have hMap : (Prod.snd <$> (($ᵗ List.Vector (BitVec 8) 32 : ProbComp (List.Vector (BitVec 8) 32)) >>=
        fun t_dr => pure (f_cli t_dr, f_ad (cliTape32AliceCoins t_dr)))) =
      (($ᵗ List.Vector (BitVec 8) 32 : ProbComp (List.Vector (BitVec 8) 32)) >>=
        fun t_dr => pure (f_ad (cliTape32AliceCoins t_dr))) := by simp [map_eq_bind_pure_comp, bind_assoc]
    rw [hMap, h_ad]
    simpa only [bind_assoc, pure_bind] using deq_cliTape32_aliceCoins.bind_left (fun ac => pure (f_ad ac))
  · intro x y hmem
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨t_dr, _, rfl, rfl⟩; exact hInv t_dr

private theorem cliPqInit_and_instRel_of_startDR {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) (hCli : CliSpecPqxdh run X W)
    (hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W)) (b : Bool) (q_rem : ℕ)
    {st2_cli : SignalPqxdh.KeyIndState S} {ds_cli' : ModelDriverState S ℓ}
    (hInv2 : CliAdapterKeyIndInv S (modelPrims X W) W st2_cli ds_cli')
    (sid : SignalPqxdh.SessionId S) (u_init u_resp : Fin S.N_id) (j_resp : Fin S.N_recv)
    (initSecIKA0 respSecIKA0 : SignalPqxdh.Bytes) (respSpk0 : SignalPqxdh.SpkBundleEntry)
    (opkOpt : Option (ℕ × SignalPqxdh.Bytes))
    (bnd : SignalPqxdh.PreKeyBundleInput) (hdr : SignalPqxdh.HandshakeHdr)
    (t_init : List.Vector (BitVec 8) 160) (t_dr : List.Vector (BitVec 8) 32)
    (ss : SignalPqxdh.Bytes) (dk : SignalPqxdh.DRKey)
    (hInitPrin : bhDrvSessionInitPrin? sid = some u_init)
    (htape_mem : (sid, u_init, bnd, t_init) ∈ ds_cli'.initTapes)
    (hfind_spk2 : st2_cli.spkBundles.find? (fun (idx, _) => idx == (u_resp.val, j_resp.val)) =
      some ((u_resp.val, j_resp.val), { respSpk0 with revealed := true }))
    (hinitSec_len : initSecIKA0.length = 32) (hrespSec_len : respSecIKA0.length = 32)
    (hspkSk_len : respSpk0.spkSk.length = 32) (hpqspkPk_len : respSpk0.pqspkPk.length = 1568)
    (hpqspkSk_len : respSpk0.pqspkSk.length = 3168)
    (hopk_sk_len : ∀ o sk, opkOpt = some (o, sk) → sk.length = 32)
    (hspkB_len : bnd.spkB.length = 32) (hspksig_len : bnd.spkSig.length = 64)
    (hpqspkB_len : bnd.pqspkB.length = 1568) (hpqsig_len : bnd.pqspkSig.length = 64)
    (hikB_len : bnd.ikB.length = 32)
    (hopk_pk_len : ∀ id pk, bnd.opkB? = some (id, pk) → pk.length = 32)
    (hikA_base : hdr.ikAPk = (modelPrims X W).x25519Base initSecIKA0)
    (hikA_pub : hdr.ikAPk = vecU8 (keyPairOf W.C (u8Vec 32 initSecIKA0)).publicKey.bytes)
    (hikB_base : bnd.ikB = (modelPrims X W).x25519Base respSecIKA0)
    (hikB_pub : bnd.ikB = vecU8 (keyPairOf W.C (u8Vec 32 respSecIKA0)).publicKey.bytes)
    (hspkB_base : bnd.spkB = (modelPrims X W).x25519Base respSpk0.spkSk)
    (hpqspkB_eq : bnd.pqspkB = respSpk0.pqspkPk)
    (hspkid_j : hdr.spkId = UInt32.ofNat j_resp.val)
    (hpqspkid_j : hdr.pqspkId = UInt32.ofNat j_resp.val)
    (hspkid_bnd : hdr.spkId = bnd.spkId) (hpqspkid_bnd : hdr.pqspkId = bnd.pqspkId)
    (hopkid_bnd : hdr.opkId? = bnd.opkB?.map Prod.fst)
    (hopk_match : (bnd.opkB? = none ∧ opkOpt = none) ∨
      (∃ opkId opkPk opkSk, bnd.opkB? = some (opkId, opkPk) ∧
        opkOpt = some (opkId.toNat, opkSk) ∧ opkPk = (modelPrims X W).x25519Base opkSk))
    (hsig_spk : (modelPrims X W).sigVerify bnd.ikB (SignalPqxdh.encodeEC bnd.spkB) bnd.spkSig = true)
    (hsig_kem : (modelPrims X W).sigVerify bnd.ikB (SignalPqxdh.encodeKEM bnd.pqspkB) bnd.pqspkSig = true)
    (henc : (modelPrims X W).kemEncaps bnd.pqspkB (tapeKemCoins t_init) = some (ss, hdr.kemCt))
    (hekA_base : hdr.ekAPk = (modelPrims X W).x25519Base (tapeEkASk t_init))
    (hikA_len : hdr.ikAPk.length = 32) (hekA_len : hdr.ekAPk.length = 32)
    (hkemCt_len : hdr.kemCt.length = 1568)
    (hdk_eq : dk = (modelPrims X W).hkdfDerive96 (SignalPqxdh.buildSecrets
      ((modelPrims X W).x25519 initSecIKA0 bnd.spkB)
      ((modelPrims X W).x25519 (tapeEkASk t_init) bnd.ikB)
      ((modelPrims X W).x25519 (tapeEkASk t_init) bnd.spkB)
      (bnd.opkB?.map (fun (_, opkPk) => (modelPrims X W).x25519 (tapeEkASk t_init) opkPk)) ss)) :
    let meA : LocalIdentity := { regId := BitVec.ofNat 32 u_init.val, idPriv := u8Vec 32 initSecIKA0 }
    let meB : LocalIdentity := { regId := BitVec.ofNat 32 u_resp.val, idPriv := u8Vec 32 respSecIKA0 }
    let keysB : ResponderPreKeySecrets :=
      { spkId := BitVec.ofNat 32 j_resp.val, spkPriv := u8Vec 32 respSpk0.spkSk,
        opk := opkOpt.map (fun (o, sk) => (BitVec.ofNat 32 o, u8Vec 32 sk)), kpkId := BitVec.ofNat 32 j_resp.val,
        kpkPub := u8Vec 1568 respSpk0.pqspkPk, kpkSec := u8Vec 3168 respSpk0.pqspkSk }
    let bundleE : PreKeyBundleFields :=
      { regId := BitVec.ofNat 32 u_resp.val,
        opk := bnd.opkB?.map (fun (id, pk) => (BitVec.ofNat 32 id.toNat, u8Vec 32 pk)),
        spkId := BitVec.ofNat 32 bnd.spkId.toNat, spkPub := u8Vec 32 bnd.spkB, spkSig := u8Vec 64 bnd.spkSig,
        kpkId := BitVec.ofNat 32 bnd.pqspkId.toNat, kpkPub := u8Vec 1568 bnd.pqspkB,
        kpkSig := u8Vec 64 bnd.pqspkSig, idPub := u8Vec 32 bnd.ikB }
    let inst : BHAdapterInstMeta S :=
      { sid := sid, u_resp := u_resp, hdr := hdr, idB := bnd.ikB, bobRemoteRegId := bhInitRegId sid }
    let ac := cliTape32AliceCoins t_dr; let s := bhBytesWord respSpk0.spkSk; let kS := bhKeySOf dk ac
    let idA := bhIdKeyOf hdr.ikAPk; let idB := bhIdKeyOf bnd.ikB
    let P_v1 := paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) idA idB
    let sch_m := sessionSchemeFixedSpk P_v1 ℓ s; let gs_m := SM.initState sch_m.sendPart kS b
    let stA0 := binStateOfUnderExtras (fun _ => bhInstExtrasA inst) (gs_m.st .A)
    let stB0 : BinState := { party := .B, bytes := [], epochs := { epoch := 0, chains := [] } }
    let bi0 : ModelDriverInstance S ℓ :=
      { sid := sid, hdr := hdr, idBBytes := bnd.ikB, respSlot := (u_resp, j_resp),
        meA := meA, meB := meB, keysB := keysB, stA0 := stA0, stB0 := stB0, gs := none }
    let scheme := cliPqScheme run W ℓ bi0 (cliPqSigsOf st2_cli bi0) stA0 stB0
    let bi : ModelDriverInstance S ℓ := { bi0 with gs := some (SM.initState scheme.sendPart () b) }
    let d : BHModelInst S ℓ := { sid := sid, hdr := hdr, idA := idA, idB := idB, spkCoins := s, gs := some gs_m }
    let im0 : ModelDriverInstanceMeta S := { respPrin := some u_resp, respSpkIdx := some j_resp, instOpkId? := bnd.opkB?.map Prod.fst }
    let im_e2e : ModelDriverInstanceMeta S := { respPrin := some u_resp, respSpkIdx := some j_resp, instOpkId? := hdr.opkId? }
    let dA : PqParty :=
      { party := .A, me := meA, peerId := some (bhIdKeyOf bnd.ikB), session := none,
        signed := [], oneTime := [], kyberOneTime := [], kyberLastResort := [] }
    cliPqInit run W dA bundleE (appendInitiateTape t_init t_dr) = some stA0 ∧
      CliAdapterInstRel X W q_rem st2_cli ds_cli' bi d im0 im_e2e inst false := by
  intro meA meB keysB bundleE inst ac s kS idA idB P_v1 sch_m gs_m stA0 stB0 bi0 scheme bi d
    im0 im_e2e dA
  set P := modelPrims X W
  have hRegIdA : bhInitRegId sid = BitVec.ofNat 32 u_init.val := by unfold bhInitRegId; rw [hInitPrin]
  have hidA_pub : idA = ⟨(keyPairOf W.C meA.idPriv).publicKey⟩ := by
    dsimp only [idA, meA]; rw [hikA_pub]; unfold bhIdKeyOf; simp [u8Vec_vecU8_eq]
  have hidB_pub : idB = ⟨(keyPairOf W.C meB.idPriv).publicKey⟩ := by
    dsimp only [idB, meB]; rw [hikB_pub]; unfold bhIdKeyOf; simp [u8Vec_vecU8_eq]
  have hidB_bnd : (⟨⟨bundleE.idPub⟩⟩ : IdentityKey) = idB := rfl
  have hextrasB : bhInstExtrasB inst = bhRecvExtrasOfHdr meA meB hdr := by
    unfold bhInstExtrasB bhRecvExtrasOfHdr
    dsimp only [inst, meA, meB, PublicKey.serialize, djbKey, djbType]; rw [hRegIdA]; rfl
  have hextrasA : bhInstExtrasA inst =
      initiatorRecordExtras meA bundleE ⟨u8Vec 32 hdr.ekAPk⟩ (u8Vec 1568 hdr.kemCt) := by
    unfold bhInstExtrasA initiatorRecordExtras; dsimp only [inst, meA, bundleE]
    have hopk_map : hdr.opkId?.map (fun id => BitVec.ofNat 32 id.toNat) =
        (bnd.opkB?.map (fun (id, pk) => (BitVec.ofNat 32 id.toNat, u8Vec 32 pk))).map Prod.fst := by
      rw [hopkid_bnd]; cases bnd.opkB? <;> rfl
    rw [hRegIdA, hspkid_bnd, hpqspkid_bnd, hopk_map]; rfl
  have hmeA_eq := mkMeEStrict_of_length_cli u_init.val hinitSec_len
  have hmeB_eq := mkMeEStrict_of_length_cli u_resp.val hrespSec_len
  have hbundleE_eq := mkBundleEStrict_of_lengths_cli u_resp.val bnd
    hspkB_len hspksig_len hpqspkB_len hpqsig_len hikB_len hopk_pk_len
  have hdh1_noz : P.x25519 initSecIKA0 bnd.spkB ≠ List.replicate 32 0 :=
    hspkB_base ▸ x25519_base_ne_zero_any P hP.toWellFormedPrimitivesδ _ _
  have hdh2_noz : P.x25519 (tapeEkASk t_init) bnd.ikB ≠ List.replicate 32 0 :=
    hikB_base ▸ x25519_base_ne_zero_any P hP.toWellFormedPrimitivesδ _ _
  have hdh3_noz : P.x25519 (tapeEkASk t_init) bnd.spkB ≠ List.replicate 32 0 :=
    hspkB_base ▸ x25519_base_ne_zero_any P hP.toWellFormedPrimitivesδ _ _
  have hdh4_noz : SignalPqxdh.dhOptNonZero
      (bnd.opkB?.map (fun (_, opkPk) => P.x25519 (tapeEkASk t_init) opkPk)) = true := by
    rcases hopk_match with ⟨hnone_b, _⟩ | ⟨opkId, opkPk, opkSk, hsome_b, _, hopk_base⟩
    · simp [hnone_b, SignalPqxdh.dhOptNonZero]
    · rw [hsome_b, hopk_base]; dsimp only [Option.map, SignalPqxdh.dhOptNonZero]
      exact bne_iff_ne.mpr (x25519_base_ne_zero_any P hP.toWellFormedPrimitivesδ _ _)
  have hhdr_struct : inst.hdr =
      { ikAPk := P.x25519Base initSecIKA0, ekAPk := P.x25519Base (tapeEkASk t_init)
        spkId := bnd.spkId, opkId? := bnd.opkB?.map Prod.fst
        pqspkId := bnd.pqspkId, kemCt := hdr.kemCt } := by
    dsimp only [inst]; cases hdr
    dsimp only at hikA_base hekA_base hspkid_bnd hopkid_bnd hpqspkid_bnd ⊢
    rw [hikA_base, hekA_base, hspkid_bnd, hopkid_bnd, hpqspkid_bnd]
  have hdA_eq : dA = cliPqDirA bi := rfl
  have hInit := cliPqInit_eq_some_binStateOfX hCli dA (hdA_eq ▸ wfPq_cliPqDirA W bi) u_init u_resp
    initSecIKA0 respSpk0.spkSk bnd meA bundleE t_init t_dr ss hdr.kemCt inst
    rfl rfl rfl rfl hmeA_eq hbundleE_eq hRegIdA rfl hsig_spk hsig_kem henc
    hkemCt_len hspkSk_len hspkB_base hdh1_noz hdh2_noz hdh3_noz hdh4_noz
    (x25519_clamp_pubKey_ne_zero X W hP) hhdr_struct
  dsimp only at hInit
  have hgA0_eq : (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K)
      ⟨(keyPairOf W.C meA.idPriv).publicKey⟩ ⟨⟨bundleE.idPub⟩⟩).initA
      (initKeysOfSampled (bhBytesWord respSpk0.spkSk) (bhKeySOf (P.hkdfDerive96 (SignalPqxdh.buildSecrets
        (P.x25519 initSecIKA0 bnd.spkB) (P.x25519 (tapeEkASk t_init) bnd.ikB)
        (P.x25519 (tapeEkASk t_init) bnd.spkB)
        (bnd.opkB?.map (fun (_, opkPk) => P.x25519 (tapeEkASk t_init) opkPk)) ss))
        (SignalSession.tapeAliceCoins (appendInitiateTape t_init t_dr)))) = gs_m.st .A := by
    rw [← hdk_eq, tapeAliceCoins_appendInitiateTape, ← hidA_pub, hidB_bnd]; rfl
  rw [hgA0_eq] at hInit; obtain ⟨his, hcli, _, hsteps⟩ := hInit; refine ⟨hcli, ?_⟩
  have hresp2_mem : ((u_resp.val, j_resp.val), { respSpk0 with revealed := true }) ∈
      st2_cli.spkBundles := List.mem_of_find?_eq_some hfind_spk2
  have hpartyA : (gs_m.st .A).party = .A := (initiateState_aligned_and_epochs his).2.2.1
  have halA : (gs_m.st .A).Aligned := (initiateState_aligned_and_epochs his).1
  have hpqA : (gs_m.st .A).session.pqRatchetState.length ≤ 640 := initiateState_pqLength_le his
  have hsteps_bi : PqSteps X W 1 (cliPqDirA bi)
      { cliPqDirA bi with session := some (bhInstExtrasA inst, gs_m.st .A) } := hdA_eq ▸ hsteps
  have hwfA := wfPq_of_pqSteps_cliPqDirA hsteps_bi (by omega)
  have ⟨hpendA, hlocA⟩ :
      (gs_m.st .A).session.pendingPreKey = true ∧ (gs_m.st .A).session.localIdentity = d.idA := by
    dsimp only [gs_m, sch_m, SM.initState, SMSchemeR.sendPart, sessionSchemeFixedSpk,
      Params.initA, P_v1, paramsIdsWithSpqr, d]
    unfold initializeInitiatorSession; dsimp only [bind, Except.bind, pure, Except.pure]
    rcases rootCreateChain W.C (initKeysOfSampled s kS).rootKey
        (KeyPair.generate W.C (initKeysOfSampled s kS).bobSpkCoins).publicKey
        (KeyPair.generate W.C (initKeysOfSampled s kS).aliceRatchetCoins).privateKey with
      _ | ⟨_, _⟩ <;> exact ⟨rfl, rfl⟩
  refine {
    im_eq := by dsimp [im0, im_e2e]; rw [hopkid_bnd]
    sid_eq := ⟨rfl, rfl⟩, hdr_eq := ⟨rfl, rfl⟩, idB_eq := ⟨rfl, rfl, rfl⟩
    respSlot_eq := rfl, respMeta_eq := ⟨rfl, rfl⟩
    regIdA_eq := ⟨hRegIdA.symm, rfl⟩, regIdB_eq := rfl
    aliceAcked_false := rfl, idA_pub_eq := hidA_pub, idB_pub_eq := hidB_pub
    extrasB_eq := hextrasB, stB0_empty := rfl
    resp_bundle_rel := ⟨{ respSpk0 with revealed := true }, hresp2_mem, rfl,
      keyPairOf_u8Vec_eq_keyPair_generate W.C hspkSk_len, rfl,
      by unfold cliPqSigsOf; dsimp only [bi, bi0]; rw [hfind_spk2]⟩
    handshake_rel := ?_, gs_rel := ?_ }
  · refine ⟨bundleE, dk, ac, u_init, bnd, t_init, ss, hextrasA, htape_mem, ?_,
      fun _ _ _ hgm _ _ => by cases hgm; rfl⟩
    intro bEntry hbEntry_mem
    obtain ⟨hsk_u, _, hpqpk_u, hpqsk_u, _, _⟩ :=
      hInv2.spk_uniq _ _ bEntry { respSpk0 with revealed := true } hbEntry_mem hresp2_mem rfl
    dsimp only at hsk_u hpqpk_u hpqsk_u
    have hpqB_b : bnd.pqspkB = bEntry.pqspkPk := hpqspkB_eq.trans hpqpk_u.symm
    refine ⟨hpqB_b, hpqB_b ▸ henc, fun hdec_ss inner => ?_⟩; dsimp only
    set m := bhExpectedPreKeyMsg bi.meA.regId bi.hdr inner
    have hm_spkId : m.spkId = bi.keysB.spkId := by
      dsimp only [m, bhExpectedPreKeyMsg, bi, bi0, keysB]; rw [hspkid_j]
      exact bitvec_ofNat_uint32_ofNat_toNat j_resp.val
    have hm_kpkId : m.kpkId = bi.keysB.kpkId := by
      dsimp only [m, bhExpectedPreKeyMsg, bi, bi0, keysB]; rw [hpqspkid_j]
      exact bitvec_ofNat_uint32_ofNat_toNat j_resp.val
    refine ⟨hm_spkId, hm_kpkId, ?_⟩
    have hkeysB_b : mkKeysEStrict j_resp.val bEntry opkOpt = some bi.keysB := by
      rw [mkKeysEStrict_of_lengths_cli j_resp.val bEntry opkOpt
        (hsk_u ▸ hspkSk_len) (hpqpk_u ▸ hpqspkPk_len) (hpqsk_u ▸ hpqspkSk_len) hopk_sk_len]
      dsimp only [bi, bi0, keysB]; rw [hsk_u, hpqpk_u, hpqsk_u]
    have hm_opkId : m.opkId = bi.keysB.opk.map Prod.fst := by
      dsimp only [m, bhExpectedPreKeyMsg, bi, bi0, keysB]; rw [hopkid_bnd]
      rcases hopk_match with ⟨hnone_b, hnone_o⟩ | ⟨_, _, _, hsome_b, hsome_o, _⟩
      · simp [hnone_b, hnone_o]
      · simp [hsome_b, hsome_o]
    have hm_base : vecU8 m.baseKey = hdr.ekAPk := vecU8_u8Vec_of_len hekA_len
    have hm_idA : vecU8 m.idPub = hdr.ikAPk := vecU8_u8Vec_of_len hikA_len
    have hm_kyber : vecU8 m.kyberCt = hdr.kemCt := vecU8_u8Vec_of_len hkemCt_len
    have hcanon : P.isCanonical (vecU8 m.baseKey) = true := by
      rw [hm_base, hekA_base]; exact hP.canon_base (tapeEkASk t_init)
    have hdh1_eq : P.x25519 bEntry.spkSk (vecU8 m.idPub) = P.x25519 initSecIKA0 bnd.spkB := by
      rw [hsk_u, hm_idA, hikA_base, hspkB_base, hP.x25519_comm]
    have hdh2_eq : P.x25519 respSecIKA0 (vecU8 m.baseKey) = P.x25519 (tapeEkASk t_init) bnd.ikB := by
      rw [hm_base, hekA_base, hikB_base, hP.x25519_comm]
    have hdh3_eq : P.x25519 bEntry.spkSk (vecU8 m.baseKey) = P.x25519 (tapeEkASk t_init) bnd.spkB := by
      rw [hsk_u, hm_base, hekA_base, hspkB_base, hP.x25519_comm]
    have hdh4_eq : opkOpt.map (fun (_, opkSk) => P.x25519 opkSk (vecU8 m.baseKey)) =
        bnd.opkB?.map (fun (_, opkPk) => P.x25519 (tapeEkASk t_init) opkPk) := by
      rcases hopk_match with ⟨hnone_b, hnone_o⟩ | ⟨_, _, _, hsome_b, hsome_o, hopk_b⟩
      · simp [hnone_b, hnone_o]
      · simp only [hsome_b, hsome_o, Option.map]; rw [hm_base, hekA_base, hopk_b, hP.x25519_comm]
    have hacc := (acceptKeys_of_mkKeysEStrict X W u_resp.val j_resp.val respSecIKA0
      bEntry opkOpt bi.meB bi.keysB m ss hmeB_eq hkeysB_b hm_opkId hcanon
      (hdh1_eq ▸ hdh1_noz) (hdh2_eq ▸ hdh2_noz) (hdh3_eq ▸ hdh3_noz)
      (hdh4_eq ▸ hdh4_noz) (hm_kyber.symm ▸ hdec_ss)).1
    dsimp only at hacc; rw [hdh1_eq, hdh2_eq, hdh3_eq, hdh4_eq, ← hdk_eq] at hacc; exact hacc
  · dsimp only [bi, bi0, d, im0]
    rw [ite_eq_right_iff.mpr (fun h => False.elim (Bool.noConfusion h))]
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, List.Forall₂.nil, hpendA, rfl,
      hlocA, fun _ => rfl, fun _ => Nat.zero_le 1, fun _ => rfl,
      fun _ _ hm => False.elim (List.not_mem_nil hm),
      fun _ _ hm => False.elim (List.not_mem_nil hm),
      fun _ => rfl, fun h => False.elim (Bool.noConfusion h),
      by unfold bhBinStateOfParty; rw [hpartyA]; rfl,
      fun _ => rfl, fun h => False.elim (Bool.noConfusion h),
      hpartyA, rfl, ⟨hwfA.1, by change 0 < 2 ^ 25; decide, halA, by omega⟩,
      fun h => False.elim (Bool.noConfusion h)⟩

private theorem cliDrvStart_step_succ {Pt : Type}
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hCli : CliSpecPqxdh run X W) (hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W))
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {b : Bool} {n : ℕ} {qs_rem : ℕ → ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b n qs_rem st_cli ds_cli σ_ad σ_e2e)
    (sid : SignalPqxdh.SessionId S) :
    cliAdapterStepCoupled X W b (n + 1) qs_rem
      (((cliDrvStart S ℓ (modelPrims X W) run W (fun _ _ _ _ _ => some b) sid).run
          ds_cli).run st_cli)
      (((cliComposedAdapterImplWith (modelPrims X W)
          (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S (modelPrims X W))
          W.C W.Q.K qep decT encT (.inl (.inr (.startDR sid)))).run σ_ad).run σ_e2e) := by
  set P := modelPrims X W
  rw [cliComposedAdapterImplWith_startDR_run]
  have hGuardEq := bhDrvGuard_eq_bhE2EGuard_of_cliRel hRel sid
  rcases hG : bhDrvGuard ds_cli sid with _ | ⟨hdr, bnd, ⟨u_resp, j_resp⟩⟩
  · have hG_e2e : bhE2EGuard σ_e2e sid = none := hGuardEq.symm.trans hG
    have h_cli : (((cliDrvStart S ℓ P run W (fun _ _ _ _ _ => some b) sid).run ds_cli).run st_cli) =
        pure ((none, ds_cli), st_cli) := by
      unfold cliDrvStart; rw [stateT_run_get_bind_cli]; simp [hG]
    rw [h_cli]; unfold adapterStartDRRun compositionLocalStart; simp only [hG_e2e, pure_bind]
    exact cliAdapterStepCoupled_ret none st_cli ds_cli σ_ad σ_e2e (hRel.mono_qStart (Nat.le_succ n))
  · have hG_e2e : bhE2EGuard σ_e2e sid = some (hdr, bnd, (u_resp, j_resp)) := hGuardEq.symm.trans hG
    have hMirror := stepMirrorGuard_of_bhDrvGuard_eq_some (ℓ := ℓ) decT encT
      ds_cli σ_ad.2.2 sid hdr bnd u_resp j_resp hRel.base_ad_eq hG
    by_cases hFresh : SignalPqxdh.isKeyIndSessionTestable st_cli sid = true
    · obtain ⟨hsends, hbundles, hspkid_j, hpqspkid_j, hprins, hopk_ok⟩ := bhDrvGuard_eq_some_facts hG
      obtain ⟨sFound, respSpk0, hsFound_mem, hsFound_sid, hsFound_spk, hsFound_hdr,
              hresp0_mem, hFindB, hresp0_spk, hresp0_pqspk,
              htest_cli, htest_e2e, hrev_cli, hrev_e2e, hSt2⟩ :=
        testSession_and_revealSpk_of_guard_some hRel.st_rel hRel.ki_inv hG hFresh
      have hsFound_wf := hRel.ki_inv.sessions_wf sFound hsFound_mem
      have hresp0_wf := hRel.ki_inv.spk_wf (u_resp.val, j_resp.val) respSpk0 hresp0_mem
      obtain ⟨_, ⟨u_init₀, t_init₀, uEntry₀, hinit_mem₀, huEntry₀_mem, hhdr_ikA₀⟩,
              hspkid_bnd, hpqspkid_bnd, hopkid_bnd,
              hspksig_len, hpqsig_len, hikA_len, hekA_len, hkemCt_len, hsig_both, hDer⟩ :=
        hRel.ki_inv.sends_wf sid bnd hdr hsends
      simp only [Bool.and_eq_true] at hsig_both; rcases hsig_both with ⟨hsig_spk, hsig_kem⟩
      rcases hfind_initTape : ds_cli.initTapes.find? (fun (s, _, _, _) => s == sid) with
        _ | ⟨sid_t, u_init, bnd_t, t_init⟩
      · exfalso; exact absurd hinit_mem₀ (by
          have hf := (List.find?_eq_none.mp hfind_initTape) (sid, u_init₀, bnd, t_init₀)
          intro hm; exact by simpa using hf hm)
      have htape_mem := List.mem_of_find?_eq_some hfind_initTape
      have hsid_t : sid_t = sid := by have hp := List.find?_some hfind_initTape; simpa using hp
      subst sid_t
      obtain ⟨hu_eq, hbnd_t_eq, ht_eq⟩ :=
        hRel.ki_inv.initTapes_uniq sid u_init bnd_t t_init u_init₀ bnd t_init₀ htape_mem hinit_mem₀
      subst u_init₀ bnd_t t_init₀
      have htape_wf := hRel.ki_inv.initTapes_wf sid u_init bnd t_init htape_mem
      rcases hfind_initPrin : st_cli.principals.find? (fun (idx, _) => idx == u_init.val) with
        _ | ⟨idx_i, initPrinEntry⟩
      · exfalso; have hf := (List.find?_eq_none.mp hfind_initPrin) (u_init.val, uEntry₀) huEntry₀_mem
        simp at hf
      have hinitPrin_mem := List.mem_of_find?_eq_some hfind_initPrin
      have hidx_i : idx_i = u_init.val := by have hp := List.find?_some hfind_initPrin; simpa using hp
      subst idx_i
      have hinitPrin_wf := hRel.ki_inv.prins_wf u_init.val initPrinEntry hinitPrin_mem
      have hinitPrin_uniq :=
        hRel.ki_inv.prins_uniq _ _ initPrinEntry uEntry₀ hinitPrin_mem huEntry₀_mem rfl
      have hikA_base : hdr.ikAPk = P.x25519Base initPrinEntry.secIKA0 := by
        rw [hhdr_ikA₀, ← hinitPrin_uniq.2.1, hinitPrin_wf.2.1]
      have hikA_pub :
          hdr.ikAPk = vecU8 (keyPairOf W.C (u8Vec 32 initPrinEntry.secIKA0)).publicKey.bytes := by
        rw [hhdr_ikA₀, ← hinitPrin_uniq.2.1, hinitPrin_wf.2.2.1]
      obtain ⟨e_resp, he_resp_mem, hikB_eq⟩ := hRel.ki_inv.ds_prins u_resp bnd.ikB hprins
      rcases hfind_respPrin : st_cli.principals.find? (fun (idx, _) => idx == u_resp.val) with
        _ | ⟨idx_r, respPrinEntry⟩
      · exfalso; have hf := (List.find?_eq_none.mp hfind_respPrin) (u_resp.val, e_resp) he_resp_mem
        simp at hf
      have hrespPrin_mem := List.mem_of_find?_eq_some hfind_respPrin
      have hidx_r : idx_r = u_resp.val := by have hp := List.find?_some hfind_respPrin; simpa using hp
      subst idx_r
      have hrespPrin_wf := hRel.ki_inv.prins_wf u_resp.val respPrinEntry hrespPrin_mem
      have hrespPrin_uniq :=
        hRel.ki_inv.prins_uniq _ _ respPrinEntry e_resp hrespPrin_mem he_resp_mem rfl
      have hikB_base : bnd.ikB = P.x25519Base respPrinEntry.secIKA0 := by
        rw [hikB_eq, ← hrespPrin_uniq.2.1, hrespPrin_wf.2.1]
      have hikB_pub :
          bnd.ikB = vecU8 (keyPairOf W.C (u8Vec 32 respPrinEntry.secIKA0)).publicKey.bytes := by
        rw [hikB_eq, ← hrespPrin_uniq.2.1, hrespPrin_wf.2.2.1]
      have hikB_len : bnd.ikB.length = 32 := by
        rw [hikB_eq, ← hrespPrin_uniq.2.1]; exact hrespPrin_wf.2.2.2.1
      have hspkB_len : bnd.spkB.length = 32 := hresp0_spk ▸ hresp0_wf.2.2.2.1
      have hpqspkB_len : bnd.pqspkB.length = 1568 := hresp0_pqspk ▸ hresp0_wf.2.2.2.2.1
      have hspkB_base : bnd.spkB = P.x25519Base respSpk0.spkSk := hresp0_spk.symm.trans hresp0_wf.2.1
      obtain ⟨ss, henc, hekA_base, hdk_eq⟩ :=
        hDer sid u_init bnd t_init sFound u_init.val initPrinEntry
          htape_mem rfl hsFound_mem hsFound_sid hinitPrin_mem rfl
      have hopk_lookup : ∃ opkOpt : Option (ℕ × SignalPqxdh.Bytes),
          (match hdr.opkId? with
           | none => some none
           | some opkId =>
             match st_cli.opkEntries.find?
                 (fun (idx, _) => idx == (u_resp.val, j_resp.val, opkId.toNat)) with
             | some (_, oe) => some (some (opkId.toNat, oe.opkSk))
             | none => none) = some opkOpt ∧
          (∀ o sk, opkOpt = some (o, sk) → sk.length = 32) ∧
          (∀ id pk, bnd.opkB? = some (id, pk) → pk.length = 32) ∧
          ((bnd.opkB? = none ∧ opkOpt = none) ∨
           (∃ opkId opkPk opkSk, bnd.opkB? = some (opkId, opkPk) ∧
             opkOpt = some (opkId.toNat, opkSk) ∧ opkPk = P.x25519Base opkSk)) := by
        rw [hopkid_bnd]; unfold bhBaseOpkOk at hopk_ok
        rcases hopk? : bnd.opkB? with _ | ⟨opkId, opkPk⟩
        · exact ⟨none, rfl, fun _ _ h => (by cases h), fun _ _ h => (by cases h), Or.inl ⟨rfl, rfl⟩⟩
        · rw [hopk?, List.any_eq_true] at hopk_ok
          rcases hopk_ok with ⟨⟨⟨u', j', o⟩, pk⟩, hopk_mem, hopk_pred⟩
          simp only [Bool.and_eq_true, beq_iff_eq] at hopk_pred
          rcases hopk_pred with ⟨⟨⟨⟨hu', hj'⟩, _⟩, ho_val⟩, hpk'⟩
          subst u' j' pk
          obtain ⟨oe₀, hoe₀_mem, hpk_eq⟩ := hRel.ki_inv.ds_opks (u_resp, j_resp, o) opkPk hopk_mem
          rw [ho_val] at hoe₀_mem
          rcases hfind_oe : st_cli.opkEntries.find?
              (fun (idx, _) => idx == (u_resp.val, j_resp.val, opkId.toNat)) with _ | ⟨idx_o, oe⟩
          · exfalso; have hf := (List.find?_eq_none.mp hfind_oe)
              ((u_resp.val, j_resp.val, opkId.toNat), oe₀) hoe₀_mem
            simp at hf
          have hoe_mem := List.mem_of_find?_eq_some hfind_oe
          have hidx_o : idx_o = (u_resp.val, j_resp.val, opkId.toNat) := by
            have hp := List.find?_some hfind_oe; simpa using hp
          subst idx_o
          have hoe_wf := hRel.ki_inv.opk_wf _ oe hoe_mem
          have hoe₀_wf := hRel.ki_inv.opk_wf _ oe₀ hoe₀_mem
          have hoe_uniq := hRel.ki_inv.opk_uniq _ _ oe oe₀ hoe_mem hoe₀_mem rfl
          dsimp only [Option.map]; rw [hfind_oe]
          exact ⟨some (opkId.toNat, oe.opkSk), rfl, fun _ sk hsk => (by cases hsk; exact hoe_wf.1),
            fun _ pk' hpk' => (by cases hpk'; rw [hpk_eq]; exact hoe₀_wf.2.2.2),
            Or.inr ⟨opkId, opkPk, oe.opkSk, rfl, rfl, (by rw [hpk_eq, ← hoe_uniq.2, hoe_wf.2.1])⟩⟩
      rcases hopk_lookup with ⟨opkOpt, hopk_eq, hopk_sk_len, hopk_pk_len, hopk_match⟩
      let target := (u_resp.val, j_resp.val)
      let st1_cli : SignalPqxdh.KeyIndState S :=
        { st_cli with sessions := st_cli.sessions.map (fun s => if s.sid == sid then { s with tested := true } else s) }
      let st1_e2e : SignalPqxdh.KeyIndState S :=
        { σ_e2e.st with sessions := σ_e2e.st.sessions.map (fun s => if s.sid == sid then { s with tested := true } else s) }
      let st2_cli : SignalPqxdh.KeyIndState S :=
        { st1_cli with spkBundles := st_cli.spkBundles.map (fun (idx, b0) =>
            if idx == target then (idx, { b0 with revealed := true }) else (idx, b0)) }
      let st2_e2e : SignalPqxdh.KeyIndState S :=
        { st1_e2e with spkBundles := σ_e2e.st.spkBundles.map (fun (idx, b0) =>
            if idx == target then (idx, { b0 with revealed := true }) else (idx, b0)) }
      have hfind_spk2 : st2_cli.spkBundles.find? (fun (idx, _) => idx == target) =
          some (target, { respSpk0 with revealed := true }) := by
        change (st_cli.spkBundles.map _).find? _ = _
        rw [find?_map_update_key_cli st_cli.spkBundles target (fun b0 => { b0 with revealed := true }), hFindB]; rfl
      let meA : LocalIdentity := { regId := BitVec.ofNat 32 u_init.val, idPriv := u8Vec 32 initPrinEntry.secIKA0 }
      let meB : LocalIdentity := { regId := BitVec.ofNat 32 u_resp.val, idPriv := u8Vec 32 respPrinEntry.secIKA0 }
      let keysB : ResponderPreKeySecrets :=
        { spkId := BitVec.ofNat 32 j_resp.val, spkPriv := u8Vec 32 respSpk0.spkSk
          opk := opkOpt.map (fun (o, sk) => (BitVec.ofNat 32 o, u8Vec 32 sk))
          kpkId := BitVec.ofNat 32 j_resp.val, kpkPub := u8Vec 1568 respSpk0.pqspkPk, kpkSec := u8Vec 3168 respSpk0.pqspkSk }
      let bundleE : PreKeyBundleFields :=
        { regId := BitVec.ofNat 32 u_resp.val
          opk := bnd.opkB?.map (fun (id, pk) => (BitVec.ofNat 32 id.toNat, u8Vec 32 pk))
          spkId := BitVec.ofNat 32 bnd.spkId.toNat, spkPub := u8Vec 32 bnd.spkB, spkSig := u8Vec 64 bnd.spkSig
          kpkId := BitVec.ofNat 32 bnd.pqspkId.toNat, kpkPub := u8Vec 1568 bnd.pqspkB
          kpkSig := u8Vec 64 bnd.pqspkSig, idPub := u8Vec 32 bnd.ikB }
      let inst : BHAdapterInstMeta S :=
        { sid := sid, u_resp := u_resp, hdr := hdr, idB := bnd.ikB, bobRemoteRegId := bhInitRegId sid }
      let s := bhBytesWord respSpk0.spkSk; let idA := bhIdKeyOf hdr.ikAPk; let idB := bhIdKeyOf bnd.ikB
      let P_v1 := paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) idA idB
      let sch_m := sessionSchemeFixedSpk P_v1 ℓ s
      let gs_m (ac : BitVec 256) := SM.initState sch_m.sendPart (bhKeySOf sFound.drKeyReal ac) b
      let stA0 (t_dr : List.Vector (BitVec 8) 32) :=
        binStateOfUnderExtras (fun _ => bhInstExtrasA inst) ((gs_m (cliTape32AliceCoins t_dr)).st .A)
      let stB0 : BinState := { party := .B, bytes := [], epochs := { epoch := 0, chains := [] } }
      let bi0 (t_dr : List.Vector (BitVec 8) 32) : ModelDriverInstance S ℓ :=
        { sid := sid, hdr := hdr, idBBytes := bnd.ikB, respSlot := (u_resp, j_resp),
          meA := meA, meB := meB, keysB := keysB, stA0 := stA0 t_dr, stB0 := stB0, gs := none }
      let bi (t_dr : List.Vector (BitVec 8) 32) : ModelDriverInstance S ℓ :=
        { bi0 t_dr with gs := some (SM.initState
            (cliPqScheme run W ℓ (bi0 t_dr) (cliPqSigsOf st2_cli (bi0 t_dr)) (stA0 t_dr) stB0).sendPart () b) }
      let im0 : ModelDriverInstanceMeta S := { respPrin := some u_resp, respSpkIdx := some j_resp, instOpkId? := bnd.opkB?.map Prod.fst }
      let im_e2e : ModelDriverInstanceMeta S := { respPrin := some u_resp, respSpkIdx := some j_resp, instOpkId? := hdr.opkId? }
      let ds_cli' (t_dr : List.Vector (BitVec 8) 32) : ModelDriverState S ℓ :=
        { ds_cli with bhInsts := ds_cli.bhInsts ++ [bi t_dr], instMeta := ds_cli.instMeta ++ [im0] }
      let d (ac : BitVec 256) : BHModelInst S ℓ :=
        { sid := sid, hdr := hdr, idA := idA, idB := idB, spkCoins := s, gs := some (gs_m ac) }
      let σ_e2e' (ac : BitVec 256) : BHE2EDrvState S ℓ :=
        { σ_e2e with st := st2_e2e, insts := σ_e2e.insts ++ [d ac], instMeta := σ_e2e.instMeta ++ [im_e2e] }
      let σ_ad' : CliAdapterState S := ((fun j => if j = σ_e2e.insts.length then some inst else σ_ad.1 j), σ_ad.2)
      have hInv2 : ∀ t_dr, CliAdapterKeyIndInv S P W st2_cli (ds_cli' t_dr) := fun _ =>
        cliAdapterKeyIndInv_of_test_and_revealSpk hRel.ki_inv sid target rfl rfl
      have hInitRel := fun t_dr =>
        cliPqInit_and_instRel_of_startDR run X W hCli hP b (qs_rem ds_cli.bhInsts.length)
          (hInv2 t_dr) sid u_init u_resp j_resp initPrinEntry.secIKA0 respPrinEntry.secIKA0
          respSpk0 opkOpt bnd hdr t_init t_dr ss sFound.drKeyReal htape_wf.2.2.1 htape_mem
          hfind_spk2 hinitPrin_wf.1 hrespPrin_wf.1 hresp0_wf.1 hresp0_wf.2.2.2.2.1
          hresp0_wf.2.2.2.2.2.1 hopk_sk_len hspkB_len hspksig_len hpqspkB_len hpqsig_len
          hikB_len hopk_pk_len hikA_base hikA_pub hikB_base hikB_pub hspkB_base hresp0_pqspk.symm
          hspkid_j hpqspkid_j hspkid_bnd hpqspkid_bnd hopkid_bnd hopk_match hsig_spk hsig_kem
          henc hekA_base hikA_len hekA_len hkemCt_len hdk_eq
      have hmeA_eq := mkMeEStrict_of_length_cli u_init.val hinitPrin_wf.1
      have hmeB_eq := mkMeEStrict_of_length_cli u_resp.val hrespPrin_wf.1
      have hkeysB_eq := mkKeysEStrict_of_lengths_cli j_resp.val { respSpk0 with revealed := true } opkOpt
        hresp0_wf.1 hresp0_wf.2.2.2.2.1 hresp0_wf.2.2.2.2.2.1 hopk_sk_len
      have hbundleE_eq := mkBundleEStrict_of_lengths_cli u_resp.val bnd
        hspkB_len hspksig_len hpqspkB_len hpqsig_len hikB_len hopk_pk_len
      have h_cli_eval :
          (((cliDrvStart S ℓ P run W (fun _ _ _ _ _ => some b) sid).run ds_cli).run st_cli) =
            (do let t_dr ← ($ᵗ List.Vector (BitVec 8) 32 : ProbComp (List.Vector (BitVec 8) 32))
                return ((some ds_cli.bhInsts.length, ds_cli' t_dr), st2_cli)) := by
        unfold cliDrvStart; rw [stateT_run_get_bind_cli, hG]; dsimp only
        simp only [StateT.run_bind, stateT_lift_run_cli, stateT_monadLift_run_cli,
          StateT.run_get, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
        rw [htest_cli]
        simp only [StateT.run_bind, stateT_lift_run_cli, stateT_monadLift_run_cli, pure_bind, bind_assoc]
        rw [hrev_cli]
        simp only [StateT.run_bind, stateT_lift_run_cli, stateT_monadLift_run_cli, pure_bind, bind_assoc]
        congr 1; funext t_dr
        rw [hfind_initTape]; dsimp only
        rw [hfind_initPrin]; dsimp only
        rw [hfind_respPrin]; dsimp only
        rw [find?_map_update_key_cli st_cli.spkBundles target
          (fun b0 => { b0 with revealed := true }), hFindB]; dsimp only [Option.map]
        have hcli_init : cliPqInit run W _ _ (appendInitiateTape t_init t_dr) = some (stA0 t_dr) :=
          (hInitRel t_dr).1
        rcases hopk_hdr : hdr.opkId? with _ | opkId
        · rw [hopk_hdr] at hopk_eq; cases hopk_eq; dsimp only
          rw [hmeA_eq]; dsimp only; rw [hmeB_eq]; dsimp only
          rw [hkeysB_eq]; dsimp only; rw [hbundleE_eq]; dsimp only
          rw [hcli_init]; dsimp only [Option.map]
          simp only [StateT.run_bind, stateT_lift_run_cli, StateT.run_set, StateT.run_pure,
            bind_assoc, pure_bind]; rfl
        · rw [hopk_hdr] at hopk_eq; dsimp only at hopk_eq ⊢
          rcases hfind_oe : st_cli.opkEntries.find?
              (fun (idx, _) => idx == (u_resp.val, j_resp.val, opkId.toNat)) with _ | ⟨_, oe⟩
          · rw [hfind_oe] at hopk_eq; cases hopk_eq
          · rw [hfind_oe] at hopk_eq ⊢; cases hopk_eq; dsimp only
            rw [hmeA_eq]; dsimp only; rw [hmeB_eq]; dsimp only
            rw [hkeysB_eq]; dsimp only; rw [hbundleE_eq]; dsimp only
            rw [hcli_init]; dsimp only [Option.map]
            simp only [StateT.run_bind, stateT_lift_run_cli, StateT.run_set, StateT.run_pure,
              bind_assoc, pure_bind]; rfl
      have h_ad_eval :
          adapterStartDRRun (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K decT encT
            sid σ_ad σ_e2e =
            (do let ac ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
                return ((some σ_e2e.insts.length, σ_ad'), σ_e2e' ac)) := by
        unfold adapterStartDRRun compositionLocalStart; rw [hMirror, hG_e2e]; dsimp only
        rw [htest_e2e]; simp only [pure_bind, bind_assoc]; rw [hrev_e2e]; simp only [pure_bind, bind_assoc]
        congr 1; funext ac; unfold bhE2EFinishStartSpk; rw [bhE2EGuard_with_st, hG_e2e, hRel.b_eq]
        simp [hsFound_wf.1, hsFound_wf.2.1, hsFound_wf.2.2.1, hresp0_wf.1, hRel.b_eq,
          σ_ad', σ_e2e', st2_e2e, st1_e2e, target, d, im_e2e, gs_m, sch_m, P_v1, idA, idB, s, inst]
      refine cliAdapterStepCoupled_of_tape32 _ _
        (fun t_dr => ((some ds_cli.bhInsts.length, ds_cli' t_dr), st2_cli))
        (fun ac => ((some σ_e2e.insts.length, σ_ad'), σ_e2e' ac)) h_cli_eval h_ad_eval (fun t_dr => ?_)
      dsimp only; refine ⟨congrArg some hRel.insts_len_eq, ?_⟩
      refine {
        b_eq := hRel.b_eq, st_rel := hSt2, ki_inv := hInv2 t_dr
        base_e2e_eq := hRel.base_e2e_eq, base_ad_eq := hRel.base_ad_eq
        corrPrins_eq := hRel.corrPrins_eq, revealedSpks_eq := hRel.revealedSpks_eq
        insts_len_le := by simp [ds_cli']; have := hRel.insts_len_le; omega
        insts_len_eq := by simp [ds_cli', σ_e2e', hRel.insts_len_eq]
        meta_cli_len_eq := by simp [ds_cli', hRel.meta_cli_len_eq]
        meta_e2e_len_eq := by simp [σ_e2e', hRel.meta_e2e_len_eq]
        ad_none_of_ge := fun i hi => by
          simp only [σ_e2e', List.length_append, List.length_singleton] at hi
          have hne : i ≠ σ_e2e.insts.length := by omega
          simpa [σ_ad', hne] using hRel.ad_none_of_ge i (by omega)
        insts_rel := fun i h_cli h_e2e h_mb h_me => ?_ }
      by_cases hi : i < ds_cli.bhInsts.length
      · have hi_e2e : i < σ_e2e.insts.length := hRel.insts_len_eq ▸ hi
        have hi_mb : i < ds_cli.instMeta.length := hRel.meta_cli_len_eq.symm ▸ hi
        have hi_me : i < σ_e2e.instMeta.length := hRel.meta_e2e_len_eq.symm ▸ hi_e2e
        have hne : i ≠ σ_e2e.insts.length := ne_of_lt hi_e2e
        obtain ⟨inst_i, h_ad_i, hInst_i⟩ := hRel.insts_rel i hi hi_e2e hi_mb hi_me
        refine ⟨inst_i, by simp [σ_ad', hne, h_ad_i], ?_⟩; dsimp only [ds_cli', σ_e2e', σ_ad']
        rw [List.getElem_append_left hi, List.getElem_append_left hi_e2e,
          List.getElem_append_left hi_mb, List.getElem_append_left hi_me]
        exact cliAdapterInstRel_of_map_reveal_spk hInst_i (fun _ hm => hm) (fun _ _ => rfl) rfl
      · simp only [ds_cli', List.length_append, List.length_singleton] at h_cli
        have hi_eq : i = ds_cli.bhInsts.length := by omega
        subst hi_eq; have hlen_e2e : ds_cli.bhInsts.length = σ_e2e.insts.length := hRel.insts_len_eq
        have hmc := hRel.meta_cli_len_eq; have hme := hRel.meta_e2e_len_eq
        have hack_f : σ_ad.2.1 ds_cli.bhInsts.length = false := (hRel.ad_none_of_ge _ (by omega)).2
        refine ⟨inst, by simp [σ_ad', hlen_e2e], ?_⟩; dsimp only [ds_cli', σ_e2e', σ_ad']
        rw [hack_f, List.getElem_append_right (le_refl _),
          List.getElem_append_right (by omega : σ_e2e.insts.length ≤ ds_cli.bhInsts.length),
          List.getElem_append_right (by omega : ds_cli.instMeta.length ≤ ds_cli.bhInsts.length),
          List.getElem_append_right (by omega : σ_e2e.instMeta.length ≤ ds_cli.bhInsts.length)]
        simp only [hlen_e2e, hmc, hme, Nat.sub_self, List.getElem_cons_zero]
        rw [← hlen_e2e]; exact (hInitRel t_dr).2
    · have hFreshF : SignalPqxdh.isKeyIndSessionTestable st_cli sid = false := Bool.eq_false_iff.mpr hFresh
      have hFreshF_e2e : SignalPqxdh.isKeyIndSessionTestable σ_e2e.st sid = false := by
        rw [eq_cliReplaceSpkBundles_of_cliKeyIndStateRel hRel.st_rel,
          isFreshKeyIndSession_cliReplaceSpkBundles]; exact hFreshF
      have htest_cliF : ((SignalPqxdh.pqxdhKeyIndImpl false S P (.testSession sid)).run st_cli) =
          pure (.noneResp, st_cli) := by
        unfold SignalPqxdh.pqxdhKeyIndImpl; simp [hFreshF, StateT.run_bind, StateT.run_get, StateT.run_pure]
      have htest_e2eF : ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P (.testSession sid)).run σ_e2e.st) =
          pure (.noneResp, σ_e2e.st) := by
        change ((SignalPqxdh.pqxdhKeyIndImpl false S P (.testSession sid)).run σ_e2e.st) = _
        unfold SignalPqxdh.pqxdhKeyIndImpl; simp [hFreshF_e2e, StateT.run_bind, StateT.run_get, StateT.run_pure]
      obtain ⟨kr2, st2_e2e, hrev2, hSt2⟩ := revealSpkSk_unilateral_rel P hRel.st_rel u_resp j_resp
      have h_cli_eval : (((cliDrvStart S ℓ P run W (fun _ _ _ _ _ => some b) sid).run ds_cli).run st_cli) =
          pure (((none : Option ℕ), ds_cli), st_cli) := by
        unfold cliDrvStart; rw [stateT_run_get_bind_cli, hG]; dsimp only
        simp only [StateT.run_bind, stateT_lift_run_cli, stateT_monadLift_run_cli,
          StateT.run_get, bind_assoc, pure_bind]
        rw [htest_cliF]; simp [StateT.run_pure]
      have h_ad_eval :
          adapterStartDRRun (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K decT encT
            sid σ_ad σ_e2e =
            (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>=
              fun _ => pure (((none : Option ℕ), σ_ad), { σ_e2e with st := st2_e2e })) := by
        unfold adapterStartDRRun compositionLocalStart; rw [hG_e2e]; dsimp only
        rw [htest_e2eF]; simp only [pure_bind, bind_assoc]; rw [hrev2]; simp only [pure_bind, bind_assoc]
        congr 1; funext ac; unfold bhE2EFinishStartSpk; rw [bhE2EGuard_with_st, hG_e2e]
      rw [h_cli_eval, h_ad_eval]
      refine cliAdapterStepCoupled_of_deq
        (cliAdapterStepCoupled_ret (none : Option ℕ) st_cli ds_cli σ_ad { σ_e2e with st := st2_e2e } ?_)
        (CryptoGames.Lazy.DEq.refl _)
        (CryptoGames.Lazy.DEq.bind_const _ _)
      exact {
        b_eq := hRel.b_eq, st_rel := hSt2, ki_inv := hRel.ki_inv
        base_e2e_eq := hRel.base_e2e_eq, base_ad_eq := hRel.base_ad_eq
        corrPrins_eq := hRel.corrPrins_eq, revealedSpks_eq := hRel.revealedSpks_eq
        insts_len_le := hRel.insts_len_le.trans (Nat.le_succ n), insts_len_eq := hRel.insts_len_eq
        meta_cli_len_eq := hRel.meta_cli_len_eq, meta_e2e_len_eq := hRel.meta_e2e_len_eq
        ad_none_of_ge := by dsimp only; exact hRel.ad_none_of_ge
        insts_rel := by dsimp only; exact hRel.insts_rel }

set_option linter.unusedVariables false in
theorem cliStartStepBridgeProp_holds
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hCli : CliSpecPqxdh run X W) (hK_tot : MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W.Q.K)
    (hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W))
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (hℓ : ℓ < 10 ^ 6)
    (hDh : Dh.Commutes) (hX : X25519RealizesDh W.C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T) (hinj : Function.Injective encT)
    (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hD : ∀ k x, W.C.D k (W.C.E k x) = x) :
    CliStartStepBridgeProp S ℓ run X W qep decT encT :=
  cliStartStepBridgeProp_of_succ fun hRel _hRem _hGood sid =>
    cliDrvStart_step_succ S ℓ run X W hCli hP qep decT encT hRel sid

end CryptoVerification.E2E
