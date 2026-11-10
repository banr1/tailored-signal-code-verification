/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.CliPqAdapterRemoteIdInv
public import Computational.Proofs.E2E.BhAdapterIjHelpersV1Core
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.Simulation
import Computational.Proofs.LibsignalCli.CliPqHandshakeStepCore
import Computational.Proofs.ReductionDsl.SM.GameCosted
import Computational.Proofs.ReductionDsl.Soundness
import Computational.Proofs.SpecLemmas.Session.StatementComposed
import Computational.Proofs.SpqrV1Sync.SendTotalExtras
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SignalSession.Closure.Version
import ProofLib.SepLogic.WP.StateNorm
import VCVio.EvalDist.Monad.Basic

/-!
# SM adapter step coupling: corrupt, send, challenge, and Alice deliver/inject

Proves step-level coupling between `cliDrvSM` and `cliComposedAdapterImplWith` for early exits,
corruption, transmit, challenge, and Alice deliver/inject queries.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.constructorNameAsVariable false
set_option linter.unusedSimpArgs false

open scoped ENNReal BigOperators
open ReductionDsl OracleComp OracleSpec MeasureTheory

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.Lazy CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.SignalSession
  CryptoVerification.LibsignalCli.Entry
open CryptoGames.LibsignalSM.Proofs.Refinement

/-! ## Cleanliness and remote-identity invariants -/

private theorem list_all_eq_of_getElem_rel {α β : Type} {f : α → Bool} {g : β → Bool}
    (xs : List α) (ys : List β) (hlen : xs.length = ys.length)
    (hrel : ∀ i (hx : i < xs.length) (hy : i < ys.length), f xs[i] = g ys[i]) :
    xs.all f = ys.all g := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  refine ⟨fun h y hy => ?_, fun h x hx => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
    exact (hrel i (hlen.symm ▸ hi) hi) ▸ h xs[i] (List.getElem_mem (hlen.symm ▸ hi))
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    exact (hrel i hi (hlen ▸ hi)).symm ▸ h ys[i] (List.getElem_mem (hlen ▸ hi))

/-- Per-instance cleanliness agrees across the CLI↔E2E coupling (`DEV-C17`). -/
theorem bhDrvInstClean_eq_bhE2EDrvInstClean_of_cliRel {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e) (i : ℕ) :
    bhDrvInstClean ds_cli i = bhE2EDrvInstClean σ_e2e i := by
  unfold bhDrvInstClean bhE2EDrvInstClean
  by_cases hi_cli : i < ds_cli.bhInsts.length
  · have hi_e2e : i < σ_e2e.insts.length := hRel.insts_len_eq ▸ hi_cli
    have hi_mb : i < ds_cli.instMeta.length := hRel.meta_cli_len_eq.symm ▸ hi_cli
    have hi_me : i < σ_e2e.instMeta.length := hRel.meta_e2e_len_eq.symm ▸ hi_e2e
    obtain ⟨_, _, hI⟩ := hRel.insts_rel i hi_cli hi_e2e hi_mb hi_me
    rw [List.getElem?_eq_getElem hi_cli, List.getElem?_eq_getElem hi_e2e,
      List.getElem?_eq_getElem hi_mb, List.getElem?_eq_getElem hi_me]
    dsimp only
    rw [← hI.im_eq, hI.respMeta_eq.1, hI.respMeta_eq.2, hI.sid_eq.1, hRel.revealedSpks_eq]
  · have hi_e2e : ¬ i < σ_e2e.insts.length := hRel.insts_len_eq ▸ hi_cli
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hi_cli),
      List.getElem?_eq_none (Nat.le_of_not_lt hi_e2e)]

theorem bhDrvInstClean_imp_ikACorrAtAccept_false {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {ds_cli : ModelDriverState S ℓ} {i : ℕ} (hclean : bhDrvInstClean ds_cli i = true)
    (hi_cli : i < ds_cli.bhInsts.length) (hi : i < ds_cli.instMeta.length) :
    ds_cli.instMeta[i].ikACorrAtAccept = false := by
  unfold bhDrvInstClean at hclean
  rw [List.getElem?_eq_getElem hi_cli, List.getElem?_eq_getElem hi] at hclean
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hclean
  exact hclean.1.2

theorem cliPartyActiveInv_mono {W : PEParams} {d0 : PqParty} {x : RecordExtras}
    {g : GhostState Bytes} {q_rem q_rem' : ℕ}
    (h : CliPartyActiveInv W d0 x g q_rem) (_hle : q_rem' ≤ q_rem) :
    CliPartyActiveInv W d0 x g q_rem' := h

theorem cliAdapterInstRel_mono_q_rem {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {q_rem q_rem' : ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {bi : ModelDriverInstance S ℓ} {d : BHModelInst S ℓ} {im im_e2e : ModelDriverInstanceMeta S}
    {inst : BHAdapterInstMeta S} {ack : Bool}
    (h : CliAdapterInstRel X W q_rem st_cli ds_cli bi d im im_e2e inst ack)
    (hle : q_rem' ≤ q_rem) :
    CliAdapterInstRel X W q_rem' st_cli ds_cli bi d im im_e2e inst ack := by
  refine { h with gs_rel := ?_ }
  have hgs := h.gs_rel
  cases hbi : bi.gs with
  | none => rw [hbi] at hgs; exact False.elim hgs
  | some gs_cli =>
    cases hd : d.gs with
    | none => rw [hbi, hd] at hgs; exact False.elim hgs
    | some gs_m =>
      rw [hbi, hd] at hgs; dsimp only at hgs ⊢
      refine ⟨hgs.1, ?_⟩
      by_cases hcorr : im.ikACorrAtAccept = true
      · simp only [hcorr, ↓reduceIte] at hgs ⊢; exact hgs.2
      · have hcf : im.ikACorrAtAccept = false := Bool.eq_false_iff.mpr hcorr
        simp only [hcf, Bool.false_eq_true, ↓reduceIte] at hgs ⊢
        rcases hgs.2 with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
          h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
        exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
          h19, h20, h21, h22, h23, h24, h25, h26, cliPartyActiveInv_mono h27 hle,
          fun hb => cliPartyActiveInv_mono (h28 hb) hle⟩

theorem cliAdapterDrvRel_mono_qs_rem {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {b : Bool} {qStart : ℕ} {qs_rem qs_rem' : ℕ → ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (hle : ∀ k, qs_rem' k ≤ qs_rem k) :
    CliAdapterDrvRel S ℓ X W b qStart qs_rem' st_cli ds_cli σ_ad σ_e2e :=
  { hRel with
    insts_rel := fun i h_cli h_e2e h_mb h_me =>
      let ⟨inst, had, hI⟩ := hRel.insts_rel i h_cli h_e2e h_mb h_me
      ⟨inst, had, cliAdapterInstRel_mono_q_rem hI (hle i)⟩ }

theorem cliAdapterDrvRel_decrement_i {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e) (i : ℕ) :
    CliAdapterDrvRel S ℓ X W b qStart (Function.update qs_rem i (qs_rem i - 1))
      st_cli ds_cli σ_ad σ_e2e :=
  cliAdapterDrvRel_mono_qs_rem hRel fun k => by
    by_cases hk : k = i
    · subst hk; simp only [Function.update_self]; exact Nat.sub_le _ _
    · simp only [Function.update_of_ne hk]; exact Nat.le_refl _

theorem cliAdapterKeyIndInv_with_insts {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {W : PEParams}
    {st : SignalPqxdh.KeyIndState S} {ds : ModelDriverState S ℓ}
    (hInv : CliAdapterKeyIndInv S P W st ds)
    (bhInsts' : List (ModelDriverInstance S ℓ)) (instMeta' : List (ModelDriverInstanceMeta S)) :
    CliAdapterKeyIndInv S P W st { ds with bhInsts := bhInsts', instMeta := instMeta' } :=
  { hInv with }

theorem cliAdapterInstRel_with_insts {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {q_rem : ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {bi : ModelDriverInstance S ℓ} {d : BHModelInst S ℓ} {im im_e2e : ModelDriverInstanceMeta S}
    {inst : BHAdapterInstMeta S} {ack : Bool}
    (h : CliAdapterInstRel X W q_rem st_cli ds_cli bi d im im_e2e inst ack)
    (bhInsts' : List (ModelDriverInstance S ℓ)) (instMeta' : List (ModelDriverInstanceMeta S)) :
    CliAdapterInstRel X W q_rem st_cli { ds_cli with bhInsts := bhInsts', instMeta := instMeta' }
      bi d im im_e2e inst ack :=
  { h with }

theorem cliAdapterDrvRel_update_inst_ad {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad σ_ad' : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    {i : ℕ} (hi_cli : i < ds_cli.bhInsts.length)
    (bi' : ModelDriverInstance S ℓ) (d' : BHModelInst S ℓ) (im' im_e2e' : ModelDriverInstanceMeta S)
    (inst' : BHAdapterInstMeta S) (ack' : Bool)
    (had_base : σ_ad'.2.2 = σ_ad.2.2) (had1_eq : σ_ad'.1 i = some inst')
    (had2_eq : σ_ad'.2.1 i = ack')
    (had1_ne : ∀ k, k ≠ i → σ_ad'.1 k = σ_ad.1 k)
    (had2_ne : ∀ k, k ≠ i → σ_ad'.2.1 k = σ_ad.2.1 k)
    (hInst' : CliAdapterInstRel X W (qs_rem i - 1) st_cli ds_cli bi' d' im' im_e2e' inst' ack') :
    CliAdapterDrvRel S ℓ X W b qStart (Function.update qs_rem i (qs_rem i - 1))
      st_cli
      { ds_cli with bhInsts := ds_cli.bhInsts.set i bi', instMeta := ds_cli.instMeta.set i im' }
      σ_ad'
      { σ_e2e with insts := σ_e2e.insts.set i d', instMeta := σ_e2e.instMeta.set i im_e2e' } := by
  refine ⟨hRel.b_eq, hRel.st_rel, cliAdapterKeyIndInv_with_insts hRel.ki_inv _ _,
    hRel.base_e2e_eq, had_base.trans hRel.base_ad_eq, hRel.corrPrins_eq, hRel.revealedSpks_eq,
    by simp only [List.length_set]; exact hRel.insts_len_le,
    by simp only [List.length_set]; exact hRel.insts_len_eq,
    by simp only [List.length_set]; exact hRel.meta_cli_len_eq,
    by simp only [List.length_set]; exact hRel.meta_e2e_len_eq,
    fun k hk => ?_, fun k h_cli h_e2e h_mb h_me => ?_⟩
  · simp only [List.length_set] at hk
    have hi_e2e : i < σ_e2e.insts.length := hRel.insts_len_eq ▸ hi_cli
    have hne : k ≠ i := by omega
    rw [had1_ne k hne, had2_ne k hne]; exact hRel.ad_none_of_ge k hk
  · simp only [List.length_set] at h_cli h_e2e h_mb h_me
    by_cases hki : k = i
    · subst hki; refine ⟨inst', had1_eq, ?_⟩
      simp only [Function.update_self, had2_eq, List.getElem_set_self]
      exact cliAdapterInstRel_with_insts hInst' _ _
    · obtain ⟨inst_k, had_k, hInst_k⟩ := hRel.insts_rel k h_cli h_e2e h_mb h_me
      refine ⟨inst_k, (had1_ne k hki).trans had_k, ?_⟩
      simp only [Function.update_of_ne hki, had2_ne k hki, List.getElem_set_ne (Ne.symm hki)]
      exact cliAdapterInstRel_with_insts hInst_k _ _

/-- Per-instance remote-identity agreement with CLI directory peer keys. -/
def CliAdapterInstRemoteIdInv {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (d : BHModelInst S ℓ) (im : ModelDriverInstanceMeta S) : Prop :=
  ∀ gs_m, d.gs = some gs_m → !im.ikACorrAtAccept →
    (gs_m.st .A).session.remoteIdentity = some d.idB ∧
    (im.bobAccepted → (gs_m.st .B).session.remoteIdentity = some d.idA)

/-- Driver-wide remote-identity invariant across all active `BHModelInst` instances. -/
def CliAdapterDrvRemoteIdInv (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (ds_cli : ModelDriverState S ℓ) (σ_e2e : BHE2EDrvState S ℓ) : Prop :=
  ∀ i (hi_e2e : i < σ_e2e.insts.length) (hi_mb : i < ds_cli.instMeta.length),
    CliAdapterInstRemoteIdInv σ_e2e.insts[i] ds_cli.instMeta[i]

theorem cliAdapterDrvRemoteIdInv_of_cliE2ERemoteIdInv {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {ds_cli : ModelDriverState S ℓ} {σ_e2e : BHE2EDrvState S ℓ}
    (hE2E : CliE2ERemoteIdInv σ_e2e) :
    CliAdapterDrvRemoteIdInv S ℓ ds_cli σ_e2e :=
  fun i hi_e2e _ gs_m hgs _ =>
    let h := hE2E σ_e2e.insts[i] (List.getElem_mem hi_e2e) gs_m hgs
    ⟨h.1, fun _ => h.2⟩

theorem cliAdapterDrvRemoteIdInv_update_inst {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {ds_cli : ModelDriverState S ℓ} {σ_e2e : BHE2EDrvState S ℓ}
    (hRem : CliAdapterDrvRemoteIdInv S ℓ ds_cli σ_e2e)
    (i : ℕ) (bi' : ModelDriverInstance S ℓ) (d' : BHModelInst S ℓ) (im' im_e2e' : ModelDriverInstanceMeta S)
    (hInstRem' : CliAdapterInstRemoteIdInv d' im') :
    CliAdapterDrvRemoteIdInv S ℓ
      { ds_cli with bhInsts := ds_cli.bhInsts.set i bi', instMeta := ds_cli.instMeta.set i im' }
      { σ_e2e with insts := σ_e2e.insts.set i d', instMeta := σ_e2e.instMeta.set i im_e2e' } := by
  intro j hj_e2e hj_mb; simp only [List.length_set] at hj_e2e hj_mb
  by_cases hji : j = i
  · subst hji; simp only [List.getElem_set_self]; exact hInstRem'
  · simp only [List.getElem_set_ne (Ne.symm hji)]; exact hRem j hj_e2e hj_mb

/-- Step-level exact coupling preserving `CliAdapterDrvRel` and `CliAdapterDrvRemoteIdInv`. -/
def cliAdapterStepCoupledRem {S : SignalPqxdh.Setup} {ℓ : ℕ} {α : Type}
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (b : Bool) (qStart' : ℕ) (qs_rem' : ℕ → ℕ)
    (c_cli : ProbComp ((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S))
    (c_ad : ProbComp ((α × CliAdapterState S) × BHE2EDrvState S ℓ)) : Prop :=
  ∃ μ : ProbComp (((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S) ×
                  ((α × CliAdapterState S) × BHE2EDrvState S ℓ)),
    CryptoGames.Lazy.DEq (Prod.fst <$> μ) c_cli ∧
    CryptoGames.Lazy.DEq (Prod.snd <$> μ) c_ad ∧
    ∀ x y, (x, y) ∈ support μ →
      x.1.1 = y.1.1 ∧
      CliAdapterDrvRel S ℓ X W b qStart' qs_rem' x.2 x.1.2 y.1.2 y.2 ∧
      CliAdapterDrvRemoteIdInv S ℓ x.1.2 y.2

theorem cliAdapterStepCoupledRem.toStepCoupled {S : SignalPqxdh.Setup} {ℓ : ℕ} {α : Type}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {b : Bool} {qStart' : ℕ} {qs_rem' : ℕ → ℕ}
    {c_cli : ProbComp ((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S)}
    {c_ad : ProbComp ((α × CliAdapterState S) × BHE2EDrvState S ℓ)}
    (h : cliAdapterStepCoupledRem X W b qStart' qs_rem' c_cli c_ad) :
    cliAdapterStepCoupled X W b qStart' qs_rem' c_cli c_ad :=
  let ⟨μ, h1, h2, hsupp⟩ := h
  ⟨μ, h1, h2, fun x y hxy => ⟨(hsupp x y hxy).1, (hsupp x y hxy).2.1⟩⟩

theorem cliAdapterStepCoupledRem_ret {S : SignalPqxdh.Setup} {ℓ : ℕ} {α : Type}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {b : Bool} {qStart' : ℕ} {qs_rem' : ℕ → ℕ}
    (r : α) (st_cli' : SignalPqxdh.KeyIndState S) (ds_cli' : ModelDriverState S ℓ)
    (σ_ad' : CliAdapterState S) (σ_e2e' : BHE2EDrvState S ℓ)
    (hRel' : CliAdapterDrvRel S ℓ X W b qStart' qs_rem' st_cli' ds_cli' σ_ad' σ_e2e')
    (hRem' : CliAdapterDrvRemoteIdInv S ℓ ds_cli' σ_e2e') :
    cliAdapterStepCoupledRem X W b qStart' qs_rem'
      (pure ((r, ds_cli'), st_cli')) (pure ((r, σ_ad'), σ_e2e')) := by
  refine ⟨pure (((r, ds_cli'), st_cli'), ((r, σ_ad'), σ_e2e')),
    by simp only [map_pure]; rfl, by simp only [map_pure]; rfl, fun x y hmem => ?_⟩
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl⟩; exact ⟨rfl, hRel', hRem'⟩

theorem cliAdapterStepCoupledRem_bind_pure {S : SignalPqxdh.Setup} {ℓ : ℕ} {α β : Type}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {b : Bool} {qStart' : ℕ} {qs_rem' : ℕ → ℕ}
    (m : ProbComp β)
    (f_cli : β → (α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S)
    (f_ad : β → (α × CliAdapterState S) × BHE2EDrvState S ℓ)
    (h : ∀ x ∈ support m,
      (f_cli x).1.1 = (f_ad x).1.1 ∧
      CliAdapterDrvRel S ℓ X W b qStart' qs_rem'
        (f_cli x).2 (f_cli x).1.2 (f_ad x).1.2 (f_ad x).2 ∧
      CliAdapterDrvRemoteIdInv S ℓ (f_cli x).1.2 (f_ad x).2) :
    cliAdapterStepCoupledRem X W b qStart' qs_rem'
      (m >>= fun x => pure (f_cli x)) (m >>= fun x => pure (f_ad x)) := by
  refine ⟨(fun x => (f_cli x, f_ad x)) <$> m,
    by rw [Functor.map_map, map_eq_bind_pure_comp]; rfl,
    by rw [Functor.map_map, map_eq_bind_pure_comp]; rfl, fun u v huv => ?_⟩
  simp only [support_map, Set.mem_image, Prod.mk.injEq] at huv
  rcases huv with ⟨x, hx, rfl, rfl⟩; exact h x hx

private theorem list_set_getElem_self {α : Type} (xs : List α) (i : ℕ) (hi : i < xs.length) :
    xs.set i xs[i] = xs := by
  apply List.ext_getElem (by simp only [List.length_set])
  intro j hj1 hj2
  by_cases hji : j = i
  · subst hji; simp only [List.getElem_set_self]
  · simp only [List.getElem_set_ne (Ne.symm hji)]

private theorem bhInst_set_same_gs {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {bi : ModelDriverInstance S ℓ} {gs : SM.GameState BinState (Plain ℓ) Bytes} (hgs : bi.gs = some gs) :
    { bi with gs := some gs } = bi := by
  cases bi; dsimp only at hgs ⊢; rw [hgs]

private theorem bhModelInst_set_same_gs {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {d : BHModelInst S ℓ} {gs : SM.GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hgs : d.gs = some gs) : { d with gs := some gs } = d := by
  cases d; dsimp only at hgs ⊢; rw [hgs]

private theorem bhDrvState_set_same_gs {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (ds : ModelDriverState S ℓ) (i : ℕ) (hi : i < ds.bhInsts.length)
    (hi_m : i < ds.instMeta.length) (gs : SM.GameState BinState (Plain ℓ) Bytes)
    (hgs : ds.bhInsts[i].gs = some gs) :
    { ds with bhInsts := ds.bhInsts.set i { ds.bhInsts[i] with gs := some gs },
              instMeta := ds.instMeta.set i ds.instMeta[i] } = ds := by
  rw [bhInst_set_same_gs hgs, list_set_getElem_self ds.bhInsts i hi,
    list_set_getElem_self ds.instMeta i hi_m]

private theorem bhE2EDrvState_set_same_gs {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ : BHE2EDrvState S ℓ) (i : ℕ) (hi : i < σ.insts.length)
    (hi_m : i < σ.instMeta.length) (gs : SM.GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (hgs : σ.insts[i].gs = some gs) :
    { σ with insts := σ.insts.set i { σ.insts[i] with gs := some gs },
             instMeta := σ.instMeta.set i σ.instMeta[i] } = σ := by
  rw [bhModelInst_set_same_gs hgs, list_set_getElem_self σ.insts i hi,
    list_set_getElem_self σ.instMeta i hi_m]

theorem cliAdapterTrans_any_pos {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {bobAccepted : Bool} {sid : SignalPqxdh.SessionId S} {hdr : SignalPqxdh.HandshakeHdr}
    {trans_cli trans_m : List (SM.Record (Plain ℓ) Bytes)}
    (h : List.Forall₂ (CliAdapterTransEntryRel bobAccepted sid hdr) trans_cli trans_m)
    (f : SM.Pos → Bool) :
    trans_cli.any (fun r => f r.pos) = trans_m.any (fun r => f r.pos) := by
  induction h with
  | nil => rfl
  | cons hrel _ ih => simp only [List.any_cons, hrel.1, ih]

theorem cliAdapterTrans_filter_map_pos {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {bobAccepted : Bool} {sid : SignalPqxdh.SessionId S} {hdr : SignalPqxdh.HandshakeHdr}
    {trans_cli trans_m : List (SM.Record (Plain ℓ) Bytes)}
    (h : List.Forall₂ (CliAdapterTransEntryRel bobAccepted sid hdr) trans_cli trans_m)
    (f : SM.Pos → Bool) :
    (trans_cli.filter (fun r => f r.pos)).map (fun r => r.pos) =
      (trans_m.filter (fun r => f r.pos)).map (fun r => r.pos) := by
  induction h with
  | nil => rfl
  | cons hrel _ ih =>
    simp only [List.filter_cons, hrel.1]
    cases f _ <;> simp only [↓reduceIte, Bool.false_eq_true, List.map_cons, hrel.1, ih]

/-! ## Early-exit and corrupt coupling -/

def cliAliceAdapterUpdate {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ_ad : CliAdapterState S) (i : ℕ) (optRr : Option (SM.RecvResult (Plain ℓ))) :
    CliAdapterState S :=
  match optRr with
  | some (.accepted _ _ _) => (σ_ad.1, (fun j => if j = i then true else σ_ad.2.1 j), σ_ad.2.2)
  | _ => σ_ad

def cliWrapAdapterSend {S : SignalPqxdh.Setup}
    (inst : BHAdapterInstMeta S) (ack : Bool) (p : Party) (ct : Bytes) : Bytes :=
  if SM.partyEnc p then
    if ct.isEmpty then [] else wireWhisper :: ct
  else if ack then
    if ct.isEmpty then [] else wireWhisper :: ct
  else bhWrapSendOut inst .A ct

section AdapterRun
variable {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
  (P : SignalPqxdh.Primitives)
  (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
  (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
  (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)

theorem cliE2EDrvImplWith_run_sm (i : ℕ)
    (sq : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (σ_e2e : BHE2EDrvState S ℓ) :
    ((cliE2EDrvImplWith P ki C K qep decT encT (.inr (.inr ⟨i, sq⟩))).run σ_e2e) =
      (bhE2EStepLocalSm C K qep decT encT σ_e2e i sq >>= fun (sr, σ') =>
        pure (bhUnpackSmResp sq sr, σ')) := by
  dsimp only [cliE2EDrvImplWith]
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_monadLift,
    monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc]

private theorem simulateQ_cliE2EDrvImplWith_sm_bind {α : Type} (i : ℕ)
    (sq : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (k : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq →
      OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σ_e2e : BHE2EDrvState S ℓ) :
    (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
      ((liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query (.inr (.inr ⟨i, sq⟩))) :
        OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) _) >>= k)).run σ_e2e =
    (bhE2EStepLocalSm C K qep decT encT σ_e2e i sq >>= fun (sr, σ_e2e') =>
      (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
        (k (bhUnpackSmResp sq sr))).run σ_e2e') := by
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_query, OracleSpec.query_def]
  dsimp [OracleQuery.cont, OracleQuery.input]
  rw [id_map, cliE2EDrvImplWith_run_sm]; simp only [bind_assoc, pure_bind]

theorem cliComposedAdapterImplWith_cr_run (i : ℕ) (p : Party)
    (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ) :
    (((cliComposedAdapterImplWith P ki C K qep decT encT (.inr ⟨i, .inr p⟩)).run σ_ad).run σ_e2e) =
      match σ_ad.1 i with
      | none => pure ((none, σ_ad), σ_e2e)
      | some inst =>
        bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inr p) >>= fun (sr, σ_e2e') =>
          match sr.2.2 with
          | none => pure ((none, σ_ad), σ_e2e')
          | some g => pure ((some (bhBinStateOfParty inst g), σ_ad), σ_e2e') := by
  change (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
    ((bhShallowAdapterImpl S ℓ (BitVec 512) (.inr (.inr ⟨i, .inr p⟩))).run σ_ad)).run σ_e2e = _
  dsimp [bhShallowAdapterImpl, bhShallowAdapterGameStep, bhShallowQueryTarget]
  rcases σ_ad.1 i with _ | inst
  · simp only [simulateQ_pure, StateT.run_pure]
  · dsimp only
    rw [simulateQ_cliE2EDrvImplWith_sm_bind]; congr 1
    funext x; rcases x with ⟨⟨_, _, _ | g⟩, σ_e2e'⟩ <;>
      simp only [bhUnpackSmResp, simulateQ_pure, StateT.run_pure]

theorem cliComposedAdapterImplWith_tr_run (i : ℕ) (p : Party) (m : Plain ℓ)
    (r : Option (BitVec 512)) (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ) :
    (((cliComposedAdapterImplWith P ki C K qep decT encT
        (.inr ⟨i, .inl (.inl (.inl (.inl (p, m, r))))⟩)).run σ_ad).run σ_e2e) =
      match σ_ad.1 i with
      | none => pure ((none, σ_ad), σ_e2e)
      | some inst =>
        bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inl (.inl (.inl (p, m, r))))) >>=
          fun (sr, σ_e2e') =>
            match sr.1 with
            | none => pure ((none, σ_ad), σ_e2e')
            | some ct => pure ((some (cliWrapAdapterSend inst (σ_ad.2.1 i) p ct), σ_ad), σ_e2e') := by
  change (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
    ((bhShallowAdapterImpl S ℓ (BitVec 512)
      (.inr (.inr ⟨i, .inl (.inl (.inl (.inl (p, m, r))))⟩))).run σ_ad)).run σ_e2e = _
  dsimp [bhShallowAdapterImpl, bhShallowAdapterGameStep, bhShallowQueryTarget,
    bhShallowWrapWhisper, cliWrapAdapterSend]
  rcases σ_ad.1 i with _ | inst
  · simp only [simulateQ_pure, StateT.run_pure]
  · dsimp only
    rw [simulateQ_cliE2EDrvImplWith_sm_bind]; congr 1
    funext x; rcases x with ⟨⟨_ | ct, _, _⟩, σ_e2e'⟩ <;>
      simp only [bhUnpackSmResp, simulateQ_pure, StateT.run_pure]

theorem cliComposedAdapterImplWith_ch_run (i : ℕ) (p : Party) (m0 m1 : Plain ℓ)
    (r : Option (BitVec 512)) (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ) :
    (((cliComposedAdapterImplWith P ki C K qep decT encT
        (.inr ⟨i, .inl (.inl (.inl (.inr (p, m0, m1, r))))⟩)).run σ_ad).run σ_e2e) =
      match σ_ad.1 i with
      | none => pure ((none, σ_ad), σ_e2e)
      | some inst =>
        bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inl (.inl (.inr (p, m0, m1, r))))) >>=
          fun (sr, σ_e2e') =>
            match sr.1 with
            | none => pure ((none, σ_ad), σ_e2e')
            | some ct => pure ((some (cliWrapAdapterSend inst (σ_ad.2.1 i) p ct), σ_ad), σ_e2e') := by
  change (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
    ((bhShallowAdapterImpl S ℓ (BitVec 512)
      (.inr (.inr ⟨i, .inl (.inl (.inl (.inr (p, m0, m1, r))))⟩))).run σ_ad)).run σ_e2e = _
  dsimp [bhShallowAdapterImpl, bhShallowAdapterGameStep, bhShallowQueryTarget,
    bhShallowWrapWhisper, cliWrapAdapterSend]
  rcases σ_ad.1 i with _ | inst
  · simp only [simulateQ_pure, StateT.run_pure]
  · dsimp only
    rw [simulateQ_cliE2EDrvImplWith_sm_bind]; congr 1
    funext x; rcases x with ⟨⟨_ | ct, _, _⟩, σ_e2e'⟩ <;>
      simp only [bhUnpackSmResp, simulateQ_pure, StateT.run_pure]

theorem cliComposedAdapterImplWith_dl_A_run (i : ℕ) (c : Bytes)
    (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ) :
    (((cliComposedAdapterImplWith P ki C K qep decT encT
        (.inr ⟨i, .inl (.inl (.inr (.A, c)))⟩)).run σ_ad).run σ_e2e) =
      match c with
      | [] =>
        bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inl (.inr (.A, [])))) >>=
          fun (sr, σ_e2e') => pure ((sr.2.1, σ_ad), σ_e2e')
      | t :: body =>
        if t == wireWhisper then
          match body with
          | [] => pure ((none, σ_ad), σ_e2e)
          | b :: bs =>
            bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inl (.inr (.A, b :: bs)))) >>=
              fun (sr, σ_e2e') => pure ((sr.2.1, cliAliceAdapterUpdate σ_ad i sr.2.1), σ_e2e')
        else pure ((none, σ_ad), σ_e2e) := by
  change (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
    ((bhShallowAdapterImpl S ℓ (BitVec 512)
      (.inr (.inr ⟨i, .inl (.inl (.inr (.A, c)))⟩))).run σ_ad)).run σ_e2e = _
  dsimp [bhShallowAdapterImpl, bhShallowAdapterGameStep, bhShallowQueryTarget,
    bhShallowWrapWhisper, bhShallowSplitWhisper, bhShallowAliceUpdate, cliAliceAdapterUpdate]
  rcases c with _ | ⟨t, body⟩
  · simp only [List.isEmpty_nil, ↓reduceIte]
    rw [simulateQ_cliE2EDrvImplWith_sm_bind]
    congr 1
  · dsimp only; cases t == wireWhisper
    · simp only [Bool.false_eq_true, ↓reduceIte, List.isEmpty_cons, BEq.rfl,
        simulateQ_pure, StateT.run_pure]
    · rcases body with _ | ⟨b, bs⟩
      · simp only [↓reduceIte, List.isEmpty_nil, simulateQ_pure, StateT.run_pure]
      · simp only [↓reduceIte, List.isEmpty_cons, Bool.false_eq_true, BEq.rfl]
        rw [simulateQ_cliE2EDrvImplWith_sm_bind]
        congr 1

local macro "simp_ij_ad" : tactic =>
  `(tactic| simp (config := {failIfUnchanged := false}) only [beq_self_eq_true, ↓reduceIte,
      Option.map_some, Option.map_none, List.isEmpty_cons, List.isEmpty_nil, Bool.false_eq_true,
      Bool.and_true, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
      simulateQ_pure, StateT.run_pure, map_pure])

theorem cliComposedAdapterImplWith_ij_A_run (i : ℕ) (c : Bytes)
    (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ) :
    (((cliComposedAdapterImplWith P ki C K qep decT encT
        (.inr ⟨i, .inl (.inr (.A, c))⟩)).run σ_ad).run σ_e2e) =
      match (match c with | t :: body => if t == wireWhisper then some body else none | [] => none) with
      | none => pure ((none, σ_ad), σ_e2e)
      | some body =>
        if decide (c.length ≤ stdinCapBytes) && shortCiphertext c then
          match bhDecodePreKeyMsgE body with
          | some _ =>
            bhE2EStepLocalSm C K qep decT encT σ_e2e i
              (.inl (.inr (.A, if body.isEmpty then [] else wireWhisper :: body))) >>=
              fun (sr, σ_e2e') => pure ((sr.2.1, cliAliceAdapterUpdate σ_ad i sr.2.1), σ_e2e')
          | none =>
            if body.isEmpty then
              bhE2EStepLocalSm C K qep decT encT σ_e2e i
                (.inl (.inr (.A, if c.isEmpty then [] else wireWhisper :: c))) >>=
                fun (sr, σ_e2e') => pure ((sr.2.1, σ_ad), σ_e2e')
            else
              bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inr (.A, body))) >>=
                fun (sr, σ_e2e') => pure ((sr.2.1, cliAliceAdapterUpdate σ_ad i sr.2.1), σ_e2e')
        else pure ((none, σ_ad), σ_e2e) := by
  change (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
    ((bhShallowAdapterImpl S ℓ (BitVec 512)
      (.inr (.inr ⟨i, .inl (.inr (.A, c))⟩))).run σ_ad)).run σ_e2e = _
  dsimp [bhShallowAdapterImpl, bhShallowAdapterGameStep, bhShallowQueryTarget,
    bhShallowWrapWhisper, bhShallowSplitWhisper, bhShallowParsePreKey,
    bhShallowAliceUpdate, cliAliceAdapterUpdate]
  rcases c with _ | ⟨t, body⟩
  · simp_ij_ad
  · dsimp only; cases t == wireWhisper
    · simp_ij_ad
    · simp_ij_ad; cases (decide ((t :: body).length ≤ stdinCapBytes) && shortCiphertext (t :: body))
      · simp_ij_ad
      · simp_ij_ad; rcases bhDecodePreKeyMsgE body with _ | m
        · rcases body with _ | ⟨b0, bs⟩ <;> {
            simp_ij_ad; rw [simulateQ_cliE2EDrvImplWith_sm_bind]; congr 1 }
        · simp_ij_ad; rw [simulateQ_cliE2EDrvImplWith_sm_bind]; congr 1

theorem cliComposedAdapterImplWith_sm_of_stepLocalSm_id_none (i : ℕ)
    (q : (cliGameSmSpec ℓ (BitVec 512)).Domain)
    (σ_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ)
    (hStep : ∀ sq : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain,
      bhE2EStepLocalSm C K qep decT encT σ_e2e i sq = pure ((none, none, none), σ_e2e)) :
    (((cliComposedAdapterImplWith P ki C K qep decT encT (.inr ⟨i, q⟩)).run σ_ad).run σ_e2e) =
      pure ((bhSmDefaultWithSpqr q, σ_ad), σ_e2e) := by
  have hQueryNone : ∀ (sq : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
      (k : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq →
        OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
          (Option (SM.RecvResult (Plain ℓ)) × CliAdapterState S)),
      (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
        (bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := BitVec 512) (.inr ⟨i, sq⟩) >>= k)).run
        σ_e2e =
      (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
        (k (bhUnpackSmResp sq (none, none, none)))).run σ_e2e := by
    intro sq k
    dsimp only [bhShallowQueryTarget]
    rw [simulateQ_cliE2EDrvImplWith_sm_bind, hStep _, pure_bind]
  rcases q with (((⟨p, m, r⟩ | ⟨p, m0, m1, r⟩) | ⟨_ | _, c⟩) | ⟨_ | _, c⟩) | p
  · rw [cliComposedAdapterImplWith_tr_run]
    rcases σ_ad.1 i with _ | inst <;> simp only [hStep _, pure_bind] <;> rfl
  · rw [cliComposedAdapterImplWith_ch_run]
    rcases σ_ad.1 i with _ | inst <;> simp only [hStep _, pure_bind] <;> rfl
  · rw [cliComposedAdapterImplWith_dl_A_run]
    rcases c with _ | ⟨t, _ | ⟨b, bs⟩⟩
    · simp only [hStep _, pure_bind]; rfl
    · dsimp only; cases (t == wireWhisper) <;> rfl
    · dsimp only; cases (t == wireWhisper) <;>
        simp only [↓reduceIte, Bool.false_eq_true, hStep _, pure_bind, cliAliceAdapterUpdate] <;> rfl
  · change (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
      (bhShallowAdapterGameStep (.inr ⟨i, .inl (.inl (.inr (.B, c)))⟩) σ_ad)).run σ_e2e = _
    dsimp only [bhShallowAdapterGameStep]
    rcases σ_ad.1 i with _ | inst
    · simp only [simulateQ_pure, StateT.run_pure]; rfl
    · dsimp only
      cases bhShallowParsePreKey c with
      | none =>
        dsimp only
        cases bhShallowSplitWhisper c with
        | none =>
          dsimp only; rw [hQueryNone]
          simp only [bhUnpackSmResp, simulateQ_pure, StateT.run_pure]; rfl
        | some body =>
          dsimp only
          cases bhShallowParsePreKey body with
          | none =>
            dsimp only
            cases bhShallowSplitWhisper (bhShallowWrapWhisper body) <;> {
              dsimp only; rw [hQueryNone]
              simp only [bhUnpackSmResp, simulateQ_pure, StateT.run_pure]; rfl }
          | some _ =>
            dsimp only; rw [hQueryNone]
            simp only [bhUnpackSmResp, simulateQ_pure, StateT.run_pure]; rfl
      | some hdr_inner =>
        dsimp only
        cases bhShallowSplitWhisper (bhShallowWrapWhisper hdr_inner.2) <;> {
          dsimp only; rw [hQueryNone]
          simp only [bhUnpackSmResp, bhShallowBobUpdate, simulateQ_pure, StateT.run_pure]; rfl }
  · rw [cliComposedAdapterImplWith_ij_A_run]
    rcases c with _ | ⟨t, body⟩
    · rfl
    · dsimp only; cases (t == wireWhisper)
      · rfl
      · simp only [↓reduceIte]
        by_cases hcap : (t :: body).length ≤ stdinCapBytes
        · simp only [decide_eq_true hcap, Bool.true_and]
          cases shortCiphertext (t :: body)
          · rfl
          · simp only [↓reduceIte]; rcases bhDecodePreKeyMsgE body with _ | _
            · cases body.isEmpty <;>
                simp only [↓reduceIte, Bool.false_eq_true, hStep _, pure_bind, cliAliceAdapterUpdate] <;> rfl
            · simp only [hStep _, pure_bind, cliAliceAdapterUpdate]; rfl
        · simp only [decide_eq_false hcap, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; rfl
  · change (simulateQ (cliE2EDrvImplWith P ki C K qep decT encT)
      (bhShallowAdapterGameStep (.inr ⟨i, .inl (.inr (.B, c))⟩) σ_ad)).run σ_e2e = _
    dsimp only [bhShallowAdapterGameStep]
    cases bhShallowSplitWhisper c with
    | none =>
      dsimp only
      cases bhShallowParsePreKey c with
      | none =>
        dsimp only; rw [hQueryNone]
        simp only [bhUnpackSmResp, simulateQ_pure, StateT.run_pure]; rfl
      | some hdr_inner =>
        dsimp only
        cases (decide (c.length ≤ stdinCapBytes) && shortCiphertext c &&
            decide (hdr_inner.2.length + 2048 < 2 ^ 32)) <;>
          simp only [Bool.false_eq_true, ↓reduceIte]
        · rw [hQueryNone]; simp only [bhUnpackSmResp, simulateQ_pure, StateT.run_pure]; rfl
        · rcases σ_ad.1 i with _ | inst
          · dsimp only; rw [hQueryNone]
            simp only [bhUnpackSmResp, simulateQ_pure, StateT.run_pure]; rfl
          · dsimp only
            cases bhShallowSplitWhisper (bhShallowWrapWhisper hdr_inner.2) with
            | none =>
              dsimp only
              cases (bhShallowUpdateInstMeta inst false false c).1 <;> {
                simp only [Bool.false_eq_true, ↓reduceIte]; rw [hQueryNone]
                simp only [bhUnpackSmResp, simulateQ_pure, StateT.run_pure]; rfl }
            | some _ =>
              dsimp only; rw [hQueryNone]
              simp only [bhUnpackSmResp, simulateQ_pure, StateT.run_pure]; rfl
    | some body =>
      dsimp only
      cases (decide (c.length ≤ stdinCapBytes) && shortCiphertext c) <;>
        simp only [Bool.false_eq_true, ↓reduceIte]
      · rw [hQueryNone]; simp only [bhUnpackSmResp, simulateQ_pure, StateT.run_pure]; rfl
      · cases bhShallowParsePreKey body with
        | none =>
          dsimp only
          cases bhShallowSplitWhisper (bhShallowWrapWhisper body) <;> {
            dsimp only; rw [hQueryNone]
            simp only [bhUnpackSmResp, simulateQ_pure, StateT.run_pure]; rfl }
        | some _ =>
          dsimp only; rw [hQueryNone]
          simp only [bhUnpackSmResp, simulateQ_pure, StateT.run_pure]; rfl
  · rw [cliComposedAdapterImplWith_cr_run]
    rcases σ_ad.1 i with _ | inst <;> simp only [hStep _, pure_bind] <;> rfl

end AdapterRun

private theorem stateT_lift_get_bind_run {σ₁ σ₂ α : Type}
    (f : σ₂ → StateT σ₁ (StateT σ₂ ProbComp) α) (s₁ : σ₁) (s₂ : σ₂) :
    (((StateT.lift (get : StateT σ₂ ProbComp σ₂) >>= f).run s₁).run s₂) =
      (((f s₂).run s₁).run s₂) := by
  change (((get : StateT σ₂ ProbComp σ₂) >>= fun a => pure (a, s₁)) >>=
    fun p => (f p.1).run p.2).run s₂ = _
  simp only [bind_assoc, pure_bind, StateT.run_bind, StateT.run_get]

private theorem stateT_lift_liftM_bind_run {σ₁ σ₂ α β : Type}
    (c : ProbComp α) (f : α → StateT σ₁ (StateT σ₂ ProbComp) β) (s₁ : σ₁) (s₂ : σ₂) :
    (((StateT.lift (liftM c : StateT σ₂ ProbComp α) >>= f).run s₁).run s₂) =
      (c >>= fun a => ((f a).run s₁).run s₂) := by
  change (((liftM c : StateT σ₂ ProbComp α) >>= fun a => pure (a, s₁)) >>=
    fun p => (f p.1).run p.2).run s₂ = _
  simp only [bind_assoc, pure_bind, StateT.run_bind, StateT.run_monadLift, monadLift_self]

private theorem cliRunStdSM_nonBobDl_run {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (run : CliRun) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ds : ModelDriverState S ℓ) (st : SignalPqxdh.KeyIndState S)
    (i : ℕ) (bi : ModelDriverInstance S ℓ) (im : ModelDriverInstanceMeta S)
    (gs : SM.GameState BinState (Plain ℓ) Bytes)
    (q : (cliGameSmSpec ℓ (BitVec 512)).Domain)
    (hq_bob : bhIsBobRecvSMQuery q = false) :
    (((cliRunStdSM S ℓ run W qep decT encT ds i bi im gs q).run ds).run st) =
      (((SM.oracleImplR (cliPqScheme run W ℓ bi (cliPqSigsOf st bi) bi.stA0 bi.stB0)
          (2 + 1) qep (bhConfigSpkS (Msg := Plain ℓ) decT encT) q).run gs) >>= fun (r, gsOut) =>
        pure ((r, { ds with bhInsts := ds.bhInsts.set i { bi with gs := some gsOut },
                            instMeta := ds.instMeta.set i im }), st)) := by
  rcases q with (((_ | _) | ⟨_ | _, c⟩) | ⟨_ | _, c⟩) | _ <;> try cases hq_bob
  all_goals {
    unfold cliRunStdSM bhMetaAfterSM bhIsBobAcceptSMResp
    rw [stateT_lift_get_bind_run]; dsimp only
    rw [stateT_lift_liftM_bind_run]
    refine bind_congr fun ⟨r, gsOut⟩ => ?_
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
      Bool.and_false, Bool.false_eq_true, ↓reduceIte] }

section EarlyAndCorrupt
variable {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
  (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) (qep : ℕ)
  (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
  (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (BHDrvM S ℓ))
  (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
  {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
  {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
  {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}

private theorem cliDrvSM_not_clean_eq
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (i : ℕ) (q : (cliGameSmSpec ℓ (BitVec 512)).Domain) (hDirty : bhDrvInstClean ds_cli i = false) :
    (((cliDrvSM S ℓ run W qep decT encT ext ⟨i, q⟩).run ds_cli).run st_cli) =
      pure ((bhSmDefaultWithSpqr q, ds_cli), st_cli) ∧
    (((cliComposedAdapterImplWith (modelPrims X W) ki W.C W.Q.K qep decT encT
        (.inr ⟨i, q⟩)).run σ_ad).run σ_e2e) =
      pure ((bhSmDefaultWithSpqr q, σ_ad), σ_e2e) := by
  have hDirty_e2e : bhE2EDrvInstClean σ_e2e i = false :=
    (bhDrvInstClean_eq_bhE2EDrvInstClean_of_cliRel hRel i).symm.trans hDirty
  refine ⟨by unfold cliDrvSM; simp only [StateT.run_bind, StateT.run_get, pure_bind, hDirty,
      Bool.not_false, ↓reduceIte, StateT.run_pure], ?_⟩
  refine cliComposedAdapterImplWith_sm_of_stepLocalSm_id_none _ _ _ _ _ _ _ _ _ _ _ fun sq => ?_
  unfold bhE2EStepLocalSm; simp only [hDirty_e2e, Bool.not_false, ↓reduceIte]

theorem cliDrvSM_adapter_couplingRem_not_clean
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (hRem : CliAdapterDrvRemoteIdInv S ℓ ds_cli σ_e2e)
    (i : ℕ) (q : (cliGameSmSpec ℓ (BitVec 512)).Domain) (hDirty : bhDrvInstClean ds_cli i = false) :
    cliAdapterStepCoupledRem X W b qStart (Function.update qs_rem i (qs_rem i - 1))
      (((cliDrvSM S ℓ run W qep decT encT ext ⟨i, q⟩).run ds_cli).run st_cli)
      (((cliComposedAdapterImplWith (modelPrims X W) ki W.C W.Q.K qep decT encT
          (.inr ⟨i, q⟩)).run σ_ad).run σ_e2e) := by
  obtain ⟨h1, h2⟩ := cliDrvSM_not_clean_eq run X W qep decT encT ext ki hRel i q hDirty
  rw [h1, h2]; exact cliAdapterStepCoupledRem_ret _ _ _ _ _ (cliAdapterDrvRel_decrement_i hRel i) hRem

private theorem cliDrvSM_oob_eq
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (i : ℕ) (q : (cliGameSmSpec ℓ (BitVec 512)).Domain) (hOob : ds_cli.bhInsts.length ≤ i) :
    (((cliDrvSM S ℓ run W qep decT encT ext ⟨i, q⟩).run ds_cli).run st_cli) =
      pure ((bhSmDefaultWithSpqr q, ds_cli), st_cli) ∧
    (((cliComposedAdapterImplWith (modelPrims X W) ki W.C W.Q.K qep decT encT
        (.inr ⟨i, q⟩)).run σ_ad).run σ_e2e) =
      pure ((bhSmDefaultWithSpqr q, σ_ad), σ_e2e) := by
  have hbi_none : ds_cli.bhInsts[i]? = none := List.getElem?_eq_none hOob
  have hd_none : σ_e2e.insts[i]? = none := List.getElem?_eq_none (hRel.insts_len_eq ▸ hOob)
  refine ⟨(by unfold cliDrvSM; simp only [StateT.run_bind, StateT.run_get, pure_bind, hbi_none]
              split_ifs <;> simp only [StateT.run_pure]), ?_⟩
  refine cliComposedAdapterImplWith_sm_of_stepLocalSm_id_none _ _ _ _ _ _ _ _ _ _ _ fun sq => ?_
  unfold bhE2EStepLocalSm; simp only [hd_none]; split_ifs <;> rfl

theorem cliDrvSM_adapter_coupling_oob
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (i : ℕ) (q : (cliGameSmSpec ℓ (BitVec 512)).Domain) (hOob : ds_cli.bhInsts.length ≤ i) :
    cliAdapterStepCoupled X W b qStart (Function.update qs_rem i (qs_rem i - 1))
      (((cliDrvSM S ℓ run W qep decT encT ext ⟨i, q⟩).run ds_cli).run st_cli)
      (((cliComposedAdapterImplWith (modelPrims X W) ki W.C W.Q.K qep decT encT
          (.inr ⟨i, q⟩)).run σ_ad).run σ_e2e) := by
  obtain ⟨h1, h2⟩ := cliDrvSM_oob_eq run X W qep decT encT ext ki hRel i q hOob
  rw [h1, h2]; exact cliAdapterStepCoupled_ret _ _ _ _ _ (cliAdapterDrvRel_decrement_i hRel i)

theorem cliDrvSM_adapter_couplingRem_oob
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (hRem : CliAdapterDrvRemoteIdInv S ℓ ds_cli σ_e2e)
    (i : ℕ) (q : (cliGameSmSpec ℓ (BitVec 512)).Domain) (hOob : ds_cli.bhInsts.length ≤ i) :
    cliAdapterStepCoupledRem X W b qStart (Function.update qs_rem i (qs_rem i - 1))
      (((cliDrvSM S ℓ run W qep decT encT ext ⟨i, q⟩).run ds_cli).run st_cli)
      (((cliComposedAdapterImplWith (modelPrims X W) ki W.C W.Q.K qep decT encT
          (.inr ⟨i, q⟩)).run σ_ad).run σ_e2e) := by
  obtain ⟨h1, h2⟩ := cliDrvSM_oob_eq run X W qep decT encT ext ki hRel i q hOob
  rw [h1, h2]; exact cliAdapterStepCoupledRem_ret _ _ _ _ _ (cliAdapterDrvRel_decrement_i hRel i) hRem

private theorem cliDrvSM_cr_core
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (i : ℕ) (p : Party) :
    ∃ resp ds_cli' σ_e2e',
      (((cliDrvSM S ℓ run W qep decT encT ext ⟨i, .inr p⟩).run ds_cli).run st_cli) =
        pure ((resp, ds_cli'), st_cli) ∧
      (((cliComposedAdapterImplWith (modelPrims X W) ki W.C W.Q.K qep decT encT
          (.inr ⟨i, .inr p⟩)).run σ_ad).run σ_e2e) =
        pure ((resp, σ_ad), σ_e2e') ∧
      CliAdapterDrvRel S ℓ X W b qStart (Function.update qs_rem i (qs_rem i - 1))
        st_cli ds_cli' σ_ad σ_e2e' ∧
      (CliAdapterDrvRemoteIdInv S ℓ ds_cli σ_e2e →
        CliAdapterDrvRemoteIdInv S ℓ ds_cli' σ_e2e') := by
  cases hClean : bhDrvInstClean ds_cli i
  · obtain ⟨h1, h2⟩ := cliDrvSM_not_clean_eq run X W qep decT encT ext ki hRel i (.inr p) hClean
    exact ⟨_, _, _, h1, h2, cliAdapterDrvRel_decrement_i hRel i, id⟩
  · by_cases hi_cli : i < ds_cli.bhInsts.length
    swap
    · obtain ⟨h1, h2⟩ := cliDrvSM_oob_eq run X W qep decT encT ext ki hRel i (.inr p)
        (Nat.le_of_not_lt hi_cli)
      exact ⟨_, _, _, h1, h2, cliAdapterDrvRel_decrement_i hRel i, id⟩
    · have hi_e2e : i < σ_e2e.insts.length := hRel.insts_len_eq ▸ hi_cli
      have hi_mb : i < ds_cli.instMeta.length := hRel.meta_cli_len_eq.symm ▸ hi_cli
      have hi_me : i < σ_e2e.instMeta.length := hRel.meta_e2e_len_eq.symm ▸ hi_e2e
      have hCorr : ds_cli.instMeta[i].ikACorrAtAccept = false :=
        bhDrvInstClean_imp_ikACorrAtAccept_false hClean hi_cli hi_mb
      obtain ⟨inst, hinst_ad, hInstRel⟩ := hRel.insts_rel i hi_cli hi_e2e hi_mb hi_me
      set bi := ds_cli.bhInsts[i]; set d := σ_e2e.insts[i]
      set im := ds_cli.instMeta[i]; set im_e2e := σ_e2e.instMeta[i]
      have hbi_opt : ds_cli.bhInsts[i]? = some bi := List.getElem?_eq_getElem hi_cli
      have hd_opt : σ_e2e.insts[i]? = some d := List.getElem?_eq_getElem hi_e2e
      have him_opt : ds_cli.instMeta[i]? = some im := List.getElem?_eq_getElem hi_mb
      have hime_opt : σ_e2e.instMeta[i]? = some im_e2e := List.getElem?_eq_getElem hi_me
      have hClean_e2e : bhE2EDrvInstClean σ_e2e i = true :=
        (bhDrvInstClean_eq_bhE2EDrvInstClean_of_cliRel hRel i).symm.trans hClean
      have hgs := hInstRel.gs_rel
      cases hgs_cli : bi.gs with
      | none => rw [hgs_cli] at hgs; exact False.elim hgs
      | some gs_cli =>
        cases hgs_m : d.gs with
        | none => rw [hgs_cli, hgs_m] at hgs; exact False.elim hgs
        | some gs_m =>
          rw [hgs_cli, hgs_m] at hgs; rcases hgs with ⟨hb_eq, hrest⟩
          simp only [hCorr, Bool.false_eq_true, ↓reduceIte] at hrest
          rcases hrest with
            ⟨h_acc, h_win, h_ep, h_idx, h_max, h_ch, h_comp, h_tL, h_lk, h_cr,
             h_tr, h_ppkA, h_ppkB, h_idA, h_ack0, h_epA0, h_epB0, h_trA0, h_cpA0, h_tL0,
             h_epB1, h_stA, h_stB0, h_stB1, h_pA, h_pB, h_actA, h_actB⟩
          have h_corrAllowed : gs_cli.corrAllowed p = gs_m.corrAllowed p := by
            unfold SM.GameState.corrAllowed; rw [h_ch, h_comp]; congr 2
            exact cliAdapterTrans_any_pos h_tr (fun pos => pos.sender == p.other && !gs_m.comp.contains pos)
          have h_inWindow : SM.inWindow gs_cli p = SM.inWindow gs_m p := by
            unfold SM.inWindow; rw [h_ep]
          have h_corrOK : (bhConfigSpkS (Msg := Plain ℓ) decT encT).corrOK gs_cli p =
              (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).corrOK gs_m p := by
            dsimp [bhConfigSpkS, configRefuseEarlyBobCorr, configR1OnCurve, SM.configR1, SM.noAliceCorrWhileAliceBelowEpoch10,
              noBobCorrInEpoch0, noBobCorrWhileAliceBelowEpoch10]; rw [h_ep]
          have h_guard :
              (gs_cli.win || !gs_cli.corrAllowed p ||
                ((bhConfigSpkS (Msg := Plain ℓ) decT encT).r1 && SM.inWindow gs_cli p) ||
                !(bhConfigSpkS (Msg := Plain ℓ) decT encT).corrOK gs_cli p) =
              (gs_m.win || !gs_m.corrAllowed p ||
                ((configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).r1 &&
                  SM.inWindow gs_m p) ||
                !(configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).corrOK gs_m p) := by
            rw [h_win, h_corrAllowed, h_inWindow, h_corrOK]; rfl
          have h_cli_step :
              (((cliDrvSM S ℓ run W qep decT encT ext ⟨i, .inr p⟩).run ds_cli).run st_cli) =
                (((cliRunStdSM S ℓ run W qep decT encT ds_cli i bi im gs_cli (.inr p)).run ds_cli).run st_cli) := by
            unfold cliDrvSM cliStepLocalSM
            simp only [StateT.run_bind, StateT.run_get, pure_bind, hClean, Bool.not_true,
              Bool.false_eq_true, ↓reduceIte, hbi_opt, him_opt, bhIsBobRecvSMQuery, Bool.and_false,
              Bool.false_and, hgs_cli]
          by_cases hG :
              (gs_m.win || !gs_m.corrAllowed p ||
                ((configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).r1 &&
                  SM.inWindow gs_m p) ||
                !(configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).corrOK gs_m p) = true
          · have hG_cli := h_guard.trans hG
            refine ⟨none, ds_cli, σ_e2e, ?_, ?_, cliAdapterDrvRel_decrement_i hRel i, id⟩
            · rw [h_cli_step, cliRunStdSM_nonBobDl_run _ _ _ _ _ _ _ _ _ _ _ _ rfl]
              dsimp [SM.oracleImplR, SM.corrR]
              simp only [pure_bind, hG_cli, ↓reduceIte, StateT.run_pure,
                bi, im, bhDrvState_set_same_gs ds_cli i hi_cli hi_mb gs_cli hgs_cli]
            · rw [cliComposedAdapterImplWith_cr_run, hinst_ad]
              dsimp [bhE2EStepLocalSm, SM.oracleImplR, SM.corrR]
              simp only [hClean_e2e, hd_opt, hime_opt, hgs_m, bhIsBobRecvSMQuery, bhIsBobAcceptSMResp,
                StateT.run_pure, pure_bind, bhPackSmResp, hG,
                Bool.not_true, Bool.false_eq_true, Bool.and_false, Bool.false_and, ↓reduceIte,
                d, im_e2e, bhE2EDrvState_set_same_gs σ_e2e i hi_e2e hi_me gs_m hgs_m]
          · simp only [Bool.not_eq_true] at hG
            have hG_cli := h_guard.trans hG
            have hacc_true : im.bobAccepted = true := by
              by_contra hnot
              have hnot' : (!im.bobAccepted) = true := by
                cases hb : im.bobAccepted <;> [rfl; exact False.elim (hnot hb)]
              have hA := h_epA0 hnot'; have hB := h_epB0 hnot'
              have hok : (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).corrOK
                  gs_m p = false := by
                dsimp [configRefuseEarlyBobCorr, configR1OnCurve, SM.configR1, SM.noAliceCorrWhileAliceBelowEpoch10, noBobCorrInEpoch0, noBobCorrWhileAliceBelowEpoch10]
                cases p
                · have h10 : gs_m.epoch .A < 10 := by omega
                  simp [h10]
                · simp [hB]
              rw [hok] at hG; simp at hG
            let gs_cli' := gs_cli.afterCorr p
            let gs_m' := gs_m.afterCorr p
            have hst_p : gs_cli.st p = bhBinStateOfParty inst (gs_m.st p) := by
              cases p <;> [exact h_stA; exact h_stB1 hacc_true]
            refine ⟨some (bhBinStateOfParty inst (gs_m.st p)),
              { ds_cli with bhInsts := ds_cli.bhInsts.set i { bi with gs := some gs_cli' },
                            instMeta := ds_cli.instMeta.set i im },
              { σ_e2e with insts := σ_e2e.insts.set i { d with gs := some gs_m' },
                           instMeta := σ_e2e.instMeta.set i im_e2e }, ?_, ?_, ?_, ?_⟩
            · rw [h_cli_step, cliRunStdSM_nonBobDl_run _ _ _ _ _ _ _ _ _ _ _ _ rfl, ← hst_p]
              dsimp [SM.oracleImplR, SM.corrR]
              simp only [StateT.run_bind, pure_bind, hG_cli, Bool.false_eq_true,
                ↓reduceIte, StateT.run_set, StateT.run_pure, gs_cli']
            · rw [cliComposedAdapterImplWith_cr_run, hinst_ad]
              dsimp [bhE2EStepLocalSm, SM.oracleImplR, SM.corrR]
              simp only [hClean_e2e, hd_opt, hime_opt, hgs_m, bhIsBobRecvSMQuery, bhIsBobAcceptSMResp,
                StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
                bhPackSmResp, hG, Bool.not_true, Bool.false_eq_true, Bool.and_false, Bool.false_and,
                ↓reduceIte, gs_m']
            · refine cliAdapterDrvRel_update_inst_ad hRel hi_cli
                { bi with gs := some gs_cli' } { d with gs := some gs_m' } im im_e2e
                inst (σ_ad.2.1 i) rfl hinst_ad rfl (fun _ _ => rfl) (fun _ _ => rfl) ?_
              refine ⟨hInstRel.im_eq, hInstRel.sid_eq, hInstRel.hdr_eq, hInstRel.idB_eq,
                hInstRel.respSlot_eq, hInstRel.respMeta_eq, hInstRel.regIdA_eq, hInstRel.regIdB_eq,
                hInstRel.aliceAcked_false, hInstRel.idA_pub_eq, hInstRel.idB_pub_eq,
                hInstRel.extrasB_eq, hInstRel.stB0_empty, hInstRel.resp_bundle_rel, ?_, ?_⟩
              · obtain ⟨bundleE, dk, ac, u_init, bnd, t_init, ss, h1, h2, h3, h4⟩ :=
                  hInstRel.handshake_rel
                refine ⟨bundleE, dk, ac, u_init, bnd, t_init, ss, h1, h2, h3,
                  fun gs_c₁ gs_m₁ hc₁ hm₁ hcorr₁ hacc₁ => ?_⟩
                simp only [Option.some.injEq] at hc₁ hm₁; subst hc₁ hm₁
                exact h4 gs_cli gs_m hgs_cli hgs_m hcorr₁ hacc₁
              · dsimp only; refine ⟨hb_eq, ?_⟩
                simp only [hCorr, Bool.false_eq_true, ↓reduceIte]
                have h_comp' : gs_cli'.comp = gs_m'.comp := by
                  dsimp [gs_cli', gs_m', SM.GameState.afterCorr, SM.GameState.leak]
                  rw [h_comp, cliAdapterTrans_filter_map_pos h_tr (fun pos => pos.sender == p.other)]
                have hnot_acc_false : ∀ {P : Prop}, !im.bobAccepted → P := fun hn => by
                  rw [hacc_true] at hn; cases hn
                exact ⟨h_acc, h_win, h_ep, h_idx, h_max, h_ch, h_comp',
                  by simp [gs_cli', gs_m', SM.GameState.afterCorr, SM.GameState.leak, h_ep, h_tL],
                  by simp [gs_cli', gs_m', SM.GameState.afterCorr, SM.GameState.leak, h_ep, h_tL, h_lk],
                  by simp [gs_cli', gs_m', SM.GameState.afterCorr, SM.GameState.leak, h_ep, h_cr],
                  h_tr, h_ppkA, h_ppkB, h_idA, h_ack0, h_epA0, h_epB0, h_trA0,
                  fun hn => hnot_acc_false hn, fun hn => hnot_acc_false hn,
                  h_epB1, h_stA, h_stB0, h_stB1, h_pA, h_pB,
                  cliPartyActiveInv_mono h_actA (Nat.sub_le _ _),
                  fun hb => cliPartyActiveInv_mono (h_actB hb) (Nat.sub_le _ _)⟩
            · intro hRem
              refine cliAdapterDrvRemoteIdInv_update_inst hRem i _ _ _ _ fun gs₁ hgs₁ hnc => ?_
              simp only [Option.some.injEq] at hgs₁; subst hgs₁
              exact hRem i hi_e2e hi_mb gs_m hgs_m hnc

/-- SM corrupt step coupling. -/
theorem cliDrvSM_adapter_coupling_cr
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (i : ℕ) (p : Party) :
    cliAdapterStepCoupled X W b qStart (Function.update qs_rem i (qs_rem i - 1))
      (((cliDrvSM S ℓ run W qep decT encT ext ⟨i, .inr p⟩).run ds_cli).run st_cli)
      (((cliComposedAdapterImplWith (modelPrims X W) ki W.C W.Q.K qep decT encT
          (.inr ⟨i, .inr p⟩)).run σ_ad).run σ_e2e) := by
  obtain ⟨r, ds', σ', h1, h2, hR, _⟩ := cliDrvSM_cr_core run X W qep decT encT ext ki hRel i p
  rw [h1, h2]; exact cliAdapterStepCoupled_ret r st_cli ds' σ_ad σ' hR

end EarlyAndCorrupt

/-! ## Per-entry `cliPqSend` and Alice `cliPqReceive` bridges -/

private def cliInstDir {S : SignalPqxdh.Setup} {ℓ : ℕ} (bi : ModelDriverInstance S ℓ)
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64) : Party → PqParty
  | .A => cliPqDirA bi
  | .B => cliPqxdhDirBobAfterAccept bi sigs

private def cliInstExtras {S : SignalPqxdh.Setup} (inst : BHAdapterInstMeta S) :
    Party → RecordExtras
  | .A => bhInstExtrasA inst
  | .B => bhInstExtrasB inst

private def cliPeerKey {S : SignalPqxdh.Setup} {ℓ : ℕ} (d : BHModelInst S ℓ) : Party → IdentityKey
  | .A => d.idB
  | .B => d.idA

private theorem wfPq_of_session_party_eq {W : PEParams} {d0 : PqParty} {x : RecordExtras}
    {g₁ g₂ : GhostState Bytes} (hwf : PqxdhPartyInSpecDomain W { d0 with session := some (x, g₁) })
    (hp : g₁.party = g₂.party) (hs : g₁.session = g₂.session) :
    PqxdhPartyInSpecDomain W { d0 with session := some (x, g₂) } := by
  refine ⟨fun x' g' hs' => ?_, ?_, hwf.2.2⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at hs'; rcases hs' with ⟨rfl, rfl⟩
    obtain ⟨⟨g₀, hR₀, hp₀, hs₀⟩, hgp₁, hlen₁⟩ := hwf.1 x g₁ rfl
    have henc : encodeRecordUnderExtras (fun _ => x) g₁ = encodeRecordUnderExtras (fun _ => x) g₂ := by
      unfold encodeRecordUnderExtras; rw [hs]
    exact ⟨⟨g₀, hR₀, hp₀.trans hp, hs₀.trans hs⟩, hp.symm.trans hgp₁, henc ▸ hlen₁⟩
  · have hencDir : encodeDir W { d0 with session := some (x, g₂) } =
        encodeDir W { d0 with session := some (x, g₁) } := by
      unfold encodeDir; dsimp only
      rw [show encodeRecordUnderExtras (fun _ => x) g₂ = encodeRecordUnderExtras (fun _ => x) g₁ by
        unfold encodeRecordUnderExtras; rw [hs.symm]]
    rw [hencDir]; exact hwf.2.1

private theorem cliInstDir_party_peerId {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {q_rem : ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {bi : ModelDriverInstance S ℓ} {d : BHModelInst S ℓ} {im im_e2e : ModelDriverInstanceMeta S}
    {inst : BHAdapterInstMeta S} {ack : Bool}
    (hInstRel : CliAdapterInstRel X W q_rem st_cli ds_cli bi d im im_e2e inst ack)
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64) (p : Party) :
    (cliInstDir bi sigs p).party = p ∧
    (cliInstDir bi sigs p).peerId = some (cliPeerKey d p) := by
  cases p
  · exact ⟨rfl, congrArg some hInstRel.idB_eq.2.2.symm⟩
  · have hidA : bhIdKeyOf bi.hdr.ikAPk = d.idA := by
      rw [hInstRel.hdr_eq.1, hInstRel.idB_eq.2.1]
    dsimp [cliInstDir, cliPeerKey, cliPqxdhDirBobAfterAccept, cliPqxdhDirBobBeforeAccept]
    unfold removeOpk markKyberUsed
    repeat' split
    all_goals simp only [Option.getD, hidA, and_self]

private theorem addrsE_len_36 (s r : Party) (a : Bytes)
    (h : serializedPartyAddresses LibsignalTripleRatchetRepr.uuidTryParse s r = some a) : a.length = 36 := by
  unfold serializedPartyAddresses at h
  rcases hs : LibsignalTripleRatchetRepr.serviceIdParse LibsignalTripleRatchetRepr.uuidTryParse
      (LibsignalTripleRatchetRepr.utf8 (partyAddressName s)) with _ | vs <;> rw [hs] at h
  · cases h
  · dsimp only [bind, Option.bind] at h
    rcases hr : LibsignalTripleRatchetRepr.serviceIdParse LibsignalTripleRatchetRepr.uuidTryParse
        (LibsignalTripleRatchetRepr.utf8 (partyAddressName r)) with _ | vr <;> rw [hr] at h
    · cases h
    · simp only [bind, Option.bind, pure, Option.some.injEq] at h; subst h
      simp only [LibsignalTripleRatchetRepr.addrBytes, List.length_append, List.length_cons,
        List.Vector.toList_length, List.length_nil]

private theorem mut_exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s = match Mut.exec m s with
      | (.ok a, s') => Mut.exec (f a) s' | (.error e, s') => (.error e, s') := by
  cases h : m s with | mk r s' =>
    cases r <;> (simp [Mut.exec, h, bind, ExceptT.bind, ExceptT.mk, StateT.bind, ExceptT.bindCont,
      StateT.run, ExceptT.run]; try rfl)
private theorem mut_exec_pure {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a : Mut σ α) s = (.ok a, s) := rfl
private theorem mut_exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl
private theorem mut_exec_get {σ : Type} (s : σ) : Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl
private theorem mut_exec_set {σ : Type} (s' s : σ) :
    Mut.exec (set s' : Mut σ Unit) s = (.ok (), s') := rfl
private theorem mut_exec_modify {σ : Type} (f : σ → σ) (s : σ) :
    Mut.exec (modify f : Mut σ Unit) s = (.ok (), f s) := rfl
private theorem mut_exec_modifyGet {σ α : Type} (f : σ → α × σ) (s : σ) :
    Mut.exec (modifyGet f : Mut σ α) s = (.ok (f s).1, (f s).2) := rfl
private theorem mut_exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r : Mut σ α) s = (r, s) := by cases r <;> rfl

private theorem bhDecodePreKeyMsgE_head_ne (t : BitVec 8) (xs : Bytes) (ht : t ≠ wirePrekey) :
    bhDecodePreKeyMsgE (t :: xs) = none := by
  unfold bhDecodePreKeyMsgE bhDecodePreKeyMsgERaw
  rcases xs with _ | ⟨_, _⟩ <;> simp [ht]

private theorem messageEncrypt_ok_cli_props (W : PEParams) (g : GhostState Bytes)
    (m : Bytes) (r : BitVec 512) (msg : SignalMessage) (s : SessionState Bytes)
    (hver : g.session.sessionVersion = 4)
    (hm : SessionState.messageEncrypt W.C protoSignalCodec (pqxdhSpqrSession W)
      ((pqxdhSessionParams W).sendAddrs g.party) m (coinBytesVec64 r).toList g.session = (.ok msg, s)) :
    msg.serialized.length ≤ m.length + 300 ∧
    msg.serialized ≠ [] ∧
    msg.serialized.isEmpty = false ∧
    (∀ body, msg.serialized ≠ wireWhisper :: body) ∧
    bhDecodePreKeyMsgE msg.serialized = none ∧
    s.pendingPreKey = g.session.pendingPreKey ∧
    s.localIdentity = g.session.localIdentity ∧
    s.remoteIdentity = g.session.remoteIdentity := by
  have hhe := hm
  rw [coinBytesVec64_toList] at hhe
  unfold SessionState.messageEncrypt OutgoingTripleRatchet.fromSessionState
    SessionState.takePqRatchetState at hhe
  simp only [mut_exec_bind, mut_exec_pure, mut_exec_throw, mut_exec_get, mut_exec_set,
    mut_exec_modify, mut_exec_modifyGet, mut_exec_liftE] at hhe
  rcases hsc : g.session.senderChain with _ | sc
  · simp [hsc, mut_exec_throw] at hhe
  · simp only [hsc, mut_exec_pure, mut_exec_bind, mut_exec_modifyGet, mut_exec_get] at hhe
    split_ifs at hhe
    · simp [mut_exec_throw] at hhe
    · rcases hrem : g.session.remoteIdentity with _ | remote
      · simp [hrem, mut_exec_throw] at hhe
      · simp only [hrem, mut_exec_pure, mut_exec_bind, mut_exec_modifyGet] at hhe
        unfold OutgoingTripleRatchet.encrypt OutgoingTripleRatchet.applyToSessionState at hhe
        simp only [mut_exec_bind, mut_exec_pure, mut_exec_throw, mut_exec_get, mut_exec_set,
          mut_exec_modify, mut_exec_modifyGet, mut_exec_liftE] at hhe
        cases hpan : (pqxdhSpqrSession W).sendPanics g.session.pqRatchetState (coinBytes r)
        case true => simp [hpan, mut_exec_throw] at hhe
        simp only [hpan, Bool.false_eq_true, ↓reduceIte] at hhe
        rcases hs : (pqxdhSpqrSession W).send g.session.pqRatchetState (coinBytes r) with
          _ | ⟨pq', key, pm⟩
        · simp [hs, mut_exec_throw] at hhe
        · have hpmlen : pm.length ≤ 64 :=
            CryptoVerification.SpqrV1Sync.SendTotal.spqrV1Send_msg_len_le
              W.C.F W.Q.K g.session.pqRatchetState r pq' key pm hs
          simp only [hs, mut_exec_pure, mut_exec_bind] at hhe
          rcases hn : sc.chainKey.nextChainKey W.C.F with _ | next
          · simp [hn, mut_exec_liftE] at hhe
          · simp only [hn, mut_exec_liftE, mut_exec_bind, mut_exec_pure, mut_exec_get,
              mut_exec_set, Prod.mk.injEq, Except.ok.injEq] at hhe
            rcases hhe with ⟨rfl, rfl⟩
            have hvar : ∀ k v, (encodeVarintAux k v).length ≤ k := by
              intro k; induction k with
              | zero => simp [encodeVarintAux]
              | succ k ih =>
                intro v; unfold encodeVarintAux; split <;>
                  [simp; (simp only [List.length_cons]; have := ih (v >>> 7); omega)]
            have hu32 : ∀ tag v, (encodeUint32Field tag v).length ≤ 20 := by
              intro tag v; cases v with
              | none => simp [encodeUint32Field]
              | some v =>
                simp only [encodeUint32Field, List.length_append]
                have h1 := hvar 10 (BitVec.ofNat 64 (tag * 8 + WireType.varint.toNat))
                have h2 := hvar 10 (v.zeroExtend 64)
                unfold encodeKey CryptoVerification.LibsignalProtoCodec.encodeVarint at *; omega
            have hbf : ∀ tag bs, (encodeBytesField tag (some bs)).length ≤ 20 + bs.length := by
              intro tag bs; simp only [encodeBytesField, List.length_append]
              have h1 := hvar 10 (BitVec.ofNat 64 (tag * 8 + WireType.lengthDelimited.toNat))
              have h2 := hvar 10 (BitVec.ofNat 64 bs.length)
              unfold encodeKey CryptoVerification.LibsignalProtoCodec.encodeVarint at *; omega
            have hblk : ∀ l : List (BitVec 128),
                (l.flatMap CBC.blockToBytesLE).length = 16 * l.length := by
              intro l; induction l with
              | nil => rfl
              | cons b t ih =>
                have hb : (CBC.blockToBytesLE b).length = 16 := by simp [CBC.blockToBytesLE]
                simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, hb]; omega
            have hct : ∀ k iv, (aesCbcEncrypt W.C.E k iv m).length = 16 * (m.length / 16 + 1) := by
              intro k iv; unfold aesCbcEncrypt; rw [hblk, List.Vector.toList_length]; rfl
            have had6 : (encodeBytesField 6
                (g.session.encryptAddresses ((pqxdhSessionParams W).sendAddrs g.party))).length ≤ 56 := by
              unfold SessionState.encryptAddresses pqxdhSessionParams Params.sendAddrs
              split_ifs
              · cases g.party <;> {
                  dsimp only
                  cases had : serializedPartyAddresses LibsignalTripleRatchetRepr.uuidTryParse _ _ with
                  | none => simp [encodeBytesField]
                  | some ad => have h1 := hbf 6 ad; have h2 := addrsE_len_36 _ _ ad had; omega }
              · simp [encodeBytesField]
            have hrk : sc.ratchetKey.publicKey.serialize.length = 33 := by simp [PublicKey.serialize]
            have h5 : (encodeBytesField 5 (if pm.isEmpty then none else some pm)).length ≤
                20 + pm.length := by split <;> [simp [encodeBytesField]; exact hbf 5 pm]
            refine ⟨?_, List.cons_ne_nil _ _, rfl, ?_, ?_, rfl, rfl, rfl⟩
            · dsimp only [SignalMessage.new]; rw [List.length_append]
              refine Nat.le_trans (Nat.add_le_add_left (List.length_take_le 8 _) _) ?_
              dsimp only [serializeContent, protoSignalCodec,
                CryptoVerification.LibsignalProtoCodec.encode]
              simp only [List.length_append, List.length_cons]
              have h1 := hbf 1 sc.ratchetKey.publicKey.serialize
              have h2 := hu32 2 (some sc.chainKey.index)
              have h3 := hu32 3 (some g.session.previousCounter)
              have h4 := hbf 4 (aesCbcEncrypt W.C.E
                ((sc.chainKey.messageKeys W.C.F).generateKeys W.C.F key).cipherKey
                ((sc.chainKey.messageKeys W.C.F).generateKeys W.C.F key).iv m)
              have h4' := hct ((sc.chainKey.messageKeys W.C.F).generateKeys W.C.F key).cipherKey
                ((sc.chainKey.messageKeys W.C.F).generateKeys W.C.F key).iv
              omega
            · intro body heq
              dsimp only [SignalMessage.new, serializeContent, BitVec.setWidth,
                SessionState.version, List.cons_append] at heq
              rw [hver] at heq; injection heq with h0 _; revert h0; decide
            · dsimp only [SignalMessage.new, serializeContent, BitVec.setWidth,
                SessionState.version, List.cons_append]
              apply bhDecodePreKeyMsgE_head_ne; rw [hver]; decide

private theorem bhWireInnerBytes_wireWhisper_local (body : Bytes) :
    bhWireInnerBytes (wireWhisper :: body) = some body := by
  have hdec : bhDecodePreKeyMsgE (wireWhisper :: body) = none := by
    unfold bhDecodePreKeyMsgE bhDecodePreKeyMsgERaw; cases body <;> rfl
  unfold bhWireInnerBytes; simp [hdec]

private theorem bhWireInnerBytes_wirePrekey_local (m : PreKeyMessageFields) :
    bhWireInnerBytes (wirePrekey :: m.bytes) = some m.inner := by
  have hk1 : Prost.key 1 0 = [0x08#8] := by rw [Prost.key, Prost.varint.eq_def]; decide
  have hk2 : Prost.key 2 2 = [0x12#8] := by rw [Prost.key, Prost.varint.eq_def]; decide
  have hk3 : Prost.key 3 2 = [0x1a#8] := by rw [Prost.key, Prost.varint.eq_def]; decide
  have hk4 : Prost.key 4 2 = [0x22#8] := by rw [Prost.key, Prost.varint.eq_def]; decide
  have hk5 : Prost.key 5 0 = [0x28#8] := by rw [Prost.key, Prost.varint.eq_def]; decide
  have hk6 : Prost.key 6 0 = [0x30#8] := by rw [Prost.key, Prost.varint.eq_def]; decide
  have hk7 : Prost.key 7 0 = [0x38#8] := by rw [Prost.key, Prost.varint.eq_def]; decide
  have hk8 : Prost.key 8 2 = [0x42#8] := by rw [Prost.key, Prost.varint.eq_def]; decide
  have hv33 : Prost.varint 33 = [0x21#8] := by rw [Prost.varint.eq_def]; decide
  have hv1569 : Prost.varint 1569 = [0xa1#8, 0x0c#8] := by
    rw [Prost.varint.eq_def]; change [0xa1#8] ++ Prost.varint 12 = [0xa1#8, 0x0c#8]
    rw [Prost.varint.eq_def]; decide
  have hdjb : ∀ (tag : ℕ) (kb : BitVec 8), Prost.key tag 2 = [kb] →
      ∀ (k : List.Vector (BitVec 8) 32) (rest : List (BitVec 8)),
      bhParseDjbKeyField kb (Prost.bytesField tag (some (djbKey k)) ++ rest) =
        some (k.toList, rest) := fun tag kb hkey ⟨kl, hkl⟩ rest => by
    have htake : (kl ++ rest).take 32 = kl := by rw [← hkl, List.take_left]
    have hdrop : (kl ++ rest).drop 32 = rest := by rw [← hkl, List.drop_left]
    simp [Prost.bytesField, hkey, djbKey, hkl, hv33, bhParseDjbKeyField, htake, hdrop]
  have hu32f : ∀ (tag : ℕ) (kb : BitVec 8), Prost.key tag 0 = [kb] →
      ∀ (v : BitVec 32) (rest : List (BitVec 8)),
      bhParseUint32Field kb (Prost.uint32Field tag (some v) ++ rest) = some (u32 v, rest) :=
    fun tag kb hkey v rest => by
      simp [Prost.uint32Field, hkey, bhParseUint32Field, bhReadProstVarint_varint_append, u32]
  have hraw : bhDecodePreKeyMsgERaw (wirePrekey :: m.bytes) = some m := by
    rcases m with ⟨regId, opkId, spkId, kpkId, ⟨ctL, hct⟩, ⟨bkL, hbk⟩, ⟨idL, hid⟩, inner⟩
    unfold PreKeyMessageFields.bytes ProtoPreKeySignalMessage.encode bhDecodePreKeyMsgERaw
    simp only [BEq.rfl, Bool.and_self, ↓reduceIte, List.append_assoc]
    have hopk : bhParseOptPreKeyId (Prost.uint32Field 1 opkId ++
        (Prost.bytesField 2 (some (djbKey ⟨bkL, hbk⟩)) ++
          (Prost.bytesField 3 (some (djbKey ⟨idL, hid⟩)) ++
            (Prost.bytesField 4 (some inner) ++
              (Prost.uint32Field 5 (some regId) ++
                (Prost.uint32Field 6 (some spkId) ++
                  (Prost.uint32Field 7 (some kpkId) ++
                    Prost.bytesField 8 (some (kyberKey ⟨ctL, hct⟩))))))))) =
        some (opkId.map u32, Prost.bytesField 2 (some (djbKey ⟨bkL, hbk⟩)) ++
          (Prost.bytesField 3 (some (djbKey ⟨idL, hid⟩)) ++
            (Prost.bytesField 4 (some inner) ++
              (Prost.uint32Field 5 (some regId) ++
                (Prost.uint32Field 6 (some spkId) ++
                  (Prost.uint32Field 7 (some kpkId) ++
                    Prost.bytesField 8 (some (kyberKey ⟨ctL, hct⟩)))))))) := by
      cases opkId
      · simp [Prost.uint32Field, Prost.bytesField, hk2, djbKey, hbk, hv33, bhParseOptPreKeyId]
      · simp [Prost.uint32Field, hk1, bhParseOptPreKeyId, bhReadProstVarint_varint_append, u32]
    have hinner : ∀ rest, bhParseInnerMsgFieldWithRest (Prost.bytesField 4 (some inner) ++ rest) =
        some (inner, rest) := fun rest => by
      simp [Prost.bytesField, hk4, bhParseInnerMsgFieldWithRest, bhReadProstVarint_varint_append]
    have hkyb : bhParseKyberCtField (Prost.bytesField 8 (some (kyberKey ⟨ctL, hct⟩))) =
        some ctL := by
      simp [Prost.bytesField, hk8, kyberKey, hct, hv1569, bhParseKyberCtField]
    rw [hopk]; dsimp only [Option.bind]
    rw [hdjb 2 0x12#8 hk2 ⟨bkL, hbk⟩]; dsimp only [Option.bind]
    rw [hdjb 3 0x1a#8 hk3 ⟨idL, hid⟩]; dsimp only [Option.bind]
    rw [hinner]; dsimp only [Option.bind]
    rw [hu32f 5 0x28#8 hk5 regId]; dsimp only [Option.bind]
    rw [hu32f 6 0x30#8 hk6 spkId]; dsimp only [Option.bind]
    rw [hu32f 7 0x38#8 hk7 kpkId]; dsimp only [Option.bind]
    rw [hkyb]; dsimp only [Option.bind, List.Vector.toList]
    have hmap : ∀ o : Option (BitVec 32), (o.map u32).map UInt32.toBitVec = o := fun o => by
      cases o <;> rfl
    simp only [hbk, hid, hct, ↓reduceDIte, hmap, u32, UInt32.toBitVec_ofBitVec]
  unfold bhWireInnerBytes bhDecodePreKeyMsgE; simp [hraw]

private theorem pqParty_with_peer_session_eq (d0 : PqParty) (k : IdentityKey)
    (s₀ s₁ : Option (RecordExtras × GhostState Bytes)) (hp : d0.peerId = some k) :
    { { d0 with session := s₀ } with peerId := some k, session := s₁ } =
      { d0 with session := s₁ } := by
  cases d0; dsimp only at hp ⊢; rw [hp]

private theorem cliPqSend_party_adapter_props {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hCli : CliSpecPqxdh run X W) (hℓ : ℓ < 10 ^ 6)
    {q_rem : ℕ} (_hq_pos : 0 < q_rem)
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {bi : ModelDriverInstance S ℓ} {d : BHModelInst S ℓ} {im im_e2e : ModelDriverInstanceMeta S}
    {inst : BHAdapterInstMeta S} {ack : Bool}
    (hInstRel : CliAdapterInstRel X W q_rem st_cli ds_cli bi d im im_e2e inst ack)
    (p : Party) (g : GhostState Bytes) (m : Plain ℓ) (r : BitVec 512) (pos : SM.Pos)
    (hpos : pos.sender = p)
    (hParty : g.party = p)
    (hppk : g.session.pendingPreKey = match p with | .A => !ack | .B => false)
    (hidA : p = .A → g.session.localIdentity = d.idA)
    (hack0 : !im.bobAccepted → ack = false)
    (hRemP : g.session.remoteIdentity = some (cliPeerKey d p))
    (hAct : CliPartyActiveInv W (cliInstDir bi (cliPqSigsOf st_cli bi) p)
      (cliInstExtras inst p) g q_rem) :
    let P_v1 := paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB
    let out_m := P_v1.send g m.toList r
    let s_bin := bhBinStateOfParty inst g
    let sigs := cliPqSigsOf st_cli bi
    let out_cli := cliPqSend run W (cliPqDirOf bi sigs s_bin) s_bin m.toList r
    out_cli.1 = bhBinStateOfParty inst out_m.1 ∧
    out_cli.2 = cliWrapAdapterSend inst ack p out_m.2 ∧
    CliAdapterTransEntryRel im.bobAccepted d.sid d.hdr ⟨pos, m, out_cli.2⟩ ⟨pos, m, out_m.2⟩ ∧
    out_m.1.party = p ∧
    out_m.1.session.pendingPreKey = g.session.pendingPreKey ∧
    out_m.1.session.localIdentity = g.session.localIdentity ∧
    out_m.1.session.remoteIdentity = some (cliPeerKey d p) ∧
    g.epoch ≤ out_m.1.epoch ∧
    CliPartyActiveInv W (cliInstDir bi sigs p) (cliInstExtras inst p) out_m.1 (q_rem - 1) := by
  intro P_v1 out_m s_bin sigs out_cli
  set d0 := cliInstDir bi sigs p
  set x := cliInstExtras inst p
  set k := cliPeerKey d p
  set st : PqParty := { d0 with session := some (x, g) }
  have hsess : st.session = some (x, g) := rfl
  obtain ⟨hd0_party, hd0_peer⟩ := cliInstDir_party_peerId hInstRel sigs p
  have hs_bin_eq : s_bin = binStateOfUnderExtras (fun _ => x) g := by
    dsimp only [s_bin, x, cliInstExtras]; unfold bhBinStateOfParty; rw [hParty]; cases p <;> rfl
  have hs_bin_party : s_bin.party = p := by rw [hs_bin_eq]; exact hParty
  have hdirOf : cliPqDirOf bi sigs s_bin = d0 := by
    rw [hs_bin_eq]; unfold cliPqDirOf binStateOfUnderExtras; dsimp only [d0, cliInstDir]
    rw [hParty]; cases p <;> [rfl; simp [encodeRecordX_isEmpty_eq_false]]
  have hm32 : m.toList.length < 2 ^ 32 := by have := m.toList_length; omega
  have hinp : cliPqInputs W d0 s_bin.bytes (.send (partyAddress p.other)) [] (coinBytes r) m.toList =
      pqSendInputs W st m.toList (coinBytesVec64 r) := by
    rw [hs_bin_eq]; unfold cliPqInputs pqSendInputs pqInputs binStateOfUnderExtras; dsimp only [st]
    have hraw : cliPqDirRaw W d0 (encodeRecordUnderExtras (fun _ => x) g) =
        encodeDir W { d0 with session := some (x, g) } :=
      cliPqDirRawSpec_encodeRecordX_eq_encodeDir W d0 x g
    rw [hraw, coinBytesVec64_toList, hd0_party]
  have hrun : run (pqSendInputs W st m.toList (coinBytesVec64 r)) =
      some (pqxdhExpectedOutcome W (pqSendInputs W st m.toList (coinBytesVec64 r))
        (pqSendModel W st m.toList (coinBytesVec64 r).toList)) := by
    have hm_sc : ¬ m.toList.length > stdinCapBytes := by
      have := m.toList_length; unfold stdinCapBytes; omega
    have hm_pc : ¬ m.toList.length > maxPlaintextBytes := by
      have := m.toList_length; unfold maxPlaintextBytes; omega
    have hrun0 := (hCli st hAct.1).2.1 m.toList (coinBytesVec64 r) hm32
    simpa only [hm_sc, hm_pc, ↓reduceIte] using hrun0
  have hSendEq : out_m = (pqxdhSessionParams W).send g m.toList (coinBytesVec64 r).toList := by
    change (paramsPqBIds W d.idA d.idB).send g m.toList r = _
    rw [paramsPqBIds_send_eq, ← paramsPqIds_idOfE W]
    unfold Params.send paramsPqIds Params.sendAddrs; cases g.party <;> rfl
  have htrust : st.trusts k = true := by
    unfold PqParty.trusts; dsimp only [st, d0, k]; rw [hd0_peer]; exact decide_eq_true rfl
  obtain ⟨⟨g₀, hR₀, _, hs₀⟩, _, _⟩ := hAct.1.1 x g rfl
  have hver : g.session.sessionVersion = 4 := hs₀ ▸ (reachPq_invCli hR₀).sessionVersion_eq
  have hal_send := aligned_send_gen (pqxdhSessionParams W) g m.toList (coinBytesVec64 r).toList hAct.2.2.1
  have hP_C : (pqxdhSessionParams W).C = W.C := rfl
  have hP_codec : (pqxdhSessionParams W).codec = protoSignalCodec := rfl
  have hP_spqr : (pqxdhSessionParams W).spqr = pqxdhSpqrSession W := rfl
  rcases henc : SessionState.messageEncrypt W.C protoSignalCodec (pqxdhSpqrSession W)
      ((pqxdhSessionParams W).sendAddrs g.party) m.toList (coinBytesVec64 r).toList g.session with
    ⟨err | msg, s⟩
  · have hout_m : out_m = (g, []) := by
      rw [hSendEq]; unfold Params.send; rw [hP_C, hP_codec, hP_spqr, henc]
    have hafter : cliPqAfter p (run (pqSendInputs W st m.toList (coinBytesVec64 r))) = none := by
      rw [hrun]
      have hobs := cliPqAfterSpec_pqObserve_eq W p (pqSendInputs W st m.toList (coinBytesVec64 r))
        (pqSendModel W st m.toList (coinBytesVec64 r).toList) (by
          intro _ _ hr; unfold pqSendModel at hr; rw [hsess] at hr; dsimp only at hr
          rw [henc] at hr; cases err <;> cases hr)
      change cliPqAfterSpec p _ = none; rw [hobs]
      unfold pqSendModel; rw [hsess]; dsimp only; rw [henc]; cases err <;> rfl
    have hout_cli : out_cli = (s_bin, []) := by
      dsimp only [out_cli]; unfold cliPqSend
      rw [hdirOf, hs_bin_party, hinp, hafter]
    have hwire : cliWrapAdapterSend inst ack p [] = [] := by
      cases p <;> (try cases ack) <;> simp [cliWrapAdapterSend, SM.partyEnc, bhWrapSendOut]
    rw [hout_cli, hout_m]
    exact ⟨rfl, hwire.symm, ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩, hParty, rfl, rfl, hRemP,
      Nat.le_refl _, cliPartyActiveInv_mono hAct (Nat.sub_le _ _)⟩
  · have hnt : (!st.trusts k) = false := by simp [htrust]
    let st_raw : PqParty := { d0 with session := some (x, { g with session := s }) }
    have hst_raw_eq :
        { st with peerId := some k, session := some (x, { g with session := s }) } = st_raw :=
      pqParty_with_peer_session_eq d0 k _ _ hd0_peer
    let rawWire := if g.session.pendingPreKey then wirePrekey :: firstMessageBody x g.session msg
      else wireWhisper :: msg.serialized
    have hmod : pqSendModel W st m.toList (coinBytesVec64 r).toList =
        some (some (st_raw, rawWire)) := by
      unfold pqSendModel rawWire; rw [hsess]; dsimp only; rw [henc]; dsimp only
      rw [hRemP]; dsimp only; rw [hnt]
      simp only [Bool.false_eq_true, ↓reduceIte, hst_raw_eq]
    have hstep : PqStep X W st st_raw :=
      PqStep.send m.toList (coinBytesVec64 r) st_raw rawWire hm32 hmod
    have hlr_st : lastResortUses st_raw < 2 ^ 25 := by
      simpa [lastResortUses, st_raw] using hAct.2.1
    obtain ⟨hwf_raw, _⟩ := wfPq_step_r3 hAct.1 hstep hlr_st
    have hafter : cliPqAfter p (run (pqSendInputs W st m.toList (coinBytesVec64 r))) =
        some (encodeRecordUnderExtras (fun _ => x) { g with session := s }, rawWire) := by
      rw [hrun]
      have hobs := cliPqAfterSpec_pqObserve_eq W p (pqSendInputs W st m.toList (coinBytesVec64 r))
        (pqSendModel W st m.toList (coinBytesVec64 r).toList) (by
          intro st' out hr; rw [hmod] at hr
          simp only [Option.some.injEq, Prod.mk.injEq] at hr; rcases hr with ⟨rfl, rfl⟩
          exact ⟨hd0_party, x, { g with session := s }, rfl⟩)
      change cliPqAfterSpec p _ = _; rw [hobs, hmod]; rfl
    have hout_m_eq : out_m =
        ({ g with session := s,
                  epoch := if g.party.sendsIn g.epoch then g.epoch else g.epoch + 1 },
         msg.serialized) := by
      rw [hSendEq]; unfold Params.send; rw [hP_C, hP_codec, hP_spqr, henc]
    have hout_m_sess : ({ g with session := s } : GhostState Bytes).session = out_m.1.session := by
      rw [hout_m_eq]
    have hout_m_party : out_m.1.party = p := by rw [hout_m_eq]; exact hParty
    have hep' : EpochGhost.ofGhost out_m.1 = s_bin.epochs.send p := by
      have h2 := hal_send.2
      rw [← hSendEq, hP_C, hP_codec, hP_spqr, henc, hParty] at h2
      simp only [Except.isOk, Except.toBool, ↓reduceIte] at h2
      rw [hs_bin_eq]; exact h2
    have hout_cli_eq : out_cli = (bhBinStateOfParty inst out_m.1, rawWire) := by
      dsimp only [out_cli]; unfold cliPqSend
      rw [hdirOf, hs_bin_party, hinp, hafter]
      have hrec_eq : encodeRecordUnderExtras (fun _ => x) { g with session := s } =
          encodeRecordUnderExtras (fun _ => x) out_m.1 := by unfold encodeRecordUnderExtras; rw [hout_m_sess]
      rw [hrec_eq, ← hep']
      unfold bhBinStateOfParty binStateOfUnderExtras; rw [hout_m_party]; cases p <;> rfl
    obtain ⟨hser_le, hser_ne, hser_emp, hser_no2, hser_no3, hs_ppk, hs_loc, hs_rem⟩ :=
      messageEncrypt_ok_cli_props W g m.toList r msg s hver henc
    have hwf_out : PqxdhPartyInSpecDomain W { d0 with session := some (x, out_m.1) } :=
      wfPq_of_session_party_eq hwf_raw (hParty.trans hout_m_party.symm) hout_m_sess
    have hlr_out : lastResortUses { d0 with session := some (x, out_m.1) } < 2 ^ 25 := by
      simpa [lastResortUses] using hAct.2.1
    have hAct' : CliPartyActiveInv W d0 x out_m.1 (q_rem - 1) :=
      ⟨hwf_out, hlr_out, hSendEq ▸ hal_send.1, pqLength_le_286196_of_wfPq hwf_out⟩
    have hser_bound : msg.serialized.length ≤ 1_000_300 ∧ msg.serialized.length + 2048 < 2 ^ 32 := by
      have := m.toList_length; omega
    have hwire_rel : rawWire = cliWrapAdapterSend inst ack p msg.serialized ∧
        CliAdapterTransEntryRel im.bobAccepted d.sid d.hdr ⟨pos, m, rawWire⟩ ⟨pos, m, msg.serialized⟩ := by
      cases p
      · have hidA' : g.session.localIdentity = bhIdKeyOf inst.hdr.ikAPk := by
          rw [hidA rfl, hInstRel.idB_eq.2.1, hInstRel.hdr_eq.2]
        have hfmb : firstMessageBody (bhInstExtrasA inst) g.session msg =
            (bhAlicePreKeyMsgE inst msg.serialized).bytes := by
          unfold firstMessageBody bhAlicePreKeyMsgE bhExpectedPreKeyMsg PreKeyMessageFields.bytes
            bhInstExtrasA PreKeySignalMessage.new SessionState.version
          rw [hver, hidA', bhIdKeyOf]; rfl
        have hexp_eq : bhAlicePreKeyMsgE inst msg.serialized =
            bhExpectedPreKeyMsg (bhInitRegId d.sid) d.hdr msg.serialized := by
          unfold bhAlicePreKeyMsgE bhExpectedPreKeyMsg
          rw [hInstRel.sid_eq.2, hInstRel.hdr_eq.2]
        cases hack : ack
        · have hppkA : g.session.pendingPreKey = true := by rw [hppk, hack]; rfl
          have hraw_eq : rawWire =
              wirePrekey :: (bhExpectedPreKeyMsg (bhInitRegId d.sid) d.hdr msg.serialized).bytes := by
            dsimp only [rawWire, x, cliInstExtras]; rw [hppkA, hfmb, hexp_eq]; rfl
          have hwrap_eq : cliWrapAdapterSend inst false .A msg.serialized =
              wirePrekey :: (bhExpectedPreKeyMsg (bhInitRegId d.sid) d.hdr msg.serialized).bytes := by
            unfold cliWrapAdapterSend SM.partyEnc bhWrapSendOut
            rw [hser_emp, hInstRel.aliceAcked_false, hexp_eq]; rfl
          rw [hraw_eq, hwrap_eq]
          exact ⟨rfl, rfl, rfl, Or.inr ⟨hser_ne, hser_no3, hser_no2, hser_bound,
            fun _ => ⟨bhWireInnerBytes_wirePrekey_local _, fun _ => rfl⟩,
            fun hB => Party.noConfusion (hpos.symm.trans hB)⟩⟩
        · have hppkA : g.session.pendingPreKey = false := by rw [hppk, hack]; rfl
          have hraw_eq : rawWire = wireWhisper :: msg.serialized := by
            dsimp only [rawWire]; rw [hppkA]; rfl
          have hwrap_eq : cliWrapAdapterSend inst true .A msg.serialized =
              wireWhisper :: msg.serialized := by
            unfold cliWrapAdapterSend SM.partyEnc; rw [hser_emp]; rfl
          rw [hraw_eq, hwrap_eq]
          exact ⟨rfl, rfl, rfl, Or.inr ⟨hser_ne, hser_no3, hser_no2, hser_bound,
            fun _ => ⟨bhWireInnerBytes_wireWhisper_local _, fun hnot =>
              False.elim (Bool.false_ne_true ((hack0 hnot).symm.trans hack))⟩,
            fun hB => Party.noConfusion (hpos.symm.trans hB)⟩⟩
      · have hppkB : g.session.pendingPreKey = false := hppk
        have hraw_eq : rawWire = wireWhisper :: msg.serialized := by
          dsimp only [rawWire]; rw [hppkB]; rfl
        have hwrap_eq : cliWrapAdapterSend inst ack .B msg.serialized =
            wireWhisper :: msg.serialized := by
          unfold cliWrapAdapterSend SM.partyEnc; rw [hser_emp]; rfl
        rw [hraw_eq, hwrap_eq]
        exact ⟨rfl, rfl, rfl, Or.inr ⟨hser_ne, hser_no3, hser_no2, hser_bound,
          fun hA => Party.noConfusion (hpos.symm.trans hA), fun _ => rfl⟩⟩
    have hout_m_2 : out_m.2 = msg.serialized := by rw [hout_m_eq]
    have hout_m_ppk : out_m.1.session.pendingPreKey = g.session.pendingPreKey := by
      rw [hout_m_eq]; exact hs_ppk
    have hout_m_loc : out_m.1.session.localIdentity = g.session.localIdentity := by
      rw [hout_m_eq]; exact hs_loc
    have hout_m_rem : out_m.1.session.remoteIdentity = some k := by
      rw [hout_m_eq]; exact hs_rem.trans hRemP
    have hout_m_ep : g.epoch ≤ out_m.1.epoch := by
      rw [hout_m_eq]; dsimp only; split_ifs <;> omega
    exact ⟨congrArg Prod.fst hout_cli_eq,
      (congrArg Prod.snd hout_cli_eq).trans (hout_m_2 ▸ hwire_rel.1),
      (congrArg Prod.snd hout_cli_eq).symm ▸ hout_m_2 ▸ hwire_rel.2,
      hout_m_party, hout_m_ppk, hout_m_loc, hout_m_rem, hout_m_ep, hAct'⟩

theorem cliPqReceive_A_nonWhisper_eq_none {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams} (hCli : CliSpecPqxdh run X W)
    {q_rem : ℕ} (bi : ModelDriverInstance S ℓ)
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64)
    (x : RecordExtras) (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256)
    (hParty : g.party = .A)
    (hAct : CliPartyActiveInv W (cliPqDirA bi) x g q_rem)
    (hno : ¬ ((∃ body, c = wireWhisper :: body) ∧ c.length < 2 ^ 32)) :
    cliPqReceive run W ℓ bi sigs (binStateOfUnderExtras (fun _ => x) g) c rc = none := by
  unfold cliPqReceive
  cases hlen : cliPqLenOk c
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hc32 : c.length < 2 ^ 32 := by
      unfold cliPqLenOk shortCiphertext at hlen
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hlen; exact hlen.1
    have hParty' : (binStateOfUnderExtras (fun _ => x) g).party = .A := hParty
    rw [hParty']; dsimp only
    cases hpk : (c.head? == some wirePrekey)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hne3 : c.head? ≠ some wirePrekey := by intro h; rw [h] at hpk; simp at hpk
      have hne2 : c.head? ≠ some wireWhisper := by
        rcases c with _ | ⟨b, body⟩
        · simp
        · intro h; simp only [List.head?, Option.some.injEq] at h
          exact hno ⟨⟨body, congrArg (· :: body) h⟩, hc32⟩
      set st : PqParty := { cliPqDirA bi with session := some (x, g) }
      have hrun := (hCli st hAct.1).2.2.2.2 c rc hc32 hne2 hne3
      have hinp : cliPqInputs W (cliPqDirA bi) (encodeRecordUnderExtras (fun _ => x) g)
          (.recv (partyAddress Party.A.other)) [] (HMAC.keyToBytes32 rc) c =
          pqRecvInputs W st c rc := by
        unfold cliPqInputs pqRecvInputs pqInputs
        have hraw : cliPqDirRaw W (cliPqDirA bi) (encodeRecordUnderExtras (fun _ => x) g) = encodeDir W st :=
          cliPqDirRawSpec_encodeRecordX_eq_encodeDir W (cliPqDirA bi) x g
        rw [hraw]; rfl
      unfold cliPqRecv cliPqDirOf binStateOfUnderExtras
      dsimp only; rw [hParty]; dsimp only; rw [hinp, hrun]
      by_cases hc_cap : c.length > stdinCapBytes <;> simp [hc_cap, cliPqAfter]
    · simp

theorem cliPqReceive_A_nil_eq_none {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams} (hCli : CliSpecPqxdh run X W)
    {q_rem : ℕ} (bi : ModelDriverInstance S ℓ)
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64)
    (x : RecordExtras) (g : GhostState Bytes) (rc : BitVec 256)
    (hParty : g.party = .A)
    (hAct : CliPartyActiveInv W (cliPqDirA bi) x g q_rem) :
    cliPqReceive run W ℓ bi sigs (binStateOfUnderExtras (fun _ => x) g) [] rc = none :=
  cliPqReceive_A_nonWhisper_eq_none hCli bi sigs x g [] rc hParty hAct
    (by rintro ⟨⟨_, h⟩, _⟩; cases h)

open CryptoVerification.E2E.BhAdapterIjHelpersV1 in
theorem cliPqReceive_A_whisper_props {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams} (hCli : CliSpecPqxdh run X W)
    {q_rem : ℕ} (_hq_pos : 0 < q_rem)
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {bi : ModelDriverInstance S ℓ} {d : BHModelInst S ℓ} {im im_e2e : ModelDriverInstanceMeta S}
    {inst : BHAdapterInstMeta S} {ack : Bool}
    (hInstRel : CliAdapterInstRel X W q_rem st_cli ds_cli bi d im im_e2e inst ack)
    (g : GhostState Bytes) (body : Bytes) (rc : BitVec 256)
    (hParty : g.party = .A)
    (hRemA : g.session.remoteIdentity = some d.idB)
    (hAct : CliPartyActiveInv W (cliPqDirA bi) (bhInstExtrasA inst) g q_rem)
    (hc32 : (wireWhisper :: body).length < 2 ^ 32)
    (hcap : (wireWhisper :: body).length ≤ stdinCapBytes) :
    let P_v1 := paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB
    let x := bhInstExtrasA inst
    let sigs := cliPqSigsOf st_cli bi
    cliPqReceive run W ℓ bi sigs (binStateOfUnderExtras (fun _ => x) g) (wireWhisper :: body) rc =
      (P_v1.receive g body rc).map (fun (g', t', idx', pt') =>
        (binStateOfUnderExtras (fun _ => x) g', t', idx', padOrTruncatePlain ℓ pt')) ∧
    (∀ g' t' idx' pt', P_v1.receive g body rc = some (g', t', idx', pt') →
      g'.party = .A ∧
      g'.session.pendingPreKey = false ∧
      g'.session.localIdentity = g.session.localIdentity ∧
      g'.session.remoteIdentity = some d.idB ∧
      CliPartyActiveInv W (cliPqDirA bi) x g' (q_rem - 1)) := by
  intro P_v1 x sigs
  set d0 := cliPqDirA bi
  set st : PqParty := { d0 with session := some (x, g) }
  have hsess : st.session = some (x, g) := rfl
  have hbody32 : body.length < 2 ^ 32 := by simp only [List.length_cons] at hc32; omega
  have hpeer : d0.peerId = some d.idB := congrArg some hInstRel.idB_eq.2.2.symm
  have htrust : st.trusts d.idB = true := by
    unfold PqParty.trusts; dsimp only [st, d0]; rw [hpeer]; exact decide_eq_true rfl
  obtain ⟨⟨g₀, hR₀, _, hs₀⟩, _, _⟩ := hAct.1.1 x g rfl
  have hinv₀ := reachPq_invCli hR₀
  have hchains : g.session.receiverChains.length ≤ maxReceiverChains :=
    hs₀ ▸ hinv₀.receiverChains_len
  have hval : CryptoVerification.SpqrV1.Top.StateSize.ValidState g.session.pqRatchetState :=
    hs₀ ▸ reachPq_validState_cli hR₀
  have hseeds : CryptoVerification.LibsignalTripleRatchet.SeedsLen32 g.session :=
    fun rc hrc mk hmk => (hs₀ ▸ hinv₀.receiverChains_inv) rc hrc |>.2.2.2 mk hmk
  have hpq64 : g.session.pqRatchetState.length < 2 ^ 64 := by have := hAct.2.2.2; omega
  have hdc_ww : bhDecodePreKeyMsgE (wireWhisper :: body) = none := by
    unfold bhDecodePreKeyMsgE bhDecodePreKeyMsgERaw
    rcases body with _ | ⟨_, _⟩ <;> rfl
  have hlenOk : cliPqLenOk (wireWhisper :: body) = true := by
    unfold cliPqLenOk shortCiphertext; rw [hdc_ww]; dsimp only; rw [Bool.and_true]
    exact decide_eq_true hc32
  have hinp : cliPqInputs W (cliPqDirA bi) (encodeRecordUnderExtras (fun _ => x) g)
      (.recv (partyAddress Party.A.other)) [] (HMAC.keyToBytes32 rc) (wireWhisper :: body) =
      pqRecvInputs W st (wireWhisper :: body) rc := by
    unfold cliPqInputs pqRecvInputs pqInputs
    have hraw : cliPqDirRaw W (cliPqDirA bi) (encodeRecordUnderExtras (fun _ => x) g) = encodeDir W st :=
      cliPqDirRawSpec_encodeRecordX_eq_encodeDir W (cliPqDirA bi) x g
    rw [hraw]; rfl
  have hrun : run (pqRecvInputs W st (wireWhisper :: body) rc) =
      some (pqxdhExpectedOutcome W (pqRecvInputs W st (wireWhisper :: body) rc)
        (pqRecvWhisperModel W st body rc)) := by
    have hrun0 := (hCli st hAct.1).2.2.1 body rc hbody32
    have hnc : ¬ (wireWhisper :: body).length > stdinCapBytes := Nat.not_lt.mpr hcap
    simpa only [hnc, ↓reduceIte] using hrun0
  have hRecvEq : P_v1.receive g body rc = (pqxdhSessionParams W).receive g body rc := by
    change (paramsPqBIds W d.idA d.idB).receive g body rc = _
    rw [paramsPqBIds_receive_eq, ← paramsPqIds_idOfE W]
    unfold Params.receive paramsPqIds Params.expectedAddrs; cases g.party <;> rfl
  have hP_C : (pqxdhSessionParams W).C = W.C := rfl
  have hP_codec : (pqxdhSessionParams W).codec = protoSignalCodec := rfl
  have hP_spqr : (pqxdhSessionParams W).spqr = pqxdhSpqrSession W := rfl
  refine ⟨?_, ?_⟩
  · unfold cliPqReceive cliPqRecv cliPqDirOf
    dsimp only [binStateOfUnderExtras]; rw [hlenOk, hParty]
    have hhead : ((wireWhisper :: body).head? == some wirePrekey) = false := by
      dsimp only [List.head?]; decide
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hhead, hinp, hrun, hRecvEq]
    rcases htry : SignalMessage.tryFrom protoSignalCodec body with _ | msg
    · have hmod : pqRecvWhisperModel W st body rc = some none := by
        simp [pqRecvWhisperModel, hsess, htry]
      have hrec_n : (pqxdhSessionParams W).receive g body rc = none := by
        unfold Params.receive; rw [hP_codec, htry]
      have hafter : cliPqAfter .A (some (pqxdhExpectedOutcome W (pqRecvInputs W st (wireWhisper :: body) rc)
          (pqRecvWhisperModel W st body rc))) = none := by
        have hobs := cliPqAfterSpec_pqObserve_eq W .A (pqRecvInputs W st (wireWhisper :: body) rc)
          (pqRecvWhisperModel W st body rc) (by intro _ _ hr; rw [hmod] at hr; cases hr)
        change cliPqAfterSpec .A _ = none; rw [hobs, hmod]; rfl
      rw [hafter, hrec_n]; rfl
    · rcases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
          ((pqxdhSessionParams W).expectedAddrs g.party) msg .whisper rc g.session with ⟨err | pt, s⟩
      · have hrec_n : (pqxdhSessionParams W).receive g body rc = none := by
          unfold Params.receive; rw [hP_codec, htry]; dsimp only; rw [hP_C, hP_spqr, hdec]
        have hafter : cliPqAfter .A (some (pqxdhExpectedOutcome W (pqRecvInputs W st (wireWhisper :: body) rc)
            (pqRecvWhisperModel W st body rc))) = none := by
          have hobs := cliPqAfterSpec_pqObserve_eq W .A
            (pqRecvInputs W st (wireWhisper :: body) rc) (pqRecvWhisperModel W st body rc) (by
              intro _ _ hr; unfold pqRecvWhisperModel pqxdhSessionDecryptModel at hr
              rw [hsess, htry] at hr; dsimp only at hr; rw [hdec] at hr; cases err <;> cases hr)
          change cliPqAfterSpec .A _ = none; rw [hobs]
          unfold pqRecvWhisperModel pqxdhSessionDecryptModel; rw [hsess, htry]; dsimp only
          rw [hdec]; cases err <;> rfl
        rw [hafter, hrec_n]; rfl
      · have hs_rem : s.remoteIdentity = some d.idB := by
          have hvr := (Closure.Version.tryDecryptFromRecord_sessionVersion_remoteIdentity
            W.C (pqxdhSpqrSession W) ((pqxdhSessionParams W).expectedAddrs g.party) msg .whisper rc g.session).2
          rw [hdec, hRemA] at hvr; exact hvr
        have hnt : (!st.trusts d.idB) = false := by simp [htrust]
        let st_raw : PqParty := { d0 with session := some (x, { g with session := s }) }
        have hst_raw_eq :
             { st with peerId := some d.idB, session := some (x, { g with session := s }) } =
            st_raw := pqParty_with_peer_session_eq d0 d.idB _ _ hpeer
        have hmod : pqRecvWhisperModel W st body rc = some (some (st_raw, pt)) := by
          simp [pqRecvWhisperModel, pqxdhSessionDecryptModel, hsess, htry, hdec, hs_rem, hnt, hst_raw_eq]
        have hafter : cliPqAfter .A (some (pqxdhExpectedOutcome W (pqRecvInputs W st (wireWhisper :: body) rc)
            (pqRecvWhisperModel W st body rc))) =
            some (encodeRecordUnderExtras (fun _ => x) { g with session := s }, pt) := by
          have hobs := cliPqAfterSpec_pqObserve_eq W .A
            (pqRecvInputs W st (wireWhisper :: body) rc) (pqRecvWhisperModel W st body rc) (by
              intro st' out hr; rw [hmod] at hr
              simp only [Option.some.injEq, Prod.mk.injEq] at hr; rcases hr with ⟨rfl, rfl⟩
              exact ⟨rfl, x, { g with session := s }, rfl⟩)
          change cliPqAfterSpec .A _ = _; rw [hobs, hmod]; rfl
        rcases hrec : (pqxdhSessionParams W).receive g body rc with _ | ⟨g', t', idx', pt'⟩
        · exfalso; unfold Params.receive at hrec
          rw [hP_codec, htry] at hrec; dsimp only at hrec; rw [hP_C, hP_spqr, hdec] at hrec
          simp at hrec
        · have hrae := recv_aligned_and_epochs_gen (pqxdhSessionParams W) g body rc hAct.2.2.1 hchains msg
            (by rw [hP_codec]; exact htry) (g', t', idx', pt') hrec
          have hrae_ep : (EpochGhost.ofGhost g).recv msg.senderRatchetKey =
              (t', EpochGhost.ofGhost g') := hrae.2.2.1
          have hrae_idx : idx' = msg.counter.toNat + 1 := hrae.2.2.2.1
          have hrae_p : g'.party = g.party := hrae.2.2.2.2
          have hg'_sess_pt : g'.session = s ∧ pt' = pt := by
            unfold Params.receive at hrec
            rw [hP_codec, htry] at hrec; dsimp only at hrec; rw [hP_C, hP_spqr, hdec] at hrec
            simp only [Option.some.injEq, Prod.mk.injEq] at hrec
            exact ⟨hrec.1.symm ▸ rfl, hrec.2.2.2.symm⟩
          have hrec_bytes : encodeRecordUnderExtras (fun _ => x) { g with session := s } =
              encodeRecordUnderExtras (fun _ => x) g' := by unfold encodeRecordUnderExtras; rw [hg'_sess_pt.1]
          have hinner : bhWireInnerBytes (wireWhisper :: body) = some body :=
            bhWireInnerBytes_wireWhisper_local body
          rw [hafter]; dsimp only [Option.map, binStateOfUnderExtras]
          rw [hinner]; dsimp only [Option.map]; rw [htry]; dsimp only
          rw [hrae_ep]; dsimp only
          rw [hrec_bytes, ← hrae_idx, ← hg'_sess_pt.2, hrae_p, hParty]
  · intro g' t' idx' pt' hrcv
    obtain ⟨hgp, hgppk, hgloc, _, _, hgAl, _, _⟩ :=
      paramsV1_receive_whisper_props W W.Q.K d.idA d.idB g body rc hrcv hseeds hchains
        hAct.2.2.1 hval hpq64
    have hrec_pq : (pqxdhSessionParams W).receive g body rc = some (g', t', idx', pt') :=
      hRecvEq ▸ hrcv
    unfold Params.receive at hrec_pq
    rcases htry : SignalMessage.tryFrom protoSignalCodec body with _ | msg
    · rw [hP_codec, htry] at hrec_pq; simp at hrec_pq
    · rw [hP_codec, htry] at hrec_pq; dsimp only at hrec_pq
      rcases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
          ((pqxdhSessionParams W).expectedAddrs g.party) msg .whisper rc g.session with ⟨_ | pt, s⟩
      · rw [hP_C, hP_spqr, hdec] at hrec_pq; simp at hrec_pq
      · rw [hP_C, hP_spqr, hdec] at hrec_pq
        simp only [Option.some.injEq, Prod.mk.injEq] at hrec_pq
        have hg'_sess : g'.session = s := hrec_pq.1 ▸ rfl
        have hs_rem : s.remoteIdentity = some d.idB := by
          have hvr := (Closure.Version.tryDecryptFromRecord_sessionVersion_remoteIdentity
            W.C (pqxdhSpqrSession W) ((pqxdhSessionParams W).expectedAddrs g.party) msg .whisper rc g.session).2
          rw [hdec, hRemA] at hvr; exact hvr
        have hnt : (!st.trusts d.idB) = false := by simp [htrust]
        let st_raw : PqParty := { d0 with session := some (x, { g with session := s }) }
        have hst_raw_eq :
            { st with peerId := some d.idB, session := some (x, { g with session := s }) } =
            st_raw := pqParty_with_peer_session_eq d0 d.idB _ _ hpeer
        have hmod : pqRecvWhisperModel W st body rc = some (some (st_raw, pt)) := by
          simp [pqRecvWhisperModel, pqxdhSessionDecryptModel, hsess, htry, hdec, hs_rem, hnt, hst_raw_eq]
        have hstep : PqStep X W st st_raw := PqStep.recvWhisper body rc st_raw pt hbody32 hmod
        have hlr_st : lastResortUses st_raw < 2 ^ 25 := by
          simpa [lastResortUses, st_raw] using hAct.2.1
        obtain ⟨hwf_raw, _⟩ := wfPq_step_r3 hAct.1 hstep hlr_st
        have hwf_out : PqxdhPartyInSpecDomain W { d0 with session := some (x, g') } :=
          wfPq_of_session_party_eq hwf_raw hgp.symm hg'_sess.symm
        have hlr_out : lastResortUses { d0 with session := some (x, g') } < 2 ^ 25 := by
          simpa [lastResortUses] using hAct.2.1
        exact ⟨hgp.trans hParty, hgppk, hgloc,
          (congrArg SessionState.remoteIdentity hg'_sess).trans hs_rem,
          ⟨hwf_out, hlr_out, hgAl, pqLength_le_286196_of_wfPq hwf_out⟩⟩

/-! ## SM transmit and challenge coupling -/

private theorem cliDrvSM_clean_std_run {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (run : CliRun) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (BHDrvM S ℓ))
    (ds : ModelDriverState S ℓ) (st : SignalPqxdh.KeyIndState S)
    (i : ℕ) (bi : ModelDriverInstance S ℓ) (im : ModelDriverInstanceMeta S)
    (gs : SM.GameState BinState (Plain ℓ) Bytes)
    (q : (cliGameSmSpec ℓ (BitVec 512)).Domain)
    (hClean : bhDrvInstClean ds i = true) (hbi_opt : ds.bhInsts[i]? = some bi)
    (him_opt : ds.instMeta[i]? = some im) (hgs : bi.gs = some gs)
    (hq_bob : bhIsBobRecvSMQuery q = false)
    (h_no_pk : match q with
      | .inl (.inl (.inr (.A, c))) => (bhDecodePreKeyMsgE c).isSome = false
      | .inl (.inr (.A, c)) => (bhDecodePreKeyMsgE c).isSome = false
      | _ => True) :
    (((cliDrvSM S ℓ run W qep decT encT ext ⟨i, q⟩).run ds).run st) =
      (((SM.oracleImplR (cliPqScheme run W ℓ bi (cliPqSigsOf st bi) bi.stA0 bi.stB0)
          (2 + 1) qep (bhConfigSpkS (Msg := Plain ℓ) decT encT) q).run gs) >>= fun (r, gsOut) =>
        pure ((r, { ds with bhInsts := ds.bhInsts.set i { bi with gs := some gsOut },
                            instMeta := ds.instMeta.set i im }), st)) := by
  have h1 : (((cliDrvSM S ℓ run W qep decT encT ext ⟨i, q⟩).run ds).run st) =
      (((cliRunStdSM S ℓ run W qep decT encT ds i bi im gs q).run ds).run st) := by
    unfold cliDrvSM
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hClean, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, hbi_opt, him_opt, hq_bob, Bool.and_false,
      Bool.false_and, hgs]
    rcases q with (((_ | _) | ⟨_ | _, c⟩) | ⟨_ | _, c⟩) | _ <;> try cases hq_bob
    all_goals { dsimp [cliStepLocalSM] at h_no_pk ⊢; try simp only [h_no_pk, Bool.false_eq_true, ↓reduceIte] }
  rw [h1, cliRunStdSM_nonBobDl_run _ _ _ _ _ _ _ _ _ _ _ _ hq_bob]

private theorem epMgmt_rel_of_gs_rel {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {im : ModelDriverInstanceMeta S} {d : BHModelInst S ℓ}
    {gs_cli : SM.GameState BinState (Plain ℓ) Bytes}
    {gs_m : SM.GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (qep : ℕ) (p : Party) (bad : Bool)
    (hb_eq : gs_cli.b = gs_m.b) (h_win : gs_cli.win = gs_m.win)
    (h_ep : gs_cli.epoch = gs_m.epoch) (h_idx : gs_cli.idx = gs_m.idx)
    (h_max : gs_cli.maxAcc = gs_m.maxAcc) (h_ch : gs_cli.chall = gs_m.chall)
    (h_comp : gs_cli.comp = gs_m.comp) (h_tL : gs_cli.tL = gs_m.tL)
    (h_lk : gs_cli.leaks = gs_m.leaks) (h_cr : gs_cli.corrs = gs_m.corrs)
    (_h_tr : List.Forall₂ (CliAdapterTransEntryRel im.bobAccepted d.sid d.hdr) gs_cli.trans gs_m.trans)
    (h_epA0 : !im.bobAccepted → gs_m.epoch .A ≤ 1)
    (h_epB0 : !im.bobAccepted → gs_m.epoch .B = 0)
    (_h_trA0 : !im.bobAccepted → ∀ r ∈ gs_m.trans, r.pos.sender = .A)
    (h_cpA0 : !im.bobAccepted → ∀ pos ∈ gs_m.comp, pos.sender = .A)
    (h_tL0 : !im.bobAccepted → gs_m.tL = none)
    (hbob_of_B : p = .B → im.bobAccepted = true) :
    (gs_cli.epMgmt (2 + 1) qep p bad = none ∧ gs_m.epMgmt (2 + 1) qep p bad = none) ∨
    (∃ s_cli s_m,
      gs_cli.epMgmt (2 + 1) qep p bad = some s_cli ∧
      gs_m.epMgmt (2 + 1) qep p bad = some s_m ∧
      s_cli.st = gs_cli.st ∧ s_m.st = gs_m.st ∧
      s_cli.trans = gs_cli.trans ∧ s_m.trans = gs_m.trans ∧
      s_cli.b = s_m.b ∧ s_cli.win = s_m.win ∧ s_cli.epoch = s_m.epoch ∧
      s_cli.idx = s_m.idx ∧ s_cli.maxAcc = s_m.maxAcc ∧ s_cli.chall = s_m.chall ∧
      s_cli.comp = s_m.comp ∧ s_cli.tL = s_m.tL ∧ s_cli.leaks = s_m.leaks ∧
      s_cli.corrs = s_m.corrs ∧
      (!im.bobAccepted → s_m.epoch .A ≤ 1) ∧ (!im.bobAccepted → s_m.epoch .B = 0) ∧
      (!im.bobAccepted → ∀ pos ∈ s_m.comp, pos.sender = .A) ∧ (!im.bobAccepted → s_m.tL = none)) := by
  have h_safeCh : gs_cli.safeCh (2 + 1) p = gs_m.safeCh (2 + 1) p := by
    unfold SM.GameState.safeCh SM.healedBy; rw [h_tL, h_ep]
  unfold SM.GameState.epMgmt SM.GameState.leak
  rw [h_ep, h_safeCh]
  split_ifs with h1 h2 h3
  · exact Or.inl ⟨rfl, rfl⟩
  · right
    refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, hb_eq, h_win, rfl, by rw [h_idx], h_max, h_ch, h_comp,
      by dsimp only; rw [h_tL], by dsimp only; rw [h_tL, h_lk], h_cr, ?_, ?_, h_cpA0, ?_⟩
    · intro hnot; cases p
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (h_epA0 hnot) with h0 | h1_eq
        · simp [Function.update, h0]
        · rw [h1_eq] at h1; cases h1
      · rw [hbob_of_B rfl] at hnot; cases hnot
    · intro hnot; cases p
      · simp [Function.update, h_epB0 hnot]
      · rw [hbob_of_B rfl] at hnot; cases hnot
    · intro hnot; exfalso; simp [SM.GameState.safeCh, SM.healedBy, h_tL0 hnot] at h3
  · right
    refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, hb_eq, h_win, by dsimp only; rw [h_ep], by rw [h_idx],
      h_max, h_ch, h_comp, h_tL, h_lk, h_cr, ?_, ?_, h_cpA0, h_tL0⟩
    · intro hnot; cases p
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (h_epA0 hnot) with h0 | h1_eq
        · simp [Function.update, h0]
        · rw [h1_eq] at h1; cases h1
      · rw [hbob_of_B rfl] at hnot; cases hnot
    · intro hnot; cases p
      · simp [Function.update, h_epB0 hnot]
      · rw [hbob_of_B rfl] at hnot; cases hnot
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨gs_cli, gs_m, rfl, rfl, rfl, rfl, rfl, rfl, hb_eq, h_win, h_ep, h_idx,
      h_max, h_ch, h_comp, h_tL, h_lk, h_cr, h_epA0, h_epB0, h_cpA0, h_tL0⟩

private theorem cliAdapterInstRel_of_send_record {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hCli : CliSpecPqxdh run X W) (hℓ : ℓ < 10 ^ 6)
    {q_rem : ℕ} (hq_pos : 0 < q_rem)
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {bi : ModelDriverInstance S ℓ} {d : BHModelInst S ℓ} {im im_e2e : ModelDriverInstanceMeta S}
    {inst : BHAdapterInstMeta S} {ack : Bool}
    (hInstRel : CliAdapterInstRel X W q_rem st_cli ds_cli bi d im im_e2e inst ack)
    (hInstRem : CliAdapterInstRemoteIdInv d im)
    {gs_cli s_cli : SM.GameState BinState (Plain ℓ) Bytes}
    {gs_m s_m : SM.GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hgs_cli : bi.gs = some gs_cli) (hgs_m : d.gs = some gs_m)
    (hCorr : im.ikACorrAtAccept = false)
    (p : Party) (m_send : Plain ℓ) (coins : BitVec 512) (isChall : Bool)
    (hbob_of_B : p = .B → im.bobAccepted = true)
    (hs_st_cli : s_cli.st = gs_cli.st) (hs_st_m : s_m.st = gs_m.st)
    (hs_tr_cli : s_cli.trans = gs_cli.trans) (hs_tr_m : s_m.trans = gs_m.trans)
    (hs_b : s_cli.b = s_m.b) (hs_win : s_cli.win = s_m.win)
    (hs_ep : s_cli.epoch = s_m.epoch) (hs_idx : s_cli.idx = s_m.idx)
    (hs_max : s_cli.maxAcc = s_m.maxAcc) (hs_ch : s_cli.chall = s_m.chall)
    (hs_comp : s_cli.comp = s_m.comp) (hs_tL : s_cli.tL = s_m.tL)
    (hs_lk : s_cli.leaks = s_m.leaks) (hs_cr : s_cli.corrs = s_m.corrs)
    (hs_epA0 : !im.bobAccepted → s_m.epoch .A ≤ 1)
    (hs_epB0 : !im.bobAccepted → s_m.epoch .B = 0)
    (hs_cpA0 : !im.bobAccepted → ∀ pos ∈ s_m.comp, pos.sender = .A)
    (hs_tL0 : !im.bobAccepted → s_m.tL = none) :
    let P_v1 := paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB
    let out_m := (sessionSchemeSpkWithSpqr P_v1 ℓ d.spkCoins).sendPart.send (s_m.st p) m_send coins
    let out_cli := (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0).sendPart.send
      (s_cli.st p) m_send coins
    let pos_cli : SM.Pos := ⟨p, s_cli.epoch p, s_cli.idx p + 1⟩
    let pos_m : SM.Pos := ⟨p, s_m.epoch p, s_m.idx p + 1⟩
    let gs_cli' := s_cli.record (2 + 1) p out_cli.1 ⟨pos_cli, m_send, out_cli.2⟩ isChall
    let gs_m' := s_m.record (2 + 1) p out_m.1 ⟨pos_m, m_send, out_m.2⟩ isChall
    out_cli.2 = cliWrapAdapterSend inst ack p out_m.2 ∧
    CliAdapterInstRel X W (q_rem - 1) st_cli ds_cli
      { bi with gs := some gs_cli' } { d with gs := some gs_m' } im im_e2e inst ack ∧
    CliAdapterInstRemoteIdInv { d with gs := some gs_m' } im := by
  intro P_v1 out_m out_cli pos_cli pos_m gs_cli' gs_m'
  have hgs := hInstRel.gs_rel
  rw [hgs_cli, hgs_m] at hgs; rcases hgs with ⟨_, hrest⟩
  simp only [hCorr, Bool.false_eq_true, ↓reduceIte] at hrest
  rcases hrest with
    ⟨h_acc, _, _, _, _, _, _, _, _, _,
     h_tr, h_ppkA, h_ppkB, h_idA, h_ack0, _, _, h_trA0, _, _,
     h_epB1, h_stA, h_stB0, h_stB1, h_pA, h_pB, h_actA, h_actB⟩
  have hRem_m := hInstRem gs_m hgs_m (by simp [hCorr])
  have hpos_eq : pos_cli = pos_m := by dsimp only [pos_cli, pos_m]; rw [hs_ep, hs_idx]
  have hst_p : gs_cli.st p = bhBinStateOfParty inst (gs_m.st p) := by
    cases p <;> [exact h_stA; exact h_stB1 (hbob_of_B rfl)]
  have hout_cli_eq : out_cli = cliPqSend run W
      (cliPqDirOf bi (cliPqSigsOf st_cli bi) (bhBinStateOfParty inst (gs_m.st p)))
      (bhBinStateOfParty inst (gs_m.st p)) m_send.toList coins := by
    dsimp only [out_cli, SMSchemeR.sendPart, cliPqScheme]; rw [hs_st_cli, hst_p]
  have hout_m_eq : out_m = P_v1.send (gs_m.st p) m_send.toList coins := by
    dsimp only [out_m, SMSchemeR.sendPart, sessionSchemeSpkWithSpqr, sessionSchemeFixedSpk]; rw [hs_st_m]
  have hSendProps := cliPqSend_party_adapter_props hCli hℓ hq_pos hInstRel
    p (gs_m.st p) m_send coins pos_m rfl
    (by cases p <;> [exact h_pA; exact h_pB])
    (by cases p <;> [exact h_ppkA; exact h_ppkB])
    (fun hA => by subst hA; exact h_idA)
    h_ack0
    (by cases p <;> [exact hRem_m.1; exact hRem_m.2 (hbob_of_B rfl)])
    (by cases p <;> [exact h_actA; exact h_actB (hbob_of_B rfl)])
  dsimp only at hSendProps
  rw [← hout_cli_eq, ← hout_m_eq] at hSendProps
  rcases hSendProps with
    ⟨hout1, hout2, hEntryRel, hp_out, hppk_out, hid_out, hrem_out, hep_out, hAct_out⟩
  refine ⟨hout2, ?_, ?_⟩
  · refine
      { im_eq := hInstRel.im_eq
        sid_eq := hInstRel.sid_eq
        hdr_eq := hInstRel.hdr_eq
        idB_eq := hInstRel.idB_eq
        respSlot_eq := hInstRel.respSlot_eq
        respMeta_eq := hInstRel.respMeta_eq
        regIdA_eq := hInstRel.regIdA_eq
        regIdB_eq := hInstRel.regIdB_eq
        aliceAcked_false := hInstRel.aliceAcked_false
        idA_pub_eq := hInstRel.idA_pub_eq
        idB_pub_eq := hInstRel.idB_pub_eq
        extrasB_eq := hInstRel.extrasB_eq
        stB0_empty := hInstRel.stB0_empty
        resp_bundle_rel := hInstRel.resp_bundle_rel
        handshake_rel := ?_
        gs_rel := ?_ }
    · obtain ⟨bundleE, dk, ac, u_init, bnd, t_init, ss, h1, h2, h3, h4⟩ := hInstRel.handshake_rel
      refine ⟨bundleE, dk, ac, u_init, bnd, t_init, ss, h1, h2, h3,
        fun gs_c₁ gs_m₁ hc₁ hm₁ hcorr₁ hacc₁ => ?_⟩
      simp only [Option.some.injEq] at hc₁ hm₁; subst hc₁ hm₁
      have hpA : p = .A := by
        cases p <;> [rfl; (rw [hbob_of_B rfl] at hacc₁; cases hacc₁)]
      subst hpA
      have hB_eq : gs_m'.st .B = gs_m.st .B := by
        dsimp [gs_m', SM.GameState.record]; rw [hs_st_m]
        simp [Function.update, (by decide : Party.B ≠ Party.A)]
      rw [hB_eq]; exact h4 gs_cli gs_m hgs_cli hgs_m hcorr₁ hacc₁
    · dsimp only; refine ⟨hs_b, ?_⟩
      simp only [hCorr, Bool.false_eq_true, ↓reduceIte]
      have h_safeCh_s : s_cli.safeCh (2 + 1) p = s_m.safeCh (2 + 1) p := by
        unfold SM.GameState.safeCh SM.healedBy; rw [hs_tL, hs_ep]
      have h_comp' : gs_cli'.comp = gs_m'.comp := by
        dsimp [gs_cli', gs_m', SM.GameState.record]; rw [h_safeCh_s, hs_comp, hpos_eq]
      have h_ch' : gs_cli'.chall = gs_m'.chall := by
        dsimp [gs_cli', gs_m', SM.GameState.record]; rw [hs_ch, hpos_eq]
      have h_idx' : gs_cli'.idx = gs_m'.idx := by
        dsimp [gs_cli', gs_m', SM.GameState.record]; rw [hs_idx, hpos_eq]
      have h_tr' : List.Forall₂ (CliAdapterTransEntryRel im.bobAccepted d.sid d.hdr)
          gs_cli'.trans gs_m'.trans := by
        dsimp [gs_cli', gs_m', SM.GameState.record]; rw [hs_tr_cli, hs_tr_m, hpos_eq]
        exact List.Forall₂.cons hEntryRel h_tr
      refine ⟨h_acc, hs_win, hs_ep, h_idx', hs_max, h_ch', h_comp', hs_tL, hs_lk, hs_cr, h_tr',
        ?_, ?_, ?_, h_ack0, hs_epA0, hs_epB0, ?_, ?_, fun h => hs_tL0 h, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp [gs_m', SM.GameState.record]; rw [hs_st_m]
        cases p <;> simp [Function.update, hppk_out, h_ppkA]
      · dsimp [gs_m', SM.GameState.record]; rw [hs_st_m]
        cases p <;> simp [Function.update, hppk_out, h_ppkB]
      · dsimp [gs_m', SM.GameState.record]; rw [hs_st_m]
        cases p <;> simp [Function.update, hid_out, h_idA]
      · intro hnot r hr
        dsimp [gs_m', SM.GameState.record] at hr; rw [hs_tr_m] at hr
        rcases List.mem_cons.mp hr with rfl | hr_old
        · dsimp [pos_m]; cases p <;> [rfl; (rw [hbob_of_B rfl] at hnot; cases hnot)]
        · exact h_trA0 hnot r hr_old
      · intro hnot pos hpos
        dsimp [gs_m', SM.GameState.record] at hpos
        split_ifs at hpos
        · exact hs_cpA0 hnot pos hpos
        · rcases List.mem_cons.mp hpos with rfl | hpos_old
          · dsimp [pos_m]; cases p <;> [rfl; (rw [hbob_of_B rfl] at hnot; cases hnot)]
          · exact hs_cpA0 hnot pos hpos_old
      · intro hacc; dsimp [gs_m', SM.GameState.record]; rw [hs_st_m]
        cases p
        · simp [Function.update, (by decide : Party.B ≠ Party.A), h_epB1 hacc]
        · simp only [Function.update, ↓reduceDIte]; exact Nat.lt_of_lt_of_le (h_epB1 hacc) hep_out
      · dsimp [gs_cli', gs_m', SM.GameState.record]; rw [hs_st_cli, hs_st_m]
        cases p <;> simp [Function.update, hout1, h_stA]
      · intro hnot; dsimp [gs_cli', SM.GameState.record]; rw [hs_st_cli]
        cases p
        · simp [Function.update, (by decide : Party.B ≠ Party.A), h_stB0 hnot]
        · rw [hbob_of_B rfl] at hnot; cases hnot
      · intro hacc; dsimp [gs_cli', gs_m', SM.GameState.record]; rw [hs_st_cli, hs_st_m]
        cases p <;> simp [Function.update, hout1, h_stB1 hacc]
      · dsimp [gs_m', SM.GameState.record]; rw [hs_st_m]
        cases p <;> simp [Function.update, hp_out, h_pA]
      · dsimp [gs_m', SM.GameState.record]; rw [hs_st_m]
        cases p <;> simp [Function.update, hp_out, h_pB]
      · dsimp [gs_m', SM.GameState.record]; rw [hs_st_m]
        cases p
        · rw [Function.update_self]; exact hAct_out
        · rw [Function.update_of_ne (by decide)]; exact cliPartyActiveInv_mono h_actA (Nat.sub_le _ _)
      · intro hacc; dsimp [gs_m', SM.GameState.record]; rw [hs_st_m]
        cases p
        · rw [Function.update_of_ne (by decide)]
          exact cliPartyActiveInv_mono (h_actB hacc) (Nat.sub_le _ _)
        · rw [Function.update_self]; exact hAct_out
  · intro gs₁ hgs₁ hnc
    simp only [Option.some.injEq] at hgs₁; subst hgs₁
    dsimp [gs_m', SM.GameState.record]; rw [hs_st_m]
    refine ⟨?_, fun hacc => ?_⟩
    · cases p
      · rw [Function.update_self]; exact hrem_out
      · rw [Function.update_of_ne (by decide)]; exact hRem_m.1
    · cases p
      · rw [Function.update_of_ne (by decide)]; exact hRem_m.2 hacc
      · rw [Function.update_self]; exact hrem_out

section SendAndChallenge
variable {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
  (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) (qep : ℕ)
  (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
  (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (BHDrvM S ℓ))
  (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
  {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
  {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
  {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}

/-- SM transmit step coupling. -/
theorem cliDrvSM_adapter_couplingRem_tr
    (hCli : CliSpecPqxdh run X W) (hℓ : ℓ < 10 ^ 6)
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (hRem : CliAdapterDrvRemoteIdInv S ℓ ds_cli σ_e2e)
    (i : ℕ) (p : Party) (m : Plain ℓ) (r : Option (BitVec 512))
    (hq_pos : 0 < qs_rem i) :
    cliAdapterStepCoupledRem X W b qStart (Function.update qs_rem i (qs_rem i - 1))
      (((cliDrvSM S ℓ run W qep decT encT ext ⟨i, .inl (.inl (.inl (.inl (p, m, r))))⟩).run ds_cli).run st_cli)
      (((cliComposedAdapterImplWith (modelPrims X W) ki W.C W.Q.K qep decT encT
          (.inr ⟨i, .inl (.inl (.inl (.inl (p, m, r))))⟩)).run σ_ad).run σ_e2e) := by
  cases hClean : bhDrvInstClean ds_cli i
  · exact cliDrvSM_adapter_couplingRem_not_clean run X W qep decT encT ext ki hRel hRem i _ hClean
  · by_cases hi_cli : i < ds_cli.bhInsts.length
    swap
    · exact cliDrvSM_adapter_couplingRem_oob run X W qep decT encT ext ki hRel hRem i _
        (Nat.le_of_not_lt hi_cli)
    · have hi_e2e : i < σ_e2e.insts.length := hRel.insts_len_eq ▸ hi_cli
      have hi_mb : i < ds_cli.instMeta.length := hRel.meta_cli_len_eq.symm ▸ hi_cli
      have hi_me : i < σ_e2e.instMeta.length := hRel.meta_e2e_len_eq.symm ▸ hi_e2e
      have hCorr : ds_cli.instMeta[i].ikACorrAtAccept = false :=
        bhDrvInstClean_imp_ikACorrAtAccept_false hClean hi_cli hi_mb
      obtain ⟨inst, hinst_ad, hInstRel⟩ := hRel.insts_rel i hi_cli hi_e2e hi_mb hi_me
      have hInstRem := hRem i hi_e2e hi_mb
      set bi := ds_cli.bhInsts[i]; set d := σ_e2e.insts[i]
      set im := ds_cli.instMeta[i]; set im_e2e := σ_e2e.instMeta[i]
      have hbi_opt : ds_cli.bhInsts[i]? = some bi := List.getElem?_eq_getElem hi_cli
      have hd_opt : σ_e2e.insts[i]? = some d := List.getElem?_eq_getElem hi_e2e
      have him_opt : ds_cli.instMeta[i]? = some im := List.getElem?_eq_getElem hi_mb
      have hime_opt : σ_e2e.instMeta[i]? = some im_e2e := List.getElem?_eq_getElem hi_me
      have hClean_e2e : bhE2EDrvInstClean σ_e2e i = true :=
        (bhDrvInstClean_eq_bhE2EDrvInstClean_of_cliRel hRel i).symm.trans hClean
      have hgs := hInstRel.gs_rel
      cases hgs_cli : bi.gs with
      | none => rw [hgs_cli] at hgs; exact False.elim hgs
      | some gs_cli =>
        cases hgs_m : d.gs with
        | none => rw [hgs_cli, hgs_m] at hgs; exact False.elim hgs
        | some gs_m =>
          rw [hgs_cli, hgs_m] at hgs; rcases hgs with ⟨hb_eq, hrest⟩
          simp only [hCorr, Bool.false_eq_true, ↓reduceIte] at hrest
          rcases hrest with
            ⟨h_acc, h_win, h_ep, h_idx, h_max, h_ch, h_comp, h_tL, h_lk, h_cr,
             h_tr, h_ppkA, h_ppkB, h_idA, h_ack0, h_epA0, h_epB0, h_trA0, h_cpA0, h_tL0,
             h_epB1, h_stA, h_stB0, h_stB1, h_pA, h_pB, h_actA, h_actB⟩
          have h_sendOK :
              (bhConfigSpkS (Msg := Plain ℓ) decT encT).sendOK gs_cli p =
                (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).sendOK gs_m p := by
            dsimp [bhConfigSpkS, configRefuseEarlyBobCorr, configR1OnCurve,
              SM.configR1, SM.noBobSendInEpoch0]; rw [h_ep]
          rw [cliDrvSM_clean_std_run _ _ _ _ _ _ _ _ _ _ _ _ _ hClean hbi_opt him_opt hgs_cli rfl trivial,
            cliComposedAdapterImplWith_tr_run, hinst_ad]
          change cliAdapterStepCoupledRem _ _ _ _ _ _
            (bhE2EStepLocalSm W.C W.Q.K qep decT encT σ_e2e i (.inl (.inl (.inl (.inl (p, m, r))))) >>=
              fun (sr, σ_e2e') =>
                match sr.1 with
                | none => pure ((none, σ_ad), σ_e2e')
                | some ct => pure ((some (cliWrapAdapterSend inst (σ_ad.2.1 i) p ct), σ_ad), σ_e2e'))
          cases h_sendOK_m : (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).sendOK gs_m p
          · have h_sendOK_cli := h_sendOK.trans h_sendOK_m
            have h_cli_run :
                (((SM.oracleImplR (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0)
                    (2 + 1) qep (bhConfigSpkS (Msg := Plain ℓ) decT encT)
                    (.inl (.inl (.inl (.inl (p, m, r)))))).run gs_cli) >>= fun (r0, gsOut) =>
                  pure ((r0, { ds_cli with bhInsts := ds_cli.bhInsts.set i { bi with gs := some gsOut },
                                           instMeta := ds_cli.instMeta.set i im }), st_cli)) =
                  pure ((none, ds_cli), st_cli) := by
              dsimp [SM.oracleImplR, SM.transmitR, SM.transmitImpl]
              simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
                h_sendOK_cli, Bool.not_false, ↓reduceIte,
                bi, im, bhDrvState_set_same_gs ds_cli i hi_cli hi_mb gs_cli hgs_cli]
            have h_ad_run :
                (bhE2EStepLocalSm W.C W.Q.K qep decT encT σ_e2e i
                    (.inl (.inl (.inl (.inl (p, m, r))))) >>= fun (sr, σ_e2e') =>
                  match sr.1 with
                  | none => pure ((none, σ_ad), σ_e2e')
                  | some ct => pure ((some (cliWrapAdapterSend inst (σ_ad.2.1 i) p ct), σ_ad), σ_e2e')) =
                  pure ((none, σ_ad), σ_e2e) := by
              dsimp [bhE2EStepLocalSm, SM.oracleImplR, SM.transmitR, SM.transmitImpl, configRefuseEarlyBobCorr, configR1OnCurve]
              dsimp only [configRefuseEarlyBobCorr, configR1OnCurve] at h_sendOK_m
              simp only [hClean_e2e, hd_opt, hime_opt, hgs_m, bhIsBobRecvSMQuery, bhIsBobAcceptSMResp,
                StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, bhPackSmResp,
                h_sendOK_m, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.and_false,
                Bool.false_and, ↓reduceIte,
                d, im_e2e, bhE2EDrvState_set_same_gs σ_e2e i hi_e2e hi_me gs_m hgs_m]
            rw [h_cli_run, h_ad_run]
            exact cliAdapterStepCoupledRem_ret _ _ _ _ _ (cliAdapterDrvRel_decrement_i hRel i) hRem
          · have h_sendOK_cli := h_sendOK.trans h_sendOK_m
            cases h_win_m : gs_m.win
            · have h_win_cli := h_win.trans h_win_m
              have hbob_of_B : p = .B → im.bobAccepted = true := by
                intro hpB; subst hpB
                by_cases hbob : im.bobAccepted = true
                · exact hbob
                · simp only [Bool.not_eq_true] at hbob
                  have hepB0 : gs_m.epoch .B = 0 := h_epB0 (by simp [hbob])
                  dsimp [configRefuseEarlyBobCorr, configR1OnCurve,
                    SM.configR1, SM.noBobSendInEpoch0] at h_sendOK_m
                  simp [hepB0] at h_sendOK_m
              let sch_cli := cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0
              let P_v1 := paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB
              let sch_m := sessionSchemeSpkWithSpqr P_v1 ℓ d.spkCoins
              let f_cli : BitVec 512 × Bool → (Option Bytes × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S :=
                fun ⟨cns, bad⟩ =>
                  match gs_cli.epMgmt (2 + 1) qep p bad with
                  | none => ((none, ds_cli), st_cli)
                  | some s_cli =>
                    let out_cli := sch_cli.sendPart.send (s_cli.st p) m cns
                    let gs_cli' := s_cli.record (2 + 1) p out_cli.1
                      ⟨⟨p, s_cli.epoch p, s_cli.idx p + 1⟩, m, out_cli.2⟩ false
                    ((some out_cli.2,
                      { ds_cli with bhInsts := ds_cli.bhInsts.set i { bi with gs := some gs_cli' },
                                    instMeta := ds_cli.instMeta.set i im }), st_cli)
              let f_ad : BitVec 512 × Bool → (Option Bytes × CliAdapterState S) × BHE2EDrvState S ℓ :=
                fun ⟨cns, bad⟩ =>
                  match gs_m.epMgmt (2 + 1) qep p bad with
                  | none => ((none, σ_ad), σ_e2e)
                  | some s_m =>
                    let out_m := sch_m.sendPart.send (s_m.st p) m cns
                    let gs_m' := s_m.record (2 + 1) p out_m.1
                      ⟨⟨p, s_m.epoch p, s_m.idx p + 1⟩, m, out_m.2⟩ false
                    ((some (cliWrapAdapterSend inst (σ_ad.2.1 i) p out_m.2), σ_ad),
                      { σ_e2e with insts := σ_e2e.insts.set i { d with gs := some gs_m' },
                                   instMeta := σ_e2e.instMeta.set i im_e2e })
              have h_cli_run :
                  (((SM.oracleImplR sch_cli (2 + 1) qep (bhConfigSpkS (Msg := Plain ℓ) decT encT)
                      (.inl (.inl (.inl (.inl (p, m, r)))))).run gs_cli) >>= fun (r0, gsOut) =>
                    pure ((r0, { ds_cli with bhInsts := ds_cli.bhInsts.set i { bi with gs := some gsOut },
                                             instMeta := ds_cli.instMeta.set i im }), st_cli)) =
                    (SM.samIfNec r >>= fun x => pure (f_cli x)) := by
                dsimp [SM.oracleImplR, SM.transmitR, SM.transmitImpl]
                simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
                  StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc,
                  h_sendOK_cli, h_win_cli, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                congr 1; funext ⟨cns, bad⟩
                rcases hep : gs_cli.epMgmt 3 qep p bad with _ | s_cli
                · simp [f_cli, hep, bi, im, bhInst_set_same_gs hgs_cli,
                    bhDrvState_set_same_gs ds_cli i hi_cli hi_mb gs_cli hgs_cli]
                · simp [f_cli, hep, sch_cli, bi, im]
              have h_ad_run :
                  (bhE2EStepLocalSm W.C W.Q.K qep decT encT σ_e2e i
                      (.inl (.inl (.inl (.inl (p, m, r))))) >>= fun (sr, σ_e2e') =>
                    match sr.1 with
                    | none => pure ((none, σ_ad), σ_e2e')
                    | some ct => pure ((some (cliWrapAdapterSend inst (σ_ad.2.1 i) p ct), σ_ad), σ_e2e')) =
                    (SM.samIfNec r >>= fun x => pure (f_ad x)) := by
                dsimp [bhE2EStepLocalSm, SM.oracleImplR, SM.transmitR, SM.transmitImpl, configRefuseEarlyBobCorr, configR1OnCurve]
                dsimp only [configRefuseEarlyBobCorr, configR1OnCurve] at h_sendOK_m
                simp only [hClean_e2e, hd_opt, hime_opt, hgs_m, bhIsBobRecvSMQuery, bhIsBobAcceptSMResp,
                  StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
                  StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc, bhPackSmResp,
                  h_sendOK_m, h_win_m, Bool.not_true, Bool.false_eq_true, Bool.and_false,
                  Bool.false_and, ↓reduceIte]
                congr 1; funext ⟨cns, bad⟩
                rcases hep : gs_m.epMgmt 3 qep p bad with _ | s_m
                · simp [f_ad, hep, d, im_e2e, bhModelInst_set_same_gs hgs_m,
                    bhE2EDrvState_set_same_gs σ_e2e i hi_e2e hi_me gs_m hgs_m]
                · simp [f_ad, hep, sch_m, sessionSchemeFixedSpk, sessionSchemeSpkWithSpqr, P_v1, d, im_e2e]
              rw [h_cli_run, h_ad_run]
              refine cliAdapterStepCoupledRem_bind_pure (SM.samIfNec r) f_cli f_ad fun ⟨cns, bad⟩ _ => ?_
              rcases epMgmt_rel_of_gs_rel qep p bad hb_eq h_win h_ep h_idx h_max h_ch h_comp h_tL h_lk h_cr
                  h_tr h_epA0 h_epB0 h_trA0 h_cpA0 h_tL0 hbob_of_B with
                ⟨hep_cli, hep_m⟩ |
                ⟨s_cli, s_m, hep_cli, hep_m, hs_st_cli, hs_st_m, hs_tr_cli, hs_tr_m,
                 hs_b, hs_win, hs_ep, hs_idx, hs_max, hs_ch, hs_comp, hs_tL, hs_lk, hs_cr,
                 hs_epA0, hs_epB0, hs_cpA0, hs_tL0⟩
              · dsimp only [f_cli, f_ad]; rw [hep_cli, hep_m]
                exact ⟨rfl, cliAdapterDrvRel_decrement_i hRel i, hRem⟩
              · dsimp only [f_cli, f_ad]; rw [hep_cli, hep_m]; dsimp only
                obtain ⟨hout2, hInstRel', hInstRem'⟩ :=
                  cliAdapterInstRel_of_send_record hCli hℓ hq_pos hInstRel hInstRem
                    hgs_cli hgs_m hCorr p m cns false hbob_of_B
                    hs_st_cli hs_st_m hs_tr_cli hs_tr_m hs_b hs_win hs_ep hs_idx
                    hs_max hs_ch hs_comp hs_tL hs_lk hs_cr hs_epA0 hs_epB0 hs_cpA0 hs_tL0
                exact ⟨congrArg some hout2,
                  cliAdapterDrvRel_update_inst_ad hRel hi_cli _ _ im im_e2e inst (σ_ad.2.1 i)
                    rfl hinst_ad rfl (fun _ _ => rfl) (fun _ _ => rfl) hInstRel',
                  cliAdapterDrvRemoteIdInv_update_inst hRem i _ _ _ _ hInstRem'⟩
            · have h_win_cli := h_win.trans h_win_m
              have h_cli_run :
                  (((SM.oracleImplR (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0)
                      (2 + 1) qep (bhConfigSpkS (Msg := Plain ℓ) decT encT)
                      (.inl (.inl (.inl (.inl (p, m, r)))))).run gs_cli) >>= fun (r0, gsOut) =>
                    pure ((r0, { ds_cli with bhInsts := ds_cli.bhInsts.set i { bi with gs := some gsOut },
                                             instMeta := ds_cli.instMeta.set i im }), st_cli)) =
                    pure ((none, ds_cli), st_cli) := by
                dsimp [SM.oracleImplR, SM.transmitR, SM.transmitImpl]
                simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
                  h_sendOK_cli, h_win_cli, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                  bi, im, bhDrvState_set_same_gs ds_cli i hi_cli hi_mb gs_cli hgs_cli]
              have h_ad_run :
                  (bhE2EStepLocalSm W.C W.Q.K qep decT encT σ_e2e i
                      (.inl (.inl (.inl (.inl (p, m, r))))) >>= fun (sr, σ_e2e') =>
                    match sr.1 with
                    | none => pure ((none, σ_ad), σ_e2e')
                    | some ct => pure ((some (cliWrapAdapterSend inst (σ_ad.2.1 i) p ct), σ_ad), σ_e2e')) =
                    pure ((none, σ_ad), σ_e2e) := by
                dsimp [bhE2EStepLocalSm, SM.oracleImplR, SM.transmitR, SM.transmitImpl, configRefuseEarlyBobCorr, configR1OnCurve]
                dsimp only [configRefuseEarlyBobCorr, configR1OnCurve] at h_sendOK_m
                simp only [hClean_e2e, hd_opt, hime_opt, hgs_m, bhIsBobRecvSMQuery, bhIsBobAcceptSMResp,
                  StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, bhPackSmResp,
                  h_sendOK_m, h_win_m, Bool.not_true, Bool.false_eq_true, Bool.and_false,
                  Bool.false_and, ↓reduceIte,
                  d, im_e2e, bhE2EDrvState_set_same_gs σ_e2e i hi_e2e hi_me gs_m hgs_m]
              rw [h_cli_run, h_ad_run]
              exact cliAdapterStepCoupledRem_ret _ _ _ _ _ (cliAdapterDrvRel_decrement_i hRel i) hRem

theorem cliDrvSM_adapter_coupling_tr
    (hCli : CliSpecPqxdh run X W) (hℓ : ℓ < 10 ^ 6)
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (hRem : CliAdapterDrvRemoteIdInv S ℓ ds_cli σ_e2e)
    (i : ℕ) (p : Party) (m : Plain ℓ) (r : Option (BitVec 512))
    (hq_pos : 0 < qs_rem i) :
    cliAdapterStepCoupled X W b qStart (Function.update qs_rem i (qs_rem i - 1))
      (((cliDrvSM S ℓ run W qep decT encT ext ⟨i, .inl (.inl (.inl (.inl (p, m, r))))⟩).run ds_cli).run st_cli)
      (((cliComposedAdapterImplWith (modelPrims X W) ki W.C W.Q.K qep decT encT
          (.inr ⟨i, .inl (.inl (.inl (.inl (p, m, r))))⟩)).run σ_ad).run σ_e2e) :=
  (cliDrvSM_adapter_couplingRem_tr run X W qep decT encT ext ki hCli hℓ hRel hRem i p m r hq_pos).toStepCoupled

/-- SM challenge step coupling. -/
theorem cliDrvSM_adapter_couplingRem_ch
    (hCli : CliSpecPqxdh run X W) (hℓ : ℓ < 10 ^ 6)
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (hRem : CliAdapterDrvRemoteIdInv S ℓ ds_cli σ_e2e)
    (i : ℕ) (p : Party) (m0 m1 : Plain ℓ) (r : Option (BitVec 512))
    (hq_pos : 0 < qs_rem i) :
    cliAdapterStepCoupledRem X W b qStart (Function.update qs_rem i (qs_rem i - 1))
      (((cliDrvSM S ℓ run W qep decT encT ext ⟨i, .inl (.inl (.inl (.inr (p, m0, m1, r))))⟩).run ds_cli).run st_cli)
      (((cliComposedAdapterImplWith (modelPrims X W) ki W.C W.Q.K qep decT encT
          (.inr ⟨i, .inl (.inl (.inl (.inr (p, m0, m1, r))))⟩)).run σ_ad).run σ_e2e) := by
  cases hClean : bhDrvInstClean ds_cli i
  · exact cliDrvSM_adapter_couplingRem_not_clean run X W qep decT encT ext ki hRel hRem i _ hClean
  · by_cases hi_cli : i < ds_cli.bhInsts.length
    swap
    · exact cliDrvSM_adapter_couplingRem_oob run X W qep decT encT ext ki hRel hRem i _
        (Nat.le_of_not_lt hi_cli)
    · have hi_e2e : i < σ_e2e.insts.length := hRel.insts_len_eq ▸ hi_cli
      have hi_mb : i < ds_cli.instMeta.length := hRel.meta_cli_len_eq.symm ▸ hi_cli
      have hi_me : i < σ_e2e.instMeta.length := hRel.meta_e2e_len_eq.symm ▸ hi_e2e
      have hCorr : ds_cli.instMeta[i].ikACorrAtAccept = false :=
        bhDrvInstClean_imp_ikACorrAtAccept_false hClean hi_cli hi_mb
      obtain ⟨inst, hinst_ad, hInstRel⟩ := hRel.insts_rel i hi_cli hi_e2e hi_mb hi_me
      have hInstRem := hRem i hi_e2e hi_mb
      set bi := ds_cli.bhInsts[i]; set d := σ_e2e.insts[i]
      set im := ds_cli.instMeta[i]; set im_e2e := σ_e2e.instMeta[i]
      have hbi_opt : ds_cli.bhInsts[i]? = some bi := List.getElem?_eq_getElem hi_cli
      have hd_opt : σ_e2e.insts[i]? = some d := List.getElem?_eq_getElem hi_e2e
      have him_opt : ds_cli.instMeta[i]? = some im := List.getElem?_eq_getElem hi_mb
      have hime_opt : σ_e2e.instMeta[i]? = some im_e2e := List.getElem?_eq_getElem hi_me
      have hClean_e2e : bhE2EDrvInstClean σ_e2e i = true :=
        (bhDrvInstClean_eq_bhE2EDrvInstClean_of_cliRel hRel i).symm.trans hClean
      have hgs := hInstRel.gs_rel
      cases hgs_cli : bi.gs with
      | none => rw [hgs_cli] at hgs; exact False.elim hgs
      | some gs_cli =>
        cases hgs_m : d.gs with
        | none => rw [hgs_cli, hgs_m] at hgs; exact False.elim hgs
        | some gs_m =>
          rw [hgs_cli, hgs_m] at hgs; rcases hgs with ⟨hb_eq, hrest⟩
          simp only [hCorr, Bool.false_eq_true, ↓reduceIte] at hrest
          rcases hrest with
            ⟨h_acc, h_win, h_ep, h_idx, h_max, h_ch, h_comp, h_tL, h_lk, h_cr,
             h_tr, h_ppkA, h_ppkB, h_idA, h_ack0, h_epA0, h_epB0, h_trA0, h_cpA0, h_tL0,
             h_epB1, h_stA, h_stB0, h_stB1, h_pA, h_pB, h_actA, h_actB⟩
          have h_sendOK :
              (bhConfigSpkS (Msg := Plain ℓ) decT encT).sendOK gs_cli p =
                (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).sendOK gs_m p := by
            dsimp [bhConfigSpkS, configRefuseEarlyBobCorr, configR1OnCurve,
              SM.configR1, SM.noBobSendInEpoch0]; rw [h_ep]
          rw [cliDrvSM_clean_std_run _ _ _ _ _ _ _ _ _ _ _ _ _ hClean hbi_opt him_opt hgs_cli rfl trivial,
            cliComposedAdapterImplWith_ch_run, hinst_ad]
          change cliAdapterStepCoupledRem _ _ _ _ _ _
            (bhE2EStepLocalSm W.C W.Q.K qep decT encT σ_e2e i (.inl (.inl (.inl (.inr (p, m0, m1, r))))) >>=
              fun (sr, σ_e2e') =>
                match sr.1 with
                | none => pure ((none, σ_ad), σ_e2e')
                | some ct => pure ((some (cliWrapAdapterSend inst (σ_ad.2.1 i) p ct), σ_ad), σ_e2e'))
          cases h_sendOK_m : (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).sendOK gs_m p
          · have h_sendOK_cli := h_sendOK.trans h_sendOK_m
            have h_cli_run :
                (((SM.oracleImplR (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0)
                    (2 + 1) qep (bhConfigSpkS (Msg := Plain ℓ) decT encT)
                    (.inl (.inl (.inl (.inr (p, m0, m1, r)))))).run gs_cli) >>= fun (r0, gsOut) =>
                  pure ((r0, { ds_cli with bhInsts := ds_cli.bhInsts.set i { bi with gs := some gsOut },
                                           instMeta := ds_cli.instMeta.set i im }), st_cli)) =
                  pure ((none, ds_cli), st_cli) := by
              dsimp [SM.oracleImplR, SM.challR, SM.challImpl]
              simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
                h_sendOK_cli, Bool.not_false, ↓reduceIte,
                bi, im, bhDrvState_set_same_gs ds_cli i hi_cli hi_mb gs_cli hgs_cli]
            have h_ad_run :
                (bhE2EStepLocalSm W.C W.Q.K qep decT encT σ_e2e i
                    (.inl (.inl (.inl (.inr (p, m0, m1, r))))) >>= fun (sr, σ_e2e') =>
                  match sr.1 with
                  | none => pure ((none, σ_ad), σ_e2e')
                  | some ct => pure ((some (cliWrapAdapterSend inst (σ_ad.2.1 i) p ct), σ_ad), σ_e2e')) =
                  pure ((none, σ_ad), σ_e2e) := by
              dsimp [bhE2EStepLocalSm, SM.oracleImplR, SM.challR, SM.challImpl, configRefuseEarlyBobCorr, configR1OnCurve]
              dsimp only [configRefuseEarlyBobCorr, configR1OnCurve] at h_sendOK_m
              simp only [hClean_e2e, hd_opt, hime_opt, hgs_m, bhIsBobRecvSMQuery, bhIsBobAcceptSMResp,
                StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, bhPackSmResp,
                h_sendOK_m, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.and_false,
                Bool.false_and, ↓reduceIte,
                d, im_e2e, bhE2EDrvState_set_same_gs σ_e2e i hi_e2e hi_me gs_m hgs_m]
            rw [h_cli_run, h_ad_run]
            exact cliAdapterStepCoupledRem_ret _ _ _ _ _ (cliAdapterDrvRel_decrement_i hRel i) hRem
          · have h_sendOK_cli := h_sendOK.trans h_sendOK_m
            cases h_win_m : gs_m.win
            · have h_win_cli := h_win.trans h_win_m
              have hbob_of_B : p = .B → im.bobAccepted = true := by
                intro hpB; subst hpB
                by_cases hbob : im.bobAccepted = true
                · exact hbob
                · simp only [Bool.not_eq_true] at hbob
                  have hepB0 : gs_m.epoch .B = 0 := h_epB0 (by simp [hbob])
                  dsimp [configRefuseEarlyBobCorr, configR1OnCurve,
                    SM.configR1, SM.noBobSendInEpoch0] at h_sendOK_m
                  simp [hepB0] at h_sendOK_m
              let sch_cli := cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0
              let P_v1 := paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB
              let sch_m := sessionSchemeSpkWithSpqr P_v1 ℓ d.spkCoins
              let cfg_cli := bhConfigSpkS (Msg := Plain ℓ) decT encT
              let cfg_m := configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT
              let f_cli : BitVec 512 × Bool → (Option Bytes × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S :=
                fun ⟨cns, bad⟩ =>
                  match gs_cli.epMgmt (2 + 1) qep p bad with
                  | none => ((none, ds_cli), st_cli)
                  | some s_cli =>
                    if !(s_cli.safeCh (2 + 1) p) || !(cfg_cli.base.challAllowedIn (s_cli.epoch p)) then
                      ((none, ds_cli), st_cli)
                    else
                      let m_send := (cfg_cli.base.challMsg (s_cli.epoch p)).getD (if gs_cli.b then m1 else m0)
                      let out_cli := sch_cli.sendPart.send (s_cli.st p) m_send cns
                      let gs_cli' := s_cli.record (2 + 1) p out_cli.1
                        ⟨⟨p, s_cli.epoch p, s_cli.idx p + 1⟩, m_send, out_cli.2⟩ true
                      ((some out_cli.2,
                        { ds_cli with bhInsts := ds_cli.bhInsts.set i { bi with gs := some gs_cli' },
                                      instMeta := ds_cli.instMeta.set i im }), st_cli)
              let f_ad : BitVec 512 × Bool → (Option Bytes × CliAdapterState S) × BHE2EDrvState S ℓ :=
                fun ⟨cns, bad⟩ =>
                  match gs_m.epMgmt (2 + 1) qep p bad with
                  | none => ((none, σ_ad), σ_e2e)
                  | some s_m =>
                    if !(s_m.safeCh (2 + 1) p) || !(cfg_m.base.challAllowedIn (s_m.epoch p)) then
                      ((none, σ_ad), σ_e2e)
                    else
                      let m_send := (cfg_m.base.challMsg (s_m.epoch p)).getD (if gs_m.b then m1 else m0)
                      let out_m := sch_m.sendPart.send (s_m.st p) m_send cns
                      let gs_m' := s_m.record (2 + 1) p out_m.1
                        ⟨⟨p, s_m.epoch p, s_m.idx p + 1⟩, m_send, out_m.2⟩ true
                      ((some (cliWrapAdapterSend inst (σ_ad.2.1 i) p out_m.2), σ_ad),
                        { σ_e2e with insts := σ_e2e.insts.set i { d with gs := some gs_m' },
                                     instMeta := σ_e2e.instMeta.set i im_e2e })
              have h_cli_run :
                  (((SM.oracleImplR sch_cli (2 + 1) qep cfg_cli
                      (.inl (.inl (.inl (.inr (p, m0, m1, r)))))).run gs_cli) >>= fun (r0, gsOut) =>
                    pure ((r0, { ds_cli with bhInsts := ds_cli.bhInsts.set i { bi with gs := some gsOut },
                                             instMeta := ds_cli.instMeta.set i im }), st_cli)) =
                    (SM.samIfNec r >>= fun x => pure (f_cli x)) := by
                dsimp [SM.oracleImplR, SM.challR, SM.challImpl, cfg_cli] at *
                simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
                  StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc,
                  h_sendOK_cli, h_win_cli, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                congr 1; funext ⟨cns, bad⟩
                rcases hep : gs_cli.epMgmt 3 qep p bad with _ | s_cli
                · simp [f_cli, hep, bi, im, bhInst_set_same_gs hgs_cli,
                    bhDrvState_set_same_gs ds_cli i hi_cli hi_mb gs_cli hgs_cli]
                · dsimp only [f_cli, hep, cfg_cli, sch_cli]
                  simp only [hep, Bool.or_eq_true, Bool.not_eq_true']
                  split_ifs <;> simp [bi, im, bhInst_set_same_gs hgs_cli,
                    bhDrvState_set_same_gs ds_cli i hi_cli hi_mb gs_cli hgs_cli]
              have h_ad_run :
                  (bhE2EStepLocalSm W.C W.Q.K qep decT encT σ_e2e i
                      (.inl (.inl (.inl (.inr (p, m0, m1, r))))) >>= fun (sr, σ_e2e') =>
                    match sr.1 with
                    | none => pure ((none, σ_ad), σ_e2e')
                    | some ct => pure ((some (cliWrapAdapterSend inst (σ_ad.2.1 i) p ct), σ_ad), σ_e2e')) =
                    (SM.samIfNec r >>= fun x => pure (f_ad x)) := by
                dsimp [bhE2EStepLocalSm, SM.oracleImplR, SM.challR, SM.challImpl, configRefuseEarlyBobCorr, configR1OnCurve]
                dsimp only [configRefuseEarlyBobCorr, configR1OnCurve] at h_sendOK_m
                simp only [hClean_e2e, hd_opt, hime_opt, hgs_m, bhIsBobRecvSMQuery, bhIsBobAcceptSMResp,
                  StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
                  StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc, bhPackSmResp,
                  h_sendOK_m, h_win_m, Bool.not_true, Bool.false_eq_true, Bool.and_false,
                  Bool.false_and, ↓reduceIte]
                congr 1; funext ⟨cns, bad⟩
                rcases hep : gs_m.epMgmt 3 qep p bad with _ | s_m
                · simp [f_ad, hep, d, im_e2e, bhModelInst_set_same_gs hgs_m,
                    bhE2EDrvState_set_same_gs σ_e2e i hi_e2e hi_me gs_m hgs_m]
                · dsimp only [f_ad, hep, cfg_m, configRefuseEarlyBobCorr, configR1OnCurve,
                    sch_m, sessionSchemeFixedSpk, P_v1, sessionSchemeSpkWithSpqr] at *
                  simp only [hep, Bool.or_eq_true, Bool.not_eq_true']
                  split_ifs <;> simp_all [d, im_e2e, bhModelInst_set_same_gs hgs_m,
                    bhE2EDrvState_set_same_gs σ_e2e i hi_e2e hi_me gs_m hgs_m]
              rw [h_cli_run, h_ad_run]
              refine cliAdapterStepCoupledRem_bind_pure (SM.samIfNec r) f_cli f_ad fun ⟨cns, bad⟩ _ => ?_
              rcases epMgmt_rel_of_gs_rel qep p bad hb_eq h_win h_ep h_idx h_max h_ch h_comp h_tL h_lk h_cr
                  h_tr h_epA0 h_epB0 h_trA0 h_cpA0 h_tL0 hbob_of_B with
                ⟨hep_cli, hep_m⟩ |
                ⟨s_cli, s_m, hep_cli, hep_m, hs_st_cli, hs_st_m, hs_tr_cli, hs_tr_m,
                 hs_b, hs_win, hs_ep, hs_idx, hs_max, hs_ch, hs_comp, hs_tL, hs_lk, hs_cr,
                 hs_epA0, hs_epB0, hs_cpA0, hs_tL0⟩
              · dsimp only [f_cli, f_ad]; rw [hep_cli, hep_m]
                exact ⟨rfl, cliAdapterDrvRel_decrement_i hRel i, hRem⟩
              · dsimp only [f_cli, f_ad]; rw [hep_cli, hep_m]
                have h_safeCh_s : s_cli.safeCh (2 + 1) p = s_m.safeCh (2 + 1) p := by
                  unfold SM.GameState.safeCh SM.healedBy; rw [hs_tL, hs_ep]
                have h_challOK_s : cfg_cli.base.challAllowedIn (s_cli.epoch p) =
                    cfg_m.base.challAllowedIn (s_m.epoch p) := by
                  dsimp [cfg_cli, cfg_m, bhConfigSpkS, configRefuseEarlyBobCorr, configR1OnCurve]
                  rw [hs_ep]; rfl
                have h_challMsg_s : cfg_cli.base.challMsg (s_cli.epoch p) =
                    cfg_m.base.challMsg (s_m.epoch p) := by
                  dsimp [cfg_cli, cfg_m, bhConfigSpkS, configRefuseEarlyBobCorr, configR1OnCurve]
                  rw [hs_ep]; rfl
                dsimp only
                rw [h_safeCh_s, h_challOK_s, h_challMsg_s, hb_eq]
                cases (!s_m.safeCh (2 + 1) p || !cfg_m.base.challAllowedIn (s_m.epoch p))
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  let m_send := (cfg_m.base.challMsg (s_m.epoch p)).getD (if gs_m.b then m1 else m0)
                  obtain ⟨hout2, hInstRel', hInstRem'⟩ :=
                    cliAdapterInstRel_of_send_record hCli hℓ hq_pos hInstRel hInstRem
                      hgs_cli hgs_m hCorr p m_send cns true hbob_of_B
                      hs_st_cli hs_st_m hs_tr_cli hs_tr_m hs_b hs_win hs_ep hs_idx
                      hs_max hs_ch hs_comp hs_tL hs_lk hs_cr hs_epA0 hs_epB0 hs_cpA0 hs_tL0
                  exact ⟨congrArg some hout2,
                    cliAdapterDrvRel_update_inst_ad hRel hi_cli _ _ im im_e2e inst (σ_ad.2.1 i)
                      rfl hinst_ad rfl (fun _ _ => rfl) (fun _ _ => rfl) hInstRel',
                    cliAdapterDrvRemoteIdInv_update_inst hRem i _ _ _ _ hInstRem'⟩
                · simp only [↓reduceIte]
                  exact ⟨trivial, cliAdapterDrvRel_decrement_i hRel i, hRem⟩
            · have h_win_cli := h_win.trans h_win_m
              have h_cli_run :
                  (((SM.oracleImplR (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0)
                      (2 + 1) qep (bhConfigSpkS (Msg := Plain ℓ) decT encT)
                      (.inl (.inl (.inl (.inr (p, m0, m1, r)))))).run gs_cli) >>= fun (r0, gsOut) =>
                    pure ((r0, { ds_cli with bhInsts := ds_cli.bhInsts.set i { bi with gs := some gsOut },
                                             instMeta := ds_cli.instMeta.set i im }), st_cli)) =
                    pure ((none, ds_cli), st_cli) := by
                dsimp [SM.oracleImplR, SM.challR, SM.challImpl]
                simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
                  h_sendOK_cli, h_win_cli, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                  bi, im, bhDrvState_set_same_gs ds_cli i hi_cli hi_mb gs_cli hgs_cli]
              have h_ad_run :
                  (bhE2EStepLocalSm W.C W.Q.K qep decT encT σ_e2e i
                      (.inl (.inl (.inl (.inr (p, m0, m1, r))))) >>= fun (sr, σ_e2e') =>
                    match sr.1 with
                    | none => pure ((none, σ_ad), σ_e2e')
                    | some ct => pure ((some (cliWrapAdapterSend inst (σ_ad.2.1 i) p ct), σ_ad), σ_e2e')) =
                    pure ((none, σ_ad), σ_e2e) := by
                dsimp [bhE2EStepLocalSm, SM.oracleImplR, SM.challR, SM.challImpl, configRefuseEarlyBobCorr, configR1OnCurve]
                dsimp only [configRefuseEarlyBobCorr, configR1OnCurve] at h_sendOK_m
                simp only [hClean_e2e, hd_opt, hime_opt, hgs_m, bhIsBobRecvSMQuery, bhIsBobAcceptSMResp,
                  StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, bhPackSmResp,
                  h_sendOK_m, h_win_m, Bool.not_true, Bool.false_eq_true, Bool.and_false,
                  Bool.false_and, ↓reduceIte,
                  d, im_e2e, bhE2EDrvState_set_same_gs σ_e2e i hi_e2e hi_me gs_m hgs_m]
              rw [h_cli_run, h_ad_run]
              exact cliAdapterStepCoupledRem_ret _ _ _ _ _ (cliAdapterDrvRel_decrement_i hRel i) hRem

theorem cliDrvSM_adapter_coupling_ch
    (hCli : CliSpecPqxdh run X W) (hℓ : ℓ < 10 ^ 6)
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (hRem : CliAdapterDrvRemoteIdInv S ℓ ds_cli σ_e2e)
    (i : ℕ) (p : Party) (m0 m1 : Plain ℓ) (r : Option (BitVec 512))
    (hq_pos : 0 < qs_rem i) :
    cliAdapterStepCoupled X W b qStart (Function.update qs_rem i (qs_rem i - 1))
      (((cliDrvSM S ℓ run W qep decT encT ext ⟨i, .inl (.inl (.inl (.inr (p, m0, m1, r))))⟩).run ds_cli).run st_cli)
      (((cliComposedAdapterImplWith (modelPrims X W) ki W.C W.Q.K qep decT encT
          (.inr ⟨i, .inl (.inl (.inl (.inr (p, m0, m1, r))))⟩)).run σ_ad).run σ_e2e) :=
  (cliDrvSM_adapter_couplingRem_ch run X W qep decT encT ext ki hCli hℓ hRel hRem i p m0 m1 r hq_pos).toStepCoupled

end SendAndChallenge

/-! ## SM Alice deliver and inject coupling -/

section AliceDeliverAndInjectHelpers
variable {S : SignalPqxdh.Setup} {ℓ : ℕ} {bobAccepted : Bool}
  {sid : SignalPqxdh.SessionId S} {hdr : SignalPqxdh.HandshakeHdr}

private theorem cliAdapterTrans_find?_B_whisper
    {trans_cli trans_m : List (SM.Record (Plain ℓ) Bytes)}
    (h : List.Forall₂ (CliAdapterTransEntryRel bobAccepted sid hdr) trans_cli trans_m)
    (body : Bytes) (hbody : body ≠ []) :
    (trans_cli.find? (fun r => r.pos.sender == .B && decide (r.ct = wireWhisper :: body))).map
        (fun r => (r.pos, r.msg)) =
      (trans_m.find? (fun r => r.pos.sender == .B && decide (r.ct = body))).map
        (fun r => (r.pos, r.msg)) := by
  induction h with
  | nil => rfl
  | @cons r_cli r_m rs_cli rs_m hrel _ ih =>
    rcases hrel with ⟨hpos, hmsg, hct⟩
    have hpred :
        (r_cli.pos.sender == .B && decide (r_cli.ct = wireWhisper :: body)) =
        (r_m.pos.sender == .B && decide (r_m.ct = body)) := by
      rw [hpos]
      cases hs : r_m.pos.sender
      · rfl
      · have hs_cli : r_cli.pos.sender = .B := by rw [hpos, hs]
        rcases hct with ⟨h1, h2⟩ | ⟨_, _, _, _, _, hB⟩
        · simp [h1, h2, Ne.symm hbody]
        · simp [hB hs_cli]
    simp only [List.find?_cons, hpred]
    cases r_m.pos.sender == .B && decide (r_m.ct = body)
    · exact ih
    · simp [hpos, hmsg]

private theorem cliAdapterTrans_find?_nil
    {trans_cli trans_m : List (SM.Record (Plain ℓ) Bytes)}
    (h : List.Forall₂ (CliAdapterTransEntryRel bobAccepted sid hdr) trans_cli trans_m)
    (p : Party) :
    (trans_cli.find? (fun r => r.pos.sender == p && decide (r.ct = []))).map
        (fun r => (r.pos, r.msg)) =
      (trans_m.find? (fun r => r.pos.sender == p && decide (r.ct = []))).map
        (fun r => (r.pos, r.msg)) := by
  induction h with
  | nil => rfl
  | @cons r_cli r_m rs_cli rs_m hrel _ ih =>
    rcases hrel with ⟨hpos, hmsg, hct⟩
    have hct_eq : decide (r_cli.ct = []) = decide (r_m.ct = []) := by
      rcases hct with ⟨h1, h2⟩ | ⟨hne, _, _, _, hA, hB⟩
      · simp [h1, h2]
      · have hcli_ne : r_cli.ct ≠ [] := by
          cases hs : r_cli.pos.sender
          · intro h0
            have hw := (hA hs).1
            rw [h0] at hw
            unfold bhWireInnerBytes bhDecodePreKeyMsgE at hw
            cases hw
          · rw [hB hs]; simp
        simp [hne, hcli_ne]
    have hpred :
        (r_cli.pos.sender == p && decide (r_cli.ct = [])) =
        (r_m.pos.sender == p && decide (r_m.ct = [])) := by rw [hpos, hct_eq]
    simp only [List.find?_cons, hpred]
    cases r_m.pos.sender == p && decide (r_m.ct = [])
    · exact ih
    · simp [hpos, hmsg]

private theorem cliAdapterTrans_filter_pos
    {trans_cli trans_m : List (SM.Record (Plain ℓ) Bytes)}
    (h : List.Forall₂ (CliAdapterTransEntryRel bobAccepted sid hdr) trans_cli trans_m)
    (pos : SM.Pos) :
    List.Forall₂ (CliAdapterTransEntryRel bobAccepted sid hdr)
      (trans_cli.filter (fun rec => rec.pos != pos))
      (trans_m.filter (fun rec => rec.pos != pos)) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons r_cli r_m rs_cli rs_m hrel _ ih =>
    have hpos : (r_cli.pos != pos) = (r_m.pos != pos) := by rw [hrel.1]
    simp only [List.filter_cons, hpos]
    cases r_m.pos != pos
    · exact ih
    · exact List.Forall₂.cons hrel ih

private theorem cliAdapterTrans_find?_B_none
    {trans_cli trans_m : List (SM.Record (Plain ℓ) Bytes)}
    (h : List.Forall₂ (CliAdapterTransEntryRel bobAccepted sid hdr) trans_cli trans_m)
    (c : Bytes) (hc : c ≠ [])
    (hbad : ∀ body, c = wireWhisper :: body → body = [] ∨ (bhDecodePreKeyMsgE body).isSome) :
    trans_cli.find? (fun r => r.pos.sender == .B && decide (r.ct = c)) = none := by
  induction h with
  | nil => rfl
  | @cons r_cli r_m rs_cli rs_m hrel _ ih =>
    rcases hrel with ⟨_, _, hct⟩
    have hp : (r_cli.pos.sender == .B && decide (r_cli.ct = c)) = false := by
      rw [Bool.eq_false_iff]; intro hm
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
      rcases hct with ⟨h1, _⟩ | ⟨hne, hdec, _, _, _, hB⟩
      · exact hc (hm.2 ▸ h1)
      · rcases hbad r_m.ct (by rw [← hm.2, hB hm.1]) with h0 | h0
        · exact hne h0
        · rw [hdec] at h0; cases h0
    simp only [List.find?_cons, hp]
    exact ih

private theorem cliAdapterTrans_m_ct_len
    {trans_cli trans_m : List (SM.Record (Plain ℓ) Bytes)}
    (h : List.Forall₂ (CliAdapterTransEntryRel bobAccepted sid hdr) trans_cli trans_m)
    (r : SM.Record (Plain ℓ) Bytes) (hr : r ∈ trans_m) (hne : r.ct ≠ []) :
    r.ct.length ≤ 1_000_300 ∧ r.ct.length + 2048 < 2 ^ 32 := by
  revert hr
  induction h with
  | nil => intro hr; simp at hr
  | @cons r_cli r_m rs_cli rs_m hrel _ ih =>
    intro hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · rcases hrel.2.2 with ⟨_, h2⟩ | ⟨_, _, _, hlen, _, _⟩
      · exact absurd h2 hne
      · exact hlen
    · exact ih hr'

private theorem cliAdapterTrans_find?_m_ww_none
    {trans_cli trans_m : List (SM.Record (Plain ℓ) Bytes)}
    (h : List.Forall₂ (CliAdapterTransEntryRel bobAccepted sid hdr) trans_cli trans_m)
    (p : Party) (rest : Bytes) :
    trans_m.find? (fun r => r.pos.sender == p && decide (r.ct = wireWhisper :: rest)) = none := by
  induction h with
  | nil => rfl
  | @cons r_cli r_m rs_cli rs_m hrel _ ih =>
    rcases hrel with ⟨_, _, hct⟩
    have hp : (r_m.pos.sender == p && decide (r_m.ct = wireWhisper :: rest)) = false := by
      rcases hct with ⟨_, h2⟩ | ⟨_, _, hww, _⟩
      · simp [h2]
      · simp [hww rest]
    simp only [List.find?_cons, hp]
    exact ih

end AliceDeliverAndInjectHelpers

private theorem cliOracleImplR_deliver_run {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (P : Party) (c : C) (s : SM.GameState St Msg C) :
    (SM.oracleImplR sm Δ qep cfg (.inl (.inl (.inr (P, c))))).run s =
      if s.win || (s.inTransit P.other c).isNone then pure (none, s)
      else ($ᵗ RCoins : ProbComp RCoins) >>= fun rc => pure (deliverRPure sm cfg P c rc s) :=
  stepR_deliver_eq sm Δ qep cfg P c s

open CryptoVerification.E2E.BhAdapterIjHelpersV1 in
private theorem cliOracleImplR_inject_run {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (P : Party) (c : C) (s : SM.GameState St Msg C) :
    (SM.oracleImplR sm Δ qep cfg (.inl (.inr (P, c)))).run s =
      if s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ) || !(cfg.injOK c) then
        pure (none, s)
      else ($ᵗ RCoins : ProbComp RCoins) >>= fun rc => pure (injectPost sm Δ qep cfg s P c rc) :=
  injectR_run sm Δ qep cfg s P c

private theorem cliDeliverRPure_reject {Key St Msg Coins RCoins C : Type} [DecidableEq Msg] [DecidableEq C]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (cfg : SM.ConfigR St Msg C)
    (P : Party) (c : C) (rc : RCoins) (s : SM.GameState St Msg C) (r : SM.Record Msg C)
    (hwin : s.win = false) (htr : s.inTransit P.other c = some r)
    (hmust : cfg.must s P r = false) (hrcv : sm.receive (s.st P) c rc = none) :
    deliverRPure sm cfg P c rc s = (some .rejected, s) := by
  unfold deliverRPure; simp [hwin, htr, hmust, hrcv]

private theorem cliDeliverRPure_accept {Key St Msg Coins RCoins C : Type} [DecidableEq Msg] [DecidableEq C]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (cfg : SM.ConfigR St Msg C)
    (P : Party) (c : C) (rc : RCoins) (s : SM.GameState St Msg C) (r : SM.Record Msg C)
    (st' : St) (t' i' : ℕ) (m' : Msg)
    (hwin : s.win = false) (htr : s.inTransit P.other c = some r)
    (hmust : cfg.must s P r = false) (hrcv : sm.receive (s.st P) c rc = some (st', t', i', m')) :
    deliverRPure sm cfg P c rc s =
      (some (.accepted t' i' (if s.chall.contains r.pos then none else some m')),
        s.accept P st' r.pos) := by
  unfold deliverRPure; simp [hwin, htr, hmust, hrcv]

private theorem bhConfigSpkS_must_cli {Pt : Type} (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ℓ : ℕ} (s : SM.GameState BinState (Plain ℓ) Bytes) (P : Party) (r : SM.Record (Plain ℓ) Bytes) :
    (bhConfigSpkS (Msg := Plain ℓ) decT encT).must s P r = false := rfl

private theorem configSpkS_must_cli {Pt : Type} (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {ℓ : ℕ} (s : SM.GameState (GhostState Bytes) (Plain ℓ) Bytes) (P : Party)
    (r : SM.Record (Plain ℓ) Bytes) :
    (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).must s P r = false := rfl

private theorem cliAdapterStepCoupledRem_congr_cli {S : SignalPqxdh.Setup} {ℓ : ℕ} {α : Type}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {b : Bool} {qStart' : ℕ} {qs_rem' : ℕ → ℕ}
    {c c' : ProbComp ((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S)}
    {c_ad : ProbComp ((α × CliAdapterState S) × BHE2EDrvState S ℓ)}
    (h : c = c') (h' : cliAdapterStepCoupledRem X W b qStart' qs_rem' c' c_ad) :
    cliAdapterStepCoupledRem X W b qStart' qs_rem' c c_ad := h ▸ h'

private theorem cliAdapterStepCoupledRem_deliver {S : SignalPqxdh.Setup} {ℓ : ℕ} {GB GM : Type}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {b : Bool} {qStart' : ℕ} {qs_rem' : ℕ → ℕ}
    (m_cli : ProbComp (Option (SM.RecvResult (Plain ℓ)) × GB))
    (m_m : ProbComp (Option (SM.RecvResult (Plain ℓ)) × GM))
    (c_cli c_m : Bool) (s_cli : GB) (s_m : GM)
    (D_cli : BitVec 256 → Option (SM.RecvResult (Plain ℓ)) × GB)
    (D_m : BitVec 256 → Option (SM.RecvResult (Plain ℓ)) × GM)
    (hm_cli : m_cli = if c_cli then pure (none, s_cli)
      else ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc => pure (D_cli rc))
    (hm_m : m_m = if c_m then pure (none, s_m)
      else ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun rc => pure (D_m rc))
    (hc : c_cli = c_m)
    (F_cli : Option (SM.RecvResult (Plain ℓ)) × GB →
      (Option (SM.RecvResult (Plain ℓ)) × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S)
    (F_m : Option (SM.RecvResult (Plain ℓ)) × GM →
      (Option (SM.RecvResult (Plain ℓ)) × CliAdapterState S) × BHE2EDrvState S ℓ)
    (h0 : c_m = true →
      (F_cli (none, s_cli)).1.1 = (F_m (none, s_m)).1.1 ∧
      CliAdapterDrvRel S ℓ X W b qStart' qs_rem'
        (F_cli (none, s_cli)).2 (F_cli (none, s_cli)).1.2 (F_m (none, s_m)).1.2 (F_m (none, s_m)).2 ∧
      CliAdapterDrvRemoteIdInv S ℓ (F_cli (none, s_cli)).1.2 (F_m (none, s_m)).2)
    (h1 : c_m = false → ∀ rc,
      (F_cli (D_cli rc)).1.1 = (F_m (D_m rc)).1.1 ∧
      CliAdapterDrvRel S ℓ X W b qStart' qs_rem'
        (F_cli (D_cli rc)).2 (F_cli (D_cli rc)).1.2 (F_m (D_m rc)).1.2 (F_m (D_m rc)).2 ∧
      CliAdapterDrvRemoteIdInv S ℓ (F_cli (D_cli rc)).1.2 (F_m (D_m rc)).2) :
    cliAdapterStepCoupledRem X W b qStart' qs_rem'
      (m_cli >>= fun x => pure (F_cli x)) (m_m >>= fun x => pure (F_m x)) := by
  subst hm_cli hm_m hc
  cases hcm : c_cli
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
    exact cliAdapterStepCoupledRem_bind_pure _ (fun rc => F_cli (D_cli rc)) (fun rc => F_m (D_m rc))
      (fun rc _ => h1 hcm rc)
  · simp only [↓reduceIte, pure_bind]
    have h := h0 hcm
    rcases hF : F_cli (none, s_cli) with ⟨⟨r1, ds1⟩, st1⟩
    rcases hG : F_m (none, s_m) with ⟨⟨r2, sa2⟩, se2⟩
    rw [hF, hG] at h
    obtain ⟨h_eq, h_rel, h_rem⟩ := h
    dsimp only at h_eq h_rel h_rem
    subst h_eq
    exact cliAdapterStepCoupledRem_ret _ _ _ _ _ h_rel h_rem

private theorem cliAdapterInstRel_set_win {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {q_rem : ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {bi : ModelDriverInstance S ℓ} {d : BHModelInst S ℓ} {im im_e2e : ModelDriverInstanceMeta S}
    {inst : BHAdapterInstMeta S} {ack : Bool}
    (hInstRel : CliAdapterInstRel X W q_rem st_cli ds_cli bi d im im_e2e inst ack)
    (hInstRem : CliAdapterInstRemoteIdInv d im)
    {gs_cli : SM.GameState BinState (Plain ℓ) Bytes}
    {gs_m : SM.GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hgs_cli : bi.gs = some gs_cli) (hgs_m : d.gs = some gs_m) :
    CliAdapterInstRel X W q_rem st_cli ds_cli
      { bi with gs := some { gs_cli with win := true } }
      { d with gs := some { gs_m with win := true } } im im_e2e inst ack ∧
    CliAdapterInstRemoteIdInv { d with gs := some { gs_m with win := true } } im := by
  refine ⟨?_, ?_⟩
  · refine
      { im_eq := hInstRel.im_eq
        sid_eq := hInstRel.sid_eq
        hdr_eq := hInstRel.hdr_eq
        idB_eq := hInstRel.idB_eq
        respSlot_eq := hInstRel.respSlot_eq
        respMeta_eq := hInstRel.respMeta_eq
        regIdA_eq := hInstRel.regIdA_eq
        regIdB_eq := hInstRel.regIdB_eq
        aliceAcked_false := hInstRel.aliceAcked_false
        idA_pub_eq := hInstRel.idA_pub_eq
        idB_pub_eq := hInstRel.idB_pub_eq
        extrasB_eq := hInstRel.extrasB_eq
        stB0_empty := hInstRel.stB0_empty
        resp_bundle_rel := hInstRel.resp_bundle_rel
        handshake_rel := ?_
        gs_rel := ?_ }
    · obtain ⟨bundleE, dk, ac, u_init, bnd, t_init, ss, h1, h2, h3, h4⟩ := hInstRel.handshake_rel
      exact ⟨bundleE, dk, ac, u_init, bnd, t_init, ss, h1, h2, h3,
        fun _ _ h5 h6 h7 h8 => by cases h5; cases h6; exact h4 gs_cli gs_m hgs_cli hgs_m h7 h8⟩
    · have hgs := hInstRel.gs_rel
      rw [hgs_cli, hgs_m] at hgs
      dsimp only
      rcases hgs with ⟨hb, hrest⟩
      refine ⟨hb, ?_⟩
      split_ifs at hrest ⊢
      · rfl
      · exact ⟨hrest.1, rfl, hrest.2.2⟩
  · intro gs₁ hgs₁ hnc
    simp only [Option.some.injEq] at hgs₁; subst hgs₁
    exact hInstRem gs_m hgs_m hnc

private theorem cliAdapterInstRel_of_alice_accept {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {q_rem : ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {bi : ModelDriverInstance S ℓ} {d : BHModelInst S ℓ} {im im_e2e : ModelDriverInstanceMeta S}
    {inst : BHAdapterInstMeta S} {ack : Bool}
    (hInstRel : CliAdapterInstRel X W q_rem st_cli ds_cli bi d im im_e2e inst ack)
    (hInstRem : CliAdapterInstRemoteIdInv d im)
    {gs_cli : SM.GameState BinState (Plain ℓ) Bytes}
    {gs_m : SM.GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hgs_cli : bi.gs = some gs_cli) (hgs_m : d.gs = some gs_m)
    (hCorr : im.ikACorrAtAccept = false) (hBacc : im.bobAccepted = true)
    (g' : GhostState Bytes) (pos : SM.Pos)
    (hg'_party : g'.party = .A)
    (hg'_ppk : g'.session.pendingPreKey = false)
    (hg'_id : g'.session.localIdentity = (gs_m.st .A).session.localIdentity)
    (hg'_rem : g'.session.remoteIdentity = some d.idB)
    (hg'_act : CliPartyActiveInv W (cliPqDirA bi) (bhInstExtrasA inst) g' (q_rem - 1)) :
    let gs_cli' := gs_cli.accept .A (binStateOfUnderExtras (fun _ => bhInstExtrasA inst) g') pos
    let gs_m' := gs_m.accept .A g' pos
    CliAdapterInstRel X W (q_rem - 1) st_cli ds_cli
      { bi with gs := some gs_cli' } { d with gs := some gs_m' } im im_e2e inst true ∧
    CliAdapterInstRemoteIdInv { d with gs := some gs_m' } im := by
  intro gs_cli' gs_m'
  have hgs := hInstRel.gs_rel
  rw [hgs_cli, hgs_m] at hgs
  rcases hgs with ⟨hb_eq, hrest⟩
  simp only [hCorr, Bool.false_eq_true, ↓reduceIte] at hrest
  rcases hrest with
    ⟨h_acc, h_win, h_ep, h_idx, h_max, h_ch, h_comp, h_tL, h_lk, h_cr,
     h_tr, _, h_ppkB, h_idA, _, _, _, _, _, _,
     h_epB1, _, _, h_stB1, _, h_pB, _, h_actB⟩
  have hRem_m := hInstRem gs_m hgs_m (by simp [hCorr])
  have hneBA : Party.B ≠ Party.A := by decide
  refine ⟨?_, ?_⟩
  · refine
      { im_eq := hInstRel.im_eq
        sid_eq := hInstRel.sid_eq
        hdr_eq := hInstRel.hdr_eq
        idB_eq := hInstRel.idB_eq
        respSlot_eq := hInstRel.respSlot_eq
        respMeta_eq := hInstRel.respMeta_eq
        regIdA_eq := hInstRel.regIdA_eq
        regIdB_eq := hInstRel.regIdB_eq
        aliceAcked_false := hInstRel.aliceAcked_false
        idA_pub_eq := hInstRel.idA_pub_eq
        idB_pub_eq := hInstRel.idB_pub_eq
        extrasB_eq := hInstRel.extrasB_eq
        stB0_empty := hInstRel.stB0_empty
        resp_bundle_rel := hInstRel.resp_bundle_rel
        handshake_rel := ?_
        gs_rel := ?_ }
    · obtain ⟨bundleE, dk, ac, u_init, bnd, t_init, ss, h1, h2, h3, _⟩ := hInstRel.handshake_rel
      refine ⟨bundleE, dk, ac, u_init, bnd, t_init, ss, h1, h2, h3, fun _ _ _ _ _ hacc₁ => ?_⟩
      rw [hBacc] at hacc₁; cases hacc₁
    · dsimp only
      refine ⟨by simpa [gs_cli', gs_m', SM.GameState.accept, SM.GameState.delete] using hb_eq, ?_⟩
      simp only [hCorr, Bool.false_eq_true, ↓reduceIte]
      refine ⟨h_acc,
        by simpa [gs_cli', gs_m', SM.GameState.accept, SM.GameState.delete] using h_win,
        by simp only [gs_cli', gs_m', SM.GameState.accept, SM.GameState.delete, h_ep],
        by simpa [gs_cli', gs_m', SM.GameState.accept, SM.GameState.delete] using h_idx,
        by simp only [gs_cli', gs_m', SM.GameState.accept, SM.GameState.delete, h_max],
        by simp only [gs_cli', gs_m', SM.GameState.accept, SM.GameState.delete, h_ch],
        by simp only [gs_cli', gs_m', SM.GameState.accept, SM.GameState.delete, h_comp],
        by simpa [gs_cli', gs_m', SM.GameState.accept, SM.GameState.delete] using h_tL,
        by simpa [gs_cli', gs_m', SM.GameState.accept, SM.GameState.delete] using h_lk,
        by simpa [gs_cli', gs_m', SM.GameState.accept, SM.GameState.delete] using h_cr,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [gs_cli', gs_m', SM.GameState.accept, SM.GameState.delete]
        exact cliAdapterTrans_filter_pos h_tr pos
      · simp [gs_m', SM.GameState.accept, SM.GameState.delete, Function.update, hg'_ppk]
      · simp [gs_m', SM.GameState.accept, SM.GameState.delete, Function.update, hneBA, h_ppkB]
      · simp [gs_m', SM.GameState.accept, SM.GameState.delete, Function.update, hg'_id.trans h_idA]
      · intro hnot; rw [hBacc] at hnot; cases hnot
      · intro hnot; rw [hBacc] at hnot; cases hnot
      · intro hnot; rw [hBacc] at hnot; cases hnot
      · intro hnot; rw [hBacc] at hnot; cases hnot
      · intro hnot; rw [hBacc] at hnot; cases hnot
      · intro hnot; rw [hBacc] at hnot; cases hnot
      · intro hacc
        simp [gs_m', SM.GameState.accept, SM.GameState.delete, Function.update, hneBA, h_epB1 hacc]
      · simp [gs_cli', gs_m', SM.GameState.accept, SM.GameState.delete, Function.update,
          bhBinStateOfParty, hg'_party]
      · intro hnot; rw [hBacc] at hnot; cases hnot
      · intro hacc
        simp [gs_cli', gs_m', SM.GameState.accept, SM.GameState.delete, Function.update,
          hneBA, h_stB1 hacc]
      · simp [gs_m', SM.GameState.accept, SM.GameState.delete, Function.update, hg'_party]
      · simp [gs_m', SM.GameState.accept, SM.GameState.delete, Function.update, hneBA, h_pB]
      · dsimp only [gs_m', SM.GameState.accept, SM.GameState.delete]
        rw [Function.update_self]; exact hg'_act
      · intro hacc
        dsimp only [gs_m', SM.GameState.accept, SM.GameState.delete]
        rw [Function.update_of_ne hneBA]
        exact cliPartyActiveInv_mono (h_actB hacc) (Nat.sub_le _ _)
  · intro gs₁ hgs₁ _
    simp only [Option.some.injEq] at hgs₁; subst hgs₁
    dsimp only [gs_m', SM.GameState.accept, SM.GameState.delete]
    refine ⟨?_, fun hacc => ?_⟩
    · rw [Function.update_self]; exact hg'_rem
    · rw [Function.update_of_ne hneBA]; exact hRem_m.2 hacc

private theorem cliDrvSM_clean_A_dl_run {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (run : CliRun) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (BHDrvM S ℓ))
    (ds : ModelDriverState S ℓ) (st : SignalPqxdh.KeyIndState S)
    (i : ℕ) (bi : ModelDriverInstance S ℓ) (im : ModelDriverInstanceMeta S)
    (gs : SM.GameState BinState (Plain ℓ) Bytes) (c : Bytes)
    (hClean : bhDrvInstClean ds i = true) (hbi_opt : ds.bhInsts[i]? = some bi)
    (him_opt : ds.instMeta[i]? = some im) (hgs : bi.gs = some gs) :
    (((cliDrvSM S ℓ run W qep decT encT ext ⟨i, .inl (.inl (.inr (.A, c)))⟩).run ds).run st) =
      if (bhDecodePreKeyMsgE c).isSome then pure ((none, ds), st)
      else
        (((SM.oracleImplR (cliPqScheme run W ℓ bi (cliPqSigsOf st bi) bi.stA0 bi.stB0)
            (2 + 1) qep (bhConfigSpkS (Msg := Plain ℓ) decT encT)
            (.inl (.inl (.inr (.A, c))))).run gs) >>= fun x =>
          pure ((x.1, { ds with bhInsts := ds.bhInsts.set i { bi with gs := some x.2 },
                                instMeta := ds.instMeta.set i im }), st)) := by
  by_cases hpk : (bhDecodePreKeyMsgE c).isSome = true
  · unfold cliDrvSM
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hClean, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, hbi_opt, him_opt, bhIsBobRecvSMQuery, Bool.and_false,
      Bool.false_and, hgs, cliStepLocalSM, hpk, StateT.run_pure]
  · have hpkf : (bhDecodePreKeyMsgE c).isSome = false := Bool.eq_false_iff.mpr hpk
    simp only [hpkf, Bool.false_eq_true, ↓reduceIte]
    exact cliDrvSM_clean_std_run run W qep decT encT ext ds st i bi im gs
      (.inl (.inl (.inr (.A, c)))) hClean hbi_opt him_opt hgs rfl hpkf

private theorem cliDrvSM_clean_A_ij_run {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (run : CliRun) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (BHDrvM S ℓ))
    (ds : ModelDriverState S ℓ) (st : SignalPqxdh.KeyIndState S)
    (i : ℕ) (bi : ModelDriverInstance S ℓ) (im : ModelDriverInstanceMeta S)
    (gs : SM.GameState BinState (Plain ℓ) Bytes) (c : Bytes)
    (hClean : bhDrvInstClean ds i = true) (hbi_opt : ds.bhInsts[i]? = some bi)
    (him_opt : ds.instMeta[i]? = some im) (hgs : bi.gs = some gs) :
    (((cliDrvSM S ℓ run W qep decT encT ext ⟨i, .inl (.inr (.A, c))⟩).run ds).run st) =
      if (bhDecodePreKeyMsgE c).isSome then pure ((none, ds), st)
      else
        (((SM.oracleImplR (cliPqScheme run W ℓ bi (cliPqSigsOf st bi) bi.stA0 bi.stB0)
            (2 + 1) qep (bhConfigSpkS (Msg := Plain ℓ) decT encT)
            (.inl (.inr (.A, c)))).run gs) >>= fun x =>
          pure ((x.1, { ds with bhInsts := ds.bhInsts.set i { bi with gs := some x.2 },
                                instMeta := ds.instMeta.set i im }), st)) := by
  by_cases hpk : (bhDecodePreKeyMsgE c).isSome = true
  · unfold cliDrvSM
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hClean, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, hbi_opt, him_opt, bhIsBobRecvSMQuery, Bool.and_false,
      Bool.false_and, hgs, cliStepLocalSM, hpk, StateT.run_pure]
  · have hpkf : (bhDecodePreKeyMsgE c).isSome = false := Bool.eq_false_iff.mpr hpk
    simp only [hpkf, Bool.false_eq_true, ↓reduceIte]
    exact cliDrvSM_clean_std_run run W qep decT encT ext ds st i bi im gs
      (.inl (.inr (.A, c))) hClean hbi_opt him_opt hgs rfl hpkf

private theorem bhE2EStepLocalSm_clean_A_dl_run {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ_e2e : BHE2EDrvState S ℓ) (i : ℕ) (d : BHModelInst S ℓ) (im : ModelDriverInstanceMeta S)
    (gs_m : SM.GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (hClean_e2e : bhE2EDrvInstClean σ_e2e i = true) (hd_opt : σ_e2e.insts[i]? = some d)
    (hime_opt : σ_e2e.instMeta[i]? = some im) (hgs_m : d.gs = some gs_m)
    (c : Bytes) :
    bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inl (.inr (.A, c)))) =
      if (bhDecodePreKeyMsgE c).isSome then pure ((none, none, none), σ_e2e)
      else
        (SM.oracleImplR (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB) ℓ
            d.spkCoins) (2 + 1) qep (configRefuseEarlyBobCorr decT encT) (.inl (.inl (.inr (.A, c))))).run gs_m >>= fun x =>
          pure ((none, x.1, none), { σ_e2e with insts := σ_e2e.insts.set i { d with gs := some x.2 },
                                                instMeta := σ_e2e.instMeta.set i im }) := by
  unfold bhE2EStepLocalSm
  simp only [hClean_e2e, hd_opt, hime_opt, hgs_m, bhIsBobRecvSMQuery, Bool.not_true,
    Bool.false_eq_true, Bool.and_false, Bool.false_and, ↓reduceIte, bhIsBobAcceptSMResp,
    bhPackSmResp, pure_bind]

private theorem bhE2EStepLocalSm_clean_A_ij_run {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ_e2e : BHE2EDrvState S ℓ) (i : ℕ) (d : BHModelInst S ℓ) (im : ModelDriverInstanceMeta S)
    (gs_m : SM.GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (hClean_e2e : bhE2EDrvInstClean σ_e2e i = true) (hd_opt : σ_e2e.insts[i]? = some d)
    (hime_opt : σ_e2e.instMeta[i]? = some im) (hgs_m : d.gs = some gs_m)
    (c : Bytes) (hdc : (bhDecodePreKeyMsgE c).isSome = false) :
    bhE2EStepLocalSm C K qep decT encT σ_e2e i (.inl (.inr (.A, c))) =
      (SM.oracleImplR (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB) ℓ
          d.spkCoins) (2 + 1) qep (configRefuseEarlyBobCorr decT encT) (.inl (.inr (.A, c)))).run gs_m >>= fun x =>
        pure ((none, x.1, none), { σ_e2e with insts := σ_e2e.insts.set i { d with gs := some x.2 },
                                              instMeta := σ_e2e.instMeta.set i im }) := by
  unfold bhE2EStepLocalSm
  simp only [hClean_e2e, hd_opt, hime_opt, hgs_m, hdc, bhIsBobRecvSMQuery, Bool.not_true,
    Bool.false_eq_true, Bool.and_false, Bool.false_and, ↓reduceIte, bhIsBobAcceptSMResp,
    bhPackSmResp, pure_bind]

section AliceRecvAndInject
variable {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
  (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) (qep : ℕ)
  (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
  (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (BHDrvM S ℓ))
  (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
  {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
  {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
  {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}

open CryptoVerification.E2E.BhAdapterIjHelpersV1 in
/-- SM Alice deliver step coupling. -/
theorem cliDrvSM_adapter_couplingRem_dl_A
    (hCli : CliSpecPqxdh run X W)
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (hRem : CliAdapterDrvRemoteIdInv S ℓ ds_cli σ_e2e)
    (i : ℕ) (c : Bytes)
    (hq_pos : i < ds_cli.bhInsts.length → 0 < qs_rem i) :
    cliAdapterStepCoupledRem X W b qStart (Function.update qs_rem i (qs_rem i - 1))
      (((cliDrvSM S ℓ run W qep decT encT ext ⟨i, .inl (.inl (.inr (.A, c)))⟩).run ds_cli).run st_cli)
      (((cliComposedAdapterImplWith (modelPrims X W) ki W.C W.Q.K qep decT encT
          (.inr ⟨i, .inl (.inl (.inr (.A, c)))⟩)).run σ_ad).run σ_e2e) := by
  cases hClean : bhDrvInstClean ds_cli i
  · exact cliDrvSM_adapter_couplingRem_not_clean run X W qep decT encT ext ki hRel hRem i _ hClean
  · by_cases hi_cli : i < ds_cli.bhInsts.length
    swap
    · exact cliDrvSM_adapter_couplingRem_oob run X W qep decT encT ext ki hRel hRem i _
        (Nat.le_of_not_lt hi_cli)
    · have hq_i : 0 < qs_rem i := hq_pos hi_cli
      have hi_e2e : i < σ_e2e.insts.length := hRel.insts_len_eq ▸ hi_cli
      have hi_mb : i < ds_cli.instMeta.length := hRel.meta_cli_len_eq.symm ▸ hi_cli
      have hi_me : i < σ_e2e.instMeta.length := hRel.meta_e2e_len_eq.symm ▸ hi_e2e
      have hCorr : ds_cli.instMeta[i].ikACorrAtAccept = false :=
        bhDrvInstClean_imp_ikACorrAtAccept_false hClean hi_cli hi_mb
      obtain ⟨inst, hinst_ad, hInstRel⟩ := hRel.insts_rel i hi_cli hi_e2e hi_mb hi_me
      have hInstRem := hRem i hi_e2e hi_mb
      set bi := ds_cli.bhInsts[i]; set d := σ_e2e.insts[i]
      set im := ds_cli.instMeta[i]; set im_e2e := σ_e2e.instMeta[i]
      have hbi_opt : ds_cli.bhInsts[i]? = some bi := List.getElem?_eq_getElem hi_cli
      have hd_opt : σ_e2e.insts[i]? = some d := List.getElem?_eq_getElem hi_e2e
      have him_opt : ds_cli.instMeta[i]? = some im := List.getElem?_eq_getElem hi_mb
      have hime_opt : σ_e2e.instMeta[i]? = some im_e2e := List.getElem?_eq_getElem hi_me
      have hClean_e2e : bhE2EDrvInstClean σ_e2e i = true :=
        (bhDrvInstClean_eq_bhE2EDrvInstClean_of_cliRel hRel i).symm.trans hClean
      have hgs := hInstRel.gs_rel
      cases hgs_cli : bi.gs with
      | none => rw [hgs_cli] at hgs; exact False.elim hgs
      | some gs_cli =>
        cases hgs_m : d.gs with
        | none => rw [hgs_cli, hgs_m] at hgs; exact False.elim hgs
        | some gs_m =>
          rw [hgs_cli, hgs_m] at hgs; rcases hgs with ⟨hb_eq, hrest⟩
          simp only [hCorr, Bool.false_eq_true, ↓reduceIte] at hrest
          rcases hrest with
            ⟨h_acc, h_win, h_ep, h_idx, h_max, h_ch, h_comp, h_tL, h_lk, h_cr,
             h_tr, h_ppkA, h_ppkB, h_idA, h_ack0, h_epA0, h_epB0, h_trA0, h_cpA0, h_tL0,
             h_epB1, h_stA, h_stB0, h_stB1, h_pA, h_pB, h_actA, h_actB⟩
          have hRem_m := hInstRem gs_m hgs_m (by simp [hCorr])
          have hR := cliAdapterDrvRel_decrement_i hRel i
          have hds_same :
              { ds_cli with bhInsts := ds_cli.bhInsts.set i { bi with gs := some gs_cli },
                            instMeta := ds_cli.instMeta.set i im } = ds_cli :=
            bhDrvState_set_same_gs ds_cli i hi_cli hi_mb gs_cli hgs_cli
          have he2e_same :
              { σ_e2e with insts := σ_e2e.insts.set i { d with gs := some gs_m },
                           instMeta := σ_e2e.instMeta.set i im_e2e } = σ_e2e :=
            bhE2EDrvState_set_same_gs σ_e2e i hi_e2e hi_me gs_m hgs_m
          have hbinA : gs_cli.st .A = binStateOfUnderExtras (fun _ => bhInstExtrasA inst) (gs_m.st .A) := by
            rw [h_stA]; simp only [bhBinStateOfParty, h_pA]
          have hdec_nil : bhDecodePreKeyMsgE ([] : Bytes) = none := by
            unfold bhDecodePreKeyMsgE; rfl
          rw [cliDrvSM_clean_A_dl_run run W qep decT encT ext ds_cli st_cli i bi im gs_cli c
              hClean hbi_opt him_opt hgs_cli,
            cliComposedAdapterImplWith_dl_A_run]
          rcases c with _ | ⟨t, body⟩
          ·
            dsimp only
            rw [bhE2EStepLocalSm_clean_A_dl_run W.C W.Q.K qep decT encT σ_e2e i d im_e2e gs_m
              hClean_e2e hd_opt hime_opt hgs_m []]
            simp only [hdec_nil, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
              bind_assoc, pure_bind]
            have hcond : (gs_cli.win || (gs_cli.inTransit Party.A.other []).isNone) =
                (gs_m.win || (gs_m.inTransit Party.A.other []).isNone) := by
              rw [h_win]
              have hnil := congrArg Option.isNone (cliAdapterTrans_find?_nil h_tr Party.B)
              simp only [Option.isNone_map] at hnil
              simp only [SM.GameState.inTransit, Party.other]
              exact congrArg (gs_m.win || ·) hnil
            refine cliAdapterStepCoupledRem_deliver _ _ _ _ gs_cli gs_m
              (fun rc => deliverRPure (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0)
                (bhConfigSpkS decT encT) .A [] rc gs_cli)
              (fun rc => deliverRPure
                (sessionSchemeFixedSpk (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB) ℓ d.spkCoins)
                (configRefuseEarlyBobCorr decT encT) .A [] rc gs_m)
              (cliOracleImplR_deliver_run _ _ _ _ _ _ _) (cliOracleImplR_deliver_run _ _ _ _ _ _ _) hcond
              _ _ ?_ ?_
            · intro _
              dsimp only
              rw [hds_same, he2e_same]
              exact ⟨rfl, hR, hRem⟩
            · intro hf rc
              have hf_cli := hcond.trans hf
              rcases hr_m : gs_m.inTransit Party.A.other [] with _ | r_m
              · rw [hr_m] at hf; simp at hf
              rcases hr_cli : gs_cli.inTransit Party.A.other [] with _ | r_cli
              · rw [hr_cli] at hf_cli; simp at hf_cli
              have hw_m : gs_m.win = false := (Bool.or_eq_false_iff.mp hf).1
              have hw_cli : gs_cli.win = false := (Bool.or_eq_false_iff.mp hf_cli).1
              have hrcv_cli : (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0).receive
                  (gs_cli.st .A) [] rc = none := by
                show cliPqReceive run W ℓ bi (cliPqSigsOf st_cli bi) (gs_cli.st .A) [] rc = none
                rw [hbinA]
                exact cliPqReceive_A_nil_eq_none hCli bi (cliPqSigsOf st_cli bi)
                  (bhInstExtrasA inst) (gs_m.st .A) rc h_pA h_actA
              have hrcv_m : (sessionSchemeFixedSpk (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB)
                  ℓ d.spkCoins).receive (gs_m.st .A) [] rc = none := by
                simp [sessionSchemeFixedSpk, params_receive_nil]
              rw [cliDeliverRPure_reject _ _ _ _ _ _ r_cli hw_cli hr_cli (bhConfigSpkS_must_cli _ _ _ _ _) hrcv_cli,
                cliDeliverRPure_reject _ _ _ _ _ _ r_m hw_m hr_m (configSpkS_must_cli _ _ _ _ _) hrcv_m]
              dsimp only
              rw [hds_same, he2e_same]
              exact ⟨rfl, hR, hRem⟩
          ·
            dsimp only
            by_cases hgood : t = wireWhisper ∧ body ≠ [] ∧ (bhDecodePreKeyMsgE body).isSome = false
            · obtain ⟨rfl, hbne, hdb⟩ := hgood
              obtain ⟨b0, bs, rfl⟩ := List.exists_cons_of_ne_nil hbne
              have hdc : (bhDecodePreKeyMsgE (wireWhisper :: b0 :: bs)).isSome = false := by
                rw [bhDecodePreKeyMsgE_head_ne _ _ (by decide)]; rfl
              simp only [beq_self_eq_true, ↓reduceIte]
              rw [bhE2EStepLocalSm_clean_A_dl_run W.C W.Q.K qep decT encT σ_e2e i d im_e2e gs_m
                hClean_e2e hd_opt hime_opt hgs_m (b0 :: bs)]
              simp only [hdc, hdb, Bool.false_eq_true, ↓reduceIte,
                bind_assoc, pure_bind]
              have hne : (b0 :: bs) ≠ [] := List.cons_ne_nil _ _
              have hfind := cliAdapterTrans_find?_B_whisper h_tr (b0 :: bs) hne
              have hcond : (gs_cli.win || (gs_cli.inTransit Party.A.other (wireWhisper :: b0 :: bs)).isNone) =
                  (gs_m.win || (gs_m.inTransit Party.A.other (b0 :: bs)).isNone) := by
                rw [h_win]
                have hnone := congrArg Option.isNone hfind
                simp only [Option.isNone_map] at hnone
                simp only [SM.GameState.inTransit, Party.other]
                exact congrArg (gs_m.win || ·) hnone
              refine cliAdapterStepCoupledRem_deliver _ _ _ _ gs_cli gs_m
                (fun rc => deliverRPure (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0)
                  (bhConfigSpkS decT encT) .A (wireWhisper :: b0 :: bs) rc gs_cli)
                (fun rc => deliverRPure
                  (sessionSchemeFixedSpk (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB) ℓ d.spkCoins)
                  (configRefuseEarlyBobCorr decT encT) .A (b0 :: bs) rc gs_m)
                (cliOracleImplR_deliver_run _ _ _ _ _ _ _) (cliOracleImplR_deliver_run _ _ _ _ _ _ _) hcond
                _ _ ?_ ?_
              · intro _
                dsimp only [cliAliceAdapterUpdate]
                rw [hds_same, he2e_same]
                exact ⟨rfl, hR, hRem⟩
              · intro hf rc
                have hf_cli := hcond.trans hf
                rcases hr_m : gs_m.inTransit Party.A.other (b0 :: bs) with _ | r_m
                · rw [hr_m] at hf; simp at hf
                rcases hr_cli : gs_cli.inTransit Party.A.other (wireWhisper :: b0 :: bs) with _ | r_cli
                · rw [hr_cli] at hf_cli; simp at hf_cli
                have hw_m : gs_m.win = false := (Bool.or_eq_false_iff.mp hf).1
                have hw_cli : gs_cli.win = false := (Bool.or_eq_false_iff.mp hf_cli).1
                have hr_m' := hr_m
                have hr_cli' := hr_cli
                simp only [SM.GameState.inTransit, Party.other] at hr_m' hr_cli'
                have hpm := hfind
                rw [hr_m', hr_cli'] at hpm
                simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hpm
                obtain ⟨hpos, _⟩ := hpm
                have hmem : r_m ∈ gs_m.trans := List.mem_of_find?_eq_some hr_m'
                have hsat := List.find?_some hr_m'
                simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hsat
                obtain ⟨hsend_m, hct⟩ := hsat
                have hlenm := cliAdapterTrans_m_ct_len h_tr r_m hmem (by rw [hct]; exact hne)
                rw [hct] at hlenm
                have hc32 : (wireWhisper :: b0 :: bs).length < 2 ^ 32 := by
                  simp only [List.length_cons] at hlenm ⊢; omega
                have hcap : (wireWhisper :: b0 :: bs).length ≤ stdinCapBytes := by
                  unfold stdinCapBytes; simp only [List.length_cons] at hlenm ⊢; omega
                obtain ⟨hrw, hpost⟩ := cliPqReceive_A_whisper_props hCli hq_i hInstRel
                  (gs_m.st .A) (b0 :: bs) rc h_pA hRem_m.1 h_actA hc32 hcap
                dsimp only at hrw hpost
                rcases hP : (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB).receive
                    (gs_m.st .A) (b0 :: bs) rc with _ | ⟨g', t', i', m'⟩
                · have hrcv_cli : (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0).receive
                      (gs_cli.st .A) (wireWhisper :: b0 :: bs) rc = none := by
                    show cliPqReceive run W ℓ bi (cliPqSigsOf st_cli bi) (gs_cli.st .A) _ rc = none
                    rw [hbinA, hrw, hP]; rfl
                  have hrcv_m : (sessionSchemeFixedSpk (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB)
                      ℓ d.spkCoins).receive (gs_m.st .A) (b0 :: bs) rc = none := by
                    show Option.map _ _ = _; rw [hP]; rfl
                  rw [cliDeliverRPure_reject _ _ _ _ _ _ r_cli hw_cli hr_cli (bhConfigSpkS_must_cli _ _ _ _ _) hrcv_cli,
                    cliDeliverRPure_reject _ _ _ _ _ _ r_m hw_m hr_m (configSpkS_must_cli _ _ _ _ _) hrcv_m]
                  dsimp only [cliAliceAdapterUpdate]
                  rw [hds_same, he2e_same]
                  exact ⟨rfl, hR, hRem⟩
                · have hrcv_cli : (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0).receive
                      (gs_cli.st .A) (wireWhisper :: b0 :: bs) rc =
                      some (binStateOfUnderExtras (fun _ => bhInstExtrasA inst) g', t', i', padOrTruncatePlain ℓ m') := by
                    show cliPqReceive run W ℓ bi (cliPqSigsOf st_cli bi) (gs_cli.st .A) _ rc = _
                    rw [hbinA, hrw, hP]; rfl
                  have hrcv_m : (sessionSchemeFixedSpk (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB)
                      ℓ d.spkCoins).receive (gs_m.st .A) (b0 :: bs) rc = some (g', t', i', padOrTruncatePlain ℓ m') := by
                    show Option.map _ _ = _; rw [hP]; rfl
                  rw [cliDeliverRPure_accept _ _ _ _ _ _ r_cli _ _ _ _ hw_cli hr_cli (bhConfigSpkS_must_cli _ _ _ _ _) hrcv_cli,
                    cliDeliverRPure_accept _ _ _ _ _ _ r_m _ _ _ _ hw_m hr_m (configSpkS_must_cli _ _ _ _ _) hrcv_m]
                  have hBacc : im.bobAccepted = true := by
                    by_contra hn
                    have := h_trA0 (by simpa using hn) r_m hmem
                    rw [hsend_m] at this; cases this
                  obtain ⟨hgp, hgppk, hgid, hgrem, hgact⟩ := hpost g' t' i' m' hP
                  obtain ⟨hInstRel', hInstRem'⟩ := cliAdapterInstRel_of_alice_accept
                    hInstRel hInstRem hgs_cli hgs_m hCorr hBacc g' r_m.pos hgp hgppk hgid hgrem hgact
                  dsimp only [cliAliceAdapterUpdate]
                  rw [hpos]
                  exact ⟨by simp only [h_ch],
                    cliAdapterDrvRel_update_inst_ad hRel hi_cli _ _ im im_e2e inst true
                      rfl hinst_ad (by simp) (fun _ _ => rfl) (fun k hk => by simp [hk]) hInstRel',
                    cliAdapterDrvRemoteIdInv_update_inst hRem i _ _ _ _ hInstRem'⟩
            ·
              have hbad : ∀ body', t :: body = wireWhisper :: body' →
                  body' = [] ∨ (bhDecodePreKeyMsgE body').isSome := by
                intro body' h
                obtain ⟨rfl, rfl⟩ := List.cons.inj h
                by_cases h0 : body = []
                · exact Or.inl h0
                · right; by_contra h1; exact hgood ⟨rfl, h0, by simpa using h1⟩
              refine cliAdapterStepCoupledRem_congr_cli (c' := pure ((none, ds_cli), st_cli)) ?_ ?_
              · have hin : (gs_cli.win || (gs_cli.inTransit Party.A.other (t :: body)).isNone) = true := by
                  simp only [SM.GameState.inTransit, Party.other,
                    cliAdapterTrans_find?_B_none h_tr _ (List.cons_ne_nil _ _) hbad, Option.isNone_none,
                    Bool.or_true]
                by_cases hdc : (bhDecodePreKeyMsgE (t :: body)).isSome = true
                · simp only [hdc, ↓reduceIte]
                · simp only [hdc, Bool.false_eq_true, ↓reduceIte]
                  rw [cliOracleImplR_deliver_run]
                  simp only [hin, ↓reduceIte, pure_bind, hds_same]
              · by_cases ht : t = wireWhisper
                · subst ht
                  rcases body with _ | ⟨b0, bs⟩
                  · simp only [beq_self_eq_true, ↓reduceIte]
                    exact cliAdapterStepCoupledRem_ret _ _ _ _ _ hR hRem
                  · have hdb : (bhDecodePreKeyMsgE (b0 :: bs)).isSome = true := by
                      by_contra h1; exact hgood ⟨rfl, List.cons_ne_nil _ _, by simpa using h1⟩
                    simp only [beq_self_eq_true, ↓reduceIte]
                    rw [bhE2EStepLocalSm_clean_A_dl_run W.C W.Q.K qep decT encT σ_e2e i d im_e2e gs_m
                      hClean_e2e hd_opt hime_opt hgs_m (b0 :: bs)]
                    simp only [hdb, ↓reduceIte, pure_bind, cliAliceAdapterUpdate]
                    exact cliAdapterStepCoupledRem_ret _ _ _ _ _ hR hRem
                · have htb : (t == wireWhisper) = false := by simpa using ht
                  simp only [htb, Bool.false_eq_true, ↓reduceIte]
                  exact cliAdapterStepCoupledRem_ret _ _ _ _ _ hR hRem

theorem cliDrvSM_adapter_coupling_dl_A
    (hCli : CliSpecPqxdh run X W)
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (hRem : CliAdapterDrvRemoteIdInv S ℓ ds_cli σ_e2e)
    (i : ℕ) (c : Bytes)
    (hq_pos : i < ds_cli.bhInsts.length → 0 < qs_rem i) :
    cliAdapterStepCoupled X W b qStart (Function.update qs_rem i (qs_rem i - 1))
      (((cliDrvSM S ℓ run W qep decT encT ext ⟨i, .inl (.inl (.inr (.A, c)))⟩).run ds_cli).run st_cli)
      (((cliComposedAdapterImplWith (modelPrims X W) ki W.C W.Q.K qep decT encT
          (.inr ⟨i, .inl (.inl (.inr (.A, c)))⟩)).run σ_ad).run σ_e2e) :=
  (cliDrvSM_adapter_couplingRem_dl_A run X W qep decT encT ext ki hCli hRel hRem i c hq_pos).toStepCoupled

open CryptoVerification.E2E.BhAdapterIjHelpersV1 in
/-- SM Alice inject step coupling. -/
theorem cliDrvSM_adapter_couplingRem_ij_A
    (hCli : CliSpecPqxdh run X W)
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (hRem : CliAdapterDrvRemoteIdInv S ℓ ds_cli σ_e2e)
    (i : ℕ) (c : Bytes)
    (hq_pos : i < ds_cli.bhInsts.length → 0 < qs_rem i) :
    cliAdapterStepCoupledRem X W b qStart (Function.update qs_rem i (qs_rem i - 1))
      (((cliDrvSM S ℓ run W qep decT encT ext ⟨i, .inl (.inr (.A, c))⟩).run ds_cli).run st_cli)
      (((cliComposedAdapterImplWith (modelPrims X W) ki W.C W.Q.K qep decT encT
          (.inr ⟨i, .inl (.inr (.A, c))⟩)).run σ_ad).run σ_e2e) := by
  cases hClean : bhDrvInstClean ds_cli i
  · exact cliDrvSM_adapter_couplingRem_not_clean run X W qep decT encT ext ki hRel hRem i _ hClean
  · by_cases hi_cli : i < ds_cli.bhInsts.length
    swap
    · exact cliDrvSM_adapter_couplingRem_oob run X W qep decT encT ext ki hRel hRem i _
        (Nat.le_of_not_lt hi_cli)
    · have hq_i : 0 < qs_rem i := hq_pos hi_cli
      have hi_e2e : i < σ_e2e.insts.length := hRel.insts_len_eq ▸ hi_cli
      have hi_mb : i < ds_cli.instMeta.length := hRel.meta_cli_len_eq.symm ▸ hi_cli
      have hi_me : i < σ_e2e.instMeta.length := hRel.meta_e2e_len_eq.symm ▸ hi_e2e
      have hCorr : ds_cli.instMeta[i].ikACorrAtAccept = false :=
        bhDrvInstClean_imp_ikACorrAtAccept_false hClean hi_cli hi_mb
      obtain ⟨inst, hinst_ad, hInstRel⟩ := hRel.insts_rel i hi_cli hi_e2e hi_mb hi_me
      have hInstRem := hRem i hi_e2e hi_mb
      set bi := ds_cli.bhInsts[i]; set d := σ_e2e.insts[i]
      set im := ds_cli.instMeta[i]; set im_e2e := σ_e2e.instMeta[i]
      have hbi_opt : ds_cli.bhInsts[i]? = some bi := List.getElem?_eq_getElem hi_cli
      have hd_opt : σ_e2e.insts[i]? = some d := List.getElem?_eq_getElem hi_e2e
      have him_opt : ds_cli.instMeta[i]? = some im := List.getElem?_eq_getElem hi_mb
      have hime_opt : σ_e2e.instMeta[i]? = some im_e2e := List.getElem?_eq_getElem hi_me
      have hClean_e2e : bhE2EDrvInstClean σ_e2e i = true :=
        (bhDrvInstClean_eq_bhE2EDrvInstClean_of_cliRel hRel i).symm.trans hClean
      have hgs := hInstRel.gs_rel
      cases hgs_cli : bi.gs with
      | none => rw [hgs_cli] at hgs; exact False.elim hgs
      | some gs_cli =>
        cases hgs_m : d.gs with
        | none => rw [hgs_cli, hgs_m] at hgs; exact False.elim hgs
        | some gs_m =>
          rw [hgs_cli, hgs_m] at hgs; rcases hgs with ⟨hb_eq, hrest⟩
          simp only [hCorr, Bool.false_eq_true, ↓reduceIte] at hrest
          rcases hrest with
            ⟨h_acc, h_win, h_ep, h_idx, h_max, h_ch, h_comp, h_tL, h_lk, h_cr,
             h_tr, -, -, h_idA, -, -, -, -, h_cpA0, h_tL0,
             -, h_stA, -, -, h_pA, -, h_actA, -⟩
          have hRem_m := hInstRem gs_m hgs_m (by simp [hCorr])
          have hR := cliAdapterDrvRel_decrement_i hRel i
          have hds_same :
              { ds_cli with bhInsts := ds_cli.bhInsts.set i { bi with gs := some gs_cli },
                            instMeta := ds_cli.instMeta.set i im } = ds_cli :=
            bhDrvState_set_same_gs ds_cli i hi_cli hi_mb gs_cli hgs_cli
          have he2e_same :
              { σ_e2e with insts := σ_e2e.insts.set i { d with gs := some gs_m },
                           instMeta := σ_e2e.instMeta.set i im_e2e } = σ_e2e :=
            bhE2EDrvState_set_same_gs σ_e2e i hi_e2e hi_me gs_m hgs_m
          have hbinA : gs_cli.st .A = binStateOfUnderExtras (fun _ => bhInstExtrasA inst) (gs_m.st .A) := by
            rw [h_stA]; simp only [bhBinStateOfParty, h_pA]
          have hsafe : gs_cli.safeInj (2 + 1) = gs_m.safeInj (2 + 1) := by
            simp only [SM.GameState.safeInj, h_tL, h_ep]
          have hrcv_cli_eq : ∀ (body' : Bytes) (rc : BitVec 256),
              (wireWhisper :: body').length < 2 ^ 32 →
              (wireWhisper :: body').length ≤ stdinCapBytes →
              (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0).receive
                  (gs_cli.st .A) (wireWhisper :: body') rc =
                ((paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB).receive
                    (gs_m.st .A) body' rc).map
                  (fun (g', t', idx', pt') =>
                    (binStateOfUnderExtras (fun _ => bhInstExtrasA inst) g', t', idx', padOrTruncatePlain ℓ pt')) := by
            intro body' rc hc32 hcap
            obtain ⟨hrw, -⟩ := cliPqReceive_A_whisper_props hCli hq_i hInstRel
              (gs_m.st .A) body' rc h_pA hRem_m.1 h_actA hc32 hcap
            show cliPqReceive run W ℓ bi (cliPqSigsOf st_cli bi) (gs_cli.st .A) _ rc = _
            rw [hbinA]; exact hrw
          have hcli_noop : ∀ c_cli : Bytes, (bhConfigSpkS (Msg := Plain ℓ) decT encT).injOK c_cli = false →
              ((SM.oracleImplR (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0)
                  (2 + 1) qep (bhConfigSpkS decT encT) (.inl (.inr (.A, c_cli)))).run gs_cli >>= fun x =>
                pure ((x.1, { ds_cli with bhInsts := ds_cli.bhInsts.set i { bi with gs := some x.2 },
                                          instMeta := ds_cli.instMeta.set i im }), st_cli)) =
                pure ((none, ds_cli), st_cli) := by
            intro c_cli hinj
            rw [cliOracleImplR_inject_run]
            simp only [hinj, Bool.not_false, Bool.or_true, ↓reduceIte, pure_bind, hds_same]
          have hboth_rej : ∀ (c_cli c_m : Bytes) (upd : Option (SM.RecvResult (Plain ℓ)) → CliAdapterState S),
              upd none = σ_ad → upd (some .rejected) = σ_ad →
              ((gs_cli.win || (gs_cli.inTransit Party.A.other c_cli).isSome || !(gs_cli.safeInj (2 + 1)) ||
                  !((bhConfigSpkS (Msg := Plain ℓ) decT encT).injOK c_cli)) =
                (gs_m.win || (gs_m.inTransit Party.A.other c_m).isSome || !(gs_m.safeInj (2 + 1)) ||
                  !((configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).injOK c_m))) →
              (∀ rc, (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0).receive
                  (gs_cli.st .A) c_cli rc = none) →
              (∀ rc, (sessionSchemeFixedSpk (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB) ℓ
                  d.spkCoins).receive (gs_m.st .A) c_m rc = none) →
              cliAdapterStepCoupledRem X W b qStart (Function.update qs_rem i (qs_rem i - 1))
                ((SM.oracleImplR (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0)
                    (2 + 1) qep (bhConfigSpkS decT encT) (.inl (.inr (.A, c_cli)))).run gs_cli >>= fun x =>
                  pure ((x.1, { ds_cli with bhInsts := ds_cli.bhInsts.set i { bi with gs := some x.2 },
                                            instMeta := ds_cli.instMeta.set i im }), st_cli))
                ((SM.oracleImplR (sessionSchemeFixedSpk (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB) ℓ
                    d.spkCoins) (2 + 1) qep (configRefuseEarlyBobCorr decT encT) (.inl (.inr (.A, c_m)))).run gs_m >>= fun x =>
                  pure ((x.1, upd x.1), { σ_e2e with insts := σ_e2e.insts.set i { d with gs := some x.2 },
                                                     instMeta := σ_e2e.instMeta.set i im_e2e })) := by
            intro c_cli c_m upd hu0 hu1 hg hrb hrm
            refine cliAdapterStepCoupledRem_deliver _ _ _ _ gs_cli gs_m
              (fun rc => injectPost (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0)
                (2 + 1) qep (bhConfigSpkS decT encT) gs_cli .A c_cli rc)
              (fun rc => injectPost (sessionSchemeFixedSpk (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB) ℓ
                d.spkCoins) (2 + 1) qep (configRefuseEarlyBobCorr decT encT) gs_m .A c_m rc)
              (cliOracleImplR_inject_run _ _ _ _ _ _ _) (cliOracleImplR_inject_run _ _ _ _ _ _ _) hg
              _ _ ?_ ?_
            · intro _
              dsimp only
              rw [hu0, hds_same, he2e_same]
              exact ⟨rfl, hR, hRem⟩
            · intro _ rc
              simp only [injectPost, hrb rc, hrm rc]
              rw [hu1, hds_same, he2e_same]
              exact ⟨trivial, hR, hRem⟩
          rw [cliComposedAdapterImplWith_ij_A_run,
            cliDrvSM_clean_A_ij_run run W qep decT encT ext ds_cli st_cli i bi im gs_cli c
              hClean hbi_opt him_opt hgs_cli]
          rcases c with _ | ⟨t, body⟩
          · have hdec : bhDecodePreKeyMsgE ([] : Bytes) = none := by unfold bhDecodePreKeyMsgE; rfl
            dsimp only
            simp only [hdec, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
            rw [hcli_noop [] (by simp [bhConfigSpkS, bhInjOK, hdec])]
            exact cliAdapterStepCoupledRem_ret _ _ _ _ _ hR hRem
          · by_cases ht : t = wireWhisper
            · subst ht
              have hdc : bhDecodePreKeyMsgE (wireWhisper :: body) = none :=
                bhDecodePreKeyMsgE_head_ne _ _ (by decide)
              dsimp only
              simp only [beq_self_eq_true, ↓reduceIte, hdc, Option.isSome_none, Bool.false_eq_true]
              by_cases hcs : (decide ((wireWhisper :: body).length ≤ stdinCapBytes) &&
                  shortCiphertext (wireWhisper :: body)) = true
              · simp only [hcs, ↓reduceIte]
                have hcap : (wireWhisper :: body).length ≤ stdinCapBytes :=
                  of_decide_eq_true (Bool.and_eq_true_iff.mp hcs).1
                have hshort : shortCiphertext (wireWhisper :: body) = true :=
                  (Bool.and_eq_true_iff.mp hcs).2
                have hc32 : (wireWhisper :: body).length < 2 ^ 32 := of_decide_eq_true hshort
                rcases hdb : bhDecodePreKeyMsgE body with _ | mb
                · rcases body with _ | ⟨b0, bs⟩
                  ·
                    simp only [List.isEmpty_nil, List.isEmpty_cons, ↓reduceIte, Bool.false_eq_true]
                    have hdc2 : bhDecodePreKeyMsgE [wireWhisper, wireWhisper] = none :=
                      bhDecodePreKeyMsgE_head_ne _ _ (by decide)
                    rw [bhE2EStepLocalSm_clean_A_ij_run W.C W.Q.K qep decT encT σ_e2e i d im_e2e gs_m
                      hClean_e2e hd_opt hime_opt hgs_m _ (by rw [hdc2]; rfl)]
                    simp only [bind_assoc, pure_bind]
                    refine hboth_rej _ _ (fun _ => σ_ad) rfl rfl ?_ ?_ ?_
                    · have h1 : gs_cli.inTransit Party.A.other [wireWhisper] = none := by
                        simp only [SM.GameState.inTransit, Party.other]
                        exact cliAdapterTrans_find?_B_none h_tr _ (List.cons_ne_nil _ _)
                          (fun b' h => Or.inl (List.cons.inj h).2.symm)
                      have h2 : gs_m.inTransit Party.A.other [wireWhisper, wireWhisper] = none := by
                        simp only [SM.GameState.inTransit, Party.other]
                        exact cliAdapterTrans_find?_m_ww_none h_tr _ _
                      have hi1 : (bhConfigSpkS (Msg := Plain ℓ) decT encT).injOK [wireWhisper] = true := by
                        simp [bhConfigSpkS, bhInjOK, stdinCapBytes, hdc, shortCiphertext, ratchetKeyAdmissible]
                      have hi2 : (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).injOK
                          [wireWhisper, wireWhisper] = true := by
                        simp [configRefuseEarlyBobCorr, configR1OnCurve, ratchetKeyAdmissible]
                      rw [h1, h2, hsafe, h_win, hi1, hi2]
                    · intro rc
                      rw [hrcv_cli_eq [] rc hc32 hcap, params_receive_nil]; rfl
                    · intro rc
                      simp only [sessionSchemeFixedSpk, params_receive_wireWhisper_cons, Option.map_none]
                  ·
                    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
                    rw [bhE2EStepLocalSm_clean_A_ij_run W.C W.Q.K qep decT encT σ_e2e i d im_e2e gs_m
                      hClean_e2e hd_opt hime_opt hgs_m _ (by rw [hdb]; rfl)]
                    simp only [bind_assoc, pure_bind]
                    have hne : (b0 :: bs) ≠ [] := List.cons_ne_nil _ _
                    have hfind := cliAdapterTrans_find?_B_whisper h_tr (b0 :: bs) hne
                    have hinT : (gs_cli.inTransit Party.A.other (wireWhisper :: b0 :: bs)).isSome =
                        (gs_m.inTransit Party.A.other (b0 :: bs)).isSome := by
                      have hs := congrArg Option.isSome hfind
                      simp only [Option.isSome_map] at hs
                      simp only [SM.GameState.inTransit, Party.other]
                      exact hs
                    have hinj : (bhConfigSpkS (Msg := Plain ℓ) decT encT).injOK (wireWhisper :: b0 :: bs) =
                        (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).injOK (b0 :: bs) := by
                      simp only [bhConfigSpkS, bhInjOK, decide_eq_true hcap, hdc, hshort, Bool.true_and,
                        beq_self_eq_true, configRefuseEarlyBobCorr, configR1OnCurve]
                    have hcond :
                        (gs_cli.win || (gs_cli.inTransit Party.A.other (wireWhisper :: b0 :: bs)).isSome ||
                          !(gs_cli.safeInj (2 + 1)) ||
                          !((bhConfigSpkS (Msg := Plain ℓ) decT encT).injOK (wireWhisper :: b0 :: bs))) =
                        (gs_m.win || (gs_m.inTransit Party.A.other (b0 :: bs)).isSome ||
                          !(gs_m.safeInj (2 + 1)) ||
                          !((configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).injOK (b0 :: bs))) := by
                      rw [h_win, hinT, hsafe, hinj]
                    refine cliAdapterStepCoupledRem_deliver _ _ _ _ gs_cli gs_m
                      (fun rc => injectPost (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0)
                        (2 + 1) qep (bhConfigSpkS decT encT) gs_cli .A (wireWhisper :: b0 :: bs) rc)
                      (fun rc => injectPost (sessionSchemeFixedSpk (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K)
                        d.idA d.idB) ℓ d.spkCoins) (2 + 1) qep (configRefuseEarlyBobCorr decT encT) gs_m .A (b0 :: bs) rc)
                      (cliOracleImplR_inject_run _ _ _ _ _ _ _) (cliOracleImplR_inject_run _ _ _ _ _ _ _) hcond
                      _ _ ?_ ?_
                    · intro _
                      dsimp only [cliAliceAdapterUpdate]
                      rw [hds_same, he2e_same]
                      exact ⟨rfl, hR, hRem⟩
                    · intro _ rc
                      obtain ⟨-, hpost⟩ := cliPqReceive_A_whisper_props hCli hq_i hInstRel
                        (gs_m.st .A) (b0 :: bs) rc h_pA hRem_m.1 h_actA hc32 hcap
                      rcases hP : (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB).receive
                          (gs_m.st .A) (b0 :: bs) rc with _ | ⟨g', t', i', m'⟩
                      · have hrb : (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0).receive
                            (gs_cli.st .A) (wireWhisper :: b0 :: bs) rc = none := by
                          rw [hrcv_cli_eq _ rc hc32 hcap, hP]; rfl
                        have hrm : (sessionSchemeFixedSpk (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB) ℓ
                            d.spkCoins).receive (gs_m.st .A) (b0 :: bs) rc = none := by
                          show Option.map _ _ = _; rw [hP]; rfl
                        simp only [injectPost, hrb, hrm]
                        dsimp only [cliAliceAdapterUpdate]
                        rw [hds_same, he2e_same]
                        exact ⟨trivial, hR, hRem⟩
                      · have hrb : (cliPqScheme run W ℓ bi (cliPqSigsOf st_cli bi) bi.stA0 bi.stB0).receive
                            (gs_cli.st .A) (wireWhisper :: b0 :: bs) rc =
                            some (binStateOfUnderExtras (fun _ => bhInstExtrasA inst) g', t', i', padOrTruncatePlain ℓ m') := by
                          rw [hrcv_cli_eq _ rc hc32 hcap, hP]; rfl
                        have hrm : (sessionSchemeFixedSpk (paramsIdsWithSpqr W.C (spqrV1SessionUniformCoins W.C.F W.Q.K) d.idA d.idB) ℓ
                            d.spkCoins).receive (gs_m.st .A) (b0 :: bs) rc = some (g', t', i', padOrTruncatePlain ℓ m') := by
                          show Option.map _ _ = _; rw [hP]; rfl
                        have hany := cliAdapterTrans_any_pos h_tr (fun p => p == (⟨Party.A.other, t', i'⟩ : SM.Pos))
                        have htriv : gs_cli.trivial (2 + 1) ⟨Party.A.other, t', i'⟩ =
                            gs_m.trivial (2 + 1) ⟨Party.A.other, t', i'⟩ := by
                          simp only [SM.GameState.trivial, h_comp, h_tL]
                          rw [hany]
                        have hbase : (bhConfigSpkS (Msg := Plain ℓ) decT encT).base.injectFull t' =
                            (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).base.injectFull t' := rfl
                        simp only [injectPost, hrb, hrm, htriv, hbase]
                        by_cases hq : qep + 1 < t'
                        · simp only [hq, ↓reduceIte]
                          dsimp only [cliAliceAdapterUpdate]
                          rw [hds_same, he2e_same]
                          exact ⟨trivial, hR, hRem⟩
                        · simp only [hq, ↓reduceIte]
                          by_cases htr : gs_m.trivial (2 + 1) ⟨Party.A.other, t', i'⟩ = true
                          · simp only [htr, ↓reduceIte]
                            have hBacc : im.bobAccepted = true := by
                              by_contra hn
                              have hn' : (!im.bobAccepted) = true := by simpa using hn
                              have htL0 := h_tL0 hn'
                              have h' := htr
                              simp [SM.GameState.trivial, htL0, SM.healedBy] at h'
                              have := h_cpA0 hn' _ h'
                              simp [Party.other] at this
                            obtain ⟨hgp, hgppk, hgid, hgrem, hgact⟩ := hpost g' t' i' m' hP
                            obtain ⟨hInstRel', hInstRem'⟩ := cliAdapterInstRel_of_alice_accept
                              hInstRel hInstRem hgs_cli hgs_m hCorr hBacc g' ⟨Party.A.other, t', i'⟩
                              hgp hgppk hgid hgrem hgact
                            dsimp only [cliAliceAdapterUpdate]
                            exact ⟨trivial,
                              cliAdapterDrvRel_update_inst_ad hRel hi_cli _ _ im im_e2e inst true
                                rfl hinst_ad (by simp) (fun _ _ => rfl) (fun k hk => by simp [hk]) hInstRel',
                              cliAdapterDrvRemoteIdInv_update_inst hRem i _ _ _ _ hInstRem'⟩
                          · simp only [htr, Bool.false_eq_true, ↓reduceIte]
                            by_cases hfull : (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).base.injectFull t' = true
                            · simp only [hfull, ↓reduceIte]
                              dsimp only [cliAliceAdapterUpdate]
                              obtain ⟨hInstRel', hInstRem'⟩ := cliAdapterInstRel_set_win
                                (cliAdapterInstRel_mono_q_rem hInstRel (Nat.sub_le _ _)) hInstRem hgs_cli hgs_m
                              exact ⟨trivial,
                                cliAdapterDrvRel_update_inst_ad hRel hi_cli _ _ im im_e2e inst (σ_ad.2.1 i)
                                  rfl hinst_ad rfl (fun _ _ => rfl) (fun _ _ => rfl) hInstRel',
                                cliAdapterDrvRemoteIdInv_update_inst hRem i _ _ _ _ hInstRem'⟩
                            · simp only [hfull, Bool.false_eq_true, ↓reduceIte]
                              dsimp only [cliAliceAdapterUpdate]
                              rw [hds_same, he2e_same]
                              exact ⟨trivial, hR, hRem⟩
                ·
                  rcases body with _ | ⟨b0, bs⟩
                  · have hd0 : bhDecodePreKeyMsgE ([] : Bytes) = none := by unfold bhDecodePreKeyMsgE; rfl
                    rw [hd0] at hdb; cases hdb
                  by_cases hb0 : b0 = wirePrekey
                  swap
                  · rw [bhDecodePreKeyMsgE_head_ne _ _ hb0] at hdb; cases hdb
                  subst hb0
                  simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
                  have hdc2 : bhDecodePreKeyMsgE (wireWhisper :: wirePrekey :: bs) = none :=
                    bhDecodePreKeyMsgE_head_ne _ _ (by decide)
                  rw [bhE2EStepLocalSm_clean_A_ij_run W.C W.Q.K qep decT encT σ_e2e i d im_e2e gs_m
                    hClean_e2e hd_opt hime_opt hgs_m _ (by rw [hdc2]; rfl)]
                  simp only [bind_assoc, pure_bind]
                  refine hboth_rej _ _ (cliAliceAdapterUpdate σ_ad i) rfl rfl ?_ ?_ ?_
                  · have h1 : gs_cli.inTransit Party.A.other (wireWhisper :: wirePrekey :: bs) = none := by
                      simp only [SM.GameState.inTransit, Party.other]
                      refine cliAdapterTrans_find?_B_none h_tr _ (List.cons_ne_nil _ _) (fun b' h => ?_)
                      obtain ⟨-, rfl⟩ := List.cons.inj h
                      right; rw [hdb]; rfl
                    have h2 : gs_m.inTransit Party.A.other (wireWhisper :: wirePrekey :: bs) = none := by
                      simp only [SM.GameState.inTransit, Party.other]
                      exact cliAdapterTrans_find?_m_ww_none h_tr _ _
                    have hi1 : (bhConfigSpkS (Msg := Plain ℓ) decT encT).injOK (wireWhisper :: wirePrekey :: bs) = true := by
                      simp only [bhConfigSpkS, bhInjOK, decide_eq_true hcap, hdc, hshort, Bool.true_and,
                        beq_self_eq_true, ratchetKeyOnCurve_wirePrekey_cons]
                    have hi2 : (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).injOK
                        (wireWhisper :: wirePrekey :: bs) = true :=
                      ratchetKeyOnCurve_wireWhisper_cons _ _ _ _
                    rw [h1, h2, hsafe, h_win, hi1, hi2]
                  · intro rc
                    rw [hrcv_cli_eq _ rc hc32 hcap, params_receive_wirePrekey_cons]; rfl
                  · intro rc
                    simp only [sessionSchemeFixedSpk, params_receive_wireWhisper_cons, Option.map_none]
              · have hcs' : (decide ((wireWhisper :: body).length ≤ stdinCapBytes) &&
                    shortCiphertext (wireWhisper :: body)) = false := by simpa using hcs
                have hinj : (bhConfigSpkS (Msg := Plain ℓ) decT encT).injOK (wireWhisper :: body) = false := by
                  rw [Bool.eq_false_iff]
                  intro h
                  apply hcs
                  unfold bhConfigSpkS bhInjOK at h
                  dsimp only at h
                  simp only [Bool.and_eq_true] at h ⊢
                  exact h.1
                simp only [hcs', Bool.false_eq_true, ↓reduceIte]
                rw [hcli_noop _ hinj]
                exact cliAdapterStepCoupledRem_ret _ _ _ _ _ hR hRem
            · have htb : (t == wireWhisper) = false := by simpa using ht
              dsimp only
              simp only [htb, Bool.false_eq_true, ↓reduceIte]
              by_cases hdc : (bhDecodePreKeyMsgE (t :: body)).isSome = true
              · simp only [hdc, ↓reduceIte]
                exact cliAdapterStepCoupledRem_ret _ _ _ _ _ hR hRem
              · simp only [hdc, Bool.false_eq_true, ↓reduceIte]
                have hdn : bhDecodePreKeyMsgE (t :: body) = none := by simpa using hdc
                rw [hcli_noop _ (by simp [bhConfigSpkS, bhInjOK, hdn, htb])]
                exact cliAdapterStepCoupledRem_ret _ _ _ _ _ hR hRem

theorem cliDrvSM_adapter_coupling_ij_A
    (hCli : CliSpecPqxdh run X W)
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (hRem : CliAdapterDrvRemoteIdInv S ℓ ds_cli σ_e2e)
    (i : ℕ) (c : Bytes)
    (hq_pos : i < ds_cli.bhInsts.length → 0 < qs_rem i) :
    cliAdapterStepCoupled X W b qStart (Function.update qs_rem i (qs_rem i - 1))
      (((cliDrvSM S ℓ run W qep decT encT ext ⟨i, .inl (.inr (.A, c))⟩).run ds_cli).run st_cli)
      (((cliComposedAdapterImplWith (modelPrims X W) ki W.C W.Q.K qep decT encT
          (.inr ⟨i, .inl (.inr (.A, c))⟩)).run σ_ad).run σ_e2e) :=
  (cliDrvSM_adapter_couplingRem_ij_A run X W qep decT encT ext ki hCli hRel hRem i c hq_pos).toStepCoupled

end AliceRecvAndInject

end CryptoVerification.E2E
