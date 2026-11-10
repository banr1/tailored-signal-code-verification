/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.CliPqBadKemBound
public import Computational.Proofs.LibsignalCli.CliPqAdapterRemoteIdInv
public import Computational.Specifications.Assumptions.KeyInd1KeyReal
import Computational.Proofs.LibsignalCli.CliPqRetainedDirEq
import Computational.Proofs.GameHop.Advantage
import Computational.Proofs.GameHop.StateSim
import ProofLib.BV.WidthNorm
import VCVio.EvalDist.Monad.Basic

/-!
# Whole-game adapter coupling up to bad KEM

**Checked by Lean.** Couples `cliPqExp` and `cliE2EExpWithKi true` at
`SignalPqxdh.pqxdhKeyIndImpl1KeyReal` up to `cliClause2BadKemBool`, deriving
`CliPqAdapterBoundProp` from the per-oracle step-bridge propositions.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.constructorNameAsVariable false

open scoped ENNReal BigOperators
open ReductionDsl OracleComp OracleSpec MeasureTheory

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.SignalSession

/-! ## Budget monotonicity -/

private theorem evalDist_bind_true_eq_probExpect_cli {α : Type}
    (mx : ProbComp α) (k : α → ProbComp Bool) :
    𝒟[mx >>= k] {true} = SignalPqxdh.Security.probExpect mx (fun a => 𝒟[k a] {true}) := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  rw [evalDist_bind_of_discrete,
      Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
  rfl

private theorem probExpect_add_cli {α : Type} (mx : ProbComp α) (f g : α → ℝ≥0∞) :
    SignalPqxdh.Security.probExpect mx (fun x => f x + g x) =
      SignalPqxdh.Security.probExpect mx f + SignalPqxdh.Security.probExpect mx g := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  unfold SignalPqxdh.Security.probExpect
  exact MeasureTheory.lintegral_add_left Measurable.of_discrete g

private theorem boolDist_le_of_evalDist_true_both_le (E₁ E₂ E_bad : ProbComp Bool)
    (h1 : 𝒟[E₁] {true} ≤ 𝒟[E₂] {true} + 𝒟[E_bad] {true})
    (h2 : 𝒟[E₂] {true} ≤ 𝒟[E₁] {true} + 𝒟[E_bad] {true}) :
    𝒟[E₁].boolDist 𝒟[E₂] ≤ 𝒟[E_bad] {true} :=
  Computational.Proofs.GameHop.Advantage.boolDist_le_of_both_true_le 𝒟[E₁] 𝒟[E₂] h1 h2

theorem CliPartyActiveInv.mono {W : PEParams} {d0 : PqParty} {x : RecordExtras}
    {g : GhostState Bytes} {q_rem q_rem' : ℕ}
    (h : CliPartyActiveInv W d0 x g q_rem) (_hle : q_rem' ≤ q_rem) :
    CliPartyActiveInv W d0 x g q_rem' := h

theorem CliAdapterInstRel.mono_q_rem {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {q_rem q_rem' : ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {bi : ModelDriverInstance S ℓ} {d : BHModelInst S ℓ} {im im_e2e : ModelDriverInstanceMeta S}
    {inst : BHAdapterInstMeta S} {ack : Bool}
    (h : CliAdapterInstRel X W q_rem st_cli ds_cli bi d im im_e2e inst ack)
    (hle : q_rem' ≤ q_rem) :
    CliAdapterInstRel X W q_rem' st_cli ds_cli bi d im im_e2e inst ack where
  im_eq := h.im_eq
  sid_eq := h.sid_eq
  hdr_eq := h.hdr_eq
  idB_eq := h.idB_eq
  respSlot_eq := h.respSlot_eq
  respMeta_eq := h.respMeta_eq
  regIdA_eq := h.regIdA_eq
  regIdB_eq := h.regIdB_eq
  aliceAcked_false := h.aliceAcked_false
  idA_pub_eq := h.idA_pub_eq
  idB_pub_eq := h.idB_pub_eq
  extrasB_eq := h.extrasB_eq
  stB0_empty := h.stB0_empty
  resp_bundle_rel := h.resp_bundle_rel
  handshake_rel := h.handshake_rel
  gs_rel := by
    have hgs := h.gs_rel
    cases hbi : bi.gs with
    | none => rw [hbi] at hgs; exact False.elim hgs
    | some gs_cli =>
      cases hd : d.gs with
      | none => rw [hbi, hd] at hgs; exact False.elim hgs
      | some gs_m =>
        rw [hbi, hd] at hgs
        dsimp only at hgs ⊢
        refine ⟨hgs.1, ?_⟩
        by_cases hcorr : im.ikACorrAtAccept = true
        · simp only [hcorr, ↓reduceIte] at hgs ⊢
          exact hgs.2
        · simp only [hcorr, Bool.false_eq_true, ↓reduceIte] at hgs ⊢
          rcases hgs.2 with
            ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
             h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, hActA, hActB⟩
          exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
            h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26,
            hActA.mono hle, fun hb => (hActB hb).mono hle⟩

theorem CliAdapterDrvRel.mono_qs_rem {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart : ℕ} {qs_rem qs_rem' : ℕ → ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (hle : ∀ i < ds_cli.bhInsts.length, qs_rem' i ≤ qs_rem i) :
    CliAdapterDrvRel S ℓ X W b qStart qs_rem' st_cli ds_cli σ_ad σ_e2e where
  b_eq := hRel.b_eq
  st_rel := hRel.st_rel
  ki_inv := hRel.ki_inv
  base_e2e_eq := hRel.base_e2e_eq
  base_ad_eq := hRel.base_ad_eq
  corrPrins_eq := hRel.corrPrins_eq
  revealedSpks_eq := hRel.revealedSpks_eq
  insts_len_le := hRel.insts_len_le
  insts_len_eq := hRel.insts_len_eq
  meta_cli_len_eq := hRel.meta_cli_len_eq
  meta_e2e_len_eq := hRel.meta_e2e_len_eq
  ad_none_of_ge := hRel.ad_none_of_ge
  insts_rel := fun i h_cli h_e2e h_mb h_me => by
    obtain ⟨inst, h_ad, hInst⟩ := hRel.insts_rel i h_cli h_e2e h_mb h_me
    exact ⟨inst, h_ad, hInst.mono_q_rem (hle i h_cli)⟩

theorem CliAdapterDrvRel.mono_qStart {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart qStart' : ℕ} {qs_rem : ℕ → ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (hle : qStart ≤ qStart') :
    CliAdapterDrvRel S ℓ X W b qStart' qs_rem st_cli ds_cli σ_ad σ_e2e :=
  { hRel with insts_len_le := hRel.insts_len_le.trans hle }

theorem cliAdapterStepCoupled.mono_qs_rem {S : SignalPqxdh.Setup} {ℓ : ℕ} {α : Type}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart' : ℕ} {qs_rem' qs_rem'' : ℕ → ℕ}
    {c_cli : ProbComp ((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S)}
    {c_ad : ProbComp ((α × CliAdapterState S) × BHE2EDrvState S ℓ)}
    (hC : cliAdapterStepCoupled X W b qStart' qs_rem' c_cli c_ad)
    (hle : ∀ k, qs_rem'' k ≤ qs_rem' k) :
    cliAdapterStepCoupled X W b qStart' qs_rem'' c_cli c_ad := by
  rcases hC with ⟨μ, h1, h2, hsupp⟩
  exact ⟨μ, h1, h2, fun x y hxy =>
    ⟨(hsupp x y hxy).1, (hsupp x y hxy).2.mono_qs_rem (fun k _ => hle k)⟩⟩

theorem cliAdapterStepCoupled.mono_qStart {S : SignalPqxdh.Setup} {ℓ : ℕ} {α : Type}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart₁ qStart₂ : ℕ} {qs_rem' : ℕ → ℕ}
    {c_cli : ProbComp ((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S)}
    {c_ad : ProbComp ((α × CliAdapterState S) × BHE2EDrvState S ℓ)}
    (hC : cliAdapterStepCoupled X W b qStart₁ qs_rem' c_cli c_ad)
    (hle : qStart₁ ≤ qStart₂) :
    cliAdapterStepCoupled X W b qStart₂ qs_rem' c_cli c_ad := by
  rcases hC with ⟨μ, h1, h2, hsupp⟩
  exact ⟨μ, h1, h2, fun x y hxy =>
    ⟨(hsupp x y hxy).1, (hsupp x y hxy).2.mono_qStart hle⟩⟩

/-! ## Per-oracle step-bridge propositions -/

/-- Step-bridge proposition for uniform sampling queries. -/
def CliUnifStepBridgeProp {Pt : Type}
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) : Prop :=
  ∀ {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ},
    CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e →
    ∀ (n : ℕ),
      cliAdapterStepCoupled X W b qStart qs_rem
        ((((QueryImpl.ofLift unifSpec ProbComp).liftTarget (BHDrvM S ℓ) n).run ds_cli).run st_cli)
        (((cliComposedAdapterImplWith (modelPrims X W)
            (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S (modelPrims X W))
            W.C W.Q.K qep decT encT (.inl (.inl (.inl n)))).run σ_ad).run σ_e2e)

theorem cliUnifStepBridgeProp_holds {Pt : Type}
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    CliUnifStepBridgeProp S ℓ X W qep decT encT := by
  intro b qStart qs_rem st_cli ds_cli σ_ad σ_e2e hRel n
  refine ⟨(query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>= fun r =>
      pure (((r, ds_cli), st_cli), ((r, σ_ad), σ_e2e)), ?_, ?_, ?_⟩
  · dsimp only [QueryImpl.ofLift, QueryImpl.liftTarget]
    simp [CryptoGames.Lazy.DEq, map_eq_bind_pure_comp, bind_assoc,
      StateT.run_monadLift, monadLift_self, OracleSpec.query_def]
  · dsimp [cliComposedAdapterImplWith, cliAdapterStepImplWith, bhShallowAdapterImpl, bhFwdU]
    simp [CryptoGames.Lazy.DEq, map_eq_bind_pure_comp, bind_assoc,
      simulateQ_bind, simulateQ_pure,
      cliE2EDrvImplWith, StateT.run_bind, StateT.run_pure, StateT.run_monadLift, monadLift_self]
  · intro x y hmem
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨r, _, rfl, rfl⟩
    exact ⟨rfl, hRel⟩

/-- Step-bridge proposition for 1-key real-HKDF `KeyInd` queries. -/
def CliKeyIndStepBridgeProp {Pt : Type}
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) : Prop :=
  ∀ {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ},
    CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e →
    CliE2ERemoteIdInv σ_e2e →
    cliClause2BadKemBool S (modelPrims X W) st_cli ds_cli = false →
    ∀ (kq : SignalPqxdh.KeyIndQuery S),
      cliAdapterStepCoupled X W b qStart qs_rem
        (((bhDrvKeyInd S ℓ (modelPrims X W) false kq).run ds_cli).run st_cli)
        (((cliComposedAdapterImplWith (modelPrims X W)
            (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S (modelPrims X W))
            W.C W.Q.K qep decT encT (.inl (.inl (.inr kq)))).run σ_ad).run σ_e2e)

/-- Step-bridge proposition for `startDR` control queries. -/
def CliStartStepBridgeProp {Pt : Type}
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) : Prop :=
  ∀ {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ},
    CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e →
    CliE2ERemoteIdInv σ_e2e →
    cliClause2BadKemBool S (modelPrims X W) st_cli ds_cli = false →
    ds_cli.bhInsts.length < qStart →
    ∀ (sid : SignalPqxdh.SessionId S),
      cliAdapterStepCoupled X W b qStart qs_rem
        (((cliDrvStart S ℓ (modelPrims X W) run W (fun _ _ _ _ _ => some b) sid).run
            ds_cli).run st_cli)
        (((cliComposedAdapterImplWith (modelPrims X W)
            (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S (modelPrims X W))
            W.C W.Q.K qep decT encT (.inl (.inr (.startDR sid)))).run σ_ad).run σ_e2e)

theorem cliStartStepBridgeProp_of_succ {Pt : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {qep : ℕ} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hSucc : ∀ {b : Bool} {n : ℕ} {qs_rem : ℕ → ℕ}
      {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
      {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ},
      CliAdapterDrvRel S ℓ X W b n qs_rem st_cli ds_cli σ_ad σ_e2e →
      CliE2ERemoteIdInv σ_e2e →
      cliClause2BadKemBool S (modelPrims X W) st_cli ds_cli = false →
      ∀ (sid : SignalPqxdh.SessionId S),
        cliAdapterStepCoupled X W b (n + 1) qs_rem
          (((cliDrvStart S ℓ (modelPrims X W) run W (fun _ _ _ _ _ => some b) sid).run
              ds_cli).run st_cli)
          (((cliComposedAdapterImplWith (modelPrims X W)
              (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S (modelPrims X W))
              W.C W.Q.K qep decT encT (.inl (.inr (.startDR sid)))).run σ_ad).run σ_e2e)) :
    CliStartStepBridgeProp S ℓ run X W qep decT encT := by
  intro b qStart qs_rem st_cli ds_cli σ_ad σ_e2e hRel hRem hGood hLenLt sid
  have hRelLen : CliAdapterDrvRel S ℓ X W b ds_cli.bhInsts.length qs_rem st_cli ds_cli σ_ad σ_e2e :=
    { hRel with insts_len_le := le_rfl }
  exact (hSucc hRelLen hRem hGood sid).mono_qStart hLenLt

/-- Step-bridge proposition for per-instance SM queries. -/
def CliSmStepBridgeProp {Pt : Type}
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) : Prop :=
  ∀ {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ},
    CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e →
    CliE2ERemoteIdInv σ_e2e →
    cliClause2BadKemBool S (modelPrims X W) st_cli ds_cli = false →
    ∀ (i : ℕ) (q : (cliGameSmSpec ℓ (BitVec 512)).Domain),
      (i < ds_cli.bhInsts.length → 0 < qs_rem i) →
      cliAdapterStepCoupled X W b qStart (Function.update qs_rem i (qs_rem i - 1))
        (((cliDrvSM S ℓ run W qep decT encT bhNoExtWithSpqr ⟨i, q⟩).run ds_cli).run st_cli)
        (((cliComposedAdapterImplWith (modelPrims X W)
            (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S (modelPrims X W))
            W.C W.Q.K qep decT encT (.inr ⟨i, q⟩)).run σ_ad).run σ_e2e)

/-! ## Whole-game `simulateQ` coupling -/

theorem evalDist_bind_coupled_both_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {α : Type}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart' : ℕ} {qs_rem' : ℕ → ℕ}
    {c_cli : ProbComp ((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S)}
    {c_ad : ProbComp ((α × CliAdapterState S) × BHE2EDrvState S ℓ)}
    (hC : cliAdapterStepCoupled X W b qStart' qs_rem' c_cli c_ad)
    (hRemPost : ∀ y ∈ support c_ad, CliE2ERemoteIdInv y.2)
    (F_cli : ((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S) → ProbComp Bool)
    (F_ad : ((α × CliAdapterState S) × BHE2EDrvState S ℓ) → ProbComp Bool)
    (F_bad : ((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S) → ProbComp Bool)
    (hIH : ∀ x y, x.1.1 = y.1.1 →
      CliAdapterDrvRel S ℓ X W b qStart' qs_rem' x.2 x.1.2 y.1.2 y.2 →
      CliE2ERemoteIdInv y.2 →
      𝒟[F_cli x] {true} ≤ 𝒟[F_ad y] {true} + 𝒟[F_bad x] {true} ∧
      𝒟[F_ad y] {true} ≤ 𝒟[F_cli x] {true} + 𝒟[F_bad x] {true}) :
    𝒟[c_cli >>= F_cli] {true} ≤ 𝒟[c_ad >>= F_ad] {true} + 𝒟[c_cli >>= F_bad] {true} ∧
    𝒟[c_ad >>= F_ad] {true} ≤ 𝒟[c_cli >>= F_cli] {true} + 𝒟[c_cli >>= F_bad] {true} := by
  rcases hC with ⟨μ, h1, h2, hsupp⟩
  have hL : ∀ G_cli : ((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S) → ProbComp Bool,
      𝒟[c_cli >>= G_cli] {true} =
        SignalPqxdh.Security.probExpect μ (fun p => 𝒟[G_cli p.1] {true}) := by
    intro G_cli
    have hd := congrArg (fun ν => ν {true}) (h1 G_cli).symm
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] at hd
    exact hd.trans (evalDist_bind_true_eq_probExpect_cli μ (fun p => G_cli p.1))
  have hR : 𝒟[c_ad >>= F_ad] {true} =
      SignalPqxdh.Security.probExpect μ (fun p => 𝒟[F_ad p.2] {true}) := by
    have hd := congrArg (fun ν => ν {true}) (h2 F_ad).symm
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] at hd
    exact hd.trans (evalDist_bind_true_eq_probExpect_cli μ (fun p => F_ad p.2))
  have hRemμ : ∀ x y, (x, y) ∈ support μ → CliE2ERemoteIdInv y.2 :=
    deq_support_snd_imp h2 hRemPost
  constructor
  · rw [hL F_cli, hR, hL F_bad, ← probExpect_add_cli]
    exact SignalPqxdh.Security.probExpect_mono_of_support μ _ _ (fun ⟨x, y⟩ hxy =>
      (hIH x y (hsupp x y hxy).1 (hsupp x y hxy).2 (hRemμ x y hxy)).1)
  · rw [hR, hL F_cli, hL F_bad, ← probExpect_add_cli]
    exact SignalPqxdh.Security.probExpect_mono_of_support μ _ _ (fun ⟨x, y⟩ hxy =>
      (hIH x y (hsupp x y hxy).1 (hsupp x y hxy).2 (hRemμ x y hxy)).2)

private theorem simulateQ_query_bind_run₂_cli {ι : Type} {spec : OracleSpec ι} {M : Type → Type}
    [Monad M] [LawfulMonad M] {σ₁ σ₂ α : Type}
    (impl : QueryImpl spec (StateT σ₁ (StateT σ₂ M)))
    (q : ι) (oa : spec.Range q → OracleComp spec α)
    (s₁ : σ₁) (s₂ : σ₂) :
    (((simulateQ impl (liftM (OracleSpec.query q) >>= oa)).run s₁).run s₂) =
      (((impl q).run s₁).run s₂ >>= fun z => ((simulateQ impl (oa z.1.1)).run z.1.2).run z.2) := by
  simp [simulateQ_bind, StateT.run_bind]

private theorem isQueryBoundP_congr_pred_cli {ι α : Type} {spec : OracleSpec ι}
    {p₁ p₂ : ι → Prop} [d₁ : DecidablePred p₁] [d₂ : DecidablePred p₂]
    (h : ∀ q, p₁ q ↔ p₂ q) {n : ℕ}
    (oa : OracleComp spec α) :
    oa.IsQueryBoundP p₁ n ↔ oa.IsQueryBoundP p₂ n :=
  ⟨Computational.Proofs.GameHop.StateSim.isQueryBoundP_congr_pred h,
   Computational.Proofs.GameHop.StateSim.isQueryBoundP_congr_pred fun q => (h q).symm⟩

/-- Whole-game `OracleComp.inductionOn` coupling up to `cliClause2BadKemBool` over any query-bounded
computation `oa : OracleComp (cliGameSpec S ℓ (BitVec 512)) α`. -/
theorem simulateQ_cliDrvImpl_adapter_coupling_both_le
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt α : Type}
    (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (hKeyInd : CliKeyIndStepBridgeProp S ℓ X W qep decT encT)
    (hStart : CliStartStepBridgeProp S ℓ run X W qep decT encT)
    (hSm : CliSmStepBridgeProp S ℓ run X W qep decT encT)
    (b : Bool) (qStart : ℕ)
    (F_cli : ((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S) → ProbComp Bool)
    (F_ad : ((α × CliAdapterState S) × BHE2EDrvState S ℓ) → ProbComp Bool)
    (hF : ∀ {n : ℕ} {qs_rem : ℕ → ℕ} x y, x.1.1 = y.1.1 →
      CliAdapterDrvRel S ℓ X W b n qs_rem x.2 x.1.2 y.1.2 y.2 →
      𝒟[F_cli x] = 𝒟[F_ad y])
    (oa : OracleComp (cliGameSpec S ℓ (BitVec 512)) α)
    {n qStart_rem : ℕ} {qs_rem : ℕ → ℕ}
    (hn : n + qStart_rem ≤ qStart)
    (hb_start : OracleComp.IsQueryBoundP oa (fun q => q matches .inl (.inr _)) qStart_rem)
    (hb_inst : ∀ k < qStart,
      OracleComp.IsQueryBoundP oa (fun q => bhIsInstQueryWithSpqr k q) (qs_rem k))
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b n qs_rem st_cli ds_cli σ_ad σ_e2e)
    (hRem : CliE2ERemoteIdInv σ_e2e) :
    let P := modelPrims X W
    let impl_cli := cliDrvImpl S ℓ P run W qep decT encT bhNoExtWithSpqr (fun _ _ _ _ _ => some b)
    let impl_ad := cliComposedAdapterImplWith P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
      W.C W.Q.K qep decT encT
    let F_bad : ((α × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S) → ProbComp Bool :=
      fun x => pure (cliClause2BadKemBool S P x.2 x.1.2)
    𝒟[(((simulateQ impl_cli oa).run ds_cli).run st_cli) >>= F_cli] {true} ≤
      𝒟[(((simulateQ impl_ad oa).run σ_ad).run σ_e2e) >>= F_ad] {true} +
        𝒟[(((simulateQ impl_cli oa).run ds_cli).run st_cli) >>= F_bad] {true} ∧
    𝒟[(((simulateQ impl_ad oa).run σ_ad).run σ_e2e) >>= F_ad] {true} ≤
      𝒟[(((simulateQ impl_cli oa).run ds_cli).run st_cli) >>= F_cli] {true} +
        𝒟[(((simulateQ impl_cli oa).run ds_cli).run st_cli) >>= F_bad] {true} := by
  intro P impl_cli impl_ad F_bad
  induction oa using OracleComp.inductionOn
      generalizing n qStart_rem qs_rem st_cli ds_cli σ_ad σ_e2e with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    have hEq := congrArg (fun ν => ν {true}) (hF ((a, ds_cli), st_cli) ((a, σ_ad), σ_e2e) rfl hRel)
    exact ⟨by rw [hEq]; exact le_self_add, by rw [← hEq]; exact le_self_add⟩
  | query_bind q oa ih =>
    by_cases hBad : cliClause2BadKemBool S P st_cli ds_cli = true
    · have hBadOne :
          𝒟[(((simulateQ impl_cli (liftM (OracleSpec.query q) >>= oa)).run ds_cli).run st_cli) >>=
              F_bad] {true} = 1 := by
        rw [evalDist_bind_true_eq_probExpect_cli]
        exact probExpect_simulateQ_cliBadKem_eq_one_of_bad S ℓ P run W qep decT encT
          (fun _ _ _ _ _ => some b) (liftM (OracleSpec.query q) >>= oa) st_cli ds_cli hBad
      rw [hBadOne]
      exact ⟨(measure_le_one _ _).trans le_add_self, (measure_le_one _ _).trans le_add_self⟩
    · have hGood : cliClause2BadKemBool S P st_cli ds_cli = false := Bool.eq_false_iff.mpr hBad
      have hRemPost : ∀ y ∈ support (((impl_ad q).run σ_ad).run σ_e2e), CliE2ERemoteIdInv y.2 :=
        cliComposedAdapterImplWith_preserves_remoteIdInv P
          (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K qep decT encT q σ_ad σ_e2e hRem
      rw [simulateQ_query_bind_run₂_cli, simulateQ_query_bind_run₂_cli, bind_assoc, bind_assoc,
          bind_assoc]
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hb_start
      have hb_inst' : ∀ k < qStart,
          (¬ (bhIsInstQueryWithSpqr k q = true) ∨ 0 < qs_rem k) ∧
          ∀ u, OracleComp.IsQueryBoundP (oa u) (fun q' => bhIsInstQueryWithSpqr k q')
            (if bhIsInstQueryWithSpqr k q = true then qs_rem k - 1 else qs_rem k) := by
        intro k hk
        simpa only [OracleComp.isQueryBoundP_query_bind_iff] using hb_inst k hk
      rcases q with ((uq | kq) | ctlq) | ⟨i, sq⟩
      ·
        have hStep := cliUnifStepBridgeProp_holds S ℓ X W qep decT encT hRel uq
        refine evalDist_bind_coupled_both_le hStep hRemPost _ _ _ (fun x y hr hRel' hRem' => ?_)
        rw [← hr]
        refine ih x.1.1 hn ?_ ?_ hRel' hRem'
        · simpa using hb_start.2 x.1.1
        · intro k hk
          have hcond : @bhIsInstQueryWithSpqr S ℓ (BitVec 512) k (.inl (.inl (.inl uq))) = false := rfl
          simpa only [hcond, Bool.false_eq_true, ↓reduceIte] using (hb_inst' k hk).2 x.1.1
      ·
        have hStep := hKeyInd hRel hRem hGood kq
        refine evalDist_bind_coupled_both_le hStep hRemPost _ _ _ (fun x y hr hRel' hRem' => ?_)
        rw [← hr]
        refine ih x.1.1 hn ?_ ?_ hRel' hRem'
        · simpa using hb_start.2 x.1.1
        · intro k hk
          have hcond : @bhIsInstQueryWithSpqr S ℓ (BitVec 512) k (.inl (.inl (.inr kq))) = false := rfl
          simpa only [hcond, Bool.false_eq_true, ↓reduceIte] using (hb_inst' k hk).2 x.1.1
      ·
        cases ctlq with
        | startDR sid =>
          have hpos : 0 < qStart_rem := by
            rcases hb_start.1 with hnot | hpos
            · exfalso; exact hnot rfl
            · exact hpos
          have hRelSucc : CliAdapterDrvRel S ℓ X W b (n + 1) qs_rem st_cli ds_cli σ_ad σ_e2e :=
            hRel.mono_qStart (Nat.le_succ n)
          have hLenLt : ds_cli.bhInsts.length < n + 1 :=
            Nat.lt_succ_of_le hRel.insts_len_le
          have hStep := hStart hRelSucc hRem hGood hLenLt sid
          refine evalDist_bind_coupled_both_le hStep hRemPost _ _ _ (fun x y hr hRel' hRem' => ?_)
          rw [← hr]
          refine ih x.1.1 (n := n + 1) (qStart_rem := qStart_rem - 1) (by omega) ?_ ?_
            hRel' hRem'
          · simpa using hb_start.2 x.1.1
          · intro k hk
            have hcond : @bhIsInstQueryWithSpqr S ℓ (BitVec 512) k (.inl (.inr (.startDR sid))) = false := rfl
            simpa only [hcond, Bool.false_eq_true, ↓reduceIte] using (hb_inst' k hk).2 x.1.1
      ·
        have hq_pos : i < ds_cli.bhInsts.length → 0 < qs_rem i := by
          intro hi
          have hi_lt : i < qStart := by
            have := hRel.insts_len_le
            omega
          rcases (hb_inst' i hi_lt).1 with hnot | hpos
          · exfalso
            apply hnot
            simp [bhIsInstQueryWithSpqr]
          · exact hpos
        have hStep := hSm hRel hRem hGood i sq hq_pos
        refine evalDist_bind_coupled_both_le hStep hRemPost _ _ _ (fun x y hr hRel' hRem' => ?_)
        rw [← hr]
        refine ih x.1.1 hn ?_ ?_ hRel' hRem'
        · simpa using hb_start.2 x.1.1
        · intro k hk
          have h := (hb_inst' k hk).2 x.1.1
          have hcond :
              (if @bhIsInstQueryWithSpqr S ℓ (BitVec 512) k (.inr ⟨i, sq⟩) = true then
                 qs_rem k - 1
               else qs_rem k) =
              Function.update qs_rem i (qs_rem i - 1) k := by
            by_cases hki : k = i
            · subst hki; simp [bhIsInstQueryWithSpqr, Function.update]
            · have hik : (i == k) = false := beq_false_of_ne (Ne.symm hki)
              simp [bhIsInstQueryWithSpqr, Function.update, hki, hik]
          rwa [hcond] at h

theorem evalDist_cliPostObs_eq_of_rel {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {n : ℕ} {qs_rem : ℕ → ℕ}
    {x : (Bool × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S}
    {y : (Bool × CliAdapterState S) × BHE2EDrvState S ℓ}
    (hr : x.1.1 = y.1.1)
    (hRel : CliAdapterDrvRel S ℓ X W b n qs_rem x.2 x.1.2 y.1.2 y.2) :
    𝒟[if !allTestedSessionsFresh (modelPrims X W) x.2 then ($ᵗ Bool : ProbComp Bool)
      else pure (x.1.1 == b || driverSomeInstanceWon x.1.2 b)] =
    𝒟[if !allTestedSessionsFresh (modelPrims X W) y.2.st then ($ᵗ Bool : ProbComp Bool)
      else pure (y.1.1 == b || bhE2EDrvWon y.2 b)] := by
  rw [bhComposedClean_eq_of_cliKeyIndStateRel hRel.st_rel, hr,
      bhDrvWon_eq_bhE2EDrvWon_of_cliRel hRel]

/-! ## Advantage bound -/

theorem cliPqExp_evalDist_both_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (hKeyInd : CliKeyIndStepBridgeProp S ℓ X W qep decT encT)
    (hStart : CliStartStepBridgeProp S ℓ run X W qep decT encT)
    (hSm : CliSmStepBridgeProp S ℓ run X W qep decT encT)
    (b_bud : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (A : CliGameAdversary S ℓ (BitVec 512))
    (hA : CliGameAdversaryPerInstanceBounded A b_bud qStart qs) :
    let P := modelPrims X W
    let B_A := (L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval (fun _ => cliGameAdversaryReassoc A) ()
    𝒟[cliPqExpProj S run X W ℓ qep decT encT A] {true} ≤
      𝒟[cliE2EExpWithKi true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K ℓ qep
          decT encT B_A] {true} +
        𝒟[cliRunBadKemExp S P run W ℓ qep decT encT A] {true} ∧
    𝒟[cliE2EExpWithKi true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K ℓ qep
        decT encT B_A] {true} ≤
      𝒟[cliPqExpProj S run X W ℓ qep decT encT A] {true} +
        𝒟[cliRunBadKemExp S P run W ℓ qep decT encT A] {true} := by
  intro P B_A
  have hb_start0 : OracleComp.IsQueryBoundP A.run (fun q => q matches .inl (.inr _)) qStart :=
    (isQueryBoundP_congr_pred_cli (fun q => by rcases q with ((_ | _) | _) | _ <;> exact Iff.rfl)
      A.run).mp hA.2.1
  have hBit : ∀ b_chal : Bool,
      let c_cli :=
        (((simulateQ (cliDrvImpl S ℓ P run W qep decT encT bhNoExtWithSpqr
            (fun _ _ _ _ _ => some b_chal)) A.run).run {}).run
          (SignalPqxdh.KeyIndState.empty S true))
      let c_e2e :=
        (simulateQ (cliE2EDrvImplWith P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K qep
            decT encT) B_A).run { b := b_chal, st := SignalPqxdh.KeyIndState.empty S true }
      let F_cli : ((Bool × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S) → ProbComp Bool :=
        fun x => if !allTestedSessionsFresh P x.2 then $ᵗ Bool
                 else pure (x.1.1 == b_chal || driverSomeInstanceWon x.1.2 b_chal)
      let F_e2e : (Bool × BHE2EDrvState S ℓ) → ProbComp Bool :=
        fun z => if !allTestedSessionsFresh P z.2.st then $ᵗ Bool
                 else pure (z.1 == b_chal || bhE2EDrvWon z.2 b_chal)
      let F_bad : ((Bool × ModelDriverState S ℓ) × SignalPqxdh.KeyIndState S) → ProbComp Bool :=
        fun x => pure (cliClause2BadKemBool S P x.2 x.1.2)
      𝒟[c_cli >>= F_cli] {true} ≤ 𝒟[c_e2e >>= F_e2e] {true} + 𝒟[c_cli >>= F_bad] {true} ∧
      𝒟[c_e2e >>= F_e2e] {true} ≤ 𝒟[c_cli >>= F_cli] {true} + 𝒟[c_cli >>= F_bad] {true} := by
    intro b_chal c_cli c_e2e F_cli F_e2e F_bad
    have hUnf : c_e2e >>= F_e2e =
        ((((simulateQ (cliComposedAdapterImplWith P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
              W.C W.Q.K qep decT encT) A.run).run (cliAdapterInitState S)).run
            { b := b_chal, st := SignalPqxdh.KeyIndState.empty S true }) >>=
          fun y => if !allTestedSessionsFresh P y.2.st then $ᵗ Bool
                   else pure (y.1.1 == b_chal || bhE2EDrvWon y.2 b_chal)) := by
      dsimp only [c_e2e, B_A, F_e2e]
      rw [simulateQ_cliE2EDrvImplWith_L_bh_run P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P)
        W.C W.Q.K qep decT encT A { b := b_chal, st := SignalPqxdh.KeyIndState.empty S true }]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    rw [hUnf]
    exact simulateQ_cliDrvImpl_adapter_coupling_both_le run X W qep decT encT hKeyInd hStart hSm
      b_chal qStart F_cli _
      (fun x y hr hRel => evalDist_cliPostObs_eq_of_rel hr hRel)
      A.run (n := 0) (qStart_rem := qStart) (qs_rem := qs)
      (Nat.zero_add qStart).le hb_start0 hA.2.2
      (cliAdapterDrvRel_init S ℓ X W b_chal 0 qs)
      (cliE2ERemoteIdInv_init S ℓ b_chal true)
  rw [cliPqExp_eq_runCliDriver]
  unfold cliE2EExpWithKi cliRunBadKemExp runCliDriver
  dsimp only [P]
  rw [evalDist_bind_true_eq_probExpect_cli ($ᵗ Bool),
      evalDist_bind_true_eq_probExpect_cli ($ᵗ Bool),
      evalDist_bind_true_eq_probExpect_cli ($ᵗ Bool)]
  exact ⟨by
      rw [← probExpect_add_cli]
      exact SignalPqxdh.Security.probExpect_mono_of_support ($ᵗ Bool) _ _ (fun b_chal _ =>
        (hBit b_chal).1),
    by
      rw [← probExpect_add_cli]
      exact SignalPqxdh.Security.probExpect_mono_of_support ($ᵗ Bool) _ _ (fun b_chal _ =>
        (hBit b_chal).2)⟩

theorem cliPqExp_boolDist_le_badKem {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (hKeyInd : CliKeyIndStepBridgeProp S ℓ X W qep decT encT)
    (hStart : CliStartStepBridgeProp S ℓ run X W qep decT encT)
    (hSm : CliSmStepBridgeProp S ℓ run X W qep decT encT)
    (b_bud : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (A : CliGameAdversary S ℓ (BitVec 512))
    (hA : CliGameAdversaryPerInstanceBounded A b_bud qStart qs) :
    let P := modelPrims X W
    let B_A := (L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval (fun _ => cliGameAdversaryReassoc A) ()
    𝒟[cliPqExpProj S run X W ℓ qep decT encT A].boolDist
      𝒟[cliE2EExpWithKi true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K ℓ qep
          decT encT B_A] ≤
      𝒟[cliRunBadKemExp S P run W ℓ qep decT encT A] {true} := by
  intro P B_A
  obtain ⟨h1, h2⟩ := cliPqExp_evalDist_both_le run X W qep decT encT hKeyInd hStart hSm
    b_bud qStart qs A hA
  exact boolDist_le_of_evalDist_true_both_le _ _ _ h1 h2

/-- Pointwise `CliPqxdhAdvantageProj` bound from the per-oracle step-bridge propositions and
`KemDeltaCorrect (modelPrims X W) δ_kem`. -/
theorem cliPqAdvantage_le_of_step_bridges {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (δ_kem : ℝ≥0∞) (hKemBin : SignalPqxdh.KemDeltaCorrect (modelPrims X W) δ_kem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (qep : ℕ)
    (hKeyInd : CliKeyIndStepBridgeProp S ℓ X W qep decT encT)
    (hStart : CliStartStepBridgeProp S ℓ run X W qep decT encT)
    (hSm : CliSmStepBridgeProp S ℓ run X W qep decT encT)
    (b_bud : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (A : CliGameAdversary S ℓ (BitVec 512))
    (hA : CliGameAdversaryPerInstanceBounded A b_bud qStart qs) :
    let P := modelPrims X W
    let B_A := (L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval (fun _ => cliGameAdversaryReassoc A) ()
    CliPqxdhAdvantageProj S run X W ℓ qep decT encT A ≤
      𝒟[cliE2EExpWithKi true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K ℓ qep
          decT encT B_A].boolBias +
        SignalPqxdh.Security.kemDecapsFailureTerm S δ_kem := by
  intro P B_A
  unfold CliPqxdhAdvantageProj
  have hDist := cliPqExp_boolDist_le_badKem run X W qep decT encT hKeyInd hStart hSm
    b_bud qStart qs A hA
  have hKem := two_mul_cliBadKemProb_modelPrims_le_kemCorrTerm S ℓ qep X run W decT encT
    δ_kem hKemBin A
  calc 𝒟[cliPqExpProj S run X W ℓ qep decT encT A].boolBias
      ≤ 𝒟[cliE2EExpWithKi true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K ℓ qep
            decT encT B_A].boolBias +
          2 * 𝒟[cliPqExpProj S run X W ℓ qep decT encT A].boolDist
            𝒟[cliE2EExpWithKi true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K ℓ qep
                decT encT B_A] :=
        SignalPqxdh.Security.boolBias_le_add_two_mul_boolDist _ _
    _ ≤ 𝒟[cliE2EExpWithKi true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K ℓ qep
            decT encT B_A].boolBias +
          2 * 𝒟[cliRunBadKemExp S P run W ℓ qep decT encT A] {true} :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hDist zero_le)
    _ ≤ 𝒟[cliE2EExpWithKi true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K ℓ qep
            decT encT B_A].boolBias +
          SignalPqxdh.Security.kemDecapsFailureTerm S δ_kem :=
        add_le_add le_rfl hKem

local notation "bhE2EExpWithKi" => cliE2EExpWithKi

/-- Bounds `CliPqxdhAdvantage` by the bias of
`bhE2EExpWithKi true` at `SignalPqxdh.pqxdhKeyIndImpl1KeyReal` on `L_bh`'s evaluation `B_A`, plus
`SignalPqxdh.Security.kemDecapsFailureTerm S δ_kem`. -/
def CliPqAdapterBoundProp' {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ) : Prop :=
  ∀ (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (_hCli : CliSpecPqxdh run X W) (_hK_tot : MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W.Q.K)
    (_hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W))
    (δ_kem : ℝ≥0∞) (_hKemBin : SignalPqxdh.KemDeltaCorrect (modelPrims X W) δ_kem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (_hℓ : ℓ < 10 ^ 6)
    (_hDh : Dh.Commutes) (_hX : X25519RealizesDh W.C Dh encPt encT)
    (_hdec : ∀ T, decT (encT T) = some T) (_hinj : Function.Injective encT)
    (_hdum : ∀ T, encT T ≠ dummyKey) (_hz : ∀ x, Dh.dh x 0 = 0)
    (_hD : ∀ k x, W.C.D k (W.C.E k x) = x)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (_hq32 : ∀ k < qStart, 2 * (qs k + 1) + 25002 < 2 ^ 32)
    (A : CliGameAdversary S ℓ (BitVec 512))
    (_hA : CliGameAdversaryPerInstanceBounded A b qStart qs),
    let P := modelPrims X W
    let B_A := (L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval (fun _ => cliGameAdversaryReassoc A) ()
    CliPqxdhAdvantage S run X W ℓ qep decT encT A ≤
      𝒟[bhE2EExpWithKi true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) W.C W.Q.K ℓ qep
          decT encT B_A].boolBias +
        SignalPqxdh.Security.kemDecapsFailureTerm S δ_kem

/-- Derives `CliPqAdapterBoundProp S ℓ` from the per-oracle step-bridge propositions. -/
theorem cliPqAdapterBoundProp_of_step_bridges
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (hKeyInd : ∀ (X : UnreachedPqxdhPrimitives) (W : PEParams)
      (_hK_tot : MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W.Q.K)
      (_hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W))
      (qep : ℕ) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
      CliKeyIndStepBridgeProp S ℓ X W qep decT encT)
    (hStart : ∀ (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
      (_hCli : CliSpecPqxdh run X W) (_hK_tot : MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W.Q.K)
      (_hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W))
      (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
      (decT : PublicKey → Option Pt) (qep : ℕ) (_hℓ : ℓ < 10 ^ 6)
      (_hDh : Dh.Commutes) (_hX : X25519RealizesDh W.C Dh encPt encT)
      (_hdec : ∀ T, decT (encT T) = some T) (_hinj : Function.Injective encT)
      (_hdum : ∀ T, encT T ≠ dummyKey) (_hz : ∀ x, Dh.dh x 0 = 0)
      (_hD : ∀ k x, W.C.D k (W.C.E k x) = x),
      CliStartStepBridgeProp S ℓ run X W qep decT encT)
    (hSm : ∀ (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams)
      (_hCli : CliSpecPqxdh run X W) (_hK_tot : MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W.Q.K)
      (_hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X W))
      (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
      (decT : PublicKey → Option Pt) (qep : ℕ) (_hℓ : ℓ < 10 ^ 6)
      (_hDh : Dh.Commutes) (_hX : X25519RealizesDh W.C Dh encPt encT)
      (_hdec : ∀ T, decT (encT T) = some T) (_hinj : Function.Injective encT)
      (_hdum : ∀ T, encT T ≠ dummyKey) (_hz : ∀ x, Dh.dh x 0 = 0)
      (_hD : ∀ k x, W.C.D k (W.C.E k x) = x),
      CliSmStepBridgeProp S ℓ run X W qep decT encT) :
    CliPqAdapterBoundProp' (Pt := Pt) S ℓ := by
  intro run X W hCli hK_tot hP δ_kem hKemBin Dh encPt encT decT qep hℓ
    hDh hX hdec hinj hdum hz hD b qStart qs _hq32 A hA
  dsimp only
  rw [cliPqxdhAdvantage_eq_proj S run X W ℓ qep decT encT A hCli hℓ]
  exact cliPqAdvantage_le_of_step_bridges run X W δ_kem hKemBin decT encT qep
    (hKeyInd X W hK_tot hP qep decT encT)
    (hStart run X W hCli hK_tot hP Dh encPt encT decT qep hℓ hDh hX hdec hinj hdum hz hD)
    (hSm run X W hCli hK_tot hP Dh encPt encT decT qep hℓ hDh hX hdec hinj hdum hz hD)
    b qStart qs A hA

end CryptoVerification.E2E
