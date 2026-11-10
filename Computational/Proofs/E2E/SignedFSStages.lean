/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SignedAdv
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalShortDefs
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.SaltHop
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.FSAEADBound
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.WireHop.Helpers
import Computational.Proofs.E2E.ComposedPrefixHelpers

/-!
# Signed FS-AEAD stages 2–4 on mixtures

Bounds the `multiOtBranch` mixture distance from `SignedThm5Gen.theorem5_mix_multi` by single
averaged salt-PRF and wire OT-CCA reductions per slot plus the integrated MAC forgery slack.
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E.Signed.FSMix

open CryptoGames CryptoGames.LibsignalSM.Proofs
open CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst CryptoGames.LibsignalSession
open CryptoGames.LibsignalSM.Proofs.SaltHop CryptoGames.LibsignalSM.Proofs.WireHop
open CryptoGames.FSAEAD.Thm5

theorem evalDist_mix_congr' {α : Type} (oa : ProbComp α) {f g : α → ProbComp Bool}
    (h : ∀ o, 𝒟[f o] = 𝒟[g o]) : 𝒟[oa >>= f] = 𝒟[oa >>= g] :=
  evalDist_bind_congr oa f g h

/-! ## Wire OT-CCA averaging -/

section Wire

variable {K AD H M M' C T : Type} [SampleableType K] [SampleableType C] [SampleableType T]
  [DecidableEq AD] [DecidableEq T]

def wBranch (ae : WireAEAD K AD H M M' C T) (b : Bool) (A : WireAEAD.WireAdversary AD H M M' T) :
    ProbComp Bool := do
  let key ← $ᵗ K
  (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (WireAEAD.WireState K AD T) ProbComp) + (ae.wireEncrypt + ae.wireDecrypt)) A).run'
    { key, b }

theorem wireOtccaAdvantage_eq_boolDist_wBranch (ae : WireAEAD K AD H M M' C T)
    (A : WireAEAD.WireAdversary AD H M M' T) :
    ae.wireOtccaAdvantage A = 𝒟[wBranch ae true A].boolDist 𝒟[wBranch ae false A] := by
  unfold WireAEAD.wireOtccaAdvantage WireAEAD.wireOtccaGame
  have hcoin : ∀ x : Bool, 𝒟[($ᵗ Bool : ProbComp Bool)] {x} = 1 / 2 := fun _ => by simp
  rw [← evalDist_boolBias_bind_coin ($ᵗ Bool) (wBranch ae true A) (wBranch ae false A)
    (hcoin true) (hcoin false)]
  congr 2
  refine bind_congr fun b => ?_
  cases b <;> simp [wBranch]

/-- Averaged wire OT-CCA adversary that samples `o ← oa` and runs `A o`. -/
def wireAvg {α : Type} (oa : ProbComp α) (A : α → WireAEAD.WireAdversary AD H M M' T) :
    WireAEAD.WireAdversary AD H M M' T :=
  bind (m := OracleComp (unifSpec + WireAEAD.wireSpec AD H M M' T))
    (liftM oa : OracleComp (unifSpec + WireAEAD.wireSpec AD H M M' T) α) A

omit [SampleableType K] in
theorem simulateQ_wImpl_liftM_run {α : Type} (ae : WireAEAD K AD H M M' C T)
    (oa : ProbComp α) (st : WireAEAD.WireState K AD T) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (WireAEAD.WireState K AD T) ProbComp) + (ae.wireEncrypt + ae.wireDecrypt))
      (liftM oa : OracleComp (unifSpec + WireAEAD.wireSpec AD H M M' T) α)).run st =
      oa >>= fun a => pure (a, st) := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    change ((liftM (OracleSpec.query (spec := unifSpec) t) : ProbComp _) >>= fun u =>
        (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (WireAEAD.WireState K AD T) ProbComp) + (ae.wireEncrypt + ae.wireDecrypt))
          (liftM (k u) : OracleComp (unifSpec + WireAEAD.wireSpec AD H M M' T) α)).run st) = _
    simp only [ih, bind_assoc]

theorem wBranch_avg {α : Type} (ae : WireAEAD K AD H M M' C T) (b : Bool) (oa : ProbComp α)
    (A : α → WireAEAD.WireAdversary AD H M M' T) :
    𝒟[wBranch ae b (wireAvg oa A)] = 𝒟[oa >>= fun o => wBranch ae b (A o)] := by
  unfold wBranch wireAvg
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, simulateQ_wImpl_liftM_run,
    bind_assoc, pure_bind, map_bind]
  exact OracleComp.evalDist_bind_bind_swap _ _ _

end Wire

/-! ## Salt stage -/

section Salt

open HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD

variable {Pt : Type} [DecidableEq Pt]

def saltNu1 (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (B : OTCCAAdversary (SaltHop.AD Pt) (Plain ℓ) SaltHop.Ct) :
    ProbComp Bool := do
  let key ← $ᵗ (BitVec 256)
  Prod.fst <$> (simulateQ (aImpl C codec ℓ encT idOf) B).run
    { key := key, b := false, chal := none }

def coinG (μ ν : ProbComp Bool) : ProbComp Bool :=
  ($ᵗ Bool : ProbComp Bool) >>= fun b => (if b then μ else ν) >>= fun z => pure (b == z)

theorem saltBranchF_eq (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (B : OTCCAAdversary (SaltHop.AD Pt) (Plain ℓ) SaltHop.Ct) :
    𝒟[MACScheme.branch (lSaltPRF32 C.F) false (lSaltRed C codec ℓ encT idOf B)] =
      𝒟[coinG (saltRun C codec ℓ encT idOf true B) (saltNu1 C codec ℓ encT idOf B)] := by
  rw [← evalDist_otccaGameWith_eq_branch_false]
  unfold otccaGameAdIdeal coinG
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, saltNu1, StateT.run'_eq, map_eq_bind_pure_comp,
      bind_assoc]
    rfl
  · simp only [↓reduceIte, StateT.run'_eq, Bool.true_beq, bind_pure]
    exact (evalDist_bind_congr ($ᵗ (BitVec 256)) _ _ fun key =>
      evalDist_aImpl_true_eq_saltRun_true C codec ℓ encT idOf key B).trans
      (OracleComp.evalDist_bind_const _ _)

theorem saltBranchT_eq (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (B : OTCCAAdversary (SaltHop.AD Pt) (Plain ℓ) SaltHop.Ct) :
    𝒟[MACScheme.branch (lSaltPRF32 C.F) true (lSaltRed C codec ℓ encT idOf B)] =
      𝒟[coinG (saltRun C codec ℓ encT idOf true B) (saltRun C codec ℓ encT idOf false B)] := by
  let μ := saltRun C codec ℓ encT idOf true B
  let ν₂ := saltRun C codec ℓ encT idOf false B
  unfold MACScheme.branch coinG
  have hkey : ∀ key : BitVec 256,
      (simulateQ (prfImpl C.F) (lSaltRed C codec ℓ encT idOf B)).run'
          { key, b := true } =
        (($ᵗ Bool : ProbComp Bool) >>= fun b =>
          (if b then μ else ν₂) >>= fun z => pure (b == z)) := by
    intro key
    change (simulateQ (prfImpl C.F) (do
        let b ← $ᵗ Bool
        let b' ← (simulateQ (lSaltRedImpl C codec ℓ encT idOf b) B).run' none
        return b == b')).run' { key, b := true } = _
    simp only [StateT.run'_eq, simulateQ_bind, simulateQ_map, StateT.run_bind, StateT.run_map,
      map_bind, simulateQ_prfImpl_liftM, StateT.run_monadLift, bind_assoc,
      pure_bind, simulateQ_pure, StateT.run_pure]
    refine bind_congr fun b => ?_
    have hsim := congrArg (fun m : ProbComp Bool => m >>= fun b' => pure (b == b'))
      (lSaltRed_simulateQ_eq C codec ℓ encT idOf b key B {})
    cases b <;>
      simpa [saltRun, saltFull, map_eq_bind_pure_comp, bind_assoc, μ, ν₂] using hsim
  change 𝒟[do let key ← $ᵗ (BitVec 256)
              (simulateQ (prfImpl C.F) (lSaltRed C codec ℓ encT idOf B)).run'
                { key, b := true }] = _
  simp only [hkey, OracleComp.evalDist_bind_const]
  rfl

theorem coinG_mix {α : Type} (oa : ProbComp α) (μ ν : α → ProbComp Bool) :
    𝒟[oa >>= fun o => coinG (μ o) (ν o)] =
      𝒟[coinG (oa >>= μ) (oa >>= ν)] := by
  unfold coinG
  rw [OracleComp.evalDist_bind_bind_swap]
  refine evalDist_bind_congr _ _ _ fun b => ?_
  cases b <;> simp

theorem salt_step_mix {α : Type} (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (oa : ProbComp α) (idOf : α → Party → IdentityKey)
    (B : α → OTCCAAdversary (SaltHop.AD Pt) (Plain ℓ) SaltHop.Ct) :
    𝒟[oa >>= fun o => saltNu1 C codec ℓ encT (idOf o) (B o)].boolDist
      𝒟[oa >>= fun o => saltRun C codec ℓ encT (idOf o) false (B o)] =
      2 * (lSaltPRF32 C.F).prfAdvantage
        (prfAvg oa fun o => lSaltRed C codec ℓ encT (idOf o) (B o)) := by
  rw [MACScheme.prfAdvantage_eq_boolDist, prfBranch_avg, prfBranch_avg,
    evalDist_mix_congr' oa (fun o => saltBranchT_eq C codec ℓ encT (idOf o) (B o)),
    evalDist_mix_congr' oa (fun o => saltBranchF_eq C codec ℓ encT (idOf o) (B o)),
    coinG_mix, coinG_mix, Measure.boolDist_comm]
  exact boolDist_bind_coin_false _ _ _

end Salt

/-! ## Stages 2–4 on mixtures -/

section Stages

open HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD
open CryptoGames.LibsignalSM.Proofs.ProstFSAEADBound

variable {Pt : Type} [DecidableEq Pt] {α : Type} (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
  (encT : Pt → PublicKey) (oa : ProbComp α) (idOf : α → Party → IdentityKey)
  (B : α → OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32)

theorem salt_mix (N : ℕ) (hoff : ∀ o, (B o).IsQueryBoundP (fun t => multiOffRange N t = true) 0) :
    𝒟[oa >>= fun o => multiOtBranch (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
        false N (B o)].boolDist
      𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (slotLift (slotSaltImpl C codec ℓ encT (idOf o)
        false)) (B o)).run (fun _ => {})] ≤
      ∑ k ∈ Finset.range N, 2 * (lSaltPRF32 C.F).prfAdvantage
        (prfAvg oa fun o => lSaltRed C codec ℓ encT (idOf o)
          (slotSaltRed C codec ℓ encT (idOf o) N k (B o))) := by
  rw [evalDist_mix_congr' oa (fun o => congrArg evalDist
      (saltHyb_zero C codec ℓ encT (idOf o) N (B o)).symm),
    evalDist_mix_congr' oa (fun o =>
      (evalDist_saltHyb_self C codec ℓ encT (idOf o) N (B o) (hoff o)).symm)]
  refine (Measure.boolDist_le_sum_range
    (fun k => 𝒟[oa >>= fun o => saltHyb C codec ℓ encT (idOf o) N k (B o)]) N).trans ?_
  refine le_of_eq (Finset.sum_congr rfl fun k hk => ?_)
  have hk' : k < N := Finset.mem_range.mp hk
  rw [evalDist_mix_congr' oa (fun o => evalDist_saltHyb_step_left C codec ℓ encT (idOf o) hk' (B
    o)),
    evalDist_mix_congr' oa (fun o => congrArg evalDist
      (saltHyb_step_right C codec ℓ encT (idOf o) N k (B o)))]
  exact salt_step_mix C codec ℓ encT oa idOf (fun o => slotSaltRed C codec ℓ encT (idOf o) N k (B
    o))

theorem mac_apply_le (hfit : SignalEncodeFits32 codec) (hℓ : ℓ + 16 < 2 ^ 31 + 16)
    (idO : Party → IdentityKey)
    (B₀ : OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32)
    {qd : ℕ} (hB : MakesAtMostDecQueries B₀ qd)
    (hshort : AEADScheme.OTEncADsOk (fun a : ℕ × (Header Pt × LibsignalMsgPublicPart) => a.2.2.shortB) B₀)
    (hdec : GuardedOTDecShort B₀) (x : Bool) :
    𝒟[Prod.fst <$> (simulateQ (slotLift (slotSaltImpl C codec ℓ encT idO false)) B₀).run
        (fun _ => {})] {x} ≤
      𝒟[Prod.fst <$> (simulateQ (slotLift (slotSaltImplNF C codec ℓ encT idO false)) B₀).run
        (fun _ => {})] {x} + (qd : ℝ≥0∞) * macForgeryProb C.F := by
  rw [← evalDist_multiSaltFlagNF_out_eq_slotLift_slotSaltImplNF_aux C codec ℓ encT idO B₀
    (fun _ => {}) false MSaltTableInv.init]
  simp only [map_eq_bind_pure_comp]
  exact (slotLift_slotSaltImpl_false_le_multiSaltFlagNF C codec ℓ encT idO B₀ pure x
    (fun _ => {})).trans
    (add_le_add le_rfl
      (multiSaltFlagNF_flag_le_aux C codec hfit ℓ hℓ encT idO hdec qd (fun _ => {})
        MSaltTableInv.init hshort hB))

theorem mac_mix (hfit : SignalEncodeFits32 codec) (hℓ : ℓ + 16 < 2 ^ 31 + 16)
    {qd : ℕ} (hB : ∀ o, MakesAtMostDecQueries (B o) qd)
    (hshort : ∀ o, AEADScheme.OTEncADsOk
      (fun a : ℕ × (Header Pt × LibsignalMsgPublicPart) => a.2.2.shortB) (B o))
    (hdec : ∀ o, GuardedOTDecShort (B o)) :
    𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (slotLift (slotSaltImpl C codec ℓ encT (idOf o)
        false)) (B o)).run (fun _ => {})].boolDist
      𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (slotLift (slotSaltImplNF C codec ℓ encT (idOf o)
        false)) (B o)).run (fun _ => {})] ≤
      (qd : ℝ≥0∞) * macForgeryProb C.F := by
  refine Measure.boolDist_le_of_apply_le _ _ fun x => ?_
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  rw [evalDist_bind_apply_lintegral, evalDist_bind_apply_lintegral]
  calc _ ≤ ∫⁻ o, (𝒟[Prod.fst <$> (simulateQ (slotLift (slotSaltImplNF C codec ℓ encT (idOf o)
          false)) (B o)).run (fun _ => {})] {x} + (qd : ℝ≥0∞) * macForgeryProb C.F) ∂𝒟[oa] :=
        lintegral_mono fun o =>
          mac_apply_le C codec ℓ encT hfit hℓ (idOf o) (B o) (hB o) (hshort o) (hdec o) x
    _ = _ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

theorem wireBranch_eq_wBranch (idO : Party → IdentityKey) (b : Bool) (j : ℕ)
    (B₀ : OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32)
    :
    wireBranch C codec ℓ encT idO b j B₀ = wBranch (lWire C codec ℓ) b (lWireRed C codec ℓ encT idO
      j B₀) :=
  rfl

theorem wire_mix (hrt : SignalRoundTripShort codec) (hℓ : ℓ + 16 < rustLenBound)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) {N : ℕ} (hN : N ≤ 2 ^ 32)
    (hoff : ∀ o, (B o).IsQueryBoundP (fun t => multiOffRange N t = true) 0)
    (hcls : ∀ o, AEADScheme.OTAllQueriesInOneADClass lCls (B o))
    (hshort : ∀ o, AEADScheme.OTEncADsOk
      (fun a : ℕ × (Header Pt × LibsignalMsgPublicPart) => a.2.2.shortB) (B o)) :
    𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (slotLift (slotSaltImplNF C codec ℓ encT (idOf o)
        false)) (B o)).run (fun _ => {})].boolDist
      𝒟[oa >>= fun o => multiOtBranch (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
        true N (B o)] ≤
      ∑ k ∈ Finset.range N, (lWire C codec ℓ).wireOtccaAdvantage
        (wireAvg oa fun o => lWireRed C codec ℓ encT (idOf o) 0
          (slotWireRed C codec ℓ encT (idOf o) k (B o))) := by
  rw [evalDist_mix_congr' oa (fun o => congrArg evalDist
      (wireHyb_zero C codec ℓ encT (idOf o) (B o)).symm),
    evalDist_mix_congr' oa (fun o =>
      (evalDist_wireHyb_self C codec ℓ encT (idOf o) N (B o) (hoff o)).symm)]
  refine (Measure.boolDist_le_sum_range
    (fun k => 𝒟[oa >>= fun o => wireHyb C codec ℓ encT (idOf o) k (B o)]) N).trans ?_
  refine le_of_eq (Finset.sum_congr rfl fun k hk => ?_)
  have hk32 : k < 2 ^ 32 := lt_of_lt_of_le (Finset.mem_range.mp hk) hN
  have hL : ∀ o, 𝒟[wireHyb C codec ℓ encT (idOf o) k (B o)] =
      𝒟[wBranch (lWire C codec ℓ) false (lWireRed C codec ℓ encT (idOf o) 0
        (slotWireRed C codec ℓ encT (idOf o) k (B o)))] := fun o => by
    rw [wireHyb_step_left C codec ℓ encT (idOf o) k (B o), ← wireBranch_eq_wBranch,
      ProstWireHop.Helpers.evalDist_wireBranch_false C codec ℓ hℓ encT (idOf o)
        (slotWireRed C codec ℓ encT (idOf o) k (B o)) hinj hdum hrt
        (slotWireRed_adClassConst C codec ℓ encT (idOf o) k (B o) (hcls o))
        (slotWireRed_badIdx C codec ℓ encT (idOf o) hk32 (B o))
        (slotWireRed_encADsOk C codec ℓ encT (idOf o) k (B o) (hshort o))]
  have hR : ∀ o, 𝒟[wireHyb C codec ℓ encT (idOf o) (k + 1) (B o)] =
      𝒟[wBranch (lWire C codec ℓ) true (lWireRed C codec ℓ encT (idOf o) 0
        (slotWireRed C codec ℓ encT (idOf o) k (B o)))] := fun o => by
    rw [wireHyb_step_right C codec ℓ encT (idOf o) k (B o), ← wireBranch_eq_wBranch,
      WireHop.evalDist_wireBranch_true_zero]
  rw [evalDist_mix_congr' oa hL, evalDist_mix_congr' oa hR, wireOtccaAdvantage_eq_boolDist_wBranch,
    wBranch_avg, wBranch_avg, Measure.boolDist_comm]

/-- Combined salt, MAC, and wire bound on `multiOtBranch` mixtures. -/
theorem multiOtBranch_mix_le (hrt : SignalRoundTripShort codec) (hfit : SignalEncodeFits32 codec)
    (hℓ : ℓ + 16 < 2 ^ 31 + 16)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) {N qd : ℕ} (hN : N ≤ 2 ^ 32)
    (hoff : ∀ o, (B o).IsQueryBoundP (fun t => multiOffRange N t = true) 0)
    (hqd : ∀ o, MakesAtMostDecQueries (B o) qd)
    (hcls : ∀ o, AEADScheme.OTAllQueriesInOneADClass lCls (B o))
    (hshort : ∀ o, AEADScheme.OTEncADsOk
      (fun a : ℕ × (Header Pt × LibsignalMsgPublicPart) => a.2.2.shortB) (B o))
    (hdec : ∀ o, GuardedOTDecShort (B o)) :
    𝒟[oa >>= fun o => multiOtBranch (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
        true N (B o)].boolDist
      𝒟[oa >>= fun o => multiOtBranch (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
        false N (B o)] ≤
      (∑ k ∈ Finset.range N,
        (2 * (lSaltPRF32 C.F).prfAdvantage
            (prfAvg oa fun o => lSaltRed C codec ℓ encT (idOf o)
              (slotSaltRed C codec ℓ encT (idOf o) N k (B o))) +
          (lWire C codec ℓ).wireOtccaAdvantage
            (wireAvg oa fun o => lWireRed C codec ℓ encT (idOf o) 0
              (slotWireRed C codec ℓ encT (idOf o) k (B o))))) +
        (qd : ℝ≥0∞) * macForgeryProb C.F := by
  have hℓ_rust : ℓ + 16 < rustLenBound := by unfold rustLenBound; omega
  rw [Measure.boolDist_comm]
  have h2 := salt_mix C codec ℓ encT oa idOf B N hoff
  have h3 := mac_mix C codec ℓ encT oa idOf B hfit hℓ hqd hshort hdec
  have h4 := wire_mix C codec ℓ encT oa idOf B hrt hℓ_rust hinj hdum hN hoff hcls hshort
  refine ((Measure.boolDist_triangle _ _ _).trans (add_le_add h2
    ((Measure.boolDist_triangle _ _ _).trans (add_le_add h3 h4)))).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib]
  ring

end Stages

end CryptoVerification.E2E.Signed.FSMix
