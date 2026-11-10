/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementComposed
public import Computational.Specifications.Pqxdh.Security.HeadlineDelta
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhModelLink
import Computational.Proofs.ReductionDsl.SizeBudgetBridge

@[expose] public section

set_option autoImplicit false

/-!
# Composed PQXDH and Double-Ratchet V1 mirror helpers and budget monotonicity

**Checked by Lean.**

Defines transcript-mirror helpers for the composed PQXDH + Double-Ratchet V1 experiment and proves
monotonicity of ratchet, FS-AEAD, SPK, and session-mixture bounds in query and epoch budgets.
Covers composed-model deviations `DEV-C5` and `DEV-C8`–`DEV-C13`, alongside inherited deviations
`DEV-LS2`, `DEV-LS22`, `DEV-LS24`, `DEV-LS28`, `DEV-LS33`, `DEV-LS34`, `DEV-LS37`, `DEV-PQ1`,
`DEV-PQ3`, `DEV-PQ5`, `DEV-PQ6`, `DEV-PQ8`, `DEV-PQ11`, `DEV-CLI11`, and `DEV-E8`.
**DEV-C14 (formalization): Per-session `u32` counter budget (`_hq32`).** Per-session query budgets
`qs k` satisfy `2 * (qs k + 1) + 25002 < 2 ^ 32`.
-/

open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD FSAEAD
  CryptoGames.Ratchet.LibsignalSim
  CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1

def bytesWord (bs : List UInt8) : BitVec 256 := bytesToKey32 (ofU8 bs)

def keySOf (dk : SignalPqxdh.DRKey) (aliceCoins : BitVec 256) : SampledSessionKey :=
  ((bytesWord dk.rootKey, bytesWord dk.chainKey), aliceCoins, bytesWord dk.pqrKey)

abbrev sessionSchemeSpkWithSpqr {PQ PQC : Type} [Inhabited PQ] (P : Params PQ PQC) (ℓ : ℕ)
    (s : BitVec 256) : SMSchemeR SampledSessionKey (GhostState PQ) (Plain ℓ) PQC (BitVec 256) Bytes :=
  sessionSchemeFixedSpk P ℓ s

abbrev smSpecWithSpqr (ℓ : ℕ) (PQC : Type) := SM.spec (GhostState Bytes) (Plain ℓ) PQC Bytes

/-- Promoted Double-Ratchet instance state in the composed driver (`gs = none` marks the externally
forwarded instance). -/
structure DrvInst (S : SignalPqxdh.Setup) (ℓ : ℕ) where
  sid : SignalPqxdh.SessionId S
  hdr : SignalPqxdh.HandshakeHdr
  idA : IdentityKey
  idB : IdentityKey
  spkCoins : BitVec 256
  gs : Option (SM.GameState (GhostState Bytes) (Plain ℓ) Bytes)

/-- Transcript-derived driver mirror of `KeyInd` answers and promoted Double-Ratchet instances. -/
structure DrvState (S : SignalPqxdh.Setup) (ℓ : ℕ) where
  insts : List (DrvInst S ℓ) := []
  prins : List (Fin S.N_id × SignalPqxdh.Bytes) := []
  bundles : List ((Fin S.N_id × Fin S.N_recv) × SignalPqxdh.Bytes) := []
  sends : List (SignalPqxdh.SessionId S × SignalPqxdh.PreKeyBundleInput ×
    SignalPqxdh.HandshakeHdr) := []

def drvMirror {S : SignalPqxdh.Setup} {ℓ : ℕ} (ds : DrvState S ℓ) :
    SignalPqxdh.KeyIndQuery S → SignalPqxdh.KeyIndResponse → DrvState S ℓ
  | .initPrin u, .initPrinResp ikAPk _ => { ds with prins := (u, ikAPk) :: ds.prins }
  | .genSPK u j, .bundleResp bnd => { ds with bundles := ((u, j), bnd.spkB) :: ds.bundles }
  | .initiateOPK u i bnd, .hdrResp hdr => { ds with sends := (.sendOPK u i, bnd, hdr) :: ds.sends }
  | .initiateNoOPK u i bnd, .hdrResp hdr =>
    { ds with sends := (.sendNoOPK u i, bnd, hdr) :: ds.sends }
  | _, _ => ds

/-! **DEV-C9 (formalization): Exact-bytes promotion guard (`startDR sid`).** Promotion requires
exact byte matches on the mirrored initiator session, `ikB`, and `spkB`, with distinct `ekAPk`
headers. -/

/-! **DEV-C12 (formalization): `KeyInd.testSession` is withheld in `composedExpWithSpqr`.**
`KeyInd` queries are forwarded and mirrored except `testSession`, which returns `.noneResp`. -/

/-! **DEV-C10 (formalization): `startDR` reveals the bundle's signed pre-key secret (`revealSpkSk`).**
**DEV-C11 (formalization): Post-promotion responder handoff to Double Ratchet.** -/

/-- Composed end-of-game freshness predicate matching `KeyInd`'s `allTestedClean`. -/
def composedClean {S : SignalPqxdh.Setup} (P : SignalPqxdh.Primitives)
    (st : SignalPqxdh.KeyIndState S) : Bool :=
  st.sessions.all (fun s =>
      !s.tested ||
        SignalPqxdh.isKeyIndInitStillFresh P true st.principals st.spkBundles st.respSessions s) &&
    st.respSessions.all (fun r =>
      !r.tested ||
        SignalPqxdh.isKeyIndRespStillFresh P true st.principals st.spkBundles st.sessions r)

/-! **DEV-C8 (formalization): ROM for the PQXDH KDF.** -/

namespace Prefix

end Prefix

/-! **DEV-C13 (formalization): Static per-instance query budgets (`qs`) and SPQR v1 modeling.** -/

end CryptoVerification.E2E

namespace Computational.Proofs.SpecLemmas.Session.StatementComposed

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD FSAEAD
  CryptoGames.Ratchet.LibsignalSim
  CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E
  Computational.Proofs.ReductionDsl

/-! ## Admissible leak-guess set -/

theorem admissibleLastLeakGuesses_mono (Δ : ℕ) {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂) :
    admissibleLastLeakGuesses Δ t₁ ⊆ admissibleLastLeakGuesses Δ t₂ := by
  intro x hx
  simp only [admissibleLastLeakGuesses, Finset.mem_insert, Finset.mem_image,
    Finset.mem_range] at hx ⊢
  rcases hx with rfl | ⟨k, hk, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨k, by omega, rfl⟩

theorem card_admissibleLastLeakGuesses_le (Δ tStar : ℕ) :
    (admissibleLastLeakGuesses Δ tStar).card ≤ (tStar + 1 - Δ) + 1 := by
  unfold admissibleLastLeakGuesses
  have h1 := Finset.card_insert_le none ((Finset.range (tStar + 1 - Δ)).image some)
  have h2 : ((Finset.range (tStar + 1 - Δ)).image some).card ≤
      (Finset.range (tStar + 1 - Δ)).card := Finset.card_image_le
  rw [Finset.card_range] at h2
  omega

theorem card_admissibleLastLeakGuesses (Δ tStar : ℕ) :
    (admissibleLastLeakGuesses Δ tStar).card = (tStar + 1 - Δ) + 1 := by
  unfold admissibleLastLeakGuesses
  have hnotmem : none ∉ (Finset.range (tStar + 1 - Δ)).image some := by
    simp
  rw [Finset.card_insert_of_notMem hnotmem,
    Finset.card_image_of_injective _ (Option.some_injective _), Finset.card_range]

/-! ## Ratchet and FS-AEAD cost and size budgets -/

theorem ratchetCostBudget_mono {q₁ q₂ qep₁ qep₂ : ℕ} (hq : q₁ ≤ q₂) (hqep : qep₁ ≤ qep₂) :
    ratchetCostBudget q₁ qep₁ ≤ ratchetCostBudget q₂ qep₂ := by
  unfold ratchetCostBudget
  have h1 : (q₁ + 1) ^ 2 ≤ (q₂ + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : maxForwardJumps + ReductionDsl.bits qep₁ ≤
      maxForwardJumps + ReductionDsl.bits qep₂ :=
    Nat.add_le_add_left (SizeBudgetBridge.bits_mono hqep) maxForwardJumps
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2

theorem ratchetCostBudget_mono_qep {q qep₁ qep₂ : ℕ} (hqep : qep₁ ≤ qep₂) :
    ratchetCostBudget q qep₁ ≤ ratchetCostBudget q qep₂ :=
  ratchetCostBudget_mono le_rfl hqep

theorem two_pow_24_mul_le_ratchetCostBudget (q qep : ℕ) :
    2 ^ 24 * (q + 1) ≤ ratchetCostBudget q qep := by
  unfold ratchetCostBudget
  have hmfj : maxForwardJumps = 25000 := rfl
  have hbits : 1 ≤ ReductionDsl.bits qep := SizeBudgetBridge.bits_pos qep
  have hsq : q + 1 ≤ (q + 1) ^ 2 := by nlinarith
  nlinarith

theorem q_add_eleven_le_ratchetCostBudget (q qep : ℕ) :
    q + 11 ≤ ratchetCostBudget q qep := by
  have h := two_pow_24_mul_le_ratchetCostBudget q qep
  omega

theorem ratchetCostBudget_pos (q qep : ℕ) :
    0 < ratchetCostBudget q qep := by
  have h := two_pow_24_mul_le_ratchetCostBudget q qep
  omega

theorem ratchetFsAdapterBudget_mono {qR₁ qR₂ qep₁ qep₂ : ℕ}
    (hqR : qR₁ ≤ qR₂) (hqep : qep₁ ≤ qep₂) :
    ratchetFsAdapterBudget qR₁ qep₁ ≤ ratchetFsAdapterBudget qR₂ qep₂ := by
  unfold ratchetFsAdapterBudget
  have h1 : 2 ^ 24 * (qR₁ + 1) ≤ 2 ^ 24 * (qR₂ + 1) := Nat.mul_le_mul_left _ (by omega)
  have h2 : 2 ^ 10 * (qR₁ + 1) ^ 2 ≤ 2 ^ 10 * (qR₂ + 1) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have h3 : 2 ^ 12 * (qR₁ + 1) * ReductionDsl.bits qep₁ ≤
      2 ^ 12 * (qR₂ + 1) * ReductionDsl.bits qep₂ :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (SizeBudgetBridge.bits_mono hqep)
  omega

theorem ratchetFsAdapterBudget_le_ratchetCostBudget (qR qep : ℕ) :
    ratchetFsAdapterBudget qR qep ≤ ratchetCostBudget qR qep := by
  unfold ratchetFsAdapterBudget ratchetCostBudget
  have hmfj : maxForwardJumps = 25000 := rfl
  have hsq : qR + 1 ≤ (qR + 1) ^ 2 := by nlinarith
  have hb : 2 ^ 12 * (qR + 1) * ReductionDsl.bits qep ≤
      2 ^ 12 * (qR + 1) ^ 2 * ReductionDsl.bits qep :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsq)
  nlinarith

theorem fsRatchetCostBudget_mono {q₁ q₂ qep₁ qep₂ : ℕ}
    (hq : q₁ ≤ q₂) (hqep : qep₁ ≤ qep₂) :
    fsRatchetCostBudget q₁ qep₁ ≤ fsRatchetCostBudget q₂ qep₂ := by
  unfold fsRatchetCostBudget
  refine min_le_min (ratchetCostBudget_mono hq hqep) ?_
  have h1 : 2 ^ 14 * (q₁ + 1) ^ 2 ≤ 2 ^ 14 * (q₂ + 1) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have h2 : 2 ^ 15 * (q₁ + 1) * (maxForwardJumps + ReductionDsl.bits qep₁) ≤
      2 ^ 15 * (q₂ + 1) * (maxForwardJumps + ReductionDsl.bits qep₂) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
      (Nat.add_le_add_left (SizeBudgetBridge.bits_mono hqep) _)
  omega

theorem fsRatchetCostBudget_le_ratchetCostBudget (q qep : ℕ) :
    fsRatchetCostBudget q qep ≤ ratchetCostBudget q qep :=
  min_le_left _ _

theorem reductionSizeBudget_add_bits_mono {B₁ B₂ : ℕ} (hB : B₁ ≤ B₂) :
    ReductionDsl.reductionSizeBudget + 2 ^ 12 * ReductionDsl.bits B₁ ≤
      ReductionDsl.reductionSizeBudget + 2 ^ 12 * ReductionDsl.bits B₂ :=
  Nat.add_le_add_left (Nat.mul_le_mul_left _ (SizeBudgetBridge.bits_mono hB)) _

theorem ratchetDescBudget_expr_mono {q₁ q₂ qep₁ qep₂ : ℕ}
    (hq : q₁ ≤ q₂) (hqep : qep₁ ≤ qep₂) :
    2 ^ 23 + 2 ^ 13 * ReductionDsl.bits (ratchetCostBudget q₁ qep₁ + qep₁) ≤
      2 ^ 23 + 2 ^ 13 * ReductionDsl.bits (ratchetCostBudget q₂ qep₂ + qep₂) :=
  Nat.add_le_add_left
    (Nat.mul_le_mul_left _
      (SizeBudgetBridge.bits_mono (Nat.add_le_add (ratchetCostBudget_mono hq hqep) hqep))) _

/-- When `ratchetCostBudget q qep + qep < 2 ^ 126`, the ratchet description-size expression fits
inside `ReductionDsl.reductionSizeBudget`. -/
theorem ratchetDescBudget_expr_le_reductionSizeBudget {q qep : ℕ}
    (hB : ratchetCostBudget q qep + qep < 2 ^ 126) :
    2 ^ 23 + 2 ^ 13 * ReductionDsl.bits (ratchetCostBudget q qep + qep) ≤
      ReductionDsl.reductionSizeBudget := by
  have hbits : ReductionDsl.bits (ratchetCostBudget q qep + qep) ≤ 126 := by
    have hpos : ratchetCostBudget q qep + qep ≠ 0 := by
      have := ratchetCostBudget_pos q qep
      omega
    have hlog : Nat.log 2 (ratchetCostBudget q qep + qep) < 126 :=
      Nat.log_lt_of_lt_pow hpos hB
    unfold ReductionDsl.bits
    omega
  unfold ReductionDsl.reductionSizeBudget
  omega

/-! ## `CostedFits`, `GRedBounded`, and `GTwoStageBounded` monotonicity -/

theorem costedFits_mono {S : ReductionDsl.Sig} {B₁ B₂ : ℕ} (hB : B₁ ≤ B₂) :
    ∀ (t : ReductionDsl.Ty S) (x : t.denote), CostedFits B₁ t x → CostedFits B₂ t x
  | .base _, _, hx => le_trans hx hB
  | .unit, _, _ => trivial
  | .bool, _, _ => trivial
  | .nat, _, hx => le_trans hx hB
  | .opt _, none, _ => trivial
  | .opt t, some a, hx => costedFits_mono hB t a hx
  | .prod t u, x, hx => ⟨costedFits_mono hB t x.1 hx.1, costedFits_mono hB u x.2 hx.2⟩
  | .sum t _, .inl a, hx => costedFits_mono hB t a hx
  | .sum _ u, .inr b, hx => costedFits_mono hB u b hx
  | .list t, _, hx => ⟨le_trans hx.1 hB, fun y hy => costedFits_mono hB t y (hx.2 y hy)⟩
  | .tbl t, _, hx => fun i => costedFits_mono hB t _ (hx i)

theorem costedMidFits_mono {S : ReductionDsl.Sig} {κ : Type} {G : OracleSpec κ} {α : Type}
    {B₁ B₂ : ℕ} (hB : B₁ ≤ B₂) (π σ ch : ReductionDsl.Ty S) :
    ∀ m : ReductionDsl.Mid G α π.denote σ.denote ch.denote,
      CostedMidFits B₁ π σ ch m → CostedMidFits B₂ π σ ch m
  | .done _ s, hs => costedFits_mono hB σ s hs
  | .paused _ c p s _, ⟨hc, hp, hs⟩ =>
    ⟨costedFits_mono hB ch c hc, costedFits_mono hB π p hp, costedFits_mono hB σ s hs⟩

theorem gRedBounded_mono_budget {S : ReductionDsl.Sig}
    {O : ReductionDsl.Ops S} {ι κ : Type}
    {T : OracleSpec ι} {I : ReductionDsl.Iface S T} {G : OracleSpec κ}
    {C : ReductionDsl.GameCodec S G} {rIn aIn aOut out : ReductionDsl.Ty S}
    {R : ReductionDsl.CostedReduction O I G C rIn aIn aOut out}
    {wTag : I.Tag → ℕ} {wSamp : I.smp.Samp → ℕ}
    {q qOut B₁ B₂ : ℕ} (hB : B₁ ≤ B₂)
    (h : GRedBounded R wTag wSamp q qOut B₁) :
    GRedBounded R wTag wSamp q qOut B₂ := by
  rcases h with ⟨hCost, hSize, hQ, hO, hS, hRun⟩
  refine ⟨le_trans hCost hB,
    le_trans hSize (reductionSizeBudget_add_bits_mono hB),
    hQ, hO, hS, fun B hOut A hAq hFit x hx => ?_⟩
  have hW : 2 * (B₁ + q + 1) * (B + 1) ≤ 2 * (B₂ + q + 1) * (B + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  rcases hRun B hOut A hAq hFit x hx with ⟨hEval, hSt⟩
  exact ⟨fun y hy => costedFits_mono hW out y (hEval y hy),
    fun r0 hr0 r1 hr1 => costedFits_mono hW R.σ r1.2 (hSt r0 hr0 r1 hr1)⟩

theorem gTwoStageBounded_mono_budget {S : ReductionDsl.Sig}
    {O : ReductionDsl.Ops S} {ι κ : Type}
    {T : OracleSpec ι} {I : ReductionDsl.Iface S T} {G : OracleSpec κ}
    {C : ReductionDsl.GameCodec S G} {rIn aIn aOut ch rIn2 out : ReductionDsl.Ty S}
    {R : ReductionDsl.TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out}
    {wTag : I.Tag → ℕ} {wSamp : I.smp.Samp → ℕ}
    {q qOut B₁ B₂ : ℕ} (hB : B₁ ≤ B₂)
    (h : GTwoStageBounded R wTag wSamp q qOut B₁) :
    GTwoStageBounded R wTag wSamp q qOut B₂ := by
  rcases h with ⟨hCost, hSize, hQ, hO, hS, hRun⟩
  refine ⟨le_trans hCost hB,
    le_trans hSize (reductionSizeBudget_add_bits_mono hB),
    hQ, hO, hS, fun B hOut A hFit x hx dflt cm hcm => ?_⟩
  have hW : 2 * (B₁ + 2 * q + 1) * (B + 1) ≤ 2 * (B₂ + 2 * q + 1) * (B + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  rcases hRun B hOut A hFit x hx dflt cm hcm with ⟨hCh, hMid, hEval2⟩
  exact ⟨costedFits_mono hW ch cm.1 hCh,
    costedMidFits_mono hW R.π R.σ ch cm.2 hMid,
    fun y hy z hz => costedFits_mono hW out z (hEval2 y hy z hz)⟩

theorem fsCostedBounds_mono_qep {Pt : Type} [DecidableEq Pt]
    {C : Crypto} {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {qR qep₁ qep₂ : ℕ} (hqep : qep₁ ≤ qep₂)
    {R : FsCostedReds C codec ℓ encT idOf}
    (h : fsCostedBounds qR qep₁ R) :
    fsCostedBounds qR qep₂ R := by
  have hAdapt : ratchetFsAdapterBudget qR qep₁ ≤ ratchetFsAdapterBudget qR qep₂ :=
    ratchetFsAdapterBudget_mono le_rfl hqep
  have hHyb : fsRatchetCostBudget qR qep₁ ≤ fsRatchetCostBudget qR qep₂ :=
    fsRatchetCostBudget_mono le_rfl hqep
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  exact ⟨gRedBounded_mono_budget hAdapt h1,
    fun j hj => gTwoStageBounded_mono_budget hHyb (h2 j hj),
    fun la => gTwoStageBounded_mono_budget hHyb (h3 la),
    fun j hj => gRedBounded_mono_budget hAdapt (h4 j hj),
    gRedBounded_mono_budget hAdapt h5,
    fun j hj => gRedBounded_mono_budget hAdapt (h6 j hj),
    gRedBounded_mono_budget hAdapt h7⟩

/-! ## Two-tier SPK budgets -/

theorem spkLeakRedUBudget_mono {q₁ q₂ : ℕ} (hq : q₁ ≤ q₂) :
    spkLeakRedUBudget q₁ ≤ spkLeakRedUBudget q₂ := by
  unfold spkLeakRedUBudget
  omega

theorem spkLeakRedUBudget_le_ratchetCostBudget (q qep : ℕ) :
    spkLeakRedUBudget q ≤ ratchetCostBudget q qep := by
  unfold spkLeakRedUBudget
  have h := two_pow_24_mul_le_ratchetCostBudget q qep
  omega

theorem spkTier1Budget_mono {q₁ q₂ qep₁ qep₂ : ℕ} (hq : q₁ ≤ q₂) (hqep : qep₁ ≤ qep₂) :
    spkTier1Budget q₁ qep₁ ≤ spkTier1Budget q₂ qep₂ := by
  unfold spkTier1Budget
  have h1 : 2 ^ 10 * (q₁ + 1) ^ 2 ≤ 2 ^ 10 * (q₂ + 1) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have h2 : 2 ^ 9 * maxForwardJumps * (q₁ + 1) ≤ 2 ^ 9 * maxForwardJumps * (q₂ + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have h3 : 2 ^ 8 * (q₁ + 1) * ReductionDsl.bits qep₁ ≤
      2 ^ 8 * (q₂ + 1) * ReductionDsl.bits qep₂ :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (SizeBudgetBridge.bits_mono hqep)
  omega

theorem spkTier2Budget_mono {q₁ q₂ qep₁ qep₂ ℓ₁ ℓ₂ : ℕ}
    (hq : q₁ ≤ q₂) (hqep : qep₁ ≤ qep₂) (hℓ : ℓ₁ ≤ ℓ₂) :
    spkTier2Budget q₁ qep₁ ℓ₁ ≤ spkTier2Budget q₂ qep₂ ℓ₂ := by
  unfold spkTier2Budget
  have hbq : ReductionDsl.bits (q₁ + 1) ≤ ReductionDsl.bits (q₂ + 1) :=
    SizeBudgetBridge.bits_mono (by omega)
  have hbep : ReductionDsl.bits qep₁ ≤ ReductionDsl.bits qep₂ :=
    SizeBudgetBridge.bits_mono hqep
  exact Nat.mul_le_mul (by omega) (by omega)

theorem spkHopBudget_mono {q₁ q₂ qep₁ qep₂ ℓ₁ ℓ₂ : ℕ}
    (hq : q₁ ≤ q₂) (hqep : qep₁ ≤ qep₂) (hℓ : ℓ₁ ≤ ℓ₂) :
    spkHopBudget q₁ qep₁ ℓ₁ ≤ spkHopBudget q₂ qep₂ ℓ₂ :=
  min_le_min (spkTier1Budget_mono hq hqep) (spkTier2Budget_mono hq hqep hℓ)

theorem spkHopBudget_mono_q {q₁ q₂ : ℕ} (hq : q₁ ≤ q₂) (qep ℓ : ℕ) :
    spkHopBudget q₁ qep ℓ ≤ spkHopBudget q₂ qep ℓ :=
  spkHopBudget_mono hq le_rfl le_rfl

theorem spkHopBudget_mono_qep {q qep₁ qep₂ ℓ : ℕ} (hqep : qep₁ ≤ qep₂) :
    spkHopBudget q qep₁ ℓ ≤ spkHopBudget q qep₂ ℓ :=
  spkHopBudget_mono le_rfl hqep le_rfl

theorem spkHopBudget_le_spkTier1Budget (q qep ℓ : ℕ) :
    spkHopBudget q qep ℓ ≤ spkTier1Budget q qep :=
  min_le_left _ _

theorem spkHopBudget_le_spkTier2Budget (q qep ℓ : ℕ) :
    spkHopBudget q qep ℓ ≤ spkTier2Budget q qep ℓ :=
  min_le_right _ _

theorem spkTier1Budget_le_ratchetCostBudget (q qep : ℕ) :
    spkTier1Budget q qep ≤ ratchetCostBudget q qep := by
  unfold spkTier1Budget ratchetCostBudget
  have hmfj : maxForwardJumps = 25000 := rfl
  have hsq : q + 1 ≤ (q + 1) ^ 2 := by nlinarith
  have hb : 2 ^ 8 * (q + 1) * ReductionDsl.bits qep ≤
      2 ^ 12 * (q + 1) ^ 2 * ReductionDsl.bits qep :=
    Nat.mul_le_mul_right _ (by nlinarith)
  nlinarith

theorem spkHopBudget_le_ratchetCostBudget (q qep ℓ : ℕ) :
    spkHopBudget q qep ℓ ≤ ratchetCostBudget q qep :=
  le_trans (spkHopBudget_le_spkTier1Budget q qep ℓ) (spkTier1Budget_le_ratchetCostBudget q qep)

theorem spkCostedBounds_mono_qep {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} {C : Crypto} {K : CryptoVerification.LibsignalSpqrV1.MlKem}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {q qep₁ qep₂ : ℕ} (hqep : qep₁ ≤ qep₂)
    {R : SpkCostedReds Pt ℓ C K Dh encPt encT decT lam}
    (h : spkCostedBounds q qep₁ R) :
    spkCostedBounds q qep₂ R := by
  have hB : spkHopBudget q qep₁ ℓ ≤ spkHopBudget q qep₂ ℓ := spkHopBudget_mono_qep hqep
  rcases h with ⟨h1, h2, h3, h4⟩
  exact ⟨gRedBounded_mono_budget hB h1, h2,
    fun k hk => gRedBounded_mono_budget hB (h3 k hk),
    fun k hk => gRedBounded_mono_budget hB (h4 k hk)⟩

/-! ## Session mixture bound monotonicity -/

theorem spuriousStepTerm_mono {Pt : Type}
    (F : ShaState → List (BitVec 8) → ShaState)
    (encPt : Pt → List (BitVec 8)) (Dh : DHFun (BitVec 256) Pt)
    {q₁ q₂ qep₁ qep₂ : ℕ} (hq : q₁ ≤ q₂) (hqep : qep₁ ≤ qep₂) :
    spuriousStepTerm F encPt Dh q₁ qep₁ ≤ spuriousStepTerm F encPt Dh q₂ qep₂ := by
  unfold spuriousStepTerm
  gcongr

theorem spuriousStepTerm_mono_qep {Pt : Type}
    (F : ShaState → List (BitVec 8) → ShaState)
    (encPt : Pt → List (BitVec 8)) (Dh : DHFun (BitVec 256) Pt) (q : ℕ)
    {qep₁ qep₂ : ℕ} (hqep : qep₁ ≤ qep₂) :
    spuriousStepTerm F encPt Dh q qep₁ ≤ spuriousStepTerm F encPt Dh q qep₂ :=
  spuriousStepTerm_mono F encPt Dh le_rfl hqep

theorem refineConst_mono_qep {Pt : Type} [DecidableEq Pt] [Zero Pt]
    (Z : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (q : ℕ) (δ : ℝ≥0∞)
    {qep₁ qep₂ : ℕ} (hqep : qep₁ ≤ qep₂) :
    refineConst Z Dh encPt q qep₁ δ ≤ refineConst Z Dh encPt q qep₂ δ := by
  unfold refineConst
  have hsp := spuriousStepTerm_mono_qep Z.F encPt Dh q hqep
  have h1 : (qep₁ : ℝ≥0∞) ≤ (qep₂ : ℝ≥0∞) := Nat.cast_le.mpr hqep
  gcongr

theorem hiddenSaltMixtureBound_mono_qep {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (Z : Crypto) (K : CryptoVerification.LibsignalSpqrV1.MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) {qep₁ qep₂ : ℕ} (hqep : qep₁ ≤ qep₂)
    (q : ℕ) (δ : ℝ≥0∞) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) :
    hiddenSaltMixtureBound Z K ℓ Dh encPt encT decT lam qep₁ q δ oa ida idb R A ≤
      hiddenSaltMixtureBound Z K ℓ Dh encPt encT decT lam qep₂ q δ oa ida idb R A :=
  letI : MeasurableSpace α := ⊤
  by
    unfold hiddenSaltMixtureBound
    dsimp only
    have hSum :
        (∑ t ∈ Finset.range ((qep₁ + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses 2 t,
          ((∫⁻ o, CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
              (((R o).B_cka tL t).eval
                (fun _ => (R o).challSimDF.eval
                  (fun _ => (R o).simDeliverForge.eval (fun _ => A o) ()) ()) ()) ∂𝒟[oa]) +
            (∫⁻ o, PRFPRNG.advantage (rootPRNG Z.F encPt)
              (((R o).B_prng tL t).eval
                (fun _ => (R o).challSimDF.eval
                  (fun _ => (R o).simDeliverForge.eval (fun _ => A o) ()) ()) ()) ∂𝒟[oa]) +
            (∑ j ∈ Finset.range q,
              ∫⁻ o, fsAeadSlotSumBound Z (min (2 * q) (q + 2)) (R o).fs
                (((R o).B_fs j tL t).eval
                  (fun _ => (R o).challSimDF.eval
                    (fun _ => (R o).simDeliverForge.eval (fun _ => A o) ()) ()) ()) ∂𝒟[oa]) +
            4 * (q : ℝ≥0∞) * CryptoVerification.LibsignalSession.macForgeryTerm Z q)) ≤
        (∑ t ∈ Finset.range ((qep₂ + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses 2 t,
          ((∫⁻ o, CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
              (((R o).B_cka tL t).eval
                (fun _ => (R o).challSimDF.eval
                  (fun _ => (R o).simDeliverForge.eval (fun _ => A o) ()) ()) ()) ∂𝒟[oa]) +
            (∫⁻ o, PRFPRNG.advantage (rootPRNG Z.F encPt)
              (((R o).B_prng tL t).eval
                (fun _ => (R o).challSimDF.eval
                  (fun _ => (R o).simDeliverForge.eval (fun _ => A o) ()) ()) ()) ∂𝒟[oa]) +
            (∑ j ∈ Finset.range q,
              ∫⁻ o, fsAeadSlotSumBound Z (min (2 * q) (q + 2)) (R o).fs
                (((R o).B_fs j tL t).eval
                  (fun _ => (R o).challSimDF.eval
                    (fun _ => (R o).simDeliverForge.eval (fun _ => A o) ()) ()) ()) ∂𝒟[oa]) +
            4 * (q : ℝ≥0∞) * CryptoVerification.LibsignalSession.macForgeryTerm Z q)) :=
      Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
    have hsp := spuriousStepTerm_mono_qep Z.F encPt Dh q hqep
    have hδ : ((qep₁ : ℝ≥0∞) + 1) * ((qep₁ : ℝ≥0∞) + 2) * δ ≤
        ((qep₂ : ℝ≥0∞) + 1) * ((qep₂ : ℝ≥0∞) + 2) * δ := by
      have hqcast : (qep₁ : ℝ≥0∞) ≤ (qep₂ : ℝ≥0∞) := Nat.cast_le.mpr hqep
      gcongr
    exact add_le_add (add_le_add hSum hsp) hδ

theorem fig8MixShortAuthV1_mono_qep {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (Z : Crypto) (K : CryptoVerification.LibsignalSpqrV1.MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) {qep₁ qep₂ : ℕ} (hqep : qep₁ ≤ qep₂)
    (q : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) :
    fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep₁ q oa ida idb R A ≤
      fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep₂ q oa ida idb R A := by
  unfold fig8MixShortAuthV1
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))) zero_le

theorem fig8MixShortPrivV1_mono_qep {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (Z : Crypto) (K : CryptoVerification.LibsignalSpqrV1.MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) {qep₁ qep₂ : ℕ} (hqep : qep₁ ≤ qep₂)
    (q : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) :
    fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep₁ q oa ida idb R A ≤
      fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep₂ q oa ida idb R A := by
  unfold fig8MixShortPrivV1
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))) zero_le

theorem uniformStartMixtureBound_mono_qep
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (Z : Crypto) (K : CryptoVerification.LibsignalSpqrV1.MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) {qep₁ qep₂ : ℕ} (hqep : qep₁ ≤ qep₂)
    (q : ℕ) (δ : ℝ≥0∞) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) :
    uniformStartMixtureBound Z K ℓ Dh encPt encT decT lam qep₁ q δ oa ida idb R A ≤
      uniformStartMixtureBound Z K ℓ Dh encPt encT decT lam qep₂ q δ oa ida idb R A := by
  unfold uniformStartMixtureBound
  have hauth := fig8MixShortAuthV1_mono_qep Z K ℓ Dh encPt encT decT lam hqep q oa ida idb R
    (fun o => RefuseB0.refuseCorrB0 (A o))
  have hpriv := fig8MixShortPrivV1_mono_qep Z K ℓ Dh encPt encT decT lam hqep q oa ida idb R
    (fun o => RefuseB0.refuseCorrB0 (A o))
  have href := refineConst_mono_qep Z Dh encPt q δ hqep
  have hhs := hiddenSaltMixtureBound_mono_qep Z K ℓ Dh encPt encT decT lam hqep q δ oa ida idb R
    (fun o => RefuseB0.refuseCorrB0 (A o))
  gcongr

end Computational.Proofs.SpecLemmas.Session.StatementComposed
