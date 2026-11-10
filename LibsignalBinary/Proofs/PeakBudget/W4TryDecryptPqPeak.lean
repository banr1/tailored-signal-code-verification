/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.ChainClone4PlacedMidBudget
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.VecGrowCredit
public import LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
public import LibsignalBinary.Proofs.PeakBudget.W4InnerHelpers
public import LibsignalBinary.Proofs.PeakBudget.W4PrevDecPeak
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep12Budget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep3Budget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget

/-!
# `try_decrypt_pq` Seam & Segment Peak Live-Heap Bounds

Parametric `(M : AllocCostModel) [HasFineReallocCredit M]` (`ModelHyps M`) sequential
`PhaseCreditSpec` bounds in exact binary call order for `try_decrypt_pq`:
1. Segment bounds for `S1` (`ChainCloneEnv`, `SenderChainCloneEnv`), `S3` (`DhCommitStep12Env`,
   `DhCommitStep3Env`), `S4` (`Vec<104>` doubling chain), `S7` (`ComputeMacEnv`,
   `VerifyMacWithAddressesEnv` with `Δlive = 0`), `S8` (`W4AesDecEnv`, `W4AesDecErrEnv` with
   `Δlive = 0` on error), and `S9` (`W4ApplySetStateEnv`).
2. Seam composition (`FromS8GenEnv` → … → `FromS1GenEnv`) over `TripleRatchet.Decrypt.RootBudgetAux`.
3. Failed-trial candidate clone + `try_decrypt_pq` + drop + `GrowOneSpeEnv` `sc = 63` cancellation
   (`W4TryDecryptCloneFailEnv`, `phaseCredit_w4TryDecryptCloneFail_cancel`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W4TryDecryptPqPeak

open CryptoGames.HKDF (Salt)
open CryptoGames.LibsignalSession (
  ChainKey Crypto MessageKeyGenerator MessageKeys ReceiverChain SenderChain
  SessionState ShaCompress SignalMessage TripleRatchet
)
open CryptoVerification.LibsignalSessionRepr (ChainGhost)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel TrGhost TryDecryptGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (SenderChainGhost UuidParser)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent FreeOnlyEvs SeqEnv
  rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.ChainClone4PlacedMidBudget (chainClonePreMkEvents)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (
  ConcatEnv IterSeqEnv ModelHyps PhaseCreditSpec
)
open LibsignalBinary.Proofs.PeakBudget.VecGrowCredit (
  doublingCap doublingCaps
  phaseCreditSpec_growOne104_chain
  rawVecCumOfSteps_le_affine rawVecMaxLiveOfSteps_le_affine rawVecPeakOfSteps_le_affine
)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak (
  W4BoundedEvs phaseCredit_growOneSpeZero_small phaseCredit_seq_freeOnly
  phaseCredit_w4BoundedEvs_small
)
open LibsignalBinary.Proofs.PeakBudget.W4InnerHelpers (
  OptRustAllocEnv phaseCredit_chainClonePreMk phaseCredit_dhCommitStep12
  phaseCredit_mkSeedFlatMap phaseCredit_optRustAlloc_ub
)
open LibsignalBinary.Proofs.PeakBudget.W4PrevDecPeak (
  phaseCredit_finishGrow_aff phaseCredit_finishGrow_small
  phaseCredit_growOne104_aff phaseCredit_growOne104_small
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (
  GrowOne104Env growOne104Events
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  finishGrowEvents publicKeySerializeEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep12Budget (DhCommitStep12Env)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep3Budget (
  DhCommitStep3Env dhCommitStep3Events dhCommitStep3aEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux (
  FromS1Env FromS1FnEnv FromS1GenEnv FromS2GenEnv FromS3GenEnv FromS4Env
  FromS4FnEnv FromS4GenEnv FromS5GenEnv FromS6GenEnv FromS7GenEnv FromS8GenEnv
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (GrowOneSpeEnv)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget (
  ChainCloneEnv SenderChainCloneEnv chainCloneEvents senderChainAsProtoGhost
  senderChainCloneEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget (
  ComputeMacEnv VerifyMacWithAddressesEnv VerifyMacWithAddressesGhost
  computeMacEvents verifyMacWithAddressesEvents
)

/-! ## Existential Ghost-Witness Combinators -/

/-- Lift uniform `(c, l, p, r)` `PhaseCreditSpec` bounds across an existential ghost witness
`fun evs => ∃ a, E a evs` (discharging `∃ trG', FromS*GenEnv ...` in `RootBudgetAux`). -/
theorem phaseCredit_exists {α : Type} {M : AllocCostModel} [HasFineReallocCredit M]
    {E : α → List AllocEvent → Prop} {c l p r : Nat}
    (h : ∀ a, PhaseCreditSpec M (E a) c l p r) :
    PhaseCreditSpec M (fun evs => ∃ a, E a evs) c l p r where
  req_align evs hex ev hev := by
    obtain ⟨a, ha⟩ := hex
    exact (h a).req_align evs ha ev hev
  credit_le st0 {_} hex := by
    obtain ⟨a, ha⟩ := hex
    exact (h a).credit_le st0 ha

/-- Lift uniform `(c, l, p, r)` `PhaseCreditSpec` bounds across a bounded existential
`fun evs => ∃ n, n ≤ cap ∧ P n evs`. -/
theorem phaseCredit_exists_le {M : AllocCostModel} [HasFineReallocCredit M]
    {P : Nat → List AllocEvent → Prop} {cap c l p r : Nat}
    (h : ∀ n, n ≤ cap → PhaseCreditSpec M (P n) c l p r) :
    PhaseCreditSpec M (fun evs => ∃ n, n ≤ cap ∧ P n evs) c l p r where
  req_align evs hex := by
    obtain ⟨n, hn, hp⟩ := hex
    exact (h n hn).req_align evs hp
  credit_le st0 {_} hex := by
    obtain ⟨n, hn, hp⟩ := hex
    exact (h n hn).credit_le st0 hp

/-! ## Segment `S1`: `ChainCloneEnv` & `SenderChainCloneEnv` Bounds -/

/-- `PhaseCreditSpec` for `FromRecordChainClone.DefsBudget.SenderChainCloneEnv g sc`
(`messageKeys = []`, `≤ 3` small key buffers `≤ 33 B`): `Δlive = 0, Δpeak = 0` when
`33 ≤ smallMaxReq M`. -/
theorem phaseCredit_senderChainCloneEnv {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {g : SenderChainGhost} {sc : SenderChain}
    (hsrk : g.srk.bytes.length ≤ 33)
    (hpriv : g.priv.bytes.length ≤ 32)
    (hSmall33 : 33 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (SenderChainCloneEnv g sc) 28815 0 0 33 := by
  have hpre := phaseCredit_chainClonePreMk hM
    (gc := senderChainAsProtoGhost g sc) hsrk hpriv hSmall33
  have himp : ∀ evs, SenderChainCloneEnv g sc evs →
      evs = chainClonePreMkEvents (senderChainAsProtoGhost g sc) := by
    rintro _ rfl
    simp [senderChainCloneEvents, senderChainAsProtoGhost, chainCloneEvents,
      chainClonePreMkEvents, List.append_assoc]
  exact (hpre.of_imp himp).mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 33)

/-- `PhaseCreditSpec` for `FromRecordChainClone.DefsBudget.ChainCloneEnv gc` with
`gc.2.messageKeys.length ≤ mkCap` and per-element `seed.length ≤ seedCap ≤ smallMaxReq M`. -/
theorem phaseCredit_chainCloneEnv {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {gc : ChainGhost × ReceiverChain} {mkCap seedCap : Nat}
    (hsrk : gc.1.srk.bytes.length ≤ 33)
    (hpriv : gc.1.priv.bytes.length ≤ 32)
    (hSmall33 : 33 ≤ HasFineReallocCredit.smallMaxReq M)
    (hlen : gc.2.messageKeys.length ≤ mkCap)
    (hseed : ∀ mkg ∈ gc.2.messageKeys, mkg.seed.length ≤ seedCap)
    (hSmallSeed : seedCap ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (ChainCloneEnv gc)
      (28815 + (2 * (104 * mkCap) + 9539) + mkCap * (2 * seedCap + 9539))
      (104 * mkCap + 8195)
      (104 * mkCap + 8195)
      (max 33 (max (104 * mkCap) seedCap)) := by
  have hpre := phaseCredit_chainClonePreMk hM hsrk hpriv hSmall33
  by_cases hnil : gc.2.messageKeys = []
  · have himp : ∀ evs, ChainCloneEnv gc evs →
        evs = chainClonePreMkEvents gc := by
      rintro _ rfl
      cases hck : gc.2.chainKey <;>
        simp [chainCloneEvents, chainClonePreMkEvents, hnil, hck, List.append_assoc]
    exact (hpre.of_imp himp).mono (by omega) (Nat.zero_le _) (Nat.zero_le _) (by omega)
  · have h104_le : 104 * gc.2.messageKeys.length ≤ 104 * mkCap :=
      Nat.mul_le_mul_left 104 hlen
    have h104_ne : 104 * gc.2.messageKeys.length ≠ 0 := by
      cases hmk : gc.2.messageKeys with
      | nil => exact False.elim (hnil hmk)
      | cons _ _ => simp
    have hout := phaseCredit_optRustAlloc_ub hM
      (n := 104 * gc.2.messageKeys.length) (al := 8) (cap := 104 * mkCap)
      (by decide) h104_le
    have hseeds := phaseCredit_mkSeedFlatMap hM hlen hseed hSmallSeed
    have hfull := hpre.concat (hout.concat hseeds)
    have himp : ∀ evs, ChainCloneEnv gc evs →
        ConcatEnv (· = chainClonePreMkEvents gc)
          (ConcatEnv (OptRustAllocEnv (104 * gc.2.messageKeys.length) 8)
            (· = gc.2.messageKeys.flatMap (fun mkg => rustAllocEvents mkg.seed.length 1))) evs := by
      rintro _ rfl
      refine ⟨chainClonePreMkEvents gc,
        rustAllocEvents (104 * gc.2.messageKeys.length) 8 ++
          gc.2.messageKeys.flatMap (fun mkg => rustAllocEvents mkg.seed.length 1),
        ?_, rfl, ?_⟩
      · cases hck : gc.2.chainKey <;>
          simp [chainCloneEvents, chainClonePreMkEvents, hnil, hck, List.append_assoc]
      · exact ⟨_, _, rfl, by simp [OptRustAllocEnv, h104_ne], rfl⟩
    exact (hfull.of_imp himp).mono (by omega) (by omega) (by omega) (by omega)

/-! ## Segment `S3` (`DhCommitStep12Env` + `DhCommitStep3Env`) & Segment `S4` (`Vec<104>`) -/

/-- Small-regime `PhaseCreditSpec` for `DhCommitStep3Env chainsCap rcLen` when `chainsCap.toNat < 5`
(`832 ≤ smallMaxReq M`): `Δcum = 11203, Δlive = 0, Δpeak = 0, maxReq = 832`. -/
theorem phaseCredit_dhCommitStep3_lt5_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {chainsCap rcLen : BitVec 64}
    (hcap : chainsCap.toNat < 5)
    (hSmall832 : 832 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (DhCommitStep3Env chainsCap rcLen) 11203 0 0 832 := by
  have hd33 := PhaseCreditSpec.rustDealloc_align16 M (req := 33) (al := 1) (by decide)
  by_cases heq : rcLen = chainsCap
  · have hg := phaseCredit_growOne104_small hM chainsCap hcap hSmall832
    have himp : ∀ evs, DhCommitStep3Env chainsCap rcLen evs →
        ConcatEnv (GrowOne104Env chainsCap) (· = rustDeallocEvents 33 1) evs := by
      rintro _ rfl
      exact ⟨growOne104Events chainsCap, rustDeallocEvents 33 1,
        by simp [dhCommitStep3Events, dhCommitStep3aEvents, heq], rfl, rfl⟩
    exact ((hg.concat hd33).of_imp himp).mono (by omega) (by omega) (by omega) (by omega)
  · have himp : ∀ evs, DhCommitStep3Env chainsCap rcLen evs → evs = rustDeallocEvents 33 1 := by
      rintro _ rfl
      simp [dhCommitStep3Events, dhCommitStep3aEvents, heq]
    exact (hd33.of_imp himp).mono (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)

/-- General `chainsCap.toNat ≤ capMax` small-regime `PhaseCreditSpec` for `DhCommitStep3Env`
(e.g., `capMax = 8` → `newBytes ≤ 1664 ≤ smallMaxReq M`). -/
theorem phaseCredit_dhCommitStep3_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {chainsCap rcLen : BitVec 64} {capMax : Nat}
    (hcap : chainsCap.toNat ≤ capMax)
    (hSmall : max (2 * capMax) 4 * 104 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (DhCommitStep3Env chainsCap rcLen)
      (2 * (max (2 * capMax) 4 * 104) + 9539) 0 0 (max (2 * capMax) 4 * 104) := by
  have hd33 := PhaseCreditSpec.rustDealloc_align16 M (req := 33) (al := 1) (by decide)
  by_cases heq : rcLen = chainsCap
  · let newCap := max (2 * chainsCap.toNat) 4
    have hold_le : chainsCap.toNat * 104 ≤ max (2 * capMax) 4 * 104 := by omega
    have hnew_le : newCap * 104 ≤ max (2 * capMax) 4 * 104 := by
      have hc2 : newCap ≤ max (2 * capMax) 4 := by dsimp [newCap]; omega
      exact Nat.mul_le_mul_right 104 hc2
    have hg := phaseCredit_finishGrow_small hM chainsCap.toNat newCap 8 104 (by decide)
      (Nat.le_trans hold_le hSmall) (Nat.le_trans hnew_le hSmall)
    have himp : ∀ evs, DhCommitStep3Env chainsCap rcLen evs →
        ConcatEnv (· = finishGrowEvents chainsCap.toNat newCap 8 104)
          (· = rustDeallocEvents 33 1) evs := by
      rintro _ rfl
      exact ⟨growOne104Events chainsCap, rustDeallocEvents 33 1,
        by simp [dhCommitStep3Events, dhCommitStep3aEvents, heq],
        by simp [growOne104Events, newCap], rfl⟩
    exact ((hg.concat hd33).of_imp himp).mono (by omega) (by omega) (by omega) (by omega)
  · have himp : ∀ evs, DhCommitStep3Env chainsCap rcLen evs → evs = rustDeallocEvents 33 1 := by
      rintro _ rfl
      simp [dhCommitStep3Events, dhCommitStep3aEvents, heq]
    exact (hd33.of_imp himp).mono (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)

/-- Regime-uniform `PhaseCreditSpec` for `DhCommitStep3Env chainsCap rcLen` (`chainsCap ≤ capMax`). -/
theorem phaseCredit_dhCommitStep3_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {chainsCap rcLen : BitVec 64} {capMax : Nat}
    (hcap : chainsCap.toNat ≤ capMax) :
    let newBytes := max (2 * capMax) 4 * 104
    PhaseCreditSpec M (DhCommitStep3Env chainsCap rcLen)
      (2 * newBytes + 9539) (newBytes + 8195) (newBytes + 8195) newBytes := by
  dsimp only
  have hd33 := PhaseCreditSpec.rustDealloc_align16 M (req := 33) (al := 1) (by decide)
  by_cases heq : rcLen = chainsCap
  · let newCap := max (2 * chainsCap.toNat) 4
    have hnew_le : newCap * 104 ≤ max (2 * capMax) 4 * 104 := by
      have hc2 : newCap ≤ max (2 * capMax) 4 := by dsimp [newCap]; omega
      exact Nat.mul_le_mul_right 104 hc2
    have hg := phaseCredit_finishGrow_aff hM chainsCap.toNat newCap 8 104 (by decide)
    have himp : ∀ evs, DhCommitStep3Env chainsCap rcLen evs →
        ConcatEnv (· = finishGrowEvents chainsCap.toNat newCap 8 104)
          (· = rustDeallocEvents 33 1) evs := by
      rintro _ rfl
      exact ⟨growOne104Events chainsCap, rustDeallocEvents 33 1,
        by simp [dhCommitStep3Events, dhCommitStep3aEvents, heq],
        by simp [growOne104Events, newCap], rfl⟩
    exact ((hg.concat hd33).of_imp himp).mono (by omega) (by omega) (by omega) (by omega)
  · have himp : ∀ evs, DhCommitStep3Env chainsCap rcLen evs → evs = rustDeallocEvents 33 1 := by
      rintro _ rfl
      simp [dhCommitStep3Events, dhCommitStep3aEvents, heq]
    exact (hd33.of_imp himp).mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)

/-- Full Segment `S3` (`DhStep`) exact-order envelope: `DhCommitStep12Env` → `DhCommitStep3Env` →
`FreeOnlyEvs` (evicted 6th receiver chain drop + DH temp drops). -/
def W4DhStepS3Env (chainsCap rcLen : BitVec 64) : List AllocEvent → Prop :=
  SeqEnv DhCommitStep12Env
    (SeqEnv (DhCommitStep3Env chainsCap rcLen) FreeOnlyEvs)

/-- Small-regime `PhaseCreditSpec` for `W4DhStepS3Env chainsCap rcLen` (`chainsCap.toNat < 5`,
`832 ≤ smallMaxReq M`): `Δcum = 40018, Δlive = 0, Δpeak = 0, maxReq = 832`. -/
theorem phaseCredit_w4DhStepS3_lt5_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {chainsCap rcLen : BitVec 64}
    (hcap : chainsCap.toNat < 5)
    (hSmall832 : 832 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (W4DhStepS3Env chainsCap rcLen) 40018 0 0 832 := by
  have hSm33 : 33 ≤ HasFineReallocCredit.smallMaxReq M :=
    Nat.le_trans (by decide : 33 ≤ 832) hSmall832
  have h12 := phaseCredit_dhCommitStep12 hM hSm33
  have h3 := phaseCredit_seq_freeOnly hM
    (phaseCredit_dhCommitStep3_lt5_small hM (rcLen := rcLen) hcap hSmall832)
  exact (h12.seq h3).mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)

/-- Closed-form `ModelHyps M` affine bound for the `ConsumeMsgKey` `Vec<104>` doubling chain
(`IterSeqEnv GrowOne104Env (doublingCaps 4 k)`, e.g. `k = 10` for `≤ 2000` skipped keys where
`doublingCap 4 10 = 2048` and `2048 * 104 = 212,992 B`), cancelling intermediate `sc = 63`
buffers on realloc via `VecGrowCredit.phaseCreditSpec_growOne104_chain`. -/
theorem phaseCredit_w4CmkGrow104Chain_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {k : Nat} (hfit : doublingCap 4 k < 2 ^ 64) :
    let finalBytes := doublingCap 4 k * 104
    PhaseCreditSpec M (IterSeqEnv GrowOne104Env (doublingCaps 4 k))
      (4 * finalBytes + 9539 * k)
      (finalBytes + 8195)
      ((3 * finalBytes) / 2 + 16390)
      finalBytes := by
  dsimp only
  have hchain := phaseCreditSpec_growOne104_chain M hfit
  have hcum := rawVecCumOfSteps_le_affine hM 104 4 8 k
  have hmin : min (doublingCap 4 k * 104) (HasFineReallocCredit.smallMaxReq M) ≤
      doublingCap 4 k * 104 := Nat.min_le_left _ _
  have hlive := rawVecMaxLiveOfSteps_le_affine hM 104 4 k
  have hpeak := rawVecPeakOfSteps_le_affine hM 104 4 k
  refine hchain.mono (by omega) ?_ ?_ (Nat.le_refl _)
  · split at hlive <;> omega
  · split at hpeak <;> omega

/-! ## Segments `S7` (`VerifyMacWithAddressesEnv`), `S8` (`W4AesDecEnv`), & `S9` (`ApplyRatchet`) -/

/-- Regime-uniform `PhaseCreditSpec` for `ComputeMacEnv`: two sequential `33 B` `alloc ++ dealloc`
pairs give `Δlive = 0` under `ModelHyps M`. -/
theorem phaseCredit_computeMac_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M ComputeMacEnv 19210 0 8228 33 := by
  have hp := PhaseCreditSpec.tempAllocFree_aff hM (req := 33) (al := 1) (by decide)
  have h2 := hp.concat hp
  have himp : ∀ evs, ComputeMacEnv evs →
      ConcatEnv
        (ConcatEnv (· = rustAllocEvents 33 1) (· = rustDeallocEvents 33 1))
        (ConcatEnv (· = rustAllocEvents 33 1) (· = rustDeallocEvents 33 1)) evs := by
    rintro _ rfl
    exact ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1,
      publicKeySerializeEvents ++ rustDeallocEvents 33 1, rfl,
      ⟨_, _, rfl, rfl, rfl⟩, ⟨_, _, rfl, rfl, rfl⟩⟩
  exact (h2.of_imp himp).mono (by decide) (Nat.le_refl 0) (by decide) (Nat.le_refl 33)

/-- Small-regime `PhaseCreditSpec` for `ComputeMacEnv` (`33 ≤ smallMaxReq M`):
`Δcum = 19210, Δlive = 0, Δpeak = 0, maxReq = 33`. -/
theorem phaseCredit_computeMac_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hSmall33 : 33 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M ComputeMacEnv 19210 0 0 33 := by
  have ha := PhaseCreditSpec.rustAlloc_small_any hM (req := 33) (al := 1) (by decide) hSmall33
  have hsa := hM.smallAlloc_le hSmall33
  have hd := PhaseCreditSpec.rustDealloc_align16 M (req := 33) (al := 1) (by decide)
  have hp := ha.concat hd
  have h2 := hp.concat hp
  have himp : ∀ evs, ComputeMacEnv evs →
      ConcatEnv
        (ConcatEnv (· = rustAllocEvents 33 1) (· = rustDeallocEvents 33 1))
        (ConcatEnv (· = rustAllocEvents 33 1) (· = rustDeallocEvents 33 1)) evs := by
    rintro _ rfl
    exact ⟨publicKeySerializeEvents ++ rustDeallocEvents 33 1,
      publicKeySerializeEvents ++ rustDeallocEvents 33 1, rfl,
      ⟨_, _, rfl, rfl, rfl⟩, ⟨_, _, rfl, rfl, rfl⟩⟩
  exact (h2.of_imp himp).mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)

/-- Regime-uniform `PhaseCreditSpec` for `VerifyMacWithAddressesEnv F parse x` (`S7`):
every temporary `33 B` or `36 B` buffer is paired with its immediate `rustDeallocEvents`, giving
`Δlive = 0` under `ModelHyps M`. -/
theorem phaseCredit_verifyMacWithAddresses_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (F : ShaCompress) (parse : UuidParser)
    (x : VerifyMacWithAddressesGhost) :
    PhaseCreditSpec M (VerifyMacWithAddressesEnv F parse x) 28821 0 8231 36 := by
  have hcm := phaseCredit_computeMac_aff hM
  have h36 := PhaseCreditSpec.tempAllocFree_aff hM (req := 36) (al := 1) (by decide)
  unfold VerifyMacWithAddressesEnv verifyMacWithAddressesEvents
  dsimp only
  split
  · have hc := hcm.concat h36
    have himp : ∀ evs,
        evs = computeMacEvents ++ (rustAllocEvents 36 1 ++ rustDeallocEvents 36 1) →
        ConcatEnv ComputeMacEnv
          (ConcatEnv (· = rustAllocEvents 36 1) (· = rustDeallocEvents 36 1)) evs := by
      rintro _ rfl
      exact ⟨computeMacEvents, _, rfl, rfl, ⟨_, _, rfl, rfl, rfl⟩⟩
    exact (hc.of_imp himp).mono (by decide) (Nat.le_refl 0) (by decide) (by decide)
  · exact hcm.mono (by decide) (Nat.le_refl 0) (by decide) (by decide)

/-- Small-regime `PhaseCreditSpec` for `VerifyMacWithAddressesEnv F parse x` (`36 ≤ smallMaxReq M`):
`Δcum = 28821, Δlive = 0, Δpeak = 0, maxReq = 36`. -/
theorem phaseCredit_verifyMacWithAddresses_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (F : ShaCompress) (parse : UuidParser)
    (x : VerifyMacWithAddressesGhost)
    (hSmall36 : 36 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (VerifyMacWithAddressesEnv F parse x) 28821 0 0 36 := by
  have hSm33 : 33 ≤ HasFineReallocCredit.smallMaxReq M :=
    Nat.le_trans (by decide : 33 ≤ 36) hSmall36
  have hcm := phaseCredit_computeMac_small hM hSm33
  have ha36 := PhaseCreditSpec.rustAlloc_small_any hM (req := 36) (al := 1) (by decide) hSmall36
  have hsa36 := hM.smallAlloc_le hSmall36
  have hd36 := PhaseCreditSpec.rustDealloc_align16 M (req := 36) (al := 1) (by decide)
  unfold VerifyMacWithAddressesEnv verifyMacWithAddressesEvents
  dsimp only
  split
  · have hc := hcm.concat (ha36.concat hd36)
    have himp : ∀ evs,
        evs = computeMacEvents ++ (rustAllocEvents 36 1 ++ rustDeallocEvents 36 1) →
        ConcatEnv ComputeMacEnv
          (ConcatEnv (· = rustAllocEvents 36 1) (· = rustDeallocEvents 36 1)) evs := by
      rintro _ rfl
      exact ⟨computeMacEvents, _, rfl, rfl, ⟨_, _, rfl, rfl, rfl⟩⟩
    exact (hc.of_imp himp).mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
  · exact hcm.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)

/-- Capped AES-CBC decryption (`S8`) envelope on ciphertext of length `ctLen ≤ ctCap`:
either `[]` (pre-alloc length/block-multiple check fails), `rustAllocEvents ctLen 1` (plaintext
buffer returned on `.some`), or `rustAllocEvents ctLen 1 ++ rustDeallocEvents ctLen 1` (buffer
dropped on PKCS#7 unpad failure). -/
def W4AesDecEnv (ctCap : Nat) (evs : List AllocEvent) : Prop :=
  evs = [] ∨
  ∃ ctLen : Nat, ctLen ≤ ctCap ∧
    (evs = rustAllocEvents ctLen 1 ∨
     evs = rustAllocEvents ctLen 1 ++ rustDeallocEvents ctLen 1)

/-- Failed-AES-CBC (`aesOpt = none`) specialization of `W4AesDecEnv ctCap`, where any allocated
output buffer is dropped before returning `.error`, cancelling `sc = 63` across all regimes. -/
def W4AesDecErrEnv (ctCap : Nat) (evs : List AllocEvent) : Prop :=
  evs = [] ∨
  ∃ ctLen : Nat, ctLen ≤ ctCap ∧
    evs = rustAllocEvents ctLen 1 ++ rustDeallocEvents ctLen 1

/-- Regime-uniform `PhaseCreditSpec` for `W4AesDecEnv ctCap`. -/
theorem phaseCredit_w4AesDec_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (ctCap : Nat) :
    PhaseCreditSpec M (W4AesDecEnv ctCap)
      (2 * ctCap + 9539) (ctCap + 8195) (ctCap + 8195) ctCap := by
  have hnil : PhaseCreditSpec M (· = [])
      (2 * ctCap + 9539) (ctCap + 8195) (ctCap + 8195) ctCap :=
    (PhaseCreditSpec.nil M).mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  have hex : PhaseCreditSpec M
      (fun evs => ∃ ctLen : Nat, ctLen ≤ ctCap ∧
        (evs = rustAllocEvents ctLen 1 ∨
         evs = rustAllocEvents ctLen 1 ++ rustDeallocEvents ctLen 1))
      (2 * ctCap + 9539) (ctCap + 8195) (ctCap + 8195) ctCap := by
    refine phaseCredit_exists_le fun ctLen hlen => ?_
    have ha : PhaseCreditSpec M (· = rustAllocEvents ctLen 1)
        (2 * ctCap + 9539) (ctCap + 8195) (ctCap + 8195) ctCap :=
      (PhaseCreditSpec.rustAlloc_aff hM (req := ctLen) (al := 1) (by decide)).mono
        (by omega) (by omega) (by omega) hlen
    have ht : PhaseCreditSpec M (· = rustAllocEvents ctLen 1 ++ rustDeallocEvents ctLen 1)
        (2 * ctCap + 9539) (ctCap + 8195) (ctCap + 8195) ctCap :=
      ((PhaseCreditSpec.tempAllocFree_aff hM (req := ctLen) (al := 1) (by decide)).of_imp
        fun _ h => ⟨_, _, h, rfl, rfl⟩).mono
        (by omega) (Nat.zero_le _) (by omega) hlen
    exact (ha.or ht).mono
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
  exact (hnil.or hex).mono
    (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)

/-- Regime-uniform `Δlive = 0` cancellation for `W4AesDecErrEnv ctCap`: even when
`ctCap > smallMaxReq M`, failed AES-CBC decryption leaves `0` live `sc = 63` bytes. -/
theorem phaseCredit_w4AesDecErr_cancel {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (ctCap : Nat) :
    PhaseCreditSpec M (W4AesDecErrEnv ctCap)
      (2 * ctCap + 9539) 0 (ctCap + 8195) ctCap := by
  have hnil : PhaseCreditSpec M (· = [])
      (2 * ctCap + 9539) 0 (ctCap + 8195) ctCap :=
    (PhaseCreditSpec.nil M).mono (Nat.zero_le _) (Nat.le_refl 0) (Nat.zero_le _) (Nat.zero_le _)
  have hex : PhaseCreditSpec M
      (fun evs => ∃ ctLen : Nat, ctLen ≤ ctCap ∧
        evs = rustAllocEvents ctLen 1 ++ rustDeallocEvents ctLen 1)
      (2 * ctCap + 9539) 0 (ctCap + 8195) ctCap := by
    refine phaseCredit_exists_le fun ctLen hlen => ?_
    exact ((PhaseCreditSpec.tempAllocFree_aff hM (req := ctLen) (al := 1) (by decide)).of_imp
      fun _ h => ⟨_, _, h, rfl, rfl⟩).mono
      (by omega) (Nat.le_refl 0) (by omega) hlen
  exact (hnil.or hex).mono
    (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)

/-- Segment `S9` (`ApplyRatchet` + `set_session_state`) exact-order envelope: `≤ 6` small ratchet
key/state writes (`≤ 34 B` each) followed by `FreeOnlyEvs` (`set_session_state` old-state drop). -/
def W4ApplySetStateEnv : List AllocEvent → Prop :=
  SeqEnv (W4BoundedEvs 6 34) FreeOnlyEvs

/-- Small-regime `PhaseCreditSpec` for `W4ApplySetStateEnv` (`34 ≤ smallMaxReq M`):
`Δcum = 57642, Δlive = 0, Δpeak = 0, maxReq = 34`. -/
theorem phaseCredit_w4ApplySetState_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hSmall34 : 34 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M W4ApplySetStateEnv 57642 0 0 34 :=
  (phaseCredit_seq_freeOnly hM (phaseCredit_w4BoundedEvs_small hM 6 34 hSmall34)).mono
    (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 34)

/-! ## Exact-Order Seam Composition (`FromS8GenEnv` → … → `FromS1GenEnv`) -/

section SeamComposition

variable {M : AllocCostModel} [HasFineReallocCredit M]
  {C : Crypto} {parse : UuidParser} {S : SpqrModel}
  {aesOpt : MessageKeys → SignalMessage → Option (List (BitVec 8))}
  {s1OkEnv : TryDecryptGhost → List AllocEvent → Prop}
  {s3Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
  {s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
    List AllocEvent → Prop}
  {s5Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
  {s6Env : MessageKeyGenerator → List AllocEvent → Prop}
  {s7Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
    List (BitVec 8) → List AllocEvent → Prop}
  {s8Env : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop}
  {s9Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
    SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}

/-- Seam `S8 → S9` composition on `RootBudgetAux.FromS8GenEnv`. -/
theorem phaseCredit_fromS8GenEnv (hM : ModelHyps M)
    {c8 l8 p8 r8 c9 l9 p9 r9 : Nat}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {mks : MessageKeys} {newPqrState : List (BitVec 8)}
    (hS8 : PhaseCreditSpec M (s8Env x mks newPqrState) c8 l8 p8 r8)
    (hS9 : PhaseCreditSpec M (s9Env x trG tr st1 newPqrState) c9 l9 p9 r9) :
    PhaseCreditSpec M (FromS8GenEnv aesOpt s8Env s9Env x trG tr st1 mks newPqrState)
      (c8 + c9) (l8 + l9) (max p8 (l8 + p9)) (max r8 r9) := by
  unfold FromS8GenEnv
  cases aesOpt mks x.msg with
  | some _ => exact hS8.seq hS9
  | none =>
    exact (phaseCredit_seq_freeOnly hM hS8).mono
      (by omega) (by omega) (Nat.le_max_left _ _) (Nat.le_max_left _ _)

/-- Seam `S7 → S9` composition on `RootBudgetAux.FromS7GenEnv`. -/
theorem phaseCredit_fromS7GenEnv (hM : ModelHyps M)
    {c7 l7 p7 r7 c8 l8 p8 r8 c9 l9 p9 r9 : Nat}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {mks : MessageKeys} {newPqrState : List (BitVec 8)}
    (hS7 : PhaseCreditSpec M (s7Env x tr mks newPqrState) c7 l7 p7 r7)
    (hS8 : PhaseCreditSpec M (s8Env x mks newPqrState) c8 l8 p8 r8)
    (hS9 : PhaseCreditSpec M (s9Env x trG tr st1 newPqrState) c9 l9 p9 r9) :
    PhaseCreditSpec M (FromS7GenEnv C parse aesOpt s7Env s8Env s9Env x trG tr st1 mks newPqrState)
      (c7 + (c8 + c9))
      (l7 + (l8 + l9))
      (max p7 (l7 + max p8 (l8 + p9)))
      (max r7 (max r8 r9)) := by
  unfold FromS7GenEnv
  split
  · exact hS7.seq (phaseCredit_fromS8GenEnv hM hS8 hS9)
  · exact (phaseCredit_seq_freeOnly hM hS7).mono
      (by omega) (by omega) (Nat.le_max_left _ _) (Nat.le_max_left _ _)

/-- Seam `S6 → S9` composition on `RootBudgetAux.FromS6GenEnv`. -/
theorem phaseCredit_fromS6GenEnv (hM : ModelHyps M)
    {c6 l6 p6 r6 c7 l7 p7 r7 c8 l8 p8 r8 c9 l9 p9 r9 : Nat}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {mkg : MessageKeyGenerator}
    {newPqrState : List (BitVec 8)} {pqrKey : Salt}
    (hS6 : PhaseCreditSpec M (s6Env mkg) c6 l6 p6 r6)
    (hS7 : ∀ mks, PhaseCreditSpec M (s7Env x tr mks newPqrState) c7 l7 p7 r7)
    (hS8 : ∀ mks, PhaseCreditSpec M (s8Env x mks newPqrState) c8 l8 p8 r8)
    (hS9 : PhaseCreditSpec M (s9Env x trG tr st1 newPqrState) c9 l9 p9 r9) :
    PhaseCreditSpec M
      (FromS6GenEnv C parse aesOpt s6Env s7Env s8Env s9Env x trG tr st1 mkg newPqrState pqrKey)
      (c6 + (c7 + (c8 + c9)))
      (l6 + (l7 + (l8 + l9)))
      (max p6 (l6 + max p7 (l7 + max p8 (l8 + p9))))
      (max r6 (max r7 (max r8 r9))) := by
  unfold FromS6GenEnv
  exact hS6.seq (phaseCredit_fromS7GenEnv hM (hS7 _) (hS8 _) hS9)

/-- Seam `S5 → S9` composition on `RootBudgetAux.FromS5GenEnv`. -/
theorem phaseCredit_fromS5GenEnv (hM : ModelHyps M)
    {c5 l5 p5 r5 c6 l6 p6 r6 c7 l7 p7 r7 c8 l8 p8 r8 c9 l9 p9 r9 : Nat}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {mkg : MessageKeyGenerator}
    (hS5 : PhaseCreditSpec M (s5Env x tr) c5 l5 p5 r5)
    (hS6 : PhaseCreditSpec M (s6Env mkg) c6 l6 p6 r6)
    (hS7 : ∀ mks pqr, PhaseCreditSpec M (s7Env x tr mks pqr) c7 l7 p7 r7)
    (hS8 : ∀ mks pqr, PhaseCreditSpec M (s8Env x mks pqr) c8 l8 p8 r8)
    (hS9 : ∀ pqr, PhaseCreditSpec M (s9Env x trG tr st1 pqr) c9 l9 p9 r9) :
    PhaseCreditSpec M
      (FromS5GenEnv C parse S aesOpt s5Env s6Env s7Env s8Env s9Env x trG tr st1 mkg)
      (c5 + (c6 + (c7 + (c8 + c9))))
      (l5 + (l6 + (l7 + (l8 + l9))))
      (max p5 (l5 + max p6 (l6 + max p7 (l7 + max p8 (l8 + p9)))))
      (max r5 (max r6 (max r7 (max r8 r9)))) := by
  unfold FromS5GenEnv
  cases S.recv tr.pqrState x.msg.pqRatchet with
  | ok pair =>
    exact hS5.seq (phaseCredit_fromS6GenEnv hM hS6
      (fun mks => hS7 mks pair.1) (fun mks => hS8 mks pair.1) (hS9 pair.1))
  | error _ =>
    exact (phaseCredit_seq_freeOnly hM hS5).mono
      (by omega) (by omega) (Nat.le_max_left _ _) (Nat.le_max_left _ _)

/-- Seam `S4 → S9` composition on `RootBudgetAux.FromS4GenEnv` (`FromS4Env` / `FromS4FnEnv`). -/
theorem phaseCredit_fromS4GenEnv (hM : ModelHyps M)
    {c4 l4 p4 r4 c5 l5 p5 r5 c6 l6 p6 r6 c7 l7 p7 r7 c8 l8 p8 r8 c9 l9 p9 r9 : Nat}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey}
    (hS4 : PhaseCreditSpec M (s4Env x trG tr ck) c4 l4 p4 r4)
    (hS5 : ∀ tr', PhaseCreditSpec M (s5Env x tr') c5 l5 p5 r5)
    (hS6 : ∀ mkg, PhaseCreditSpec M (s6Env mkg) c6 l6 p6 r6)
    (hS7 : ∀ tr' mks pqr, PhaseCreditSpec M (s7Env x tr' mks pqr) c7 l7 p7 r7)
    (hS8 : ∀ mks pqr, PhaseCreditSpec M (s8Env x mks pqr) c8 l8 p8 r8)
    (hS9 : ∀ trG' tr' pqr, PhaseCreditSpec M (s9Env x trG' tr' st1 pqr) c9 l9 p9 r9) :
    PhaseCreditSpec M
      (FromS4GenEnv C parse S aesOpt s4Env s5Env s6Env s7Env s8Env s9Env x trG tr st1 ck)
      (c4 + (c5 + (c6 + (c7 + (c8 + c9)))))
      (l4 + (l5 + (l6 + (l7 + (l8 + l9)))))
      (max p4 (l4 + max p5 (l5 + max p6 (l6 + max p7 (l7 + max p8 (l8 + p9))))))
      (max r4 (max r5 (max r6 (max r7 (max r8 r9))))) := by
  unfold FromS4GenEnv
  split
  · next mkg r2 _ =>
    exact hS4.seq
      (phaseCredit_fromS5GenEnv hM (hS5 _) (hS6 mkg) (hS7 _) hS8 (hS9 trG _))
  · exact (phaseCredit_seq_freeOnly hM hS4).mono
      (by omega) (by omega) (Nat.le_max_left _ _) (Nat.le_max_left _ _)

/-- Seam `S3 → S9` composition on `RootBudgetAux.FromS3GenEnv`. -/
theorem phaseCredit_fromS3GenEnv (hM : ModelHyps M)
    {c3 l3 p3 r3 c4 l4 p4 r4 c5 l5 p5 r5 c6 l6 p6 r6 c7 l7 p7 r7 c8 l8 p8 r8 c9 l9 p9 r9 : Nat}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))}
    (hS3 : PhaseCreditSpec M (s3Env x trG tr) c3 l3 p3 r3)
    (hS4 : ∀ trG' tr' ck, PhaseCreditSpec M (s4Env x trG' tr' ck) c4 l4 p4 r4)
    (hS5 : ∀ tr', PhaseCreditSpec M (s5Env x tr') c5 l5 p5 r5)
    (hS6 : ∀ mkg, PhaseCreditSpec M (s6Env mkg) c6 l6 p6 r6)
    (hS7 : ∀ tr' mks pqr, PhaseCreditSpec M (s7Env x tr' mks pqr) c7 l7 p7 r7)
    (hS8 : ∀ mks pqr, PhaseCreditSpec M (s8Env x mks pqr) c8 l8 p8 r8)
    (hS9 : ∀ trG' tr' pqr, PhaseCreditSpec M (s9Env x trG' tr' st1 pqr) c9 l9 p9 r9) :
    PhaseCreditSpec M
      (FromS3GenEnv C parse S aesOpt s3Env s4Env s5Env s6Env s7Env s8Env s9Env x trG tr st1)
      (c3 + (c4 + (c5 + (c6 + (c7 + (c8 + c9))))))
      (l3 + (l4 + (l5 + (l6 + (l7 + (l8 + l9))))))
      (max p3 (l3 + max p4 (l4 + max p5 (l5 + max p6 (l6 + max p7 (l7 + max p8 (l8 + p9)))))))
      (max r3 (max r4 (max r5 (max r6 (max r7 (max r8 r9)))))) := by
  unfold FromS3GenEnv
  split
  · next ck r1 _ =>
    exact hS3.seq (phaseCredit_fromS4GenEnv hM (hS4 _ _ ck) hS5 hS6 hS7 hS8 hS9)
  · exact (phaseCredit_seq_freeOnly hM hS3).mono
      (by omega) (by omega) (Nat.le_max_left _ _) (Nat.le_max_left _ _)

/-- Seam `S2 → S9` composition on `RootBudgetAux.FromS2GenEnv` (either `some ck` skips `S3`,
`none` runs `S3`, or `.error` emits `FreeOnlyEvs`). -/
theorem phaseCredit_fromS2GenEnv (hM : ModelHyps M)
    {c3 l3 p3 r3 c4 l4 p4 r4 c5 l5 p5 r5 c6 l6 p6 r6 c7 l7 p7 r7 c8 l8 p8 r8 c9 l9 p9 r9 : Nat}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))}
    (hS3 : PhaseCreditSpec M (s3Env x trG tr) c3 l3 p3 r3)
    (hS4 : ∀ trG' tr' ck, PhaseCreditSpec M (s4Env x trG' tr' ck) c4 l4 p4 r4)
    (hS5 : ∀ tr', PhaseCreditSpec M (s5Env x tr') c5 l5 p5 r5)
    (hS6 : ∀ mkg, PhaseCreditSpec M (s6Env mkg) c6 l6 p6 r6)
    (hS7 : ∀ tr' mks pqr, PhaseCreditSpec M (s7Env x tr' mks pqr) c7 l7 p7 r7)
    (hS8 : ∀ mks pqr, PhaseCreditSpec M (s8Env x mks pqr) c8 l8 p8 r8)
    (hS9 : ∀ trG' tr' pqr, PhaseCreditSpec M (s9Env x trG' tr' st1 pqr) c9 l9 p9 r9) :
    PhaseCreditSpec M
      (FromS2GenEnv C parse S aesOpt s3Env s4Env s5Env s6Env s7Env s8Env s9Env x trG tr st1)
      (c3 + (c4 + (c5 + (c6 + (c7 + (c8 + c9))))))
      (l3 + (l4 + (l5 + (l6 + (l7 + (l8 + l9))))))
      (max p3 (l3 + max p4 (l4 + max p5 (l5 + max p6 (l6 + max p7 (l7 + max p8 (l8 + p9)))))))
      (max r3 (max r4 (max r5 (max r6 (max r7 (max r8 r9)))))) := by
  unfold FromS2GenEnv
  split
  · next ck _ =>
    exact (phaseCredit_fromS4GenEnv hM (hS4 trG tr ck) hS5 hS6 hS7 hS8 hS9).mono
      (by omega) (by omega) (by omega) (Nat.le_max_right _ _)
  · exact phaseCredit_fromS3GenEnv hM hS3 hS4 hS5 hS6 hS7 hS8 hS9
  · exact (PhaseCreditSpec.freeOnly_of_hyps hM).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)

/-- Full `try_decrypt_pq` seam composition bounding `RootBudgetAux.FromS1GenEnv` (and hence
`FromS1Env` and `FromS1FnEnv`) across segments `S1..S9` in exact binary call order. -/
theorem phaseCredit_fromS1GenEnv (hM : ModelHyps M)
    {c1 l1 p1 r1 c3 l3 p3 r3 c4 l4 p4 r4 c5 l5 p5 r5 c6 l6 p6 r6
     c7 l7 p7 r7 c8 l8 p8 r8 c9 l9 p9 r9 : Nat}
    {x : TryDecryptGhost}
    (hS1 : PhaseCreditSpec M (s1OkEnv x) c1 l1 p1 r1)
    (hS3 : ∀ trG' tr', PhaseCreditSpec M (s3Env x trG' tr') c3 l3 p3 r3)
    (hS4 : ∀ trG' tr' ck, PhaseCreditSpec M (s4Env x trG' tr' ck) c4 l4 p4 r4)
    (hS5 : ∀ tr', PhaseCreditSpec M (s5Env x tr') c5 l5 p5 r5)
    (hS6 : ∀ mkg, PhaseCreditSpec M (s6Env mkg) c6 l6 p6 r6)
    (hS7 : ∀ tr' mks pqr, PhaseCreditSpec M (s7Env x tr' mks pqr) c7 l7 p7 r7)
    (hS8 : ∀ mks pqr, PhaseCreditSpec M (s8Env x mks pqr) c8 l8 p8 r8)
    (hS9 : ∀ trG' tr' st1 pqr, PhaseCreditSpec M (s9Env x trG' tr' st1 pqr) c9 l9 p9 r9) :
    PhaseCreditSpec M
      (FromS1GenEnv C parse S aesOpt s1OkEnv s3Env s4Env s5Env s6Env s7Env s8Env s9Env x)
      (c1 + (c3 + (c4 + (c5 + (c6 + (c7 + (c8 + c9)))))))
      (l1 + (l3 + (l4 + (l5 + (l6 + (l7 + (l8 + l9)))))))
      (max p1 (l1 + max p3 (l3 + max p4 (l4 + max p5 (l5 +
        max p6 (l6 + max p7 (l7 + max p8 (l8 + p9))))))))
      (max r1 (max r3 (max r4 (max r5 (max r6 (max r7 (max r8 r9))))))) := by
  unfold FromS1GenEnv
  split
  · exact (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  · next tr0 st1 _ =>
    exact hS1.seq (phaseCredit_fromS2GenEnv hM (hS3 _ tr0) hS4 hS5 hS6 hS7 hS8
      (fun trG' tr' pqr => hS9 trG' tr' st1 pqr))

end SeamComposition

/-! ## Failed-Trial Candidate Clone + `try_decrypt_pq` + Drop + `GrowOneSpeEnv` Cancellation -/

/-- Exact-order failed `try_decrypt_pq` trial on a cloned candidate session (`CloneEnv`):
`((CloneEnv ++ TrialFailEnv) ++ DropCloneEnv)` followed by `SeqEnv (GrowOneSpeEnv 0#64) FreeOnlyEvs`
(pushing `SignalProtocolError` into the `errors` `Vec` and dropping error temporaries). -/
def W4TryDecryptCloneFailEnv
    (CloneEnv TrialFailEnv DropCloneEnv : List AllocEvent → Prop) : List AllocEvent → Prop :=
  SeqEnv
    (ConcatEnv (ConcatEnv CloneEnv TrialFailEnv) DropCloneEnv)
    (SeqEnv (GrowOneSpeEnv 0#64) FreeOnlyEvs)

/-- `sc = 63` cancellation for a failed cloned-session `try_decrypt_pq` trial: when
`CloneEnv ... DropCloneEnv` cancels the candidate session's `sc = 63` buffers (`hCloneCancel`),
`TrialFailEnv` has `Δlive = 0`, and `192 ≤ smallMaxReq M`, the failed trial leaves `Δlive = 0`. -/
theorem phaseCredit_w4TryDecryptCloneFail_cancel {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    {CloneEnv TrialFailEnv DropCloneEnv : List AllocEvent → Prop}
    {c_cl p_cl r_cl c_tr p_tr r_tr : Nat}
    (hSmall192 : 192 ≤ HasFineReallocCredit.smallMaxReq M)
    (hTrialFail : PhaseCreditSpec M TrialFailEnv c_tr 0 p_tr r_tr)
    (hCloneCancel : PhaseCreditSpec M TrialFailEnv c_tr 0 p_tr r_tr →
      PhaseCreditSpec M (ConcatEnv (ConcatEnv CloneEnv TrialFailEnv) DropCloneEnv)
        (c_cl + c_tr) 0 (p_cl + p_tr) (max r_cl r_tr)) :
    PhaseCreditSpec M (W4TryDecryptCloneFailEnv CloneEnv TrialFailEnv DropCloneEnv)
      (c_cl + c_tr + 9923)
      0
      (p_cl + p_tr)
      (max (max r_cl r_tr) 192) := by
  have hCancel := hCloneCancel hTrialFail
  have hSpe := phaseCredit_seq_freeOnly hM (phaseCredit_growOneSpeZero_small hM hSmall192)
  exact (hCancel.seq hSpe).mono (by omega) (by omega) (by omega) (Nat.le_refl _)

end LibsignalBinary.Proofs.PeakBudget.W4TryDecryptPqPeak
