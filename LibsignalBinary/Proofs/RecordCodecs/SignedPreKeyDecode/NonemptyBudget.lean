/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.Nonempty
public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.Defs
public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.DefsBudget
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.Epilogue
public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.EpilogueBudget
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.Loop
public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.LoopBudget

/-!
# Budget-Threaded Full-Domain and Non-Empty `SignedPreKeyRecordStructure::decode`

`RustCliAllocBudget`-threaded relocatable `[LibsignalPlacement]` proofs of
`signedDecodeActualPlacedSpec` (all inputs) and `signedDecodeNonemptyPlacedSpec` (`x.bytes ≠ []`)
on Block `562`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.NonemptyBudget

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecs
open CryptoVerification
open CryptoVerification.RecordCodecs.Placed
open LibsignalBinary.Heap
open CryptoVerification.RecordCodecsBinary (DecodeGhost signedDecodeResultAt signedDecodeStack)
open CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers (spkActualDecode spkActualDecode_of_nonempty)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget (SignedHooksPlaced SignedPortDepsPlaced SpkDecodeEnv SpkLoopEnv signedDecodePlacedSpec signedDecodeRawSpec)
open LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.DefsBudget (noPanicQp)
open LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.EpilogueBudget (converge_656_to_ret_placed_wp spkRetPostPlaced)
open LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.LoopBudget (prologue_0_to_converge_placed_wp)

/-- Image-free raw budget-threaded contract satisfied by `<SignedPreKeyRecordStructure as Message>::decode::<&[u8]>`
across all inputs (`x.bytes = []` returns `none`; `x.bytes ≠ []` returns `decode x.bytes`). -/
def signedDecodeActualRawSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DecodeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.bytesA ∧
      (s.readReg64 .x2).toNat = x.bytes.length ∧ x.bytes.length < 2 ^ 32 ∧
      FitsEnv M lim st (SpkLoopEnv (2 * x.bytes.length + 3) x.bytes.length)⌝ ∗
      (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗ stackAt s.sp signedDecodeStack ∗
      A.pool lim st s
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ evs : List AllocEvent, ⌜SpkDecodeEnv x.bytes.length evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      signedDecodeResultAt A.repAlloc x.ret (spkActualDecode x.bytes) ∗
      (x.bytesA ↦ₛ x.bytes) ∗ stackAt s0.sp signedDecodeStack

/-- Relocatable `[CryptoVerification.LibsignalPlacement]` contract of `<SignedPreKeyRecordStructure as Message>::decode::<&[u8]>`
(block `562`) across all inputs (`[]` and `b :: bs`). -/
abbrev signedDecodeActualPlacedSpec [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (DecodeGhost × M.σ) :=
  CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (signedDecodeActualRawSpec A lim)

/-- Image-free raw `signedDecodeRawSpec` restricted to `x.bytes ≠ []`. -/
def signedDecodeNonemptyRawSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DecodeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.bytesA ∧
      (s.readReg64 .x2).toNat = x.bytes.length ∧ x.bytes.length < 2 ^ 32 ∧
      x.bytes ≠ [] ∧
      FitsEnv M lim st (SpkLoopEnv (2 * x.bytes.length + 3) x.bytes.length)⌝ ∗
      (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗ stackAt s.sp signedDecodeStack ∗
      A.pool lim st s
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ evs : List AllocEvent, ⌜SpkDecodeEnv x.bytes.length evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      signedDecodeResultAt A.repAlloc x.ret (SignedPreKeyRecordStructure.decode x.bytes) ∗
      (x.bytesA ↦ₛ x.bytes) ∗ stackAt s0.sp signedDecodeStack

/-- Relocatable `[CryptoVerification.LibsignalPlacement]` contract of `<SignedPreKeyRecordStructure as Message>::decode::<&[u8]>`
(block `562`) restricted to `x.bytes ≠ []`. -/
abbrev signedDecodeNonemptyPlacedSpec [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (DecodeGhost × M.σ) :=
  CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (signedDecodeNonemptyRawSpec A lim)

/-- Complete 206-instruction relocatable verification: block `562` meets
`signedDecodeActualPlacedSpec A lim` across all inputs (`x.bytes.length < 2 ^ 32`). -/
theorem signedDecodeActual_placed_ok_of_deps [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hH : SignedHooksPlaced M A lim H) (d : SignedPortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_562 H) (blkPl_562).base (signedDecodeActualPlacedSpec A lim) := by
  refine subroutine_ok.of_codeLoaded fun (x, st) R s0 hpc hrun hpre hsp hL => ?_
  obtain ⟨hcrl, hpre_raw⟩ := CryptoVerification.LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  dsimp only [signedDecodeActualRawSpec] at hpre_raw
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre_raw
  rcases hpre_raw with ⟨⟨hx0, hx1, hx2_nat, hlt, hFit⟩, hmem⟩
  have hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 x.bytes.length := by
    rw [← hx2_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hmem' : s0.mem ⊨
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗
        stackAt s0.sp signedDecodeStack ∗ A.pool lim st s0) ∗ R := by
    ac_nf at hmem ⊢
  have h1 := prologue_0_to_converge_placed_wp hH d (x := x) (st := st) hlt hpc hrun hsp hcrl hx0 hx1 hx2 hFit
  have hfull : Wire.SepWPp (lsProg_562 H) (s0.readReg64 .x30) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗
        stackAt s0.sp signedDecodeStack ∗ A.pool lim st s0)
      (spkRetPostPlaced A lim st (SpkDecodeEnv x.bytes.length) s0 x (spkActualDecode x.bytes))
      (noPanicQp s0) := by
    refine Wire.SepWPp.bind h1 ?_
    intro sm Pm hpcm hrunm ⟨hstm, evsL, hevsL, hentm⟩
    exact Wire.SepWPp.mono_pre hentm
      (converge_656_to_ret_placed_wp hH (x := x) (out := spkActualDecode x.bytes) hevsL hstm hpcm hrunm)
  obtain ⟨sf, hsteps, hex⟩ := hfull R hmem' hL
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hex with ⟨hpc_f, hrun_f, Pf, hmf, ⟨hsp_f, hcs_f, hent_f⟩, hv_f⟩ | ⟨_, _, _, hpan⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨⟨hpc_f, hsp_f, hrun_f⟩, ⟨hsp_f, hcs_f hv_f⟩, ?_⟩
    dsimp only [signedDecodeActualPlacedSpec, CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded, signedDecodeActualRawSpec]
    exact Satisfies.mono (sepConj_mono_left hent_f) hmf
  · exact hpan.elim
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Relocatable outcome bridge from `signedDecodePlacedSpec.pre` for any non-empty input `x.bytes ≠ []`. -/
theorem signedDecode_placed_outcome_of_nonempty [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hH : SignedHooksPlaced M A lim H) (d : SignedPortDepsPlaced M A lim H)
    {x : DecodeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    (hne : x.bytes ≠ [])
    (hpc : s0.pc = (blkPl_562).base)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (signedDecodePlacedSpec A lim).pre (x, st) s0 ∗ R)
    (hsp : s0.spAligned = true) :
    reaches_outcome (lsProg_562 H) (signedDecodePlacedSpec A lim) (x, st) R s0 s0 := by
  have hpre_act : s0.mem ⊨ (signedDecodeActualPlacedSpec A lim).pre (x, st) s0 ∗ R := by
    obtain ⟨hcrl, hraw⟩ := CryptoVerification.LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
    dsimp only [signedDecodeRawSpec] at hraw
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hraw
    rcases hraw with ⟨⟨hx0, hx1, hx2, _hpos, hlt, hFit⟩, hmem⟩
    have hact_raw : s0.mem ⊨ (signedDecodeActualRawSpec A lim).pre (x, st) s0 ∗ R := by
      dsimp only [signedDecodeActualRawSpec]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2, hlt, hFit⟩, hmem⟩
    dsimp only [signedDecodeActualPlacedSpec, CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded]
    rw [show ((signedDecodeActualRawSpec A lim).pre (x, st) s0 ∗ ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ R =
      ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ ((signedDecodeActualRawSpec A lim).pre (x, st) s0 ∗ R) by ac_rfl,
      satisfies_pure_sepConj]
    exact ⟨hcrl, hact_raw⟩
  refine (signedDecodeActual_placed_ok_of_deps hH d).mono_outcome (x, st) R s0 hpc hrun hpre_act hsp ?_
  intro sf hout
  dsimp only [SubroutineOutcome, signedDecodeActualPlacedSpec, signedDecodePlacedSpec,
    CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded, signedDecodeActualRawSpec, signedDecodeRawSpec] at hout ⊢
  rw [spkActualDecode_of_nonempty hne] at hout
  exact hout

/-- Relocatable non-empty contract: block `562` meets `signedDecodeNonemptyPlacedSpec A lim`. -/
theorem signedDecode_nonempty_placed_ok_of_deps [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hH : SignedHooksPlaced M A lim H) (d : SignedPortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_562 H) (blkPl_562).base (signedDecodeNonemptyPlacedSpec A lim) := by
  refine subroutine_ok.of_codeLoaded fun (x, st) R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hraw⟩ := CryptoVerification.LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  dsimp only [signedDecodeNonemptyRawSpec] at hraw
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hraw
  rcases hraw with ⟨⟨hx0, hx1, hx2, hlt, hne, hFit⟩, hmem⟩
  have hpre_spec : s0.mem ⊨ (signedDecodePlacedSpec A lim).pre (x, st) s0 ∗ R := by
    have hspec_raw : s0.mem ⊨ (signedDecodeRawSpec A lim).pre (x, st) s0 ∗ R := by
      dsimp only [signedDecodeRawSpec]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2, List.length_pos_of_ne_nil hne, hlt, hFit⟩, hmem⟩
    dsimp only [signedDecodePlacedSpec, CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded]
    rw [show ((signedDecodeRawSpec A lim).pre (x, st) s0 ∗ ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ R =
      ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ ((signedDecodeRawSpec A lim).pre (x, st) s0 ∗ R) by ac_rfl,
      satisfies_pure_sepConj]
    exact ⟨hcrl, hspec_raw⟩
  exact (signedDecode_placed_outcome_of_nonempty hH d hne hpc hrun hpre_spec hsp).mono_outcome
    fun _ hout => hout

end LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.NonemptyBudget
