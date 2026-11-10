/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeTightPlacedBudgetC308Aux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedNoHeaderReceivedClPlacedBudget
import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymB
import LibsignalBinary.Proofs.SignalSession.Cli.SpqrChunkedMergePlacedInst
import LibsignalBinary.Proofs.SpqrV1.Auth.AuthEncodeMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.SpqrV1.Varint.VarintCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym

/-!
# Guarded-Tight Placed Budget Contract for `Chunked.NoHeaderReceived::merge` (Block `308`)

Proves `tlb_ChunkedNoHeaderReceivedMergePlacedTightOkOf` on Block `308` within
`SpqrTightEvs maxOps 345567 2560` (`authOps + decOps ≤ maxOps`, default `39 = 4 + 35`:
`Authenticator` `2,952` B + `PolynomialDecoder` `342,615` B) on canonical
`tlb_ChunkedNoHeaderReceivedDom` inputs, falling back to `ChunkedNoHeaderReceivedMergeEnv` outside the domain.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeTightPlacedBudgetC

open Arm64 ProofLib SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement instIsLsBlockProg_261
   instIsLsBlockProg_263 instIsLsBlockProg_291 instIsLsBlockProg_295
   libsignalMutatedBlocks libsignalSessionExterns libsignalSessionLib
   ls_blockPlacement_base ls_externAt?_blockProgram_eq_of_externs_eq lsmpl withLsCodeLoaded)
open CryptoVerification.RecordCodecs.Placed (instIsLsBlockProg_257)
open CryptoVerification.LibsignalTripleRatchet
  (extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
   withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedNoHeaderReceivedMergeGhost blkPC_308 blkPl_308 instIsLsBlockProg_296
   instIsLsBlockProg_308)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_AuthGuardedEnvOf tlb_AuthMergePlacedTightOkOf
   tlb_ChunkedNoHeaderReceivedDom tlb_ChunkedNoHeaderReceivedGuardedEnvOf
   tlb_ChunkedNoHeaderReceivedMergePlacedTightOk
   tlb_ChunkedNoHeaderReceivedMergePlacedTightOkOf
   tlb_PolyDecoderGuardedEnvOf tlb_PolyDecoderMergePlacedTightOkOf
   tlb_authMergeTightSpecOfEnv tlb_fitsEnv_fallback_of_not_dom
   tlb_polyDecoderMergeTightSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget (authMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (chunkedNoHeaderReceivedMergePostEnv_imp_pre chunkedNoHeaderReceivedMergeSpec
   chunkedNoHeaderReceivedMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeTightPlacedBudgetC308Aux
  (e2kc_chunkedNoHeaderReceived_dom_ok)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeTightPlacedBudgetC308UcAux
  (e2kc_chunkedNoHeaderReceivedDomSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedNoHeaderReceivedClPlacedBudget
  (chunked_no_header_received_merge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (polyDecoderMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (decodeVarint2Spec)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

/-! ## 1. Own-Block ↔ Caller-Block Transfer Helpers (`e2kc_`) -/

class e2kc_IsLsValidBlock [LibsignalPlacement] (j : Nat) : Prop where
  lt_blocks : j < 624
  not_mutated : (j ∈ libsignalMutatedBlocks) = false
  externs_eq : (libsignalSessionLib.blockLib j).text.externs = libsignalSessionExterns

instance [LibsignalPlacement] : e2kc_IsLsValidBlock 257 :=
  ⟨by decide, by decide, (instIsLsBlockProg_257 (fun _ => none)).externs_eq⟩
instance [LibsignalPlacement] : e2kc_IsLsValidBlock 261 :=
  ⟨by decide, by decide, (instIsLsBlockProg_261 (fun _ => none)).externs_eq⟩
instance [LibsignalPlacement] : e2kc_IsLsValidBlock 263 :=
  ⟨by decide, by decide, (instIsLsBlockProg_263 (fun _ => none)).externs_eq⟩
instance [LibsignalPlacement] : e2kc_IsLsValidBlock 291 :=
  ⟨by decide, by decide, (instIsLsBlockProg_291 (fun _ => none)).externs_eq⟩
instance [LibsignalPlacement] : e2kc_IsLsValidBlock 295 :=
  ⟨by decide, by decide, (instIsLsBlockProg_295 (fun _ => none)).externs_eq⟩
instance [LibsignalPlacement] : e2kc_IsLsValidBlock 296 :=
  ⟨by decide, by decide, (instIsLsBlockProg_296 (fun _ => none)).externs_eq⟩
instance [LibsignalPlacement] : e2kc_IsLsValidBlock 308 :=
  ⟨by decide, by decide, (instIsLsBlockProg_308 (fun _ => none)).externs_eq⟩

theorem e2kc_lift_cro_of_own [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hj : e2kc_IsLsValidBlock j] {spec : Spec α}
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j)
      (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok callerProg (lsmpl.base j) (withLsCodeRoLoaded lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hfr0, _⟩ := extract_withLsCodeRoLoaded hpre
  have hQL : (libsignalSessionLib.blockProgram lsmpl j H).CodeLoaded s0.mem :=
    hfr0.1 j hj.lt_blocks hj.not_mutated H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc, (libsignalSessionLib.blockProgram lsmpl j H).externAt? pc = callerProg.externAt? pc :=
    fun pc => by
      rw [hcaller.eq_blockProgram,
        ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
          (hj.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : (libsignalSessionLib.blockProgram lsmpl j H).svc = callerProg.svc := by
    rw [hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome hout)

theorem e2kc_lift_cl_of_own [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [e2kc_IsLsValidBlock j] {spec : Spec α}
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j)
      (withLsCodeLoaded lsmpl spec)) :
    subroutine_ok callerProg (lsmpl.base j) (withLsCodeRoLoaded lsmpl spec) :=
  e2kc_lift_cro_of_own (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hcallee)

theorem e2kc_own_of_blk_cro [LibsignalPlacement] {α : Type}
    {blkProg : Program} {i : Nat} {H : LibsignalHooks}
    [hprog : IsLsBlockProg blkProg i H] {spec : Spec α}
    (h : subroutine_ok blkProg (libsignalSessionLib.blockPlacement lsmpl i).base
      (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl i H) (lsmpl.base i)
      (withLsCodeRoLoaded lsmpl spec) := by
  rw [← hprog.eq_blockProgram, ← ls_blockPlacement_base lsmpl i]
  exact h

/-! ## 2. Block `308` (`V1State.Chunked.NoHeaderReceived::merge`) -/

/-- Non-domain (`¬ tlb_ChunkedNoHeaderReceivedDom x`) fallback for Block `308`: discharges the
non-canonical branch directly from `chunked_no_header_received_merge_cl_placed_ok_of_contracts`
and `chunkedNoHeaderReceivedMergePostEnv_imp_pre`. -/
theorem e2kc_chunkedNoHeaderReceived_not_dom_reaches_outcome [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps : Nat}
    (hLoose : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (blkPl_308).base
      (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A lim)))
    {x : ChunkedNoHeaderReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    (hNotDom : ¬ tlb_ChunkedNoHeaderReceivedDom x)
    (hpc : s0.pc = (blkPl_308).base)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (withLsCodeRoLoaded lsmpl
      (chunkedNoHeaderReceivedMergeSpecOfEnv A lim
        (tlb_ChunkedNoHeaderReceivedGuardedEnvOf maxOps)
        (tlb_ChunkedNoHeaderReceivedGuardedEnvOf maxOps))).pre (x, st) s0 ∗ R)
    (hsp : s0.spAligned = true) :
    reaches_outcome ((blkPC_308).rebase (blkPl_308).base H)
      (withLsCodeRoLoaded lsmpl
        (chunkedNoHeaderReceivedMergeSpecOfEnv A lim
          (tlb_ChunkedNoHeaderReceivedGuardedEnvOf maxOps)
          (tlb_ChunkedNoHeaderReceivedGuardedEnvOf maxOps)))
      (x, st) R s0 s0 := by
  have hpre1 : s0.mem ⊨ (withLsCodeRoLoaded lsmpl
      (chunkedNoHeaderReceivedMergeSpec A lim)).pre (x, st) s0 ∗ R := by
    refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left ?_)) hpre
    dsimp only [chunkedNoHeaderReceivedMergeSpec, chunkedNoHeaderReceivedMergeSpecOfEnv]
    exact sepConj_mono_left (Entails.pure_mono fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
      tlb_fitsEnv_fallback_of_not_dom hNotDom h.2.2.2.2⟩)
  refine hLoose.mono_outcome (x, st) R s0 hpc hrun hpre1 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    refine Satisfies.mono
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_)))) hq
    exact Entails.sepExists_elim fun evs => Entails.sepExists_right evs
      (sepConj_mono_left (Entails.pure_mono fun hevs =>
        Or.inr ⟨hNotDom, chunkedNoHeaderReceivedMergePostEnv_imp_pre hevs⟩))
  · exact Or.inr hrest

/-- Block `308` (`V1State.Chunked.NoHeaderReceived::merge`) `maxOps`-monotone tight contract on
`((blkPC_308).rebase (blkPl_308).base H)` for any `maxOps` with `authOps + decOps ≤ maxOps`:
`authOps + decOps` non-free ops (default `4 + 35 = 39`), `cumCap = 345,567` B, `maxReq = 2,560` B. -/
theorem e2kc_chunkedNoHeaderReceived_merge_tight_blk308_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {authOps decOps maxOps : Nat}
    (hOps : authOps + decOps ≤ maxOps)
    (hFromCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hAuthLoose : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hPolyLoose : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)))
    (hAuthTight : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (tlb_authMergeTightSpecOfEnv A lim (tlb_AuthGuardedEnvOf authOps) (tlb_AuthGuardedEnvOf authOps))))
    (hPolyTight : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyDecoderMergeTightSpecOfEnv A lim
          (tlb_PolyDecoderGuardedEnvOf decOps) (tlb_PolyDecoderGuardedEnvOf decOps)))) :
    subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (blkPl_308).base
      (withLsCodeRoLoaded lsmpl
        (chunkedNoHeaderReceivedMergeSpecOfEnv A lim
          (tlb_ChunkedNoHeaderReceivedGuardedEnvOf maxOps)
          (tlb_ChunkedNoHeaderReceivedGuardedEnvOf maxOps))) := by
  have hLoose := chunked_no_header_received_merge_cl_placed_ok_of_contracts
    hFromCall hPushCall hVarintCall hSkipCall hAuthLoose hPolyLoose
  have hDomOk := e2kc_chunkedNoHeaderReceived_dom_ok hOps hVarintCall hAuthTight hPolyTight
  apply subroutine_ok_outcome_intro
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp
  by_cases hDom : tlb_ChunkedNoHeaderReceivedDom x
  · have hpre_dom : s0.mem ⊨ (withLsCodeRoLoaded lsmpl
        (e2kc_chunkedNoHeaderReceivedDomSpec A lim maxOps)).pre (x, st) s0 ∗ R := by
      refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left ?_)) hpre
      dsimp only [e2kc_chunkedNoHeaderReceivedDomSpec]
      exact Entails.pure_right hDom (Entails.refl _)
    exact hDomOk.mono_outcome (x, st) R s0 hpc hrun hpre_dom hsp fun _ hout => hout
  · exact e2kc_chunkedNoHeaderReceived_not_dom_reaches_outcome hLoose hDom hpc hrun hpre hsp

/-- `maxOps`-monotone own-block tight contract for Block `308` (`V1State.Chunked.NoHeaderReceived::merge`, `authOps + decOps ≤ maxOps`). -/
theorem e2kc_chunkedNoHeaderReceived_merge_tight_placed_ok_le [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {authOps decOps maxOps : Nat}
    (hOps : authOps + decOps ≤ maxOps)
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hAuthLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hPolyLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim authOps ext)
    (hPolyTight : tlb_PolyDecoderMergePlacedTightOkOf A lim decOps ext) :
    tlb_ChunkedNoHeaderReceivedMergePlacedTightOkOf A lim maxOps ext :=
  e2kc_own_of_blk_cro (e2kc_chunkedNoHeaderReceived_merge_tight_blk308_ok_of_contracts hOps
    (e2kc_lift_cl_of_own hFrom) (e2kc_lift_cl_of_own hPush)
    (e2kc_lift_cl_of_own hVarint) (e2kc_lift_cl_of_own hSkip)
    (e2kc_lift_cro_of_own hAuthLoose) (e2kc_lift_cro_of_own hPolyLoose)
    (e2kc_lift_cro_of_own hAuthTight) (e2kc_lift_cro_of_own hPolyTight))

/-- `maxOps`-parametric own-block tight contract for Block `308` (`V1State.Chunked.NoHeaderReceived::merge`) at `authOps + decOps`. -/
theorem e2kc_chunkedNoHeaderReceived_merge_tight_placed_ok_of [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {authOps decOps : Nat}
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hAuthLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hPolyLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim authOps ext)
    (hPolyTight : tlb_PolyDecoderMergePlacedTightOkOf A lim decOps ext) :
    tlb_ChunkedNoHeaderReceivedMergePlacedTightOkOf A lim (authOps + decOps) ext :=
  e2kc_chunkedNoHeaderReceived_merge_tight_placed_ok_le (Nat.le_refl _)
    hFrom hPush hVarint hSkip hAuthLoose hPolyLoose hAuthTight hPolyTight

/-- Default `2`-op/bytes specialization (`4 + 35 = 39` ops, `345,567` B, `2,560` B) for Block `308`. -/
theorem e2kc_chunkedNoHeaderReceived_merge_tight_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hAuthLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hPolyLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim 4 ext)
    (hPolyTight : tlb_PolyDecoderMergePlacedTightOkOf A lim 35 ext) :
    tlb_ChunkedNoHeaderReceivedMergePlacedTightOk A lim ext :=
  e2kc_chunkedNoHeaderReceived_merge_tight_placed_ok_of
    hFrom hPush hVarint hSkip hAuthLoose hPolyLoose hAuthTight hPolyTight

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeTightPlacedBudgetC
