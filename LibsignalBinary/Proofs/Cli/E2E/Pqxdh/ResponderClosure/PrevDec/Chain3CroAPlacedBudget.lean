/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroAPlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.BytesMerge6PlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `VerNe.Chain3` (Block `516`) Part A under `LibsignalCodeRoLoaded`

Total-correctness (`RustCliAllocBudget M`) loop framework, cross-block caller lift, and `Entry`
slice (`chain3Entry_cro_placed_ok`) for `message::merge<Chain> [local#4]` (Block `516`) under
`StoreKit.LibsignalCodeRoLoaded`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroAPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
  lsHandleErrorSym lsMemcpySym lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym lsRustReallocSym
  ls_subroutine_ok_cl_of_block lsmpl withLsCl withLsCodeLoaded
)
open CryptoVerification.LibsignalProtoCodec (
  decodeVarint decodeVarint_encodeVarint encodeVarint
)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  DecodeVarintSlowGhost sliceCursorAfter sliceCursorAt
)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded extract_withLsCodeRoLoaded withLsCodeRoLoaded
)
open CryptoVerification.E2E.Record (
  bytesField encMessageKey lenField msgField uint32Field
)
open CryptoVerification.E2E.Record.DeserializeSeed (
  sep_ac_seedChain sliceCursorAfter_append_eq_seedChain
)
open CryptoVerification.E2E.Record.DeserializeGeneral (
  ChainField ChainG ChainMergeGenGhost chainField_tag_cases chainGAfter segStepG_then
)
open CryptoVerification.CliHandshake.Placed (blkLib_eq_516 blkPl_516 lsProg_516)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3 (
  chain3Cells chain3GAt chain3SavedRegs chainMerge3StackX chainMerge3SubStackX
  extract_withLsCl_post_c3 intro_withLsCl_c3 libsignalCodeLoaded_preserve_c3
  stackAt_c3Sub_to_decodeVarint stackAt_chainMerge3StackX_split
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  framelessMemcpyBudgetSpec noAllocShimBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (
  DecodeVarintSliceEnv decodeVarintSliceEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (growOneChainSpecX)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsXBudget (
  ChainMergeGenEnv ChainPrefixEnv chainPrefixEnv_zero
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeDefsBudget (
  bytesMerge3RawSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5Budget (
  DecodeVarint2Env decodeVarint2SpecX
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.BytesMerge6PlacedBudget (
  bm6_decodeVarint5_placed_of_hooks bytes_merge_6_placed_ok_cro
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroAPlacedBudgetAux (
  Chain3LoopPlacedAtW Chain3PlacedOkAtW Chain3RetPlacedAtW Chain3StepPlacedAtW Chain5PlacedOkAtW
  GrowAllocPlaced chain3Exit_placed_ok chainMerge3PlacedSpecW chainMerge3RawSpecW
  chainMerge5PlacedSpecW growOneChain_placed_ok_cl_of_hooks grow_one_104_of_growAlloc
  hookSat_withPanics_of_mem isPanicSymbol_false_of_mem_lsExterns ls_externAt?_withPanics_eq
  sessionShimBudget_of_noAllocShim sepWPp_mono_pre_c3 step_chain3Exit_placed
  withPanics_apply_lsExtern
)

open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (
  intro_withLsCodeRoLoaded_c3 sp_sub_240_aligned_c3_cro
)

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (
  intro_withLsCodeRoLoaded_c3 sp_sub_240_aligned_c3_cro
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `Chain3CalleesCroPlacedW`, Loop Framework, and Caller Lift -/

private theorem storeKit_cro_of_tr_cro [LibsignalPlacement] {α : Type} {P : Program}
    {entry : BitVec 64} {S : Spec α}
    (h : subroutine_ok P entry
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl S)) :
    subroutine_ok P entry (withLsCodeRoLoaded lsmpl S) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      dsimp only [withLsCodeRoLoaded, LibsignalCodeRoLoaded,
        CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded] at hp ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hp)
    (fun _ _ _ _ hq => by
      dsimp only [withLsCodeRoLoaded,
        CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded] at hq ⊢
      exact hq)
    (hpanic := fun _ _ _ _ hp => hp)
    (hexit := fun _ _ _ _ _ he => he)
    (hoom := fun _ _ _ _ ho => ho)

/-- Budget-threaded callee contracts for `message::merge<Chain> [local#4]` (Block `516`) where
`bytes::merge` uses `withLsCodeRoLoaded` instead of `withLsCl`. -/
structure Chain3CalleesCroPlacedW [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : LibsignalHooks) : Prop where
  dv : subroutine_ok (lsProg_516 (Rust.withPanics ext)) (lsmpl.base 515)
    (withLsCl lsmpl (decodeVarint2SpecX A lim))
  bm : subroutine_ok (lsProg_516 (Rust.withPanics ext)) (lsmpl.base 514)
    (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim))
  grow : subroutine_ok (lsProg_516 (Rust.withPanics ext)) (lsmpl.base 43)
    (withLsCl lsmpl (growOneChainSpecX M A lim))

theorem chain3CalleesCro_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hshim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat ext lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat ext lsMemcpySym framelessMemcpyBudgetSpec)
    (hpanic_raw : ext lsHandleErrorSym = some Rust.panicked) :
    Chain3CalleesCroPlacedW M A lim ext := by
  have hshim' : HookSat (Rust.withPanics ext) lsRustNoAllocShimSym noAllocShimBudgetSpec :=
    hookSat_withPanics_of_mem (by decide) hshim
  have halloc' : HookSat (Rust.withPanics ext) lsRustAllocSym (rustCliAllocBudgetSpec M A lim false) :=
    hookSat_withPanics_of_mem (by decide) halloc
  have hrealloc' : HookSat (Rust.withPanics ext) lsRustReallocSym (rustCliReallocBudgetSpec M A lim) :=
    hookSat_withPanics_of_mem (by decide) hrealloc
  have hdealloc' : HookSat (Rust.withPanics ext) lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim) :=
    hookSat_withPanics_of_mem (by decide) hdealloc
  have hmc' : HookSat (Rust.withPanics ext) lsMemcpySym framelessMemcpyBudgetSpec :=
    hookSat_withPanics_of_mem (by decide) hmc
  have hpan_raw' : Rust.withPanics ext lsHandleErrorSym = some Rust.panicked :=
    (withPanics_apply_lsExtern (by decide)).trans hpanic_raw
  refine ⟨?_, ?_, ?_⟩
  · exact ls_subroutine_ok_cl_of_block (callerProg := lsProg_516 (Rust.withPanics ext))
      (bm6_decodeVarint5_placed_of_hooks hshim' halloc')
  · exact storeKit_cro_of_tr_cro
      (bytes_merge_6_placed_ok_cro (callerProg := lsProg_516 (Rust.withPanics ext))
        hshim' halloc' hrealloc' hdealloc' hmc' hpan_raw')
  · exact growOneChain_placed_ok_cl_of_hooks (callerProg := lsProg_516 (Rust.withPanics ext))
      hshim' halloc' hrealloc'

/-- Budget-threaded loop invariant of `message::merge<Chain> [local#4]` augmented with
`LibsignalCodeRoLoaded lsmpl`. -/
def Chain3LoopCroPlacedAtW [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : LibsignalHooks)
    (x : ChainMergeGenGhost) (st : M.σ) (R : SepProp)
    (s0 : State) (k : Nat) (s : State) : Prop :=
  LibsignalCodeRoLoaded lsmpl s.mem ∧
    Chain3LoopPlacedAtW M A lim ext x st R s0 k s

def Chain3EntryCroStmt [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : LibsignalHooks) : Prop :=
  Chain3CalleesCroPlacedW M A lim ext →
  ∀ (x : ChainMergeGenGhost) (st : M.σ) (R : SepProp) (s0 : State),
    s0.pc = lsmpl.base 516 → s0.status = .Running →
    (s0.mem ⊨ (withLsCodeRoLoaded lsmpl (chainMerge3RawSpecW M A lim)).pre (x, st) s0 ∗ R) →
    s0.spAligned = true →
    Chain3StepPlacedAtW M A lim ext x st R s0 s0 (Chain3LoopCroPlacedAtW M A lim ext x st R s0 0)

def Chain3SrkCroStmt [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : LibsignalHooks) : Prop :=
  Chain3CalleesCroPlacedW M A lim ext →
  ∀ (x : ChainMergeGenGhost) (st : M.σ) (R : SepProp)
    (s0 : State) (k : Nat) (s : State) (hk : k < x.c.fields.length),
    ((x.c.fields[k]'hk).tag = 1 ∨ (x.c.fields[k]'hk).tag = 2) →
    Chain3LoopCroPlacedAtW M A lim ext x st R s0 k s →
    Chain3StepPlacedAtW M A lim ext x st R s0 s
      (Chain3LoopCroPlacedAtW M A lim ext x st R s0 (k + 1))

def Chain3ChainKeyCroStmt [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : LibsignalHooks) : Prop :=
  Chain3CalleesCroPlacedW M A lim ext →
  ∀ (x : ChainMergeGenGhost) (st : M.σ) (R : SepProp)
    (s0 : State) (k : Nat) (s : State) (hk : k < x.c.fields.length),
    (x.c.fields[k]'hk).tag = 3 →
    Chain3LoopCroPlacedAtW M A lim ext x st R s0 k s →
    Chain3StepPlacedAtW M A lim ext x st R s0 s
      (Chain3LoopCroPlacedAtW M A lim ext x st R s0 (k + 1))

def Chain3MessageKeysCroStmt [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : LibsignalHooks) : Prop :=
  Chain3CalleesCroPlacedW M A lim ext →
  ∀ (x : ChainMergeGenGhost) (st : M.σ) (R : SepProp)
    (s0 : State) (k : Nat) (s : State) (hk : k < x.c.fields.length),
    (x.c.fields[k]'hk).tag = 4 →
    Chain3LoopCroPlacedAtW M A lim ext x st R s0 k s →
    Chain3StepPlacedAtW M A lim ext x st R s0 s
      (Chain3LoopCroPlacedAtW M A lim ext x st R s0 (k + 1))

theorem chain3Loop_cro_run [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (ext : LibsignalHooks)
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (hSrk : Chain3SrkCroStmt M A lim ext) (hCk : Chain3ChainKeyCroStmt M A lim ext)
    (hMk : Chain3MessageKeysCroStmt M A lim ext)
    {x : ChainMergeGenGhost} {st : M.σ} {R : SepProp} {s0 : State} :
    ∀ (m k : Nat) (s : State), k + m = x.c.fields.length →
      Chain3LoopCroPlacedAtW M A lim ext x st R s0 k s →
      reaches_outcome (lsProg_516 (Rust.withPanics ext))
        (withLsCodeRoLoaded lsmpl (chainMerge3RawSpecW M A lim)) (x, st) R s0 s := by
  intro m
  induction m with
  | zero =>
    intro k s hk ⟨_hcro, hs⟩
    simp only [Nat.add_zero] at hk
    subst hk
    apply reaches_outcome.of_codeLoaded
    intro hL
    obtain ⟨sf, hst, ⟨hret, hcc, hm⟩ | ⟨hpan, hmpan⟩⟩ :=
      chain3Exit_placed_ok ext x st R s0 s hs hL
    · dsimp only [chainMerge3PlacedSpecW, withLsCl, withLsCodeLoaded] at hm
      rw [sepConj_assoc, satisfies_pure_sepConj] at hm
      exact Arm64.reaches_outcome_steps hst
        (reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, hm.2⟩))
    · exact Arm64.reaches_outcome_steps hst
        (reaches_outcome.of_outcome (Or.inr (Or.inl ⟨hpan, hmpan⟩)))
  | succ m ih =>
    intro k s hk hs
    have hlt : k < x.c.fields.length := by omega
    have next : ∀ s', Chain3LoopCroPlacedAtW M A lim ext x st R s0 (k + 1) s' →
        reaches_outcome (lsProg_516 (Rust.withPanics ext))
          (withLsCodeRoLoaded lsmpl (chainMerge3RawSpecW M A lim)) (x, st) R s0 s' :=
      fun s' hs' => ih (k + 1) s' (by omega) hs'
    rcases chainField_tag_cases (x.c.fields[k]'hlt) with h12 | h3 | h4
    · exact segStepG_then (hSrk hC x st R s0 k s hlt h12 hs) next
    · exact segStepG_then (hCk hC x st R s0 k s hlt h3 hs) next
    · exact segStepG_then (hMk hC x st R s0 k s hlt h4 hs) next

theorem chainMerge3W_cro_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (ext : LibsignalHooks)
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (hEntry : Chain3EntryCroStmt M A lim ext) (hSrk : Chain3SrkCroStmt M A lim ext)
    (hCk : Chain3ChainKeyCroStmt M A lim ext) (hMk : Chain3MessageKeysCroStmt M A lim ext) :
    subroutine_ok (lsProg_516 (Rust.withPanics ext)) (lsmpl.base 516)
      (withLsCodeRoLoaded lsmpl (chainMerge3RawSpecW M A lim)) := by
  apply subroutine_ok.of_codeLoaded
  intro ⟨x, st⟩ R s0 hpc hrun hpre hal _hL
  exact segStepG_then (hEntry hC x st R s0 hpc hrun hpre hal) fun s hs =>
    chain3Loop_cro_run ext hC hSrk hCk hMk x.c.fields.length 0 s (Nat.zero_add _) hs

/-- Lift `message::merge<Chain> [local#4]` (Block `516`) from `lsProg_516 (Rust.withPanics ext)` to any `callerProg` over `ext` under `withLsCodeRoLoaded`. -/
theorem chainMerge5_cro_of_block [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [hcaller : IsLsBlockProg callerProg callerBlk ext]
    (hC5 : subroutine_ok (lsProg_516 (Rust.withPanics ext)) (lsmpl.base 516)
      (withLsCodeRoLoaded lsmpl (chainMerge3RawSpecW M A lim))) :
    subroutine_ok callerProg (lsmpl.base 516)
      (withLsCodeRoLoaded lsmpl (chainMerge3RawSpecW M A lim)) := by
  apply subroutine_ok_outcome_intro
  intro xst R s0 hpc hrun hpre hsp
  have ⟨hcrl0, _⟩ := extract_withLsCodeRoLoaded hpre
  have hcallee : IsLsBlockProg (lsProg_516 (Rust.withPanics ext)) 516 (Rust.withPanics ext) :=
    inferInstance
  have hQL : (lsProg_516 (Rust.withPanics ext)).CodeLoaded s0.mem :=
    hcallee.eq_blockProgram ▸
      hcrl0.1 516 (by decide) (by decide) (Rust.withPanics ext) (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hC5.no_fault_before_outcome xst R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc, (lsProg_516 (Rust.withPanics ext)).externAt? pc =
      callerProg.externAt? pc :=
    ls_externAt?_withPanics_eq (prog1 := lsProg_516 (Rust.withPanics ext)) (prog2 := callerProg)
  have hsvc : (lsProg_516 (Rust.withPanics ext)).svc = callerProg.svc := by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact Arm64.reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ)
    (reaches_outcome.of_outcome hout)

/-- Cut a `SepWPp` proof at `mid` while forwarding `LibsignalCodeRoLoaded` across `Steps.keepsFrozen`. -/
theorem SepWPp.bind_lscro [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q1 Q Qp : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWPp prog mid s P Q1 Qp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem → Q1 sm Pm →
      SepWPp prog ret sm Pm Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hst1, ⟨hpcm, hrunm, Pm, hmm, hq1⟩ | hpan | hoom⟩ := h1 R hm hL
  · obtain ⟨sf, hst2, hout⟩ :=
      h2 sm Pm hpcm hrunm (hcro.of_keepsFrozen hst1.keepsFrozen) hq1 R hmm (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hout⟩
  · exact ⟨sm, hst1, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hst1, Or.inr (Or.inr hoom)⟩

/-- Lift a `Chain3StepPlacedAtW` step to preserve `LibsignalCodeRoLoaded` automatically. -/
theorem segStepG_keep_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    {x : ChainMergeGenGhost} {st : M.σ} {R : SepProp}
    {s0 s : State} {Q : State → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : Chain3StepPlacedAtW M A lim ext x st R s0 s Q) :
    Chain3StepPlacedAtW M A lim ext x st R s0 s
      (fun s' => LibsignalCodeRoLoaded lsmpl s'.mem ∧ Q s') := by
  intro hL
  obtain ⟨sf, hst, hq | hpan⟩ := hstep hL
  · exact ⟨sf, hst, Or.inl ⟨hcro.of_keepsFrozen hst.keepsFrozen, hq⟩⟩
  · exact ⟨sf, hst, Or.inr hpan⟩

private theorem chainG_enc_eq_fields_c3_cro (c : ChainG) :
    c.enc = c.fields.flatMap ChainField.enc := by
  rcases c with ⟨srk, priv, ck, keys⟩
  unfold ChainG.enc ChainG.fields
  simp only [List.flatMap_append, List.flatMap_map]
  have h1 : bytesField 1 srk =
      List.flatMap ChainField.enc (if srk = [] then [] else [ChainField.srk srk]) := by
    unfold bytesField; split <;> simp [ChainField.enc]
  have h2 : bytesField 2 priv =
      List.flatMap ChainField.enc (if priv = [] then [] else [ChainField.priv priv]) := by
    unfold bytesField; split <;> simp [ChainField.enc]
  have h3 : msgField 3 (Option.map (fun ik => uint32Field 1 ik.1 ++ bytesField 2 ik.2) ck) =
      List.flatMap ChainField.enc
        (match ck with | some (i, k) => [ChainField.ck i k] | none => []) := by
    cases ck <;> simp [msgField, ChainField.enc]
  have h4 : (List.map (fun m => lenField 4 (encMessageKey m)) keys).flatten =
      List.flatMap (fun a => (ChainField.key a).enc) keys := by
    rw [← List.flatMap_def]; rfl
  rw [h1, h2, h3, h4]; rfl

private theorem fitsEnv_dv2_of_some {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {bs : List (BitVec 8)} {p : BitVec 64 × List (BitVec 8)}
    (hdv : decodeVarint bs = some p) :
    FitsEnv M lim st (DecodeVarint2Env bs) := by
  intro evs hevs
  simp only [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents, hdv] at hevs
  subst hevs
  trivial

private theorem dv2_evs_eq_nil_of_some {bs : List (BitVec 8)} {p : BitVec 64 × List (BitVec 8)}
    {evs : List AllocEvent} (hdv : decodeVarint bs = some p) (hevs : DecodeVarint2Env bs evs) :
    evs = [] := by
  simp only [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents, hdv] at hevs
  exact hevs

/-! ## VM-Preserving `Entry` Steppers and `c3_dv_call_cro` -/

section EntrySlice

attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg
attribute [local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.calleeSavedVRegs_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.calleeSavedVRegs_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.sp_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.sp_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg64_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg64_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg32_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg32_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg_setMem_setPC_pre_seedChain
attribute [local simp, local arm64_norm]
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.getLsbD_63_eq_seedChain

private theorem w0_and_255_eq_two_c3 {w : BitVec 64} (h : w.setWidth 8 = 2#8) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 w) &&& 255#64 = 2#64 := by
  apply BitVec.eq_of_toNat_eq
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.truncate, BitVec.zeroExtend, BitVec.toNat_setWidth,
    BitVec.toNat_and, BitVec.toNat_ofNat] at h' ⊢
  rw [show 255 % 2 ^ 64 = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

private theorem bv_ofNat_add_sub_left_c3 (m k : Nat) :
    BitVec.ofNat 64 (m + k) - BitVec.ofNat 64 m = BitVec.ofNat 64 k := by
  rw [BitVec.ofNat_add, BitVec.add_comm, BitVec.add_sub_cancel]

private theorem ult_ofNat_add_left_false_c3 {m k : Nat} (hlt : m + k < 2 ^ 62) :
    (BitVec.ofNat 64 (m + k)).ult (BitVec.ofNat 64 m) = false := by
  simp only [BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : m + k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : m < 2 ^ 64),
    decide_eq_false_iff_not]
  omega

private theorem ule_ofNat_add_right_true_c3 {m k : Nat} (hlt : m + k < 2 ^ 62) :
    (BitVec.ofNat 64 m).ule (BitVec.ofNat 64 (m + k)) = true := by
  simp only [BitVec.ule, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : m + k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : m < 2 ^ 64),
    decide_eq_true_eq]
  omega

set_option maxHeartbeats 400000 in
theorem step_chain3Entry_pre_placed_vm [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (a bufRef sp0 : BitVec 64)
    {s0 : State} {post : State → SepProp → Prop}
    (hpc : s0.pc = lsmpl.base 516)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0) (hsp_align : sp0 &&& 15#64 = 0#64)
    (hx0 : (s0.readReg64 .x0).setWidth 8 = 2#8) (hx1 : s0.readReg64 .x1 = a)
    (hx2 : s0.readReg64 .x2 = bufRef)
    (hnext : ∀ (sm : State),
      sm.pc = lsmpl.base 515 →
      sm.status = .Running → sm.sp = sp0 - 0xf0#64 → sm.trace = s0.trace →
      VmPreserved s0 sm →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .lr = lsmpl.base 516 + 0x38#64 →
      sm.readReg64 .x0 = bufRef → sm.readReg64 .x19 = bufRef → sm.readReg64 .x20 = a →
      sm.readReg64 .x26 = s0.readReg64 .x26 → sm.readReg64 .x27 = s0.readReg64 .x27 →
      sm.readReg64 .x28 = s0.readReg64 .x28 → sm.readReg64 .x29 = sp0 - 0x50#64 →
      ∀ Pm, (Pm ⊢ stackAt (sp0 - 0xf0#64) chainMerge3SubStackX ∗ chain3SavedRegs sp0 s0) →
        post sm Pm) :
    SepWP (lsProg_516 (Rust.withPanics ext))
      (lsmpl.base 515) s0
      (stackAt sp0 chainMerge3StackX) post := by
  subst hsp
  have hsp_sub_align : (s0.sp - 0xf0#64) &&& 15#64 = 0#64 := sp_sub_240_aligned_c3_cro hsp_align
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 515)
  intro m_strip
  change s0.pc = (blkPl_516).base at hpc
  have h1 : s0.readReg64 (Reg.gpr 1#5) = a := hx1
  have h2 : s0.readReg64 (Reg.gpr 2#5) = bufRef := hx2
  have hw0 : BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64 =
      2#64 := w0_and_255_eq_two_c3 hx0
  rw [stackAt_chainMerge3StackX_split s0.sp]
  unfold chain3Cells
  simp only [sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w80; apply SepWP.exists_elim; intro w72
  apply SepWP.exists_elim; intro w64; apply SepWP.exists_elim; intro w56
  apply SepWP.exists_elim; intro w48; apply SepWP.exists_elim; intro w40
  apply SepWP.exists_elim; intro w32; apply SepWP.exists_elim; intro w24
  apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w8
  iterate 14 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s0 _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  refine hnext _ (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) hvm (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]; rfl) (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) _ ?_
  unfold chain3SavedRegs
  rw [ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.sepExists_right w56 (sep_ac_seedChain (by ac_rfl))

set_option maxHeartbeats 400000 in
theorem step_chain3Entry_post_placed_vm [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (a bufRef slot ptr' sp0 x26 x27 x28 : BitVec 64) (m k : Nat) (hlt : m + k < 2 ^ 62)
    {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 516 + 0x38#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 0xf0#64) (hsp_align : sp0 &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = 0#64) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 m)
    (hx19 : s.readReg64 .x19 = bufRef) (hx20 : s.readReg64 .x20 = a)
    (hx26 : s.readReg64 .x26 = x26) (hx27 : s.readReg64 .x27 = x27)
    (hx28 : s.readReg64 .x28 = x28) (hx29 : s.readReg64 .x29 = sp0 - 0x50#64)
    (hnext : ∀ (sm : State),
      sm.pc = lsmpl.base 516 + 0xa8#64 →
      sm.status = .Running → sm.sp = sp0 - 0xf0#64 → sm.trace = s.trace →
      VmPreserved s sm →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .x19 = bufRef → sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = BitVec.ofNat 64 k → sm.readReg64 .x22 = sp0 - 0xe8#64 →
      sm.readReg64 .x23 = 1#64 → sm.readReg64 .x24 = 104#64 →
      sm.readReg64 .x26 = x26 → sm.readReg64 .x27 = x27 → sm.readReg64 .x28 = x28 →
      sm.readReg64 .x29 = sp0 - 0x50#64 →
      ∀ Pm, (Pm ⊢ (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ ptr') ∗
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (m + k))) → post sm Pm) :
    SepWP (lsProg_516 (Rust.withPanics ext)) (lsmpl.base 516 + 0xa8#64) s
      ((bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ ptr') ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (m + k)))
      post := by
  have hsp_sub_align : s.sp &&& 15#64 = 0#64 := by rw [hsp]; exact sp_sub_240_aligned_c3_cro hsp_align
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 516 + 0xa8#64)
  intro m_strip
  change s.pc = (blkPl_516).base + 0x38#64 at hpc
  have h0 : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 m := hx1
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h26 : s.readReg64 (Reg.gpr 26#5) = x26 := hx26
  have h27 : s.readReg64 (Reg.gpr 27#5) = x27 := hx27
  have h28 : s.readReg64 (Reg.gpr 28#5) = x28 := hx28
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp0 - 0x50#64 := hx29
  have hsub := bv_ofNat_add_sub_left_c3 m k
  have hult := ult_ofNat_add_left_false_c3 hlt
  have hule := ule_ofNat_add_right_true_c3 hlt
  iterate 10 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  refine hnext _ (by simp only [wp_norm, arm64_norm]; rfl) (by simp only [hrun, wp_norm, arm64_norm])
    (by simp only [hsp, wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) hvm (by simp only [wp_norm, arm64_norm])
    (by simp only [h19, wp_norm, arm64_norm]) (by simp only [h20, wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
    (by simp only [h26, wp_norm, arm64_norm]) (by simp only [h27, wp_norm, arm64_norm])
    (by simp only [h28, wp_norm, arm64_norm]) (by simp only [h29, wp_norm, arm64_norm]) _ ?_
  exact sep_ac_seedChain (by ac_rfl)

set_option maxHeartbeats 400000 in
/-- Budget-threaded Entry slice under `LibsignalCodeRoLoaded`: from the entry of `message::merge<Chain> [local#4]` to `+0x0a8` with 0 fields consumed (`evs = []`). -/
theorem chain3Entry_cro_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (ext : LibsignalHooks) :
    Chain3EntryCroStmt M A lim ext := by
  intro hC x st R s0 hpc hrun hpre hal
  obtain ⟨hcro0, hpre⟩ := extract_withLsCodeRoLoaded hpre
  refine segStepG_keep_cro hcro0 ?_
  intro hL0
  rcases x with ⟨a, c, bufRef, slot, ptr, tail⟩
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := hcro0.1
  dsimp only [chainMerge3RawSpecW] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hcOk, hlen_lt, hfit⟩, hmem⟩
  have hsp_align : s0.sp &&& 15#64 = 0#64 := by simpa [State.spAligned, beq_iff_eq] using hal
  have hsp_sub_align : (s0.sp - 240#64) &&& 15#64 = 0#64 := sp_sub_240_aligned_c3_cro hsp_align
  have hmem1 : s0.mem ⊨ stackAt s0.sp chainMerge3StackX ∗
      (chain3GAt A.repAlloc a ChainG.empty ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr (c.payload ++ tail) ∗ A.pool lim st s0 ∗ R) :=
    Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
  obtain ⟨s1, hst1, ⟨hpc1, hrun1, P1, hm1, hsp1, htr1, hvm1, hvregs1, hlr1, hx0_1, hx19_1, hx20_1,
      hx26_1, hx27_1, hx28_1, hx29_1, hent1⟩ | ⟨_, hoom1⟩⟩ :=
    (step_chain3Entry_pre_placed_vm (ext := ext) a bufRef s0.sp
      (post := fun sm Pm =>
        sm.sp = s0.sp - 240#64 ∧ sm.trace = s0.trace ∧ VmPreserved s0 sm ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        sm.readReg64 .lr = lsmpl.base 516 + 56#64 ∧
        sm.readReg64 .x0 = bufRef ∧ sm.readReg64 .x19 = bufRef ∧ sm.readReg64 .x20 = a ∧
        sm.readReg64 .x26 = s0.readReg64 .x26 ∧ sm.readReg64 .x27 = s0.readReg64 .x27 ∧
        sm.readReg64 .x28 = s0.readReg64 .x28 ∧ sm.readReg64 .x29 = s0.sp - 80#64 ∧
        (Pm ⊢ stackAt (s0.sp - 240#64) chainMerge3SubStackX ∗ chain3SavedRegs s0.sp s0))
      hpc hrun rfl hsp_align hx0 hx1 hx2
      (fun _ _ _ hsp' htr' hvm' hvregs' hlr' hx0' hx19' hx20' hx26' hx27' hx28' hx29' _ hent =>
        ⟨hsp', htr', hvm', hvregs', hlr', hx0', hx19', hx20', hx26', hx27', hx28', hx29',
          hent⟩)).elim hmem1 hL0
  rotate_left; · exact (not_satisfies_false_sepConj hoom1).elim
  have hm1' := Satisfies.mono (sepConj_mono_left hent1) hm1
  have hpool1 : A.pool lim st s0 = A.pool lim st s1 :=
    (congrArg CryptoVerification.RustHeap.RustAlloc.pool (A.atState_eq_of_vmPreserved lim st hvm1)).symm
  have hal1 : s1.spAligned = true := by simp only [State.spAligned, hsp1, beq_iff_eq]; exact hsp_sub_align
  have hdec : decodeVarint (c.payload ++ tail) = some (BitVec.ofNat 64 c.enc.length, c.enc ++ tail) := by
    rw [show c.payload ++ tail = encodeVarint (BitVec.ofNat 64 c.enc.length) ++ (c.enc ++ tail) by
      unfold ChainG.payload; rw [List.append_assoc]]
    exact decodeVarint_encodeVarint (BitVec.ofNat 64 c.enc.length) (c.enc ++ tail)
  let gvar : DecodeVarintSlowGhost := ⟨bufRef, slot, ptr, c.payload ++ tail⟩
  let F_call : SepProp :=
    memRegion (s0.sp - 240#64 - BitVec.ofNat 64 chainMerge3SubStackX)
        (chainMerge3SubStackX - CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.decodeVarint2StackX) ∗
      chain3SavedRegs s0.sp s0 ∗ chain3GAt A.repAlloc a ChainG.empty
  have hlen63 : (c.payload ++ tail).length < 2 ^ 63 := Nat.lt_trans hlen_lt (by decide)
  have hfit_dv : FitsEnv M lim st (DecodeVarint2Env gvar.bs) := fitsEnv_dv2_of_some hdec
  have hm1_call : s1.mem ⊨ (withLsCl lsmpl (decodeVarint2SpecX A lim)).pre (gvar, st) s1 ∗ (F_call ∗ R) := by
    refine intro_withLsCl_c3 (libsignalCodeLoaded_preserve_c3 hcl0 hst1) ?_
    unfold decodeVarint2SpecX; dsimp only [gvar]
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨⟨hx0_1, hlen63, hfit_dv⟩, ?_⟩
    rw [stackAt_c3Sub_to_decodeVarint (s0.sp - 240#64), hpool1] at hm1'
    rw [hsp1]; dsimp only [F_call]; convert hm1' using 1; ac_rfl
  obtain ⟨s2, hst2, ⟨⟨hpc2, _, hrun2⟩, ⟨hsp2, hcs2⟩, hm2⟩ | ⟨_, hm2_pan⟩ | ⟨_, _, hm2_ex⟩ | ⟨_, hm2_oom⟩, _⟩ :=
    (hC.dv).no_fault_before_outcome (gvar, st) (F_call ∗ R) s1 hpc1 hrun1 hm1_call hal1 (hst1.codeLoaded hL0)
  · have hpc2' : s2.pc = lsmpl.base 516 + 56#64 := by rw [hpc2, hlr1]
    have hsp2' : s2.sp = s0.sp - 240#64 := by rw [hsp2, hsp1]
    rcases hcs2 with ⟨hx19_c, hx20_c, _, _, _, _, _, hx26_c, hx27_c, hx28_c, hx29_c, hvregs_c⟩
    have hx19_2 : s2.readReg64 .x19 = bufRef := hx19_c.trans hx19_1
    have hx20_2 : s2.readReg64 .x20 = a := hx20_c.trans hx20_1
    have hx26_2 : s2.readReg64 .x26 = s0.readReg64 .x26 := hx26_c.trans hx26_1
    have hx27_2 : s2.readReg64 .x27 = s0.readReg64 .x27 := hx27_c.trans hx27_1
    have hx28_2 : s2.readReg64 .x28 = s0.readReg64 .x28 := hx28_c.trans hx28_1
    have hx29_2 : s2.readReg64 .x29 = s0.sp - 80#64 := hx29_c.trans hx29_1
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs_c.trans hvregs1
    obtain ⟨_, hm2⟩ := extract_withLsCl_post_c3 hm2
    unfold decodeVarint2SpecX at hm2; dsimp only [gvar] at hm2; rw [hdec] at hm2; dsimp only at hm2
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm2
    rcases hm2 with ⟨evs0, hm2⟩
    have hm2_pure : s2.mem ⊨
        ⌜(s2.readReg64 .x0 = 0#64 ∧ s2.readReg64 .x1 = BitVec.ofNat 64 c.enc.length) ∧
          s2.trace = s1.trace ∧ DecodeVarint2Env (c.payload ++ tail) evs0⌝ ∗
        ((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs0 st) s2 ∗
          stackAt s1.sp CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.decodeVarint2StackX ∗
          sliceCursorAfter slot ptr (c.payload ++ tail) (c.enc ++ tail) ∗ F_call ∗ R) := by
      have h1 : s2.mem ⊨
          ⌜s2.readReg64 .x0 = 0#64 ∧ s2.readReg64 .x1 = BitVec.ofNat 64 c.enc.length⌝ ∗
          (⌜s2.trace = s1.trace⌝ ∗
            (⌜DecodeVarint2Env (c.payload ++ tail) evs0⌝ ∗
              ((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs0 st) s2 ∗
                stackAt s1.sp CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.decodeVarint2StackX ∗
                sliceCursorAfter slot ptr (c.payload ++ tail) (c.enc ++ tail) ∗ F_call ∗ R))) :=
        Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hm2
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj] at h1
      rw [satisfies_pure_sepConj]
      exact ⟨⟨h1.1, h1.2.1, h1.2.2.1⟩, h1.2.2.2⟩
    rw [satisfies_pure_sepConj] at hm2_pure
    rcases hm2_pure with ⟨⟨⟨hx0_2, hx1_2⟩, htr2, hevs0⟩, hm2_rest⟩
    have hevs0_nil : evs0 = [] := dv2_evs_eq_nil_of_some hdec hevs0
    subst hevs0_nil
    rw [hsp1] at hm2_rest
    have hlenA : (c.enc ++ tail).length = c.enc.length + tail.length := List.length_append
    have hlt2 : c.enc.length + tail.length < 2 ^ 62 := by
      unfold ChainG.payload at hlen_lt; simp only [List.length_append] at hlen_lt; omega
    let p1 := ptr + BitVec.ofNat 64 ((c.payload ++ tail).length - (c.enc ++ tail).length)
    unfold sliceCursorAfter at hm2_rest
    have hm2_post : s2.mem ⊨
        ((bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ p1) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (c.enc.length + tail.length))) ∗
        ((ptr ↦ₛ (c.payload ++ tail)) ∗ A.pool lim (M.stepEvents [] st) s2 ∗
          stackAt (s0.sp - 240#64) CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.decodeVarint2StackX ∗
          F_call ∗ R) := by
      rw [← hlenA]; dsimp only [p1]; refine Satisfies.mono (sep_ac_seedChain ?_) hm2_rest
      ac_rfl
    obtain ⟨s3, hst3, ⟨hpc3, hrun3, P3, hm3, hsp3, htr3, hvm3, hvregs3, hx19_3, hx20_3, hx21_3,
        hx22_3, hx23_3, hx24_3, hx26_3, hx27_3, hx28_3, hx29_3, hent3⟩ | ⟨_, hoom3⟩⟩ :=
      (step_chain3Entry_post_placed_vm (ext := ext) a bufRef slot p1 s0.sp
        (s0.readReg64 .x26) (s0.readReg64 .x27) (s0.readReg64 .x28) c.enc.length tail.length hlt2
        (post := fun sm Pm =>
          sm.sp = s0.sp - 240#64 ∧ sm.trace = s2.trace ∧ VmPreserved s2 sm ∧
          calleeSavedVRegs sm = calleeSavedVRegs s2 ∧
          sm.readReg64 .x19 = bufRef ∧ sm.readReg64 .x20 = a ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 tail.length ∧ sm.readReg64 .x22 = s0.sp - 232#64 ∧
          sm.readReg64 .x23 = 1#64 ∧ sm.readReg64 .x24 = 104#64 ∧
          sm.readReg64 .x26 = s0.readReg64 .x26 ∧ sm.readReg64 .x27 = s0.readReg64 .x27 ∧
          sm.readReg64 .x28 = s0.readReg64 .x28 ∧ sm.readReg64 .x29 = s0.sp - 80#64 ∧
          (Pm ⊢ (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ p1) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (c.enc.length + tail.length))))
        hpc2' hrun2 hsp2' hsp_align hx0_2 hx1_2 hx19_2 hx20_2 hx26_2 hx27_2 hx28_2 hx29_2
        (fun _ _ _ hsp' htr' hvm' hvregs' hx19' hx20' hx21' hx22' hx23' hx24' hx26' hx27' hx28' hx29' _ hent =>
          ⟨hsp', htr', hvm', hvregs', hx19', hx20', hx21', hx22', hx23', hx24', hx26', hx27', hx28', hx29', hent⟩)).elim
        hm2_post ((hst1.trans hst2).codeLoaded hL0)
    rotate_left; · exact (not_satisfies_false_sepConj hoom3).elim
    have hm3' := Satisfies.mono (sepConj_mono_left hent3) hm3
    have hpool3 : A.pool lim (M.stepEvents [] st) s2 = A.pool lim (M.stepEvents [] st) s3 :=
      (congrArg CryptoVerification.RustHeap.RustAlloc.pool
        (A.atState_eq_of_vmPreserved lim (M.stepEvents [] st) hvm3)).symm
    have hst_all := (hst1.trans hst2).trans hst3
    refine ⟨s3, hst_all, Or.inl ⟨hpc3, hrun3, (htr3.trans htr2).trans htr1,
      hvregs3.trans hvregs2, libsignalCodeLoaded_preserve_c3 hcl0 hst_all, hsp3,
      by simp only [State.spAligned, hsp3, beq_iff_eq]; exact hsp_sub_align,
      hx29_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx26_3, hx27_3, hx28_3,
      hcOk, hlen_lt, hfit, [], chainPrefixEnv_zero c, ?_⟩⟩
    dsimp only
    rw [show chainGAfter c 0 = ChainG.empty from rfl,
      show (c.fields.drop 0).flatMap ChainField.enc = c.enc by
        rw [List.drop_zero, ← chainG_enc_eq_fields_c3_cro c]]
    unfold sliceCursorAfter
    rw [hlenA, stackAt_c3Sub_to_decodeVarint (s0.sp - 240#64)]
    dsimp only [F_call, p1] at hm3'; rw [hlenA, hpool3] at hm3'
    exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hm3'
  · dsimp only [withLsCl, decodeVarint2SpecX] at hm2_pan
    exact False.elim (not_satisfies_false_sepConj hm2_pan)
  · exact False.elim (not_satisfies_false_sepConj hm2_ex)
  · exact False.elim (not_satisfies_false_sepConj hm2_oom)

set_option maxHeartbeats 400000 in
/-- Unified budget-threaded `bl decode_varint [local#4]` (Block `515`) call helper for
`Chain3CalleesCroPlacedW` (`0` allocations on `decodeVarint (enc ++ rest) = some (v, rest)`, so
`A.pool lim st_cur` is preserved with no `FitsEnv` precondition required). -/
theorem c3_dv_call_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (bufRef slot curPtr sp0 ret_pc v : BitVec 64) (enc rest : List (BitVec 8))
    (hdv : decodeVarint (enc ++ rest) = some (v, rest))
    (hlen_lt : (enc ++ rest).length < 2 ^ 62)
    {st_cur : M.σ} {ret : BitVec 64} {s0 s : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 515)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 240#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = bufRef)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → sm.readReg64 .x0 = 0#64 → sm.readReg64 .x1 = v →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ (curPtr ↦ₛ enc) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 enc.length) rest ∗
          A.pool lim st_cur sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot curPtr (enc ++ rest) ∗
        A.pool lim st_cur s ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q Qp := by
  have hlen_lt63 : (enc ++ rest).length < 2 ^ 63 := by omega
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_240_aligned_c3_cro halign
  have hfit_dv : FitsEnv M lim st_cur (DecodeVarint2Env (enc ++ rest)) := fitsEnv_dv2_of_some hdv
  let gvar : DecodeVarintSlowGhost := ⟨bufRef, slot, curPtr, enc ++ rest⟩
  let F_dv : SepProp :=
    memRegion (sp0 - 240#64 - BitVec.ofNat 64 chainMerge3SubStackX)
        (chainMerge3SubStackX - CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.decodeVarint2StackX) ∗ F
  intro R' hm hL
  have hm_call : s.mem ⊨ (withLsCl lsmpl (decodeVarint2SpecX A lim)).pre (gvar, st_cur) s ∗ (F_dv ∗ R') := by
    refine intro_withLsCl_c3 hcl ?_
    rw [stackAt_c3Sub_to_decodeVarint (sp0 - 240#64)] at hm
    unfold decodeVarint2SpecX; dsimp only [gvar]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hlen_lt63, hfit_dv⟩, ?_⟩
    rw [hsp]; dsimp only [F_dv]; convert hm using 1; ac_rfl
  obtain ⟨sm, hst1, ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hm_post⟩ | ⟨_, hm_pan⟩ | ⟨_, _, hm_ex⟩ | ⟨_, hm_oom⟩, _⟩ :=
    (hC.dv).no_fault_before_outcome (gvar, st_cur) (F_dv ∗ R') s hpc hrun hm_call hsp_aligned hL
  · rw [hlr] at hpcm
    rw [hsp] at hspm
    obtain ⟨hclm, hm_post⟩ := extract_withLsCl_post_c3 hm_post
    unfold decodeVarint2SpecX at hm_post; dsimp only [gvar] at hm_post; rw [hdv] at hm_post; dsimp only at hm_post
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_post
    rcases hm_post with ⟨evs0, hm_post⟩
    have hm_pure : sm.mem ⊨
        ⌜(sm.readReg64 .x0 = 0#64 ∧ sm.readReg64 .x1 = v) ∧
          sm.trace = s.trace ∧ DecodeVarint2Env (enc ++ rest) evs0⌝ ∗
        ((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs0 st_cur) sm ∗
          stackAt s.sp CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.decodeVarint2StackX ∗
          sliceCursorAfter slot curPtr (enc ++ rest) rest ∗ F_dv ∗ R') := by
      have h1 : sm.mem ⊨
          ⌜sm.readReg64 .x0 = 0#64 ∧ sm.readReg64 .x1 = v⌝ ∗
          (⌜sm.trace = s.trace⌝ ∗
            (⌜DecodeVarint2Env (enc ++ rest) evs0⌝ ∗
              ((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs0 st_cur) sm ∗
                stackAt s.sp CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.decodeVarint2StackX ∗
                sliceCursorAfter slot curPtr (enc ++ rest) rest ∗ F_dv ∗ R'))) :=
        Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hm_post
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj] at h1
      rw [satisfies_pure_sepConj]
      exact ⟨⟨h1.1, h1.2.1, h1.2.2.1⟩, h1.2.2.2⟩
    rw [satisfies_pure_sepConj] at hm_pure
    rcases hm_pure with ⟨⟨⟨hx0m, hx1m⟩, htrm, hevs0⟩, hm_rest⟩
    have hevs0_nil : evs0 = [] := dv2_evs_eq_nil_of_some hdv hevs0
    subst hevs0_nil
    rw [hsp] at hm_rest
    have hm_next : sm.mem ⊨
        (((bufRef ↦₆₄ slot) ∗ (curPtr ↦ₛ enc) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 enc.length) rest ∗
          A.pool lim st_cur sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F) ∗ R' := by
      rw [sliceCursorAfter_append_eq_seedChain slot curPtr enc rest] at hm_rest
      have hst_eq : A.pool lim (M.stepEvents [] st_cur) sm = A.pool lim st_cur sm := rfl
      rw [hst_eq] at hm_rest
      dsimp only [F_dv] at hm_rest
      rw [stackAt_c3Sub_to_decodeVarint (sp0 - 240#64)]
      exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hm_rest
    obtain ⟨sf, hst2, hout2⟩ :=
      hnext sm hpcm hrunm hspm hclm (htrm.trans htr) hcsm hx0m hx1m R' hm_next (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hout2⟩
  · dsimp only [withLsCl, decodeVarint2SpecX] at hm_pan
    exact False.elim (not_satisfies_false_sepConj hm_pan)
  · exact False.elim (not_satisfies_false_sepConj hm_ex)
  · exact False.elim (not_satisfies_false_sepConj hm_oom)

end EntrySlice

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroAPlacedBudget
