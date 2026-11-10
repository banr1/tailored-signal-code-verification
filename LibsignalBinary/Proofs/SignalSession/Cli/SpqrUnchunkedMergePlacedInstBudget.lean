/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrAuthMergePlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrUnchunkedMergePlacedInst
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.DecodeErrorPushMergePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedClPlacedBudget
import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymB
import LibsignalBinary.Proofs.SpqrV1.Auth.AuthEncodeMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.BytesMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlaced

/-!
# Budget-Threaded Placed `unchunked::{Ct1Sent,EkSentCt1Received}::merge`

Code-and-rodata-loaded placed budget contracts for `<DecodeError>::push` (Block 257,
`decodeErrorPushMergeBudgetSpec`), `unchunked::Ct1Sent::merge` (Block 312), and
`unchunked::EkSentCt1Received::merge` (Block 311), in own-block, caller-transferred, and
leaf-discharged forms under `CliGhostAllocHooks M A lim gh`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrUnchunkedMergePlacedInstBudget

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement
   blkPC_311 blkPC_312 blkPl_311 blkPl_312
   libsignalSessionLib ls_blockPlacement_base ls_subroutine_ok_of_block lsmpl
   lsProg_261 lsProg_263 lsProg_290 lsProg_291 lsProg_295 lsProg_311 lsProg_312
   withLsCl withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchet
  (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded)
open CryptoVerification.RecordCodecs.Placed
  (blkPC_257 blkPl_257 instIsLsBlockProg_257 lsProg_257)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliGhostExterns hookSat_of_eq withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots
  (cliGhostExterns_panic_handle_error)
open CryptoVerification.SpqrV1.Top.Recv
  (ls_subroutine_ok_cro_of_cl ls_subroutine_ok_cro_of_cro)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks
   cliExternsPlaced_alloc_budget_sat
   cliExternsPlaced_noAllocShim_budget_sat
   cliExternsPlaced_realloc_budget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrAuthMergePlacedInstBudget
  (cliBytesMerge3_blockProgram_cro
   cliDecodeErrorFrom_blockProgram_cl
   cliDecodeVarint2_blockProgram_cl
   cliSkipField3_blockProgram_cl)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget (authMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.ProofBudget (bytesMerge3RawSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (decodeErrorPushMergeBudgetSpec
   unchunkedCt1SentMergeSpec
   unchunkedEkSentCt1ReceivedMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.DecodeErrorPushMergePlacedBudget
  (decode_error_push_merge_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentClPlacedBudget
  (unchunkedCt1SentMerge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedClPlacedBudget
  (unchunkedEkSentCt1ReceivedMerge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (decodeVarint2Spec)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

/-! ### 1. Internal `IsLsBlockProg` & Wrapper Lifting Helpers -/

private theorem isLsBlockProg_257 [LibsignalPlacement] (H : LibsignalHooks) :
    IsLsBlockProg (libsignalSessionLib.blockProgram lsmpl 257 H) 257 H :=
  ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_257 H) 257 H).externs_eq⟩

private theorem isLsBlockProg_261 [LibsignalPlacement] (H : LibsignalHooks) :
    IsLsBlockProg (libsignalSessionLib.blockProgram lsmpl 261 H) 261 H :=
  ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_261 H) 261 H).externs_eq⟩

private theorem isLsBlockProg_263 [LibsignalPlacement] (H : LibsignalHooks) :
    IsLsBlockProg (libsignalSessionLib.blockProgram lsmpl 263 H) 263 H :=
  ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_263 H) 263 H).externs_eq⟩

private theorem isLsBlockProg_290 [LibsignalPlacement] (H : LibsignalHooks) :
    IsLsBlockProg (libsignalSessionLib.blockProgram lsmpl 290 H) 290 H :=
  ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_290 H) 290 H).externs_eq⟩

private theorem isLsBlockProg_291 [LibsignalPlacement] (H : LibsignalHooks) :
    IsLsBlockProg (libsignalSessionLib.blockProgram lsmpl 291 H) 291 H :=
  ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_291 H) 291 H).externs_eq⟩

private theorem isLsBlockProg_295 [LibsignalPlacement] (H : LibsignalHooks) :
    IsLsBlockProg (libsignalSessionLib.blockProgram lsmpl 295 H) 295 H :=
  ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_295 H) 295 H).externs_eq⟩

private theorem isLsBlockProg_311 [LibsignalPlacement] (H : LibsignalHooks) :
    IsLsBlockProg (libsignalSessionLib.blockProgram lsmpl 311 H) 311 H :=
  ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_311 H) 311 H).externs_eq⟩

private theorem isLsBlockProg_312 [LibsignalPlacement] (H : LibsignalHooks) :
    IsLsBlockProg (libsignalSessionLib.blockProgram lsmpl 312 H) 312 H :=
  ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_312 H) 312 H).externs_eq⟩

private theorem rebase_to_blockProgram [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {H : LibsignalHooks}
    [hcallee : IsLsBlockProg calleeProg j H] {spec : Spec α}
    (h : subroutine_ok calleeProg (libsignalSessionLib.blockPlacement lsmpl j).base spec) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j) spec := by
  have h' : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H)
      (libsignalSessionLib.blockPlacement lsmpl j).base spec :=
    hcallee.eq_blockProgram ▸ h
  rwa [ls_blockPlacement_base (i := j)] at h'

theorem withLsCodeLoaded_of_withLsCl [LibsignalPlacement] {α : Type}
    {P : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok P entry (withLsCl lsmpl spec)) :
    subroutine_ok P entry (withLsCodeLoaded lsmpl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      dsimp only [withLsCl, withLsCodeLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)

private theorem hookSat_of_hExt {α : Type} {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks}
    {W : CliHooks} {H : String → Option (State → State)} {sym : String} {spec : Spec α}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    (hne : sym ≠ "libsignal_session_rng_fill" := by decide)
    (hsat : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym spec) :
    HookSat H sym spec :=
  hookSat_of_eq (hExt sym hne) hsat

private theorem hExt_withPanics (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      Rust.withPanics ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym := by
  intro sym hne
  have h1 : Rust.withPanics ext sym =
      Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym := by
    simp only [Rust.withPanics, hExt sym hne]
  exact h1.trans (congrFun (withPanics_cliGhostExterns mmpl gh W) sym)

/-! ### 1b. Block `257` (`decodeErrorPushMergeBudgetSpec`) CLI Instantiations -/

/-- Block `257` (`<DecodeError>::push`, `decodeErrorPushMergeBudgetSpec`) with
`withLsCodeLoaded lsmpl` under `hExt` and `CliGhostAllocHooks M A lim gh`. -/
theorem cliDecodeErrorPushMerge_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      ((blkPC_257).rebase (blkPl_257).base H)
      (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)) := by
  rw [← ls_blockPlacement_base (i := 257)]
  exact decode_error_push_merge_placed_ok
    ((hExt _ (by decide)).trans (cliGhostExterns_panic_handle_error mmpl gh W))
    (hookSat_of_hExt hExt (by decide) (cliExternsPlaced_noAllocShim_budget_sat mmpl gh W hA.shim_eq))
    (hookSat_of_hExt hExt (by decide) (cliExternsPlaced_alloc_budget_sat mmpl gh W hA))
    (hookSat_of_hExt hExt (by decide) (cliExternsPlaced_realloc_budget_sat mmpl gh W hA))

/-- Block `257` (`decodeErrorPushMergeBudgetSpec`) with `withLsCodeRoLoaded lsmpl`. -/
theorem cliDecodeErrorPushMerge_cro [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      ((blkPC_257).rebase (blkPl_257).base H)
      (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (cliDecodeErrorPushMerge_cl mmpl gh W hA hExt)

/-- Own-block `blockProgram` form of Block `257` (`decodeErrorPushMergeBudgetSpec`) under
`Rust.withPanics ext` (`withLsCodeLoaded`). -/
theorem cliDecodeErrorPushMerge_blockProgram_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)) := by
  rw [← IsLsBlockProg.eq_blockProgram
    (prog := (blkPC_257).rebase (blkPl_257).base (Rust.withPanics ext))]
  exact cliDecodeErrorPushMerge_cl mmpl gh W hA (hExt_withPanics mmpl gh W hExt)

/-- Own-block `blockProgram` form of Block `257` (`decodeErrorPushMergeBudgetSpec`) under
`Rust.withPanics ext` (`withLsCodeRoLoaded`). -/
theorem cliDecodeErrorPushMerge_blockProgram_cro [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (cliDecodeErrorPushMerge_blockProgram_cl mmpl gh W hA hExt)

/-- Block `257` (`decodeErrorPushMergeBudgetSpec`) lifted to any caller block `i`
(`withLsCodeLoaded`). -/
theorem cliDecodeErrorPushMerge_at_block_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [hcaller : IsLsBlockProg callerProg i H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)) :=
  ls_subroutine_ok_of_block (i := i) (j := 257) (cliDecodeErrorPushMerge_cl mmpl gh W hA hExt) hi

/-- Block `257` (`decodeErrorPushMergeBudgetSpec`) lifted to any caller block `i`
(`withLsCodeRoLoaded`). -/
theorem cliDecodeErrorPushMerge_at_block_cro [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [hcaller : IsLsBlockProg callerProg i H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)) :=
  ls_subroutine_ok_cro_of_cl (i := i) (j := 257) (cliDecodeErrorPushMerge_cl mmpl gh W hA hExt) hi

/-! ### 2. Hook-Generic Own-Block & Caller-Transferred Theorems (`312` and `311`) -/

/-- Block `312` (`unchunked::Ct1Sent::merge`) on `(blkPC_312).rebase` from own-block
`withLsCodeLoaded` (`257, 261, 263, 291`) and `withLsCodeRoLoaded` (`290, 295`) callee contracts. -/
theorem unchunkedCt1SentMerge_312_rebase_cro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (h261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 H) (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (h263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 H) (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (h290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)))
    (h291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 H) (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (h295 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim))) :
    subroutine_ok ((blkPC_312).rebase (blkPl_312).base H)
      (blkPl_312).base
      (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A lim)) := by
  let _ := isLsBlockProg_257 H
  let _ := isLsBlockProg_261 H
  let _ := isLsBlockProg_263 H
  let _ := isLsBlockProg_290 H
  let _ := isLsBlockProg_291 H
  let _ := isLsBlockProg_295 H
  exact unchunkedCt1SentMerge_cl_placed_ok_of_contracts
    (ls_subroutine_ok_cro_of_cl (i := 312) (j := 261) h261)
    (ls_subroutine_ok_cro_of_cl (i := 312) (j := 257) h257)
    (ls_subroutine_ok_cro_of_cl (i := 312) (j := 291) h291)
    (ls_subroutine_ok_cro_of_cl (i := 312) (j := 263) h263)
    (ls_subroutine_ok_cro_of_cro (i := 312) (j := 290) h290)
    (ls_subroutine_ok_cro_of_cro (i := 312) (j := 295) h295)

/-- own-block `blockProgram` contract for Block `312` (`unchunked::Ct1Sent::merge`). -/
theorem unchunkedCt1SentMerge_312_cro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (h261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 H) (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (h263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 H) (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (h290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)))
    (h291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 H) (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (h295 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 312 H)
      (lsmpl.base 312)
      (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A lim)) :=
  rebase_to_blockProgram (j := 312)
    (unchunkedCt1SentMerge_312_rebase_cro h257 h261 h263 h290 h291 h295)

/-- Block `311` (`unchunked::EkSentCt1Received::merge`) on `(blkPC_311).rebase` from own-block `withLsCodeLoaded` (`257, 261, 263, 291`) and `withLsCodeRoLoaded` (`290, 295`) callee
contracts. -/
theorem unchunkedEkSentCt1ReceivedMerge_311_rebase_cro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (h261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 H) (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (h263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 H) (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (h290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)))
    (h291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 H) (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (h295 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim))) :
    subroutine_ok ((blkPC_311).rebase (blkPl_311).base H)
      (blkPl_311).base
      (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A lim)) := by
  let _ := isLsBlockProg_257 H
  let _ := isLsBlockProg_261 H
  let _ := isLsBlockProg_263 H
  let _ := isLsBlockProg_290 H
  let _ := isLsBlockProg_291 H
  let _ := isLsBlockProg_295 H
  exact unchunkedEkSentCt1ReceivedMerge_cl_placed_ok_of_contracts
    (ls_subroutine_ok_cro_of_cl (i := 311) (j := 261) h261)
    (ls_subroutine_ok_cro_of_cl (i := 311) (j := 257) h257)
    (ls_subroutine_ok_cro_of_cl (i := 311) (j := 291) h291)
    (ls_subroutine_ok_cro_of_cl (i := 311) (j := 263) h263)
    (ls_subroutine_ok_cro_of_cro (i := 311) (j := 290) h290)
    (ls_subroutine_ok_cro_of_cro (i := 311) (j := 295) h295)

/-- own-block `blockProgram` contract for Block `311`
(`unchunked::EkSentCt1Received::merge`). -/
theorem unchunkedEkSentCt1ReceivedMerge_311_cro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (h261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 H) (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (h263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 H) (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (h290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)))
    (h291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 H) (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (h295 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 311 H)
      (lsmpl.base 311)
      (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A lim)) :=
  rebase_to_blockProgram (j := 311)
    (unchunkedEkSentCt1ReceivedMerge_311_rebase_cro h257 h261 h263 h290 h291 h295)

/-! ### 3. `hExt` Instantiations for `V1State::merge` / `Chunked*` Callers -/

/-- Own-block `blockProgram` contract for Block `312` (`unchunked::Ct1Sent::merge`),
generic in `hExt`, from own-block callee contracts
(`257, 261, 263, 290, 291, 295`). -/
theorem cliUnchunkedCt1SentMerge_312_cro [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (_hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    (h257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (h261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (h263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (h290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)))
    (h291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (h295 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 312 (Rust.withPanics ext))
      (lsmpl.base 312)
      (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A lim)) :=
  unchunkedCt1SentMerge_312_cro h257 h261 h263 h290 h291 h295

/-- Caller-transferred contract for Block `312` (`unchunked::Ct1Sent::merge`) onto any block
`i < 619` (e.g. `ChunkedCt1Sampled` `300`, `ChunkedCt1Acknowledged` `307`,
`ChunkedEkReceivedCt1Sampled` `310`), generic in `hExt`, in the exact
`withLsCodeRoLoaded` form consumed by `V1State::merge` arms. -/
theorem cliUnchunkedCt1SentMerge_caller_cro [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [hcaller : IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (h257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (h261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (h263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (h290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)))
    (h291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (h295 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 312)
      (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A lim)) := by
  let _ := isLsBlockProg_312 (Rust.withPanics ext)
  exact ls_subroutine_ok_cro_of_cro (i := i) (j := 312)
    (cliUnchunkedCt1SentMerge_312_cro mmpl gh W hExt h257 h261 h263 h290 h291 h295) hi

/-- Own-block `blockProgram` contract for Block `311` (`unchunked::EkSentCt1Received::merge`),
generic in `hExt`, from own-block callee contracts
(`257, 261, 263, 290, 291, 295`). -/
theorem cliUnchunkedEkSentCt1ReceivedMerge_311_cro [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (_hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    (h257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (h261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (h263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (h290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)))
    (h291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (h295 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 311 (Rust.withPanics ext))
      (lsmpl.base 311)
      (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A lim)) :=
  unchunkedEkSentCt1ReceivedMerge_311_cro h257 h261 h263 h290 h291 h295

/-- Caller-transferred contract for Block `311` (`unchunked::EkSentCt1Received::merge`) onto any
block `i < 619` (e.g. `ChunkedCt1Received` `303`, `ChunkedEkSentCt1Received` `309`), generic in
`hExt`, in the exact `withLsCodeRoLoaded` form consumed by `V1State::merge` arms. -/
theorem cliUnchunkedEkSentCt1ReceivedMerge_caller_cro [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [hcaller : IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (h257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (h261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (h263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (h290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)))
    (h291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (h295 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 311)
      (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A lim)) := by
  let _ := isLsBlockProg_311 (Rust.withPanics ext)
  exact ls_subroutine_ok_cro_of_cro (i := i) (j := 311)
    (cliUnchunkedEkSentCt1ReceivedMerge_311_cro mmpl gh W hExt h257 h261 h263 h290 h291 h295) hi

/-!
### 4. Uniform `withLsCodeRoLoaded` Variants (All 6 Callees in `withLsCodeRoLoaded` Form)
-/

/-- Own-block `blockProgram` contract for Block `312` (`unchunked::Ct1Sent::merge`),
generic in `hExt`, when all 6 callee contracts are given in `withLsCodeRoLoaded`
form. -/
theorem cliUnchunkedCt1SentMerge_312_of_cro [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (_hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    (h257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (h261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (h263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (h290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)))
    (h291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (h295 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 312 (Rust.withPanics ext))
      (lsmpl.base 312)
      (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A lim)) := by
  let _ := isLsBlockProg_257 (Rust.withPanics ext)
  let _ := isLsBlockProg_261 (Rust.withPanics ext)
  let _ := isLsBlockProg_263 (Rust.withPanics ext)
  let _ := isLsBlockProg_290 (Rust.withPanics ext)
  let _ := isLsBlockProg_291 (Rust.withPanics ext)
  let _ := isLsBlockProg_295 (Rust.withPanics ext)
  exact rebase_to_blockProgram (j := 312)
    (unchunkedCt1SentMerge_cl_placed_ok_of_contracts
      (ls_subroutine_ok_cro_of_cro (i := 312) (j := 261) h261)
      (ls_subroutine_ok_cro_of_cro (i := 312) (j := 257) h257)
      (ls_subroutine_ok_cro_of_cro (i := 312) (j := 291) h291)
      (ls_subroutine_ok_cro_of_cro (i := 312) (j := 263) h263)
      (ls_subroutine_ok_cro_of_cro (i := 312) (j := 290) h290)
      (ls_subroutine_ok_cro_of_cro (i := 312) (j := 295) h295))

/-- Own-block `blockProgram` contract for Block `311` (`unchunked::EkSentCt1Received::merge`),
generic in `hExt`, when all 6 callee contracts are given in `withLsCodeRoLoaded`
form. -/
theorem cliUnchunkedEkSentCt1ReceivedMerge_311_of_cro [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (_hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    (h257 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (h261 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (h263 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (h290 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)))
    (h291 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (h295 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 311 (Rust.withPanics ext))
      (lsmpl.base 311)
      (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A lim)) := by
  let _ := isLsBlockProg_257 (Rust.withPanics ext)
  let _ := isLsBlockProg_261 (Rust.withPanics ext)
  let _ := isLsBlockProg_263 (Rust.withPanics ext)
  let _ := isLsBlockProg_290 (Rust.withPanics ext)
  let _ := isLsBlockProg_291 (Rust.withPanics ext)
  let _ := isLsBlockProg_295 (Rust.withPanics ext)
  exact rebase_to_blockProgram (j := 311)
    (unchunkedEkSentCt1ReceivedMerge_cl_placed_ok_of_contracts
      (ls_subroutine_ok_cro_of_cro (i := 311) (j := 261) h261)
      (ls_subroutine_ok_cro_of_cro (i := 311) (j := 257) h257)
      (ls_subroutine_ok_cro_of_cro (i := 311) (j := 291) h291)
      (ls_subroutine_ok_cro_of_cro (i := 311) (j := 263) h263)
      (ls_subroutine_ok_cro_of_cro (i := 311) (j := 290) h290)
      (ls_subroutine_ok_cro_of_cro (i := 311) (j := 295) h295))

/-!
### 5. Leaf-Discharged `CliGhostAllocHooks` Corollaries (`257, 261, 263, 290, 291` Discharged)
-/

/-- Own-block `blockProgram` contract for Block `312` (`unchunked::Ct1Sent::merge`) under
`hExt` and `CliGhostAllocHooks M A lim gh`, discharging all five leaf callees
(`257, 261, 263, 290, 291`). -/
theorem cliUnchunkedCt1SentMerge_312_of_auth [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    (h295 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 312 (Rust.withPanics ext))
      (lsmpl.base 312)
      (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A lim)) :=
  cliUnchunkedCt1SentMerge_312_cro mmpl gh W hExt
    (cliDecodeErrorPushMerge_blockProgram_cl mmpl gh W hA hExt)
    (cliDecodeErrorFrom_blockProgram_cl mmpl gh W hA hExt)
    (cliSkipField3_blockProgram_cl mmpl gh W hA hExt)
    (cliBytesMerge3_blockProgram_cro mmpl gh W hA hExt)
    (cliDecodeVarint2_blockProgram_cl mmpl gh W hA hExt)
    h295

/-- Caller-transferred Block `312` (`unchunked::Ct1Sent::merge`) contract under
`hExt` and `CliGhostAllocHooks M A lim gh`, discharging all five leaf callees. -/
theorem cliUnchunkedCt1SentMerge_caller_of_auth [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [hcaller : IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (h295 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 312)
      (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A lim)) :=
  cliUnchunkedCt1SentMerge_caller_cro mmpl gh W hExt
    (cliDecodeErrorPushMerge_blockProgram_cl mmpl gh W hA hExt)
    (cliDecodeErrorFrom_blockProgram_cl mmpl gh W hA hExt)
    (cliSkipField3_blockProgram_cl mmpl gh W hA hExt)
    (cliBytesMerge3_blockProgram_cro mmpl gh W hA hExt)
    (cliDecodeVarint2_blockProgram_cl mmpl gh W hA hExt)
    h295 hi

/-- Own-block `blockProgram` contract for Block `311` (`unchunked::EkSentCt1Received::merge`) under
`hExt` and `CliGhostAllocHooks M A lim gh`, discharging all five leaf callees
(`257, 261, 263, 290, 291`). -/
theorem cliUnchunkedEkSentCt1ReceivedMerge_311_of_auth [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    (h295 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 311 (Rust.withPanics ext))
      (lsmpl.base 311)
      (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A lim)) :=
  cliUnchunkedEkSentCt1ReceivedMerge_311_cro mmpl gh W hExt
    (cliDecodeErrorPushMerge_blockProgram_cl mmpl gh W hA hExt)
    (cliDecodeErrorFrom_blockProgram_cl mmpl gh W hA hExt)
    (cliSkipField3_blockProgram_cl mmpl gh W hA hExt)
    (cliBytesMerge3_blockProgram_cro mmpl gh W hA hExt)
    (cliDecodeVarint2_blockProgram_cl mmpl gh W hA hExt)
    h295

/-- Caller-transferred Block `311` (`unchunked::EkSentCt1Received::merge`) contract under
`hExt` and `CliGhostAllocHooks M A lim gh`, discharging all five leaf callees. -/
theorem cliUnchunkedEkSentCt1ReceivedMerge_caller_of_auth [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [hcaller : IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (h295 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 311)
      (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A lim)) :=
  cliUnchunkedEkSentCt1ReceivedMerge_caller_cro mmpl gh W hExt
    (cliDecodeErrorPushMerge_blockProgram_cl mmpl gh W hA hExt)
    (cliDecodeErrorFrom_blockProgram_cl mmpl gh W hA hExt)
    (cliSkipField3_blockProgram_cl mmpl gh W hA hExt)
    (cliBytesMerge3_blockProgram_cro mmpl gh W hA hExt)
    (cliDecodeVarint2_blockProgram_cl mmpl gh W hA hExt)
    h295 hi

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrUnchunkedMergePlacedInstBudget
