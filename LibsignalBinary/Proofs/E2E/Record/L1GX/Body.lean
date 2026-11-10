/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Adapters
public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Defs
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.DeserD0X
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.DeserDExitX
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.DeserDIterX
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.ProstSSGXRepr
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.B3DeserQ

/-!
# PQXDH-Scope `SessionRecord::deserialize` Composition

Composes the entry (`DeserD0X`), field-loop iteration (`DeserDIterX`), loop exit (`DeserDExitX`),
and representation (`ProstSSGXRepr`) leaves to establish both `deserializeXExactSpec` (raw
`prostSSGXAt` postcondition) and `deserializeXSpec` (canonical `sessionRecordAt` postcondition) for
`SessionRecord::deserialize` (`0x16ed4`, block `46`) on records in `DeserializeScopeP`, along with
relocatable `[LibsignalPlacement]` corollaries.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.L1GX

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (OkAt CanonRecord)
open CryptoVerification.E2E.RecordX (DeserializeScopeP)
open CryptoVerification.E2E.Record.L1GX.Leaf.DeserD0X (deserD0X_ok)
open CryptoVerification.E2E.Record.L1GX.Leaf.DeserDIterX (deserDIterX_ok)
open CryptoVerification.E2E.Record.L1GX.Leaf.DeserDExitX (deserDExitX_ok)
open CryptoVerification.E2E.Record.L1GX.Leaf.ProstSSGXRepr (deserReprX_ok)

/-- Exact PQXDH-scope contract for `SessionRecord::deserialize` with raw `deserOutRawX` postcondition. -/
noncomputable def deserializeXExactSpec : Spec DeserializeGenGhost where
  pre := deserializeXSpec.pre
  post := fun x s0 sf => deserOutRawX x s0 sf
  onPanic := deserializeXSpec.onPanic

theorem deserStepX_exact {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {x : DeserializeGenGhost} {R : SepProp}
    {s0 s : State} {Q : State → Prop} (h : DeserStepX C ctl x R s0 s Q abs) :
    SegStepG (recordProg C ctl abs) deserializeXExactSpec x R s0 s Q := h

/-- Raw output `deserOutRawX` entails `deserializeXSpec.post`. -/
theorem deserOutX_post {x : DeserializeGenGhost} {R : SepProp} {s0 sf : State}
    (hr : DeserializeScopeP x.r) (h : sf.mem ⊨ deserOutRawX x s0 sf ∗ R) :
    sf.mem ⊨ deserializeXSpec.post x s0 sf ∗ R := by
  have hrepr := deserReprX_ok x.r hr x.out
  refine Satisfies.mono (sepConj_mono_left ?_) h
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hrepr))

/-- Field-loop induction from `DeserLoopX` after `k` fields to `deserializeXExactSpec.post`. -/
theorem deserLoopX_run {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hMF : MergeFieldXOk C ctl (fun _ => True) abs) {x : DeserializeGenGhost} {R : SepProp}
    {s0 : State} (hr : DeserializeScopeP x.r) :
    ∀ (m k : Nat) (s : State), k + m = (recFieldsX x.r).length →
      DeserLoopX C ctl x R s0 k s →
      reaches_outcome (recordProg C ctl abs) deserializeXExactSpec x R s0 s := by
  intro m
  induction m with
  | zero =>
    intro k s hk hs
    simp only [Nat.add_zero] at hk
    subst hk
    refine segStepG_then (deserStepX_exact
      (deserDExitX_ok C ctl (abs := abs) x R s0 s hr hs)) ?_
    intro sf ⟨hret, hcc, hmem⟩
    exact reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, hmem⟩)
  | succ m ih =>
    intro k s hk hs
    have hlt : k < (recFieldsX x.r).length := by omega
    exact segStepG_then (deserStepX_exact (deserDIterX_ok C ctl hMF x R s0 k s hr hlt hs))
      (fun s' hs' => ih (k + 1) s' (by omega) hs')

/-- Field-loop induction from `DeserLoopX` after `k` fields to `deserializeXSpec.post`. -/
theorem deserLoopX_run_gen {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hMF : MergeFieldXOk C ctl (fun _ => True) abs) {x : DeserializeGenGhost} {R : SepProp}
    {s0 : State} (hr : DeserializeScopeP x.r) :
    ∀ (m k : Nat) (s : State), k + m = (recFieldsX x.r).length →
      DeserLoopX C ctl x R s0 k s →
      reaches_outcome (recordProg C ctl abs) deserializeXSpec x R s0 s := by
  intro m
  induction m with
  | zero =>
    intro k s hk hs
    simp only [Nat.add_zero] at hk
    subst hk
    refine segStepG_then (deserDExitX_ok C ctl (abs := abs) x R s0 s hr hs) ?_
    intro sf ⟨hret, hcc, hmem⟩
    exact reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, deserOutX_post hr hmem⟩)
  | succ m ih =>
    intro k s hk hs
    have hlt : k < (recFieldsX x.r).length := by omega
    exact segStepG_then (deserDIterX_ok C ctl hMF x R s0 k s hr hlt hs)
      (fun s' hs' => ih (k + 1) s' (by omega) hs')

theorem deserializeScopeP_of_pre {x : DeserializeGenGhost} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨ deserializeXSpec.pre x s0 ∗ R) : DeserializeScopeP x.r := by
  have h := hpre
  simp only [deserializeXSpec, sepConj_assoc, satisfies_pure_sepConj] at h
  exact h.1.2.2.2.1

/-- `SessionRecord::deserialize` (`0x16ed4`) satisfies `deserializeXExactSpec` on `tripleRatchetProgAt`. -/
theorem deserializeBodyXExact_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) (hMF : MergeFieldXOk C ctl (fun _ => True) abs) :
    OkAt sessionImg0.base C ctl abs recDeserializeName deserializeXExactSpec := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hr : DeserializeScopeP x.r := deserializeScopeP_of_pre hpre
  exact segStepG_then (deserStepX_exact (deserD0X_ok C ctl hC x R s0 hpc hrun hpre hal))
    (fun s hs => deserLoopX_run hMF hr _ 0 s (Nat.zero_add _) hs)

/-- `SessionRecord::deserialize` (`0x16ed4`) satisfies `deserializeXSpec` on `tripleRatchetProgAt`. -/
theorem deserializeBodyX_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) (hMF : MergeFieldXOk C ctl (fun _ => True) abs) :
    OkAt sessionImg0.base C ctl abs recDeserializeName deserializeXSpec := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hr : DeserializeScopeP x.r := deserializeScopeP_of_pre hpre
  exact segStepG_then (deserD0X_ok C ctl hC x R s0 hpc hrun hpre hal)
    (fun s hs => deserLoopX_run_gen hMF hr _ 0 s (Nat.zero_add _) hs)

/-! ## Relocatable `[LibsignalPlacement]` Corollaries -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem L1_L1GX_Body_Placed : True := trivial

theorem deserializeXExact_placed_ok_of_alloc [LibsignalPlacement]
    {H : LibsignalHooks}
    (hA : Proofs.libsignal.Stage1X.AllocContractsPlaced A0 H)
    (hMemcpy : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
      subroutine_ok callerProg (lsρ "memcpy")
        (withLsCl lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      Symbolic.Swarm.TRREF.B3DeserQ.deserializeQExactPlacedSpecW :=
  Symbolic.Swarm.TRREF.B3DeserQ.deserializeExactAtQ_placed_ok_of_alloc hA hMemcpy

theorem deserializeX_placed_ok_of_alloc [LibsignalPlacement]
    {H : LibsignalHooks}
    (hA : Proofs.libsignal.Stage1X.AllocContractsPlaced A0 H)
    (hMemcpy : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
      subroutine_ok callerProg (lsρ "memcpy")
        (withLsCl lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      Symbolic.Swarm.TRREF.B3DeserQ.deserializeQPlacedSpecW :=
  Symbolic.Swarm.TRREF.B3DeserQ.deserializeBodyQ_placed_ok_of_alloc hA hMemcpy

theorem deserializeXExact_placed_ok_of_stage2 [LibsignalPlacement]
    {H : LibsignalHooks}
    (hStage2 : Proofs.libsignal.Hooks2.Stage2ContractsA0Placed H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      Symbolic.Swarm.TRREF.B3DeserQ.deserializeQExactPlacedSpecW :=
  Symbolic.Swarm.TRREF.B3DeserQ.deserializeExactAtQ_placed_ok_of_stage2 hStage2

theorem deserializeX_placed_ok_of_stage2 [LibsignalPlacement]
    {H : LibsignalHooks}
    (hStage2 : Proofs.libsignal.Hooks2.Stage2ContractsA0Placed H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      Symbolic.Swarm.TRREF.B3DeserQ.deserializeQPlacedSpecW :=
  Symbolic.Swarm.TRREF.B3DeserQ.deserializeBodyQ_placed_ok_of_stage2 hStage2

set_option maxRecDepth 200000 in
/-- Relocatable `SessionRecord::deserialize` (block `46`) satisfies `deserializeQExactPlacedSpecW` on
`lsProg_46 H` under allocator, `memcpy`, `memmove`, shim, and panic hook contracts. -/
theorem deserializeXExact_placed_ok [LibsignalPlacement]
    {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A0))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A0))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A0))
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (hmemcpy : HookSat H "memcpy" (sessionMemcpySpec extHookStack))
    (hmemmove : HookSat H "memmove" (sessionMemmoveSpec extHookStack))
    (hpan_err : H lsHandleErrorSym = some Rust.panicked)
    (hpan_alloc : H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      Symbolic.Swarm.TRREF.B3DeserQ.deserializeQExactPlacedSpecW :=
  Symbolic.Swarm.TRREF.B3DeserQ.deserializeExactAtQ_placed_ok_of_alloc
    (Proofs.libsignal.Stage1X.AllocContractsPlaced.of_hooks
      halloc hdealloc hrealloc hshim hmemmove hpan_err hpan_alloc)
    (ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hmemcpy))

set_option maxRecDepth 200000 in
/-- Relocatable `SessionRecord::deserialize` (block `46`) satisfies `deserializeQPlacedSpecW` on
`lsProg_46 H` under allocator, `memcpy`, `memmove`, shim, and panic hook contracts. -/
theorem deserializeX_placed_ok [LibsignalPlacement]
    {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A0))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A0))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A0))
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (hmemcpy : HookSat H "memcpy" (sessionMemcpySpec extHookStack))
    (hmemmove : HookSat H "memmove" (sessionMemmoveSpec extHookStack))
    (hpan_err : H lsHandleErrorSym = some Rust.panicked)
    (hpan_alloc : H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      Symbolic.Swarm.TRREF.B3DeserQ.deserializeQPlacedSpecW :=
  Symbolic.Swarm.TRREF.B3DeserQ.deserializeBodyQ_placed_ok_of_alloc
    (Proofs.libsignal.Stage1X.AllocContractsPlaced.of_hooks
      halloc hdealloc hrealloc hshim hmemmove hpan_err hpan_alloc)
    (ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hmemcpy))

end Placed

end CryptoVerification.E2E.Record.L1GX
