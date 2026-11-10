/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Adapters
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsX
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.ChainMerge
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.DeserializeLeaves
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.MergeField
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.Callees
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Deser.RecordDeserializeX

/-!
# General `SessionRecord::deserialize` Composition and Relocatable Corollaries

Composes the loop-entry, loop-iteration, loop-exit, and representation leaves (`DeserializeLeaves`,
`MergeField`, `ChainMerge`, `Fields`) to establish `deserializeGen_ok` on `tripleRatchetProgAt`, and
lifts it to `[LibsignalPlacement]` (`deserializeGen_placed_ok`, Block `46`).
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.Serialization (OkAt CanonRecord)

theorem deserOutG_post {x : DeserializeGenGhost} {R : SepProp} {s0 sf : State}
    (hr : DeserializeScope x.r) (h : sf.mem ⊨ deserOutRawG x s0 sf ∗ R) :
    sf.mem ⊨ deserializeGenSpec.post x s0 sf ∗ R := by
  have hrepr := deserReprG_ok x.r hr x.out
  refine Satisfies.mono (sepConj_mono_left ?_) h
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hrepr))

/-- By induction on the remaining fields `m`, execution from `DeserLoopG` after `k` fields reaches
`deserializeGenSpec.post` (or panics with `deserializeGenSpec.onPanic`). -/
theorem deserLoopG_run {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hMF : MergeFieldGenOk C ctl (fun _ => True) abs) {x : DeserializeGenGhost} {R : SepProp}
    {s0 : State} (hr : DeserializeScope x.r) :
    ∀ (m k : Nat) (s : State), k + m = (recFields x.r).length →
      DeserLoopG C ctl x R s0 k s →
      reaches_outcome (recordProg C ctl abs) deserializeGenSpec x R s0 s := by
  intro m
  induction m with
  | zero =>
    intro k s hk hs
    simp only [Nat.add_zero] at hk
    subst hk
    refine segStepG_then (deserLoopExitG_ok C ctl (abs := abs) x R s0 s hr hs) ?_
    intro sf ⟨hret, hcc, hmem⟩
    exact Arm64.reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, deserOutG_post hr hmem⟩)
  | succ m ih =>
    intro k s hk hs
    have hlt : k < (recFields x.r).length := by omega
    exact segStepG_then (deserLoopIterG_ok C ctl hMF x R s0 k s hr hlt hs)
      (fun s' hs' => ih (k + 1) s' (by omega) hs')

theorem deserializeBodyG_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) (hMF : MergeFieldGenOk C ctl (fun _ => True) abs) :
    OkAt sessionImg0.base C ctl abs recDeserializeName deserializeGenSpec := by
  refine Arm64.subroutine_ok_outcome_intro ?_
  intro x R s0 hpc hrun hpre hal
  have hr : DeserializeScope x.r := by
    have h := hpre
    simp only [deserializeGenSpec, sepConj_assoc, satisfies_pure_sepConj] at h
    exact h.1.2.2.2.1
  exact segStepG_then (deserLoopEntryG_ok C ctl hC x R s0 hpc hrun hpre hal)
    (fun s hs => deserLoopG_run hMF hr _ 0 s (Nat.zero_add _) hs)

/-- `SessionRecord::deserialize` (`0x16ed4`) satisfies `deserializeGenSpec` on
`tripleRatchetProgAt`. -/
theorem deserializeGen_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hAlloc : AllocHooks A0 abs) :
    OkAt sessionImg0.base C ctl abs recDeserializeName deserializeGenSpec :=
  have hC := deserializeCallees_ok_of_hooks C ctl hAlloc
  deserializeBodyG_ok C ctl hC
    (mergeFieldGen_ok C ctl hC (chainMergeGen_ok C ctl hC))

/-! ## Relocatable `[LibsignalPlacement]` Corollaries (Block `46`) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem deserializeGen_placed_ok_of_alloc [LibsignalPlacement]
    {H : LibsignalHooks}
    (hA : Proofs.libsignal.Stage1X.AllocContractsPlaced A0 H)
    (hMemcpy : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
      subroutine_ok callerProg (lsρ "memcpy")
        (withLsCl lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      Proofs.libsignal.Hooks2.deserializeGenPlacedSpec :=
  Proofs.libsignal.Hooks2.deserializeGen_placed_ok_of_alloc hA hMemcpy

theorem deserializeGen_placed_ok_of_stage2 [LibsignalPlacement]
    {H : LibsignalHooks}
    (hStage2 : Proofs.libsignal.Hooks2.Stage2ContractsA0Placed H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      Proofs.libsignal.Hooks2.deserializeGenPlacedSpec :=
  Proofs.libsignal.Hooks2.deserializeGen_placed_ok_of_stage2 hStage2

set_option maxRecDepth 200000 in
/-- Relocatable `SessionRecord::deserialize` (Block `46`) satisfies `deserializeGenPlacedSpec` on
`lsProg_46 H` for any hook map `H` meeting the allocator, `memcpy`, `memmove`, shim, and panic
contracts. -/
theorem deserializeGen_placed_ok [LibsignalPlacement]
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
      Proofs.libsignal.Hooks2.deserializeGenPlacedSpec :=
  Proofs.libsignal.Hooks2.deserializeGen_placed_ok_of_alloc
    (Proofs.libsignal.Stage1X.AllocContractsPlaced.of_hooks
      halloc hdealloc hrealloc hshim hmemmove hpan_err hpan_alloc)
    (ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hmemcpy))

end Placed

end CryptoVerification.E2E.Record.DeserializeGeneral
