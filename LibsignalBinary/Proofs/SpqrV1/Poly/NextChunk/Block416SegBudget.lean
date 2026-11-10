/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.NextChunkCodeSym
public meta import Lean -- shake: keep
public meta import ProofLib.SepLogic.WP -- shake: keep
public meta import ProofLib.SepLogic.WPp -- shake: keep

/-!
# Cached Block `416` Non-Syscall Segment Wrappers

Caches `checkBlockNoSvc0 blkLib_416.text = true` (`noSvc0_416`) so `sepWP_seg_416`,
`sepWPp_seg_416`, and `wp_steps_sync_416` step non-syscall segments of Block `416`
(`<PolyEncoder as Encoder>::next_chunk`) without repeated `checkBlockNoSvc0` kernel reduction.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget

open Arm64 ProofLib
open CryptoVerification
  (LibsignalHooks LibsignalPlacement blkLib_416 blkLib_eq_416 blkPC_416 blkPl_416)
open VerifiedLibraries.RustStd (checkBlockNoSvc0)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync
  (hooksException sepWP_seg_ls_vm sepWPp_seg_ls_vm)

set_option maxHeartbeats 1600000 in
/-- Cached non-`svc #0` scan over the 1,225 instructions of Block `416`. -/
theorem noSvc0_416 : checkBlockNoSvc0 blkLib_416.text = true := by rfl

/-- Run a pure non-`svc #0` instruction segment of Block `416` up to `mid`, delivering
    `ProofLib.NonSyscallPreserved` using the pre-cached `noSvc0_416` witness. -/
theorem sepWP_seg_416 [LibsignalPlacement] {H : LibsignalHooks}
    {mid target : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hseg : ∀ m_strip : Memory,
      SepWP ((blkPC_416).rebase (blkPl_416).base (hooksException H)) mid (s.setMem m_strip) Pre
        (fun sm' Pm =>
          ∀ m_real : Memory, ProofLib.NonSyscallPreserved s (sm'.setMem m_real) →
            SepWP ((blkPC_416).rebase (blkPl_416).base H) target (sm'.setMem m_real) Pm post oom)) :
    SepWP ((blkPC_416).rebase (blkPl_416).base H) target s Pre post oom :=
  sepWP_seg_ls_vm (Q := (blkPC_416).rebase (blkPl_416).base (hooksException H))
    blkLib_eq_416 noSvc0_416 hseg

/-- Panic-aware (`SepWPp`) counterpart of `sepWP_seg_416`. -/
theorem sepWPp_seg_416 [LibsignalPlacement] {H : LibsignalHooks}
    {mid ret : BitVec 64} {s : State} {Pre : SepProp}
    {post Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hseg : ∀ m_strip : Memory,
      SepWP ((blkPC_416).rebase (blkPl_416).base (hooksException H)) mid (s.setMem m_strip) Pre
        (fun sm' Pm =>
          ∀ m_real : Memory, ProofLib.NonSyscallPreserved s (sm'.setMem m_real) →
            SepWPp ((blkPC_416).rebase (blkPl_416).base H) ret (sm'.setMem m_real) Pm post Qp oom)) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base H) ret s Pre post Qp oom :=
  sepWPp_seg_ls_vm (Q := (blkPC_416).rebase (blkPl_416).base (hooksException H))
    blkLib_eq_416 noSvc0_416 hseg

end LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget

public meta section

namespace LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget

open Lean Meta Elab Tactic Arm64 ProofLib in
/-- Step CPU instructions of Block `416` up to `mid` and transport `A.pool lim st s`
    (or `(A.atState lim st s).pool`) across `SepWP.step_str*` / `SepWP.step_stp*` memory
    abstractions using the pre-cached `noSvc0_416` witness. -/
elab "wp_steps_sync_416 " mid:term : tactic => do
  let g ← getMainGoal
  let isWpp ← g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    if ty.isAppOfArity ``SepWP 6 then pure false
    else if ty.isAppOfArity ``SepWPp 7 then pure true
    else throwError "wp_steps_sync_416: expected SepWP or SepWPp goal"
  if isWpp then
    evalTactic (← `(tactic| (
      apply LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget.sepWPp_seg_416 (mid := $mid)
      intro _m_strip
      wp_steps
      refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
      first
        | refine ProofLib.SepWPp.transport_budgetPool
            (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
            (hnext := ?_)
        | refine ProofLib.SepWPp.transport_atStatePool
            (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
            (hnext := ?_)
    )))
  else
    evalTactic (← `(tactic| (
      apply LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget.sepWP_seg_416 (mid := $mid)
      intro _m_strip
      wp_steps
      refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
      first
        | refine ProofLib.SepWP.transport_budgetPool
            (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
            (hnext := ?_)
        | refine ProofLib.SepWP.transport_atStatePool
            (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
            (hnext := ?_)
    )))

end LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget

end
