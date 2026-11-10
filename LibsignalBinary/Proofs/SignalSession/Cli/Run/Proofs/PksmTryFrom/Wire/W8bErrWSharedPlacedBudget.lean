/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWShared
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWSharedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ParseLemmas
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded `[LibsignalPlacement]` Shared `+0x504` Error-Epilogue Closing

Proves `spAligned_of_postEpilogueStatePlaced` and budget-threaded
`w8b_errTail_close_placed` (`+0x504 → ret`) over `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoGames.LibsignalSession (SignalProtocolError)
open CryptoVerification (LibsignalHooks LibsignalPlacement blkPl_111)
open CryptoVerification.E2E.Pqxdh.ResponderWire (preKeyCalleeSavedAt preKeyPlacedProg preKeyTryFromSubStack)
open CryptoVerification.LibsignalTripleRatchet (lsLogOff smallRootStack)
open CryptoVerification.LibsignalTripleRatchet.Wire (PostEpilogueStatePlaced entails_of_eq tryFromQp)
open CryptoVerification.SignalSession.Cli.RunProofs.PksmWire (pksmErrE)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWSharedPlacedBudget

open Arm64 ProofLib.ProgramReflection
open ProofLib hiding SepWPp
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCPlacedBudget (
  err_epilogue_504_placed_wp
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget (
  w8bRetPost w8b_errRetPost_placed
)

private theorem spAligned_of_sub608 {sp : BitVec 64}
    (h : ((sp - 608#64) &&& 15#64 == 0#64) = true) :
    (sp &&& 15#64 == 0#64) = true := by
  simp only [beq_iff_eq] at h ⊢
  apply BitVec.eq_of_toNat_eq
  have h1 : ((sp - 608#64) &&& 15#64).toNat = 0 := by rw [h]; rfl
  rw [BitVec.toNat_and, show (15#64 : BitVec 64).toNat = 2 ^ 4 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_sub] at h1
  rw [BitVec.toNat_and, show (15#64 : BitVec 64).toNat = 2 ^ 4 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  have hlt := sp.isLt
  simp only [BitVec.toNat_ofNat] at h1 ⊢
  omega

/-- Recovers `s0.spAligned = true` from `PostEpilogueStatePlaced s0 (s0.sp - 608#64) s`. -/
theorem spAligned_of_postEpilogueStatePlaced [LibsignalPlacement] {s0 s : State}
    (hst : PostEpilogueStatePlaced s0 (s0.sp - 608#64) s) :
    s0.spAligned = true := by
  rcases hst with ⟨hsp_eq, hsp, _, _⟩
  unfold State.spAligned at hsp ⊢
  rw [hsp_eq] at hsp
  exact spAligned_of_sub608 hsp

/-- Shared `+0x504` (`1284`) error-epilogue closing under `[LibsignalPlacement]`:
steps `err_epilogue_504_placed_wp` and closes `w8bRetPost A lim RemEnv x st s0` for any
pre-accumulated `evs` satisfying `RemEnv evs`. -/
theorem w8b_errTail_close_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {RemEnv : List AllocEvent → Prop}
    {H : LibsignalHooks} {x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost} {st : M.σ} {evs : List AllocEvent}
    {s0 s : State} {R : SepProp} {fn : List (BitVec 8)} {e : SignalProtocolError}
    (hparse : CryptoVerification.SignalSession.Cli.RunProofs.Pksm.pksmParse x.bytes = none)
    (hevs : RemEnv evs)
    (hst : PostEpilogueStatePlaced s0 (s0.sp - 608#64) s)
    (hpc : s.pc = (blkPl_111).base + 1284#64)
    (hrun : s.status = .Running) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) s
      (pksmErrE A.repAlloc fn x.ret e ∗ R ∗
        stackAt (s0.sp - 608#64) preKeyTryFromSubStack ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool lim (M.stepEvents evs st) s)
      (w8bRetPost A lim RemEnv x st s0)
      (tryFromQp s0) := by
  have hsp0 : s0.spAligned = true := spAligned_of_postEpilogueStatePlaced hst
  have hsub_eq : smallRootStack = preKeyTryFromSubStack := rfl
  refine CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.SepWPp.mono_post
    (CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
      (P' := stackAt (s0.sp - 608#64) smallRootStack ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        (pksmErrE A.repAlloc fn x.ret e ∗ R) ∗
        (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool lim (M.stepEvents evs st) s)
      (by rw [hsub_eq]; apply entails_of_eq; sep_ac_rfl)
      (err_epilogue_504_placed_wp (A := A) (lim := lim) (x := x)
        (sretOut := pksmErrE A.repAlloc fn x.ret e ∗ R)
        (st := M.stepEvents evs st) hsp0 hst hpc hrun)) ?_
  intro sf Pf _ _ hq
  exact w8b_errRetPost_placed hparse hevs hq

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWSharedPlacedBudget
