/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmVarintBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmVarintPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5Budget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5PlacedBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget
import Arm64.Trusted.Spec.Hoare
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Varint Arm Entrypoints

Canonical `[LibsignalPlacement]` total-correctness (`RustCliAllocBudget M`) entrypoints for the
varint field arms (tags 1, 5, 10, 11) on Block `518` (`lsProg_518 ext`), backed by
`PrevDec.ArmVarintBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmVarintPlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkPl_518 lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (
  OverDecG OverDecRegsPlaced OverDecVarintField overDecArmOff overDecWt
)
open Symbolic.Swarm.TRREF.B3DeserQ (GenFieldQ SSGQ)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsBudget (
  OverDecArmCroPlacedAtTR OverDecArmPlacedStmtTR OverDecFieldEnv overDecHeapBudget
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5Budget (
  decodeVarint2SpecX
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5PlacedBudget (
  DecodeVarint5PlacedOkExtX decodeVarint5_placed_ok_ext_x
)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (AllocContractsPlaced)

export LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmVarintBudget (
  overDecVarint_pre_tag1_placed overDecVarint_post_tag1_placed
  overDecVarint_pre_tag5_placed overDecVarint_post_tag5_placed
  overDecVarint_pre_tag10_placed overDecVarint_post_tag10_placed
  overDecVarint_pre_tag11_placed overDecVarint_post_tag11_placed
)

/-- Plain (`OverDecRegsPlaced`, no `LibsignalCodeRoLoaded`) budget-threaded varint arms on `lsProg_518 ext`. -/
theorem overDecArm_varint_placed_ext_of_dv5 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hDv5 : subroutine_ok (lsProg_518 ext) (lsmpl.base 515) (decodeVarint2SpecX A lim)) :
    ∀ (st : M.σ) (s0 s : State) (g : OverDecG) (v : SSGQ) (fl : GenFieldQ) (rest : List (BitVec 8)),
      OverDecVarintField fl → fl.Ok → fl.Fresh v →
      (fl.enc ++ rest) <:+ g.enc → g.enc.length < 2 ^ 62 →
      FitsEnv M lim st (OverDecFieldEnv fl) →
      OverDecRegsPlaced ext s0 g (overDecArmOff fl) s →
      s.readReg64 .x0 = overDecWt fl →
      s.readReg64 .x22 = BitVec.ofNat 64 (fl.tag * 8 + (overDecWt fl).toNat) →
      SepWPp (lsProg_518 ext) ((blkPl_518).base + 8544#64) s
        (overDecHeapBudget A lim st s g (fl.payload ++ rest) v)
        (fun sf P_f => OverDecRegsPlaced ext s0 g 8544#64 sf ∧
          ∃ evs, OverDecFieldEnv fl evs ∧
            (P_f ⊢ overDecHeapBudget A lim (M.stepEvents evs st) sf g rest (v.apply fl)))
        (fun _ _ => False) :=
  ArmVarintBudget.overDecArm_varint_placed_ext_of_dv5 hDv5

/-- Fixed-`ext` `LibsignalCodeRoLoaded` budget-threaded varint arms from `withLsCodeLoaded`
`decodeVarint2SpecX` on `lsmpl.base 515`. -/
theorem overDecArm_varint_cro_placed_of_dv5_lscl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hDv5 : subroutine_ok (lsProg_518 ext) (lsmpl.base 515)
      (withLsCodeLoaded lsmpl (decodeVarint2SpecX A lim))) :
    OverDecArmCroPlacedAtTR A lim ext OverDecVarintField :=
  ArmVarintBudget.overDecArm_varint_cro_placed_of_dv5_lscl hDv5

alias overDecArm_varint_cro_placed_of_lscl_dv5 := overDecArm_varint_cro_placed_of_dv5_lscl

theorem overDecArm_varint_cro_placed_of_dv5_cl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hDv5 : DecodeVarint5PlacedOkExtX A lim ext) :
    OverDecArmCroPlacedAtTR A lim ext OverDecVarintField :=
  ArmVarintBudget.overDecArm_varint_cro_placed_of_dv5_cl hDv5

alias overDecArm_varint_cro_placed_of_dv5 := overDecArm_varint_cro_placed_of_dv5_cl

/-- Fixed-`ext` `LibsignalCodeRoLoaded` budget-threaded varint arms discharged directly from
`AllocContractsPlaced M A lim ext`. -/
theorem overDecArm_varint_cro_placed_of_alloc [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hAlloc : AllocContractsPlaced M A lim ext) :
    OverDecArmCroPlacedAtTR A lim ext OverDecVarintField :=
  ArmVarintBudget.overDecArm_varint_cro_placed_of_alloc hAlloc

alias overDecArm_varint_cro_placed_of_hooks := overDecArm_varint_cro_placed_of_alloc

theorem overDecArm_varint_placed_of_dv5 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hDv5 : ∀ ext, DecodeVarint5PlacedOkExtX A lim ext) :
    OverDecArmPlacedStmtTR A lim OverDecVarintField :=
  ArmVarintBudget.overDecArm_varint_placed_of_dv5 hDv5

alias overDecArm_varint_cli_placed_of_dv5 := overDecArm_varint_placed_of_dv5

theorem overDecArm_varint_placed_of_dv5_plain [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hDv5 : ∀ ext, subroutine_ok (lsProg_518 ext) (lsmpl.base 515) (decodeVarint2SpecX A lim)) :
    OverDecArmPlacedStmtTR A lim OverDecVarintField :=
  ArmVarintBudget.overDecArm_varint_placed_of_dv5_plain hDv5

theorem overDecArm_varint_placed_of_alloc [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hAlloc : ∀ ext, AllocContractsPlaced M A lim ext) :
    OverDecArmPlacedStmtTR A lim OverDecVarintField :=
  fun ext => overDecArm_varint_cro_placed_of_alloc (hAlloc ext)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmVarintPlacedBudget
