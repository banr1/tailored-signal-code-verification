/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersParsePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.WorkFramePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Work Frame Unpack and Error-Frame Bridges for Arm `R1b`

Provides budget-threaded `init1MemPlaced` unpack and `r1b_invCore_placed` to `r1b_errCommon_placed`
frame conversion lemmas over `RustCliAllocBudget M` and `A.pool lim st s`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.WorkFramePlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement lsLogFilterAddr)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall ownedBytes)
open CryptoVerification.SignalSession.Cli.RunCompose
  (Init1Data r1b_errCommon r1b_invCore_placed runFsp)
open CryptoVerification.SignalSession.Cli.RunSkeleton (runFrame)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget (init1MemPlaced)

theorem r1b_invCore_placed_atState_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (g : RunCall) (d : Init1Data) (s0 : State) :
    r1b_invCore_placed (A.atState lim st s) g d s0 = r1b_invCore_placed A.repAlloc g d s0 := rfl

theorem r1b_init1Mem_unpack_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (g : RunCall) (d : Init1Data) (s0 s : State) (resStack : Nat) :
    let fsp := runFsp s0
    init1MemPlaced A lim st g d s0 s resStack ⊢
      r1b_invCore_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        memRegion fsp 0x110 ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 8 ∗ memRegion (fsp + 0x128#64) 8 ∗
        memRegion (fsp + 0x130#64) 8 ∗ memRegion (fsp + 0x138#64) 8 ∗
        memRegion (fsp + 0x140#64) 8 ∗ memRegion (fsp + 0x148#64) 8 ∗
        memRegion (fsp + 0x150#64) 8 ∗ memRegion (fsp + 0x158#64) 8 ∗
        memRegion (fsp + 0x164#64) 4 ∗
        memRegion (fsp + 0x168#64) 8 ∗ memRegion (fsp + 0x170#64) 8 ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 8 ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
        memRegion (fsp + 0x198#64) 16 ∗ ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
        ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
        memRegion (fsp + 0x1b4#64) 4 ∗
        memRegion (fsp + 0x4d0#64) 48 ∗ memRegion (fsp + 0x1750#64) 24 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s :=
  CryptoVerification.SignalSession.Cli.RunCompose.r1b_init1Mem_unpack_placed
    (A.atState lim st s) g d s0 resStack

theorem r1b_invCore_to_errCommon_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (g : RunCall) (d : Init1Data) (s0 s : State) (resStack : Nat) :
    let fsp := runFsp s0
    (r1b_invCore_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
      memRegion fsp 0x110 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
      memRegion (fsp + 0x164#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim st s) ⊢
      r1b_errCommon (A.atState lim st s) g d s0 resStack :=
  CryptoVerification.SignalSession.Cli.RunCompose.r1b_invCore_to_errCommon_placed
    (A.atState lim st s) g d s0 resStack

theorem r1b_stage_to_err_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (g : RunCall) (d : Init1Data) (s0 s : State) (resStack : Nat) (v164 : BitVec 32) :
    let fsp := runFsp s0
    (r1b_invCore_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
      memRegion fsp 0x110 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
      ((fsp + 0x164#64) ↦₃₂ v164) ∗
      ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
      ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
      ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
      memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim st s) ⊢
      r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x190#64) 8 ∗ memRegion (fsp + 0x1a8#64) 16 :=
  CryptoVerification.SignalSession.Cli.RunCompose.r1b_stage_to_err_placed
    (A.atState lim st s) g d s0 resStack v164

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.WorkFramePlacedBudget
