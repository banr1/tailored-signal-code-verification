/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2CalleesPlacedBudgetFd

/-!
# Descriptor-Threaded Relocatable Stage P2 Substage P2.4

Lifts budget-threaded placed Substage P2.4 (`opkId? = none` and `opkId? = some opkId`) via
`AllocWithFds.withFds A` to preserve `FdsGe3Closed`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4PlacedBudgetFd

open Arm64 Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  IdentitySelfStoreSpec IdentitySelfVtablesPlacedOk IdentityStoreSpec PreKeyStoreSpec
)
open CryptoVerification.RecordCodecs (PreKeyRecord)
open CryptoVerification.E2E.Pqxdh.Initiator (AcceptKeysInput DRKey Primitives)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (stageP2PureAndErrStack)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (
  BoxAllocEnv PreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget (
  IdentitySelfStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentitySelfStoreKitPlacedOkIFds PreKeyStoreKitPlacedOkFds
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  StageP2ClosureHooksPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudgetFd (
  pkKitFds_toWithFds
  selfKitFds_toWithFds
  stageP2ClosureHooks_toWithFds
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (
  FdsGe3Closed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds (
  withFds withFds_live withFds_pool_enforced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2CalleesPlacedBudgetFd (
  StageP2PureCalleesPlaced4KOfEnvFd
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget (
  boxAllocEvents
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4AuxPlacedBudget (
  p2OpkRecFreeEvents
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4PlacedBudget (
  stageP2Sub4SomeKitsPlacedProp stageP2_sub4_some_kits_ext_placed
  stageP2_sub4_some_kits_seqEnv_ext_placed
)

/-- `FdsGe3Closed`-preserving Substage P2.4-Some (`+0x0d5c -> +0x36ac` or `+0x09c4` Arm 3) via
`(withFds A, lim)`. -/
theorem stageP2_sub4_some_kits_ext_placed_fd [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true)
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlaced4KOfEnvFd P A lim F BobV1Env AcceptErrEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (pkEnv : PreKeyStoreBudgetEnv pkKit)
    (hpk_fds : pkKit.fdsOk = FdsGe3Closed)
    (hpkOk : PreKeyStoreKitPlacedOkFds A lim pkKit pkEnv ext)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (skit : IdentitySelfStoreSpec ikit)
    (senv : IdentitySelfStoreBudgetEnv skit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hskit_fds : skit.fdsOk = FdsGe3Closed)
    (hskitOk : IdentitySelfStoreKitPlacedOkIFds A lim ikit skit senv ext)
    (stk : Nat) (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_pk_shim : pkKit.getShimStack ≤ stk) (hstk_pk_poll : pkKit.getPollStack ≤ stk)
    (hstk_kp_shim : skit.kpShimStack ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (ret : BitVec 64) (st : M.σ) (s0 s : State) (Frame : SepProp)
    (Q : State → SepProp → Prop) {Qp : State → SepProp → Prop}
    (coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr ctSlicePtr
     v_98 v_a0 v_b0 u_a8 u_b8 u_d0 u_488 u_4f8 u_500 : BitVec 64)
    (opkId : BitVec 32) (stPk : pkKit.PkState)
    (b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
     c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init : BitVec 8)
    (cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init : BitVec 64)
    (hfits_shim : FitsEnv M lim st (BoxAllocEnv pkKit.getBoxSize))
    (hfits_poll : FitsEnv M lim (M.stepEvents (boxAllocEvents pkKit.getBoxSize) st)
      (pkEnv.getPollEnv stPk opkId))
    (hfits_kp : ∀ (r : PreKeyRecord) (evs_poll : List AllocEvent) (pubCap privCap : Nat),
      pkKit.getRel stPk opkId (.ok r) → pkKit.RecOk r →
      pkEnv.getPollEnv stPk opkId evs_poll →
      33 ≤ pubCap → 32 ≤ privCap →
      FitsEnv M lim
        (M.stepEvents
          (boxAllocEvents pkKit.getBoxSize ++ evs_poll ++
            p2OpkRecFreeEvents pkKit.getBoxSize pubCap privCap) st)
        (BoxAllocEnv skit.kpBoxSize)) :
    stageP2Sub4SomeKitsPlacedProp (withFds A) lim
      ext pkKit pkEnv ikit skit
      stk ret st s0 s Frame Q Qp
      coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr ctSlicePtr
      v_98 v_a0 v_b0 u_a8 u_b8 u_d0 u_488 u_4f8 u_500 opkId stPk
      b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
      c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init
      cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init :=
  stageP2_sub4_some_kits_ext_placed
    (A := withFds A) (lim := lim)
    (Qp := Qp) ext
    (stageP2ClosureHooks_toWithFds hH)
    (hPure.toWithFds henf)
    pkKit pkEnv (pkKitFds_toWithFds henf hpk_fds hpkOk)
    ikit skit senv hskitVt (selfKitFds_toWithFds henf hskit_fds hskitOk)
    stk hstk_pure hstk_pk_shim hstk_pk_poll hstk_kp_shim hstk_lt
    ret st s0 s Frame Q
    coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr ctSlicePtr
    v_98 v_a0 v_b0 u_a8 u_b8 u_d0 u_488 u_4f8 u_500 opkId stPk
    b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
    c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init
    cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init
    hfits_shim
    hfits_poll
    hfits_kp

theorem stageP2_sub4_some_kits_seqEnv_ext_placed_fd [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true)
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlaced4KOfEnvFd P A lim F BobV1Env AcceptErrEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (pkEnv : PreKeyStoreBudgetEnv pkKit)
    (hpk_fds : pkKit.fdsOk = FdsGe3Closed)
    (hpkOk : PreKeyStoreKitPlacedOkFds A lim pkKit pkEnv ext)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (skit : IdentitySelfStoreSpec ikit)
    (senv : IdentitySelfStoreBudgetEnv skit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hskit_fds : skit.fdsOk = FdsGe3Closed)
    (hskitOk : IdentitySelfStoreKitPlacedOkIFds A lim ikit skit senv ext)
    (stk : Nat) (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_pk_shim : pkKit.getShimStack ≤ stk) (hstk_pk_poll : pkKit.getPollStack ≤ stk)
    (hstk_kp_shim : skit.kpShimStack ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (ret : BitVec 64) (st : M.σ) (s0 s : State) (Frame : SepProp)
    (Q : State → SepProp → Prop) {Qp : State → SepProp → Prop}
    (coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr ctSlicePtr
     v_98 v_a0 v_b0 u_a8 u_b8 u_d0 u_488 u_4f8 u_500 : BitVec 64)
    (opkId : BitVec 32) (stPk : pkKit.PkState)
    (b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
     c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init : BitVec 8)
    (cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init : BitVec 64)
    (hfits : FitsEnv M lim st
      (SeqEnv (BoxAllocEnv pkKit.getBoxSize)
        (SeqEnv (pkEnv.getPollEnv stPk opkId)
          (SeqEnv FreeOnlyEvs (BoxAllocEnv skit.kpBoxSize))))) :
    stageP2Sub4SomeKitsPlacedProp (withFds A) lim
      ext pkKit pkEnv ikit skit
      stk ret st s0 s Frame Q Qp
      coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr ctSlicePtr
      v_98 v_a0 v_b0 u_a8 u_b8 u_d0 u_488 u_4f8 u_500 opkId stPk
      b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
      c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init
      cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init :=
  stageP2_sub4_some_kits_seqEnv_ext_placed
    (A := withFds A) (lim := lim)
    (Qp := Qp) ext
    (stageP2ClosureHooks_toWithFds hH)
    (hPure.toWithFds henf)
    pkKit pkEnv (pkKitFds_toWithFds henf hpk_fds hpkOk)
    ikit skit senv hskitVt (selfKitFds_toWithFds henf hskit_fds hskitOk)
    stk hstk_pure hstk_pk_shim hstk_pk_poll hstk_kp_shim hstk_lt
    ret st s0 s Frame Q
    coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr ctSlicePtr
    v_98 v_a0 v_b0 u_a8 u_b8 u_d0 u_488 u_4f8 u_500 opkId stPk
    b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
    c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init
    cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init
    hfits

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4PlacedBudgetFd
