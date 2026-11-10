/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA3PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4AuxPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4Aux
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs

/-!
# Budget-Threaded Relocatable Stage P2 Substage P2.4 Helpers, `None` Branch, and Post-Drop Tail

Defines `P2Sub4NoneEnv` and `P2Sub4SomeTailEnv`, and proves budget-threaded placed Substage
P2.4-None (`+0x0d5c → +0x36ac`) and post-`futDrop` tail (`+0x0e40 → +0x36ac`) on Block `518`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4AuxPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  publicKeySerializeSpec publicKeySerializeSpecWithStack
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit hiding
  kitPreKeyGetShimSpec kitPreKeyGetPollSpec kitPreKeyGetPollSpecE kitKpShimSpec
  PreKeyStoreKitPlacedOk IdentitySelfStoreKitPlacedOkI
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Shared
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderStore hiding
  sessionRecordEmptyHeaderAt promoteMatchingSessionEmptySpec promoteStateEmptySpec
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits hiding
  StageP2ClosureHooksPlaced
  StageP2PureCalleesPlaced
  StageP2PureCalleesPlaced4K
  StageP2PureCalleesExtPlaced
  InitializeBobV1OkPlaced
  InitializeBobV1OkPlaced4K
  promoteStateEmpty4KSpec
  isSameAccountDistinctAtSpec
  p2Memcpy4KSpec
  p2_seg4_none_ext_placed_wp
  p2_seg4d_hooks_placed_wp
  p2_seg4e_hooks_placed_wp
  p2_pkGetShim_pre_intro_placed
  p2_pkGetPoll_pre_intro_placed
  p2_kpShim_pre_intro_placed
  stageP2_sub4_none_kits_placed
  stageP2_sub4_none_kits_ext_placed
  stageP2_sub4_none_kits_4k_placed
  stageP2_sub4_none_kits_hooks_placed
  stageP2_sub4_some_tail_kits_ext_placed
  stageP2_sub4_some_tail_kits_4k_placed
  stageP2_sub4_some_tail_kits_hooks_placed
  stageP2_sub4_some_tail_kits_placed
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FitsStep
  FreeOnlyEvs RustCliAllocBudget SeqEnv VmPreserved coarseCostModel coarseStep
  coarseStepReserve fitsEvents_append rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (
  BoxAllocEnv PreKeyStoreBudgetEnv kitPreKeyGetShimSpec kitPreKeyGetPollSpec
  kitPreKeyGetPollSpecE
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget (
  IdentitySelfStoreBudgetEnv kitKpShimSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  PreKeyStoreKitPlacedOk IdentitySelfStoreKitPlacedOkI
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  StageP2ClosureHooksPlaced
  StageP2PureCalleesPlaced StageP2PureCalleesPlaced4K
  StageP2PureCalleesPlaced4KOfEnv StageP2PureCalleesPlacedOfEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA3PlacedBudget (
  p2_seg4_none_ext_placed_wp
  p2_seg4d_hooks_placed_wp
  p2_seg4e_hooks_placed_wp
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget (
  boxAllocEvents boxAllocEnv_iff_eq fitsEnv_boxAllocEnv_iff
  p2_bind_sepWP_qp_frame_state_placed
  p2_call_nopanic_lscl_steps_frame_placed
  p2_call_rocl_nopanic_steps_frame_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2PlacedBudget (
  freeOnlyEvs_rustDeallocEvents
)

set_option maxRecDepth 200000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  protocolAddressAt decryptPrekeySavedRegsAt

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [RustCliAllocBudget.repAlloc_live]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

/-! ## 1. Placed Budget Store-Kit Precondition Introduction Helpers -/

/-- Budget-threaded `kitPreKeyGetShimSpec` precondition introduction at `b = 0#64`. -/
theorem p2_pkGetShim_pre_intro_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {pkKit : PreKeyStoreSpec A.repAlloc 0#64}
    {x : PreKeyShimCall} {st : M.σ} {s : State}
    (hx0 : s.readReg64 .x0 = x.self) (hx1 : s.readReg32 .x1 = x.id)
    (hfits : FitsEnv M lim st (BoxAllocEnv pkKit.getBoxSize)) :
    A.pool lim st s ∗ stackAt s.sp pkKit.getShimStack ⊢
      (kitPreKeyGetShimSpec M A lim pkKit).pre (x, st) s := by
  dsimp only [kitPreKeyGetShimSpec]
  exact Entails.pure_right ⟨rfl, hx0, hx1, hfits⟩ (Entails.refl _)

/-- Budget-threaded `kitPreKeyGetPollSpecE` precondition introduction at `b = 0#64`. -/
theorem p2_pkGetPoll_pre_intro_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {pkKit : PreKeyStoreSpec A.repAlloc 0#64}
    {pkEnv : PreKeyStoreBudgetEnv pkKit}
    {x : PreKeyPollCall} {st0 : pkKit.PkState} {st : M.σ} {s : State}
    (henv : pkKit.envOk s.fs.files)
    (hx0 : s.readReg64 .x0 = x.fut) (hx8 : s.readReg64 .x8 = x.out)
    (hid : pkKit.getIdOk x.id)
    (hfits : FitsEnv M lim st (pkEnv.getPollEnv st0 x.id)) :
    pkKit.getBoxAt x.fut x.self x.id 0#8 ∗ pkKit.storeAt x.self st0 ∗
      memRegion x.out 56 ∗ A.pool lim st s ∗ stackAt s.sp pkKit.getPollStack ⊢
        (kitPreKeyGetPollSpecE M A lim pkKit pkEnv).pre (x, st0, st) s := by
  dsimp only [kitPreKeyGetPollSpecE, withEnvPre, kitPreKeyGetPollSpec]
  exact Entails.pure_right henv (Entails.pure_right ⟨rfl, hx0, hx8, hid, hfits⟩ (Entails.refl _))

/-- Budget-threaded `kitKpShimSpec` precondition introduction at `b = 0#64`. -/
theorem p2_kpShim_pre_intro_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {skit : IdentitySelfStoreSpec ikit}
    {self : BitVec 64} {st : M.σ} {s : State}
    (hx0 : s.readReg64 .x0 = self)
    (hfits : FitsEnv M lim st (BoxAllocEnv skit.kpBoxSize)) :
    A.pool lim st s ∗ stackAt s.sp skit.kpShimStack ⊢
      (kitKpShimSpec M A lim skit).pre (self, st) s := by
  dsimp only [kitKpShimSpec]
  exact Entails.pure_right ⟨hx0, hfits⟩ (Entails.refl _)

/-! ## 2. Substage P2.4-None & Post-Poll Tail Event Lists and Envelopes -/

/-- Exact deterministic allocator event list of Substage P2.4-None (`+0x0d5c -> +0x36ac`):
`skit.kpShim` (`boxAllocEvents kpBoxSize`). -/
def p2Sub4NoneEvents (kpBoxSize : Nat) : List AllocEvent :=
  boxAllocEvents kpBoxSize

/-- Exact allocator event envelope of Substage P2.4-None (`+0x0d5c -> +0x36ac`). -/
def P2Sub4NoneEnv (kpBoxSize : Nat) (evs : List AllocEvent) : Prop :=
  evs = p2Sub4NoneEvents kpBoxSize

theorem fitsEnv_p2Sub4NoneEnv_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (kpBoxSize : Nat) :
    FitsEnv M lim st (P2Sub4NoneEnv kpBoxSize) ↔
      FitsEvents M lim st (p2Sub4NoneEvents kpBoxSize) :=
  FitsEnv.eq_iff

theorem p2Sub4NoneEnv_iff_boxAllocEnv (kpBoxSize : Nat) (evs : List AllocEvent) :
    P2Sub4NoneEnv kpBoxSize evs ↔ BoxAllocEnv kpBoxSize evs :=
  (boxAllocEnv_iff_eq kpBoxSize evs).symm

-- Concrete `FitsEnv` non-vacuity witness for `P2Sub4NoneEnv 64` under `coarseCostModel`.
example :
    FitsEnv coarseCostModel
      { staticCount := 64, staticBytes := 67108864, physCap := 536870912, enforced := true }
      coarseCostModel.init
      (P2Sub4NoneEnv 64) := by
  rw [fitsEnv_p2Sub4NoneEnv_iff]
  have hevs : p2Sub4NoneEvents 64 = [.alloc 64] := by decide
  rw [hevs]
  dsimp only [FitsEvents, FitsEvent, AllocEvent.withinMaxAlloc, FitsStep,
    AllocCostModel.step, coarseCostModel, coarseStep, coarseStepReserve]
  decide

/-- Exact deterministic deallocation events performed along the `.ok r` post-`futDrop` tail of
Substage P2.4 (`+0x0e40 -> skit.kpShim`):
`__rust_dealloc(opkBoxSize, 8)` on the OPK poll future box followed by freeing the cloned
`publicKey` and `privateKey` `Vec<u8>` buffers. -/
def p2OpkRecFreeEvents (opkBoxSize pubCap privCap : Nat) : List AllocEvent :=
  rustDeallocEvents opkBoxSize 8 ++
    rustDeallocEvents pubCap 1 ++
    rustDeallocEvents privCap 1

theorem p2OpkRecFreeEvents_freeOnly (opkBoxSize pubCap privCap : Nat) :
    FreeOnlyEvs (p2OpkRecFreeEvents opkBoxSize pubCap privCap) :=
  FreeOnlyEvs.append
    (FreeOnlyEvs.append (freeOnlyEvs_rustDeallocEvents opkBoxSize 8)
      (freeOnlyEvs_rustDeallocEvents pubCap 1))
    (freeOnlyEvs_rustDeallocEvents privCap 1)

/-- Exact deterministic allocator event list of the post-`futDrop` tail of Substage P2.4-Some
(`+0x0e40 -> +0x36ac`): `p2OpkRecFreeEvents` followed by `skit.kpShim`'s
`boxAllocEvents kpBoxSize`. -/
def p2Sub4SomeTailEvents (opkBoxSize pubCap privCap kpBoxSize : Nat) : List AllocEvent :=
  p2OpkRecFreeEvents opkBoxSize pubCap privCap ++ boxAllocEvents kpBoxSize

/-- Exact allocator event envelope for the post-`futDrop` tail of Substage P2.4-Some
(`+0x0e40 -> +0x36ac`). -/
def P2Sub4SomeTailEnv (opkBoxSize pubCap privCap kpBoxSize : Nat)
    (evs : List AllocEvent) : Prop :=
  evs = p2Sub4SomeTailEvents opkBoxSize pubCap privCap kpBoxSize

theorem fitsEnv_p2Sub4SomeTailEnv_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (opkBoxSize pubCap privCap kpBoxSize : Nat) :
    FitsEnv M lim st (P2Sub4SomeTailEnv opkBoxSize pubCap privCap kpBoxSize) ↔
      FitsEvents M lim st (p2Sub4SomeTailEvents opkBoxSize pubCap privCap kpBoxSize) :=
  FitsEnv.eq_iff

-- Concrete `FitsEnv` non-vacuity witness for `P2Sub4SomeTailEnv 64 33 32 64` under `coarseCostModel`.
example :
    FitsEnv coarseCostModel
      { staticCount := 64, staticBytes := 67108864, physCap := 536870912, enforced := true }
      coarseCostModel.init
      (P2Sub4SomeTailEnv 64 33 32 64) := by
  rw [fitsEnv_p2Sub4SomeTailEnv_iff]
  have hevs : p2Sub4SomeTailEvents 64 33 32 64 =
      [.free 8 64, .free 1 33, .free 1 32, .alloc 64] := by decide
  rw [hevs]
  dsimp only [FitsEvents, FitsEvent, AllocEvent.withinMaxAlloc, FitsStep,
    AllocCostModel.step, coarseCostModel, coarseStep, coarseStepReserve]
  decide

/-! ## 3. Budget-Threaded Placed Substage P2.4-None (`+0x0d5c -> +0x36ac`) -/

set_option maxHeartbeats 1200000 in
/-- Budget-Threaded Placed Kit-Generic Substage P2.4-None (`+0x0d5c -> +0x36ac`, `opkId? = none`,
`[msgPtr + 0x78] = 0#32`) in CPS form on `stageP1ProgPlaced ext`:
stores `ctSlicePtr` at `[coroPtr + 0x488]`, sets `[coroPtr + 0x4b0] = 0#8`, and invokes
`skit.kpShim` reaching `+0x36ac` (`hOk`) with
`A.pool lim (M.stepEvents (boxAllocEvents skit.kpBoxSize) st) sf` (`0` panics / `0` OOM under
`FitsEnv M lim st (BoxAllocEnv skit.kpBoxSize)`). -/
theorem stageP2_sub4_none_kits_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (skit : IdentitySelfStoreSpec ikit)
    (senv : IdentitySelfStoreBudgetEnv skit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (stk : Nat) (hstk_kp_shim : skit.kpShimStack ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (ret : BitVec 64) (st : M.σ) (s0 s : State) (Frame : SepProp)
    (Q : State → SepProp → Prop) {Qp : State → SepProp → Prop}
    (coroPtr msgPtr ctxPtr idStorePtr ctSlicePtr v_b0 u_488 : BitVec 64)
    (opkId : BitVec 32) (b_4b0 : BitVec 8)
    (hfits : FitsEnv M lim st (BoxAllocEnv skit.kpBoxSize))
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = stageP1EntryPlaced + 0xd5c#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = ctSlicePtr)
    (hOk : ∀ (idKpFutPtr : BitVec 64) (sf : State),
      Steps (stageP1ProgPlaced ext) s sf →
      sf.pc = stageP1EntryPlaced + 0x36ac#64 →
      sf.status = .Running → sf.sp = s.sp → sf.trace = s.trace →
      sf.readReg64 .x0 = idKpFutPtr → sf.readReg64 .x1 = 0#64 + skit.kpFutVtOff →
      idKpFutPtr ≠ 0#64 → idKpFutPtr.toNat % 8 = 0 →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x21 = v_b0 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.sp + 0x370#64 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = ctxPtr → sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (stageP1ProgPlaced ext) ret sf
        (A.live idKpFutPtr skit.kpBoxSize 8 ∗
         skit.kpBoxAt idKpFutPtr idStorePtr 0#8 ∗
         ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
         ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
         ((coroPtr + 0x488#64) ↦₆₄ ctSlicePtr) ∗
         ((coroPtr + 0x4b0#64) ↦₈ 0#8) ∗
         ((msgPtr + 0x78#64) ↦₃₂ 0#32) ∗
         ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗
         ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
         ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
         A.pool lim (M.stepEvents (boxAllocEvents skit.kpBoxSize) st) sf ∗
         stackAt s.sp stk ∗ Frame)
        Q Qp) :
    SepWPp (stageP1ProgPlaced ext) ret s
      (((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
       ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗
       ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
       ((msgPtr + 0x78#64) ↦₃₂ 0#32) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       A.pool lim st s ∗ stackAt s.sp stk ∗ Frame)
      Q Qp := by
  refine p2_ro_intro_sepWPp (hskitVt.kpSlot hCode.2) ?_
  have hstep1 := p2_seg4_none_ext_placed_wp (A := A) (lim := lim) ext st s coroPtr msgPtr ctxPtr
    idStorePtr ikit.id_vt (0#64 + skit.kpShimOff) ctSlicePtr v_b0 u_488 opkId b_4b0
    hpc hrun hsp_align hx19 hx21
  refine p2_bind_sepWP_qp_frame_state_placed hCode hstep1 (by sep_focus)
    fun s1 hst01 hpc1 hrun1 hCode1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx19_1, hx21_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  refine p2_sub4_drop_sep_frame
    (Drop := ((ikit.id_vt + 0x18#64) ↦₆₄ᵣ (0#64 + skit.kpShimOff))) (by sep_focus) ?_
  have hstk_shim := p2_stackAt_split_of_le s.sp stk skit.kpShimStack hstk_kp_shim hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_shim) (by sep_focus) ?_
  sep_norm
  refine p2_call_rocl_nopanic_steps_frame_placed
    (x := (idStorePtr, st))
    hCode1 (hskitOk.kpShim (by decide)) hpc1 hrun1 hsp1_al hx30_1
    (hsp1 ▸ p2_kpShim_pre_intro_placed hx0_1 hfits)
    (by sep_focus)
    (hnext := fun sf hst1f hpcf hrunf hspf_1 _ hcsf hCodef => ?_)
  dsimp only [kitKpShimSpec]
  rcases hcsf with ⟨hcsf_19, _, hcsf_21, _, hcsf_23, hcsf_24, hcsf_25, hcsf_26, hcsf_27, hcsf_28,
    hcsf_29, hvregsf_1⟩
  rw [hsp1]
  sep_norm
  refine SepWPp.exists_elim fun evs_kp =>
    SepWPp.pure_elim fun ⟨hx1_f, hx0_nz, hx0_al, htrf_1, hevs_kp⟩ => ?_
  have hevs_kp_eq : evs_kp = boxAllocEvents skit.kpBoxSize :=
    (boxAllocEnv_iff_eq skit.kpBoxSize evs_kp).mp hevs_kp
  rw [hevs_kp_eq]
  refine SepWPp.weaken_frame (Entails.of_eq hstk_shim.symm) (by sep_focus) ?_
  have hok := hOk (sf.readReg64 .x0) sf (hst01.trans hst1f) hpcf hrunf (hspf_1.trans hsp1)
    (htrf_1.trans htr1) rfl hx1_f hx0_nz hx0_al
    (hcsf_19.trans hx19_1) (hcsf_21.trans hx21_1) (hcsf_23.trans hx23_1)
    (hcsf_24.trans hx24_1) (hcsf_25.trans hx25_1) (hcsf_26.trans hx26_1)
    (hcsf_27.trans hx27_1) (hcsf_28.trans hx28_1) (hcsf_29.trans hx29_1)
    (by rw [hvregsf_1, hvregs1, hvregs]) hCodef
  exact p2_sepWPp_weaken_eq hok (by sep_focus)

abbrev stageP2_sub4_none_kits_ext_placed := @stageP2_sub4_none_kits_placed
abbrev stageP2_sub4_none_kits_4k_placed := @stageP2_sub4_none_kits_placed
abbrev stageP2_sub4_none_kits_hooks_placed := @stageP2_sub4_none_kits_placed

/-! ## 4. Budget-Threaded Placed Post-`futDrop` Tail (`+0x0e40 -> +0x36ac`) -/

set_option maxHeartbeats 1400000 in
/-- Budget-Threaded Placed Post-`futDrop` Tail (`+0x0e40 -> +0x36ac`) of
`stageP2_sub4_some_kits_placed`:
deallocates `opkFutPtr`, calls `PreKeyRecord::key_pair` (`VmPreserved`), stores the clamped OPK
keypair at `coroPtr + 0x4b0..0x4f0`, frees `pubPtr`/`privPtr` (`p2OpkRecFreeEvents`), and invokes
`skit.kpShim` reaching `+0x36ac` (`hDone`) with
`A.pool lim (M.stepEvents (p2Sub4SomeTailEvents pkKit.getBoxSize pubCap.toNat privCap.toNat skit.kpBoxSize) st) sf`. -/
theorem stageP2_sub4_some_tail_kits_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlaced4KOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (skit : IdentitySelfStoreSpec ikit)
    (senv : IdentitySelfStoreBudgetEnv skit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (stk : Nat) (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_kp_shim : skit.kpShimStack ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (ret : BitVec 64) (st : M.σ) (s0 s6 : State) (sp : BitVec 64)
    (TailFrame : SepProp) (Q : State → SepProp → Prop) {Qp : State → SepProp → Prop}
    (coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr opkFutPtr
     pubCap pubPtr privCap privPtr opkIdWord u_ac8 v_98 v_a0 v_b0 : BitVec 64)
    (opkId : BitVec 32) (opkPubBytes opkPrivBytes : List (BitVec 8))
    (b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
     c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init : BitVec 8)
    (cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init : BitVec 64)
    (hfits_kp : FitsEnv M lim
      (M.stepEvents (p2OpkRecFreeEvents pkKit.getBoxSize pubCap.toNat privCap.toNat) st)
      (BoxAllocEnv skit.kpBoxSize))
    (hpub_len : opkPubBytes.length = 32) (hpriv_len : opkPrivBytes.length = 32)
    (hpub_le : (5#8 :: opkPubBytes).length ≤ pubCap.toNat)
    (hpub_nz : pubCap ≠ 0#64) (hpub_ne1 : pubCap ≠ 0xffffffffffffffff#64)
    (hCode6 : StoreKit.LibsignalCodeRoLoaded lsmpl s6.mem)
    (hpc6 : s6.pc = stageP1EntryPlaced + 0xe40#64)
    (hrun6 : s6.status = .Running) (hsp6 : s6.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hvregs6 : calleeSavedVRegs s6 = calleeSavedVRegs s0)
    (hx19_6 : s6.readReg64 .x19 = coroPtr) (hx21_6 : s6.readReg64 .x21 = opkFutPtr)
    (hx22_6 : s6.readReg64 .x22 = pubCap) (hx23_6 : s6.readReg64 .x23 = 33#64)
    (hx24_6 : s6.readReg64 .x24 = 0#64 + pkKit.getFutVtOff)
    (hx26_6 : s6.readReg64 .x26 = pubPtr) (hx27_6 : s6.readReg64 .x27 = opkIdWord)
    (hx28_6 : s6.readReg64 .x28 = sp + 0xa90#64)
    (hDone : ∀ (idKpFutPtr : BitVec 64)
      (b0 b1 b2 b3 b4 b5 b6 b63 c0 c1 c2 c3 c4 c5 c6 : BitVec 8)
      (w0 w1 w2 w3 w4 w5 w6 u0_kp u1_kp u2_kp u3_kp u4_kp u5_kp u6_kp u7_kp : BitVec 64)
      (sf : State),
      Steps (stageP1ProgPlaced ext) s6 sf →
      (∀ a : BitVec 64, (a ↦ₛ opkPubBytes) =
        (a ↦₆₄ u0_kp) ∗ ((a + 8#64) ↦₆₄ u1_kp) ∗ ((a + 16#64) ↦₆₄ u2_kp) ∗
          ((a + 24#64) ↦₆₄ u3_kp)) →
      (∀ a : BitVec 64, (a ↦ₛ clampBv8List opkPrivBytes) =
        (a ↦₆₄ u4_kp) ∗ ((a + 8#64) ↦₆₄ u5_kp) ∗ ((a + 16#64) ↦₆₄ u6_kp) ∗
          ((a + 24#64) ↦₆₄ u7_kp)) →
      (∀ a : BitVec 64,
        bytes7At a b0 b1 b2 b3 b4 b5 b6 ∗
        ((a + 7#64) ↦₆₄ w0) ∗ ((a + 15#64) ↦₆₄ w1) ∗ ((a + 23#64) ↦₆₄ w2) ∗ ((a + 31#64) ↦₆₄ w3) =
          (a ↦₆₄ u0_kp) ∗ ((a + 8#64) ↦₆₄ u1_kp) ∗ ((a + 16#64) ↦₆₄ u2_kp) ∗
            ((a + 24#64) ↦₆₄ u3_kp) ∗ bytes7At (a + 32#64) c0 c1 c2 c3 c4 c5 c6) →
      (∀ a : BitVec 64,
        bytes7At a c0 c1 c2 c3 c4 c5 c6 ∗
        ((a + 7#64) ↦₆₄ w4) ∗ ((a + 15#64) ↦₆₄ w5) ∗ ((a + 23#64) ↦₆₄ w6) ∗ ((a + 31#64) ↦₈ b63) =
          (a ↦₆₄ u4_kp) ∗ ((a + 8#64) ↦₆₄ u5_kp) ∗ ((a + 16#64) ↦₆₄ u6_kp) ∗
            ((a + 24#64) ↦₆₄ u7_kp)) →
      sf.pc = stageP1EntryPlaced + 0x36ac#64 →
      sf.status = .Running → sf.sp = sp → sf.trace = s6.trace →
      sf.readReg64 .x0 = idKpFutPtr → sf.readReg64 .x1 = 0#64 + skit.kpFutVtOff →
      idKpFutPtr ≠ 0#64 → idKpFutPtr.toNat % 8 = 0 →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x21 = v_b0 →
      sf.readReg64 .x23 = v_a0 → sf.readReg64 .x24 = sp + 0x370#64 →
      sf.readReg64 .x25 = s6.readReg64 .x25 → sf.readReg64 .x26 = v_98 →
      sf.readReg64 .x27 = ctxPtr → sf.readReg64 .x28 = sp + 0xa90#64 →
      sf.readReg64 .x29 = s6.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (stageP1ProgPlaced ext) ret sf
        (A.live idKpFutPtr skit.kpBoxSize 8 ∗
         skit.kpBoxAt idKpFutPtr idStorePtr 0#8 ∗
         ((sp + 0x98#64) ↦₆₄ v_98) ∗ ((sp + 0xa0#64) ↦₆₄ v_a0) ∗
         ((sp + 0xa8#64) ↦₆₄ 32#64) ∗ ((sp + 0xb0#64) ↦₆₄ v_b0) ∗
         ((sp + 0xb8#64) ↦₆₄ privCap) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
         ((sp + 0xd0#64) ↦₆₄ privPtr) ∗ memRegion (sp + 0x270#64) 9 ∗
         bytes7At (sp + 0x3b0#64) b0 b1 b2 b3 b4 b5 b6 ∗
         memRegion (sp + 0x3e0#64) 88 ∗ memRegion (sp + 0x930#64) 56 ∗
         memRegion (sp + 0xa90#64) 65 ∗
         ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
         ((coroPtr + 0x4b0#64) ↦₈ 1#8) ∗
         keyPair64UnalignedAt (coroPtr + 0x4b1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
         ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
         ((0#64 + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
         ((0#64 + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         A.pool lim
           (M.stepEvents
             (p2Sub4SomeTailEvents pkKit.getBoxSize pubCap.toNat privCap.toNat skit.kpBoxSize) st)
           sf ∗
         stackAt sp stk ∗ TailFrame)
        Q Qp) :
    SepWPp (stageP1ProgPlaced ext) ret s6
      (pkKit.getBoxAt opkFutPtr preKeyStorePtr opkId 1#8 ∗
       A.live opkFutPtr pkKit.getBoxSize 8 ∗
       preKeyRecordOut64At (sp + 0xa90#64) pubCap pubPtr 33#64 privCap privPtr 32#64 opkIdWord u_ac8 ∗
       memRegion (sp + 0xad0#64) 1 ∗
       A.live pubPtr pubCap.toNat 1 ∗ (pubPtr ↦ₛ (5#8 :: opkPubBytes)) ∗
       memRegion (pubPtr + BitVec.ofNat 64 (5#8 :: opkPubBytes).length)
         (pubCap.toNat - (5#8 :: opkPubBytes).length) ∗
       vecU8Buf A.repAlloc privCap privPtr opkPrivBytes ∗
       ((sp + 0x98#64) ↦₆₄ v_98) ∗ ((sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((sp + 0xa8#64) ↦₆₄ 32#64) ∗ ((sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((sp + 0xb8#64) ↦₆₄ privCap) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((sp + 0xd0#64) ↦₆₄ privPtr) ∗ memRegion (sp + 0x270#64) 9 ∗
       bytes7At (sp + 0x3b0#64) s0_b s1_b s2_b s3_b s4_b s5_b s6_b ∗
       memRegion (sp + 0x3e0#64) 88 ∗ memRegion (sp + 0x930#64) 56 ∗
       ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
       ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
       keyPair64UnalignedAt (coroPtr + 0x4b1#64) c0_init c1_init c2_init c3_init
         c4_init c5_init c6_init cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init
         cw6_init c63_init ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((0#64 + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
       ((0#64 + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.pool lim st s6 ∗ stackAt sp stk ∗ TailFrame)
      Q Qp := by
  have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by rw [hsp6]; exact hsp_align
  refine SepWPp.weaken_frame (p2_vecU8Buf_nonempty A.repAlloc privCap privPtr opkPrivBytes (by omega))
    (by sep_focus) ?_
  sep_norm
  refine SepWPp.pure_elim fun ⟨hpriv_le, _, hpriv_nz, _, _⟩ => ?_
  refine SepWPp.weaken_frame (pkKit.getBoxAt_memRegion opkFutPtr preKeyStorePtr opkId 1#8)
    (by sep_focus) ?_
  rw [show sp + 0xad0#64 = (sp + 0xa90#64) + 0x40#64 by bv_omega]
  refine SepWPp.weaken_frame
    (p2_preKeyRecordOut64_65_entails_memRegion (sp + 0xa90#64)
      pubCap pubPtr 33#64 privCap privPtr 32#64 opkIdWord u_ac8)
    (by sep_focus) ?_
  have hstk_alloc := p2_stackAt_split_of_le sp stk allocHookStack
    (Nat.le_trans p2_alloc_le_pure hstk_pure) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_memRegion_56_split_7words (sp + 0x930#64)))
    (by sep_focus) ?_
  rw [show (sp + 0x930#64) + 0x08#64 = sp + 0x938#64 by bv_omega,
      show (sp + 0x930#64) + 0x10#64 = sp + 0x940#64 by bv_omega,
      show (sp + 0x930#64) + 0x18#64 = sp + 0x948#64 by bv_omega,
      show (sp + 0x930#64) + 0x20#64 = sp + 0x950#64 by bv_omega,
      show (sp + 0x930#64) + 0x28#64 = sp + 0x958#64 by bv_omega,
      show (sp + 0x930#64) + 0x30#64 = sp + 0x960#64 by bv_omega]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun r6 => SepWPp.exists_elim fun r5 =>
    SepWPp.exists_elim fun r4 => SepWPp.exists_elim fun r3 =>
    SepWPp.exists_elim fun r2 => SepWPp.exists_elim fun r1 =>
    SepWPp.exists_elim fun r0 => ?_
  have hstep7 := p2_seg4d_hooks_placed_wp ext hH st s6 coroPtr opkFutPtr
    (0#64 + pkKit.getFutVtOff) pubCap pubPtr privCap privPtr opkIdWord
    r0 r1 r2 r3 r4 r5 r6 pkKit.getBoxSize
    hpc6 hrun6 hsp6_align hpub_ne1 pkKit.getBoxSize_ne_zero pkKit.getBoxSize_lt
    hx19_6 hx21_6 hx22_6 hx23_6 hx24_6 hx26_6 hx27_6
  rw [hsp6] at hstep7
  refine p2_bind_sepWP_qp_frame_state_placed hCode6 hstep7 (by sep_focus)
    fun s7 hst67 hpc7 hrun7 hCode7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7, htr7_6, hx0_7, hx8_7, hx19_7, _, hx22_7, _, _, hx25_7, hx26_7, _,
    hx28_7, hx29_7, hx30_7, hvregs7_6⟩
  simp only [arm64_norm] at hpc7
  have hsp7_al : s7.spAligned = true := by simpa only [State.spAligned, hsp7] using hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
  have hstk_kp1 := p2_stackAt_split_of_le sp stk 176
    (Nat.le_trans p2_pkKeyPairStack_le_pure hstk_pure) hstk_lt
  have hstk_kp2 := stackAt_176_keypair_eq sp
  have hmr88_split : memRegion (sp + 0x3e0#64) 88 =
      memRegion (sp + 0x3e0#64) 65 ∗ memRegion (sp + 0x421#64) 23 :=
    ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 65) (k := 23)
      (b' := sp + 0x421#64) rfl (by bv_omega) (by decide)
  refine SepWPp.weaken_frame (Entails.of_eq hstk_kp1) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_kp2) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hmr88_split) (by sep_focus) ?_
  sep_norm
  have h938 : (sp + 0x930#64) + 8#64 = sp + 0x938#64 := by bv_omega
  have h940 : (sp + 0x930#64) + 16#64 = sp + 0x940#64 := by bv_omega
  have h948 : (sp + 0x930#64) + 24#64 = sp + 0x948#64 := by bv_omega
  have h950 : (sp + 0x930#64) + 32#64 = sp + 0x950#64 := by bv_omega
  have h958 : (sp + 0x930#64) + 40#64 = sp + 0x958#64 := by bv_omega
  have h960 : (sp + 0x930#64) + 48#64 = sp + 0x960#64 := by bv_omega
  let st_debox := M.stepEvents (rustDeallocEvents pkKit.getBoxSize 8) st
  refine p2_call_nopanic_lscl_steps_frame_placed
    (x := (sp + 0x930#64, pubPtr, opkPubBytes, privPtr, opkPrivBytes, sp + 0x3e0#64))
    (T := (((sp + 0x930#64) + 8#64) ↦₆₄ pubPtr) ∗ (((sp + 0x930#64) + 16#64) ↦₆₄ 33#64) ∗
      (((sp + 0x930#64) + 32#64) ↦₆₄ privPtr) ∗ (((sp + 0x930#64) + 40#64) ↦₆₄ 32#64) ∗
      (pubPtr ↦ₛ (5#8 :: opkPubBytes)) ∗ (privPtr ↦ₛ opkPrivBytes) ∗
      memRegion (sp + 0x3e0#64) 65 ∗ cells (sp - 176#64) 8 ∗ cells (sp - 112#64) 14)
    hCode7 hPure.preKeyRecordKeyPair hpc7 hrun7 hsp7_al hx30_7
    (by
      dsimp only [
        LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesBudget.preKeyRecordKeyPairBudgetSpec,
        LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget.preKeyRecordKeyPairBudgetSpec,
        withVmPreserved, preKeyRecordKeyPairOkSpec]
      rw [hsp7])
    (And.intro hx0_7 (And.intro hx8_7 (And.intro hpub_len hpriv_len)))
    (by rw [h938, h940, h950, h958]; sep_focus)
    (hnext := fun s8 hst78 hpc8 hrun8 hsp8_7 _ hcs8 hCode8 => ?_)
  dsimp only [
    LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesBudget.preKeyRecordKeyPairBudgetSpec,
    LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget.preKeyRecordKeyPairBudgetSpec,
    withVmPreserved, preKeyRecordKeyPairOkSpec]
  rcases hcs8 with ⟨hcs8_19, _, _, hcs8_22, _, _, hcs8_25, hcs8_26, _, hcs8_28, hcs8_29, hvregs8_7⟩
  have hsp8 : s8.sp = sp := hsp8_7.trans hsp7
  have hsp8_align : (s8.sp &&& 15#64 == 0#64) = true := by rw [hsp8]; exact hsp_align
  have h3e1 : (sp + 0x3e0#64) + 1#64 = sp + 0x3e1#64 := by bv_omega
  have h401 : (sp + 0x3e0#64) + 33#64 = sp + 0x401#64 := by bv_omega
  rw [hsp7, h938, h940, h950, h958, h3e1, h401]; simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hvm78 => SepWPp.pure_elim fun htr8_7 => ?_
  refine SepWPp.transport_budgetPool hvm78 (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_kp2.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_kp1.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (p2_words7_entails_memRegion_56 (sp + 0x930#64)
      pubCap pubPtr 33#64 privCap privPtr 32#64 opkIdWord)
    (by rw [h938, h940, h948, h950, h958, h960]; sep_focus) ?_
  have hclamp_len : (clampBv8List opkPrivBytes).length = 32 := clampBv8List_length hpriv_len
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b63, c0, c1, c2, c3, c4, c5, c6,
    w0, w1, w2, w3, w4, w5, w6, u0_kp, u1_kp, u2_kp, u3_kp, u4_kp, u5_kp, u6_kp, u7_kp,
    hpk_words, hsk_words, hkp64_eq, hkp_lo, hkp_hi⟩ := exists_keyPair64_decomp hpub_len hclamp_len
  have h3e1_eq : ((sp + 0x3e1#64) ↦ₛ opkPubBytes) ∗ ((sp + 0x401#64) ↦ₛ clampBv8List opkPrivBytes) =
      keyPair64UnalignedAt (sp + 0x3e1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 := by
    rw [show sp + 0x401#64 = (sp + 0x3e1#64) + 32#64 by bv_omega]; exact hkp64_eq (sp + 0x3e1#64)
  refine SepWPp.weaken_frame (Entails.of_eq h3e1_eq) (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_vecU8Buf_rejoin pubPtr pubCap (5#8 :: opkPubBytes) hpub_le)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_vecU8Buf_rejoin privPtr privCap opkPrivBytes hpriv_le)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_memRegion_9_sp270_eq sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun b_278 => SepWPp.exists_elim fun u_270 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
  refine p2_ro_intro_sepWPp (hskitVt.kpSlot hCode8.2) ?_
  sep_norm
  have hstep9 := p2_seg4e_hooks_placed_wp ext hH st_debox s8 coroPtr msgPtr ctxPtr
    pubCap pubPtr privCap privPtr idStorePtr ikit.id_vt (0#64 + skit.kpShimOff)
    v_98 v_a0 v_b0 u_270 opkId b0 b1 b2 b3 b4 b5 b6 b63
    s0_b s1_b s2_b s3_b s4_b s5_b s6_b
    c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init b_4b0 b_278
    w0 w1 w2 w3 w4 w5 w6 cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init
    hpc8 hrun8 hsp8_align hpub_nz hpriv_nz
    (hcs8_19.trans hx19_7) (hcs8_22.trans hx22_7) (hcs8_26.trans hx26_7)
  rw [hsp8] at hstep9
  refine p2_bind_sepWP_qp_frame_state_placed hCode8 hstep9 (by sep_focus)
    fun s9 hst89 hpc9 hrun9 hCode9 hregs9 => ?_
  rcases hregs9 with ⟨hsp9, htr9_8, hx0_9, hx19_9, hx21_9, hx23_9, hx24_9, hx25_9, hx26_9, hx27_9,
    hx28_9, hx29_9, hx30_9, hvregs9_8⟩
  have hsp9_al : s9.spAligned = true := by simpa only [State.spAligned, hsp9] using hsp_align
  let st_free := M.stepEvents (p2OpkRecFreeEvents pkKit.getBoxSize pubCap.toNat privCap.toNat) st
  have hst9_eq :
      M.stepEvents (rustDeallocEvents pubCap.toNat 1 ++ rustDeallocEvents privCap.toNat 1) st_debox =
        st_free := by
    dsimp only [st_debox, st_free, p2OpkRecFreeEvents]
    simp only [M.stepEvents_append, List.append_assoc]
  rw [hst9_eq]
  refine p2_sub4_drop_sep_frame
    (Drop := ((ikit.id_vt + 0x18#64) ↦₆₄ᵣ (0#64 + skit.kpShimOff))) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_sp270_9_entails_memRegion sp w6 b63) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq h3e1_eq.symm) (by sep_focus) ?_
  rw [← h3e1, ← h401]
  refine SepWPp.weaken_frame
    (sp_a90_65_entails_memRegion (sp + 0x3e0#64) 0#8 opkPubBytes (clampBv8List opkPrivBytes)
      hpub_len hclamp_len) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hmr88_split.symm) (by sep_focus) ?_
  have hstk_kp_shim := p2_stackAt_split_of_le sp stk skit.kpShimStack hstk_kp_shim hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_kp_shim) (by sep_focus) ?_
  sep_norm
  have htr9 : s9.trace = s6.trace := by rw [htr9_8, htr8_7, htr7_6]
  refine p2_call_rocl_nopanic_steps_frame_placed
    (x := (idStorePtr, st_free))
    hCode9 (hskitOk.kpShim (by decide)) hpc9 hrun9 hsp9_al hx30_9
    (hsp9 ▸ p2_kpShim_pre_intro_placed hx0_9 hfits_kp)
    (by sep_focus)
    (hnext := fun sf hst9f hpcf hrunf hspf_9 _ hcsf hCodef => ?_)
  dsimp only [kitKpShimSpec]
  rcases hcsf with ⟨hcsf_19, _, hcsf_21, _, hcsf_23, hcsf_24, hcsf_25, hcsf_26, hcsf_27, hcsf_28,
    hcsf_29, hvregsf_9⟩
  rw [hsp9]
  sep_norm
  refine SepWPp.exists_elim fun evs_kp =>
    SepWPp.pure_elim fun ⟨hx1_f, hx0_nz, hx0_al, htrf_9, hevs_kp⟩ => ?_
  have hevs_kp_eq : evs_kp = boxAllocEvents skit.kpBoxSize :=
    (boxAllocEnv_iff_eq skit.kpBoxSize evs_kp).mp hevs_kp
  have hpool_eq :
      M.stepEvents evs_kp st_free =
        M.stepEvents
          (p2Sub4SomeTailEvents pkKit.getBoxSize pubCap.toNat privCap.toNat skit.kpBoxSize) st := by
    rw [hevs_kp_eq]
    dsimp only [st_free, p2Sub4SomeTailEvents]
    simp only [M.stepEvents_append, List.append_assoc]
  rw [hpool_eq]
  refine SepWPp.weaken_frame (Entails.of_eq hstk_kp_shim.symm) (by sep_focus) ?_
  have hst6f := hst67.trans (hst78.trans (hst89.trans hst9f))
  have hdone := hDone (sf.readReg64 .x0) b0 b1 b2 b3 b4 b5 b6 b63 c0 c1 c2 c3 c4 c5 c6
    w0 w1 w2 w3 w4 w5 w6 u0_kp u1_kp u2_kp u3_kp u4_kp u5_kp u6_kp u7_kp sf
    hst6f hpk_words hsk_words hkp_lo hkp_hi
    hpcf hrunf (hspf_9.trans hsp9) (htrf_9.trans htr9) rfl hx1_f hx0_nz hx0_al
    (hcsf_19.trans hx19_9) (hcsf_21.trans hx21_9) (hcsf_23.trans hx23_9) (hcsf_24.trans hx24_9)
    (by rw [hcsf_25, hx25_9, hcs8_25, hx25_7])
    (hcsf_26.trans hx26_9) (hcsf_27.trans hx27_9)
    (by rw [hcsf_28, hx28_9, hcs8_28, hx28_7, hx28_6])
    (by rw [hcsf_29, hx29_9, hcs8_29, hx29_7])
    (by rw [hvregsf_9, hvregs9_8, hvregs8_7, hvregs7_6, hvregs6]) hCodef
  exact p2_sepWPp_weaken_eq hdone (by sep_focus)

abbrev stageP2_sub4_some_tail_kits_4k_placed := @stageP2_sub4_some_tail_kits_ext_placed
abbrev stageP2_sub4_some_tail_kits_hooks_placed := @stageP2_sub4_some_tail_kits_ext_placed

theorem stageP2_sub4_some_tail_kits_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlacedOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (skit : IdentitySelfStoreSpec ikit)
    (senv : IdentitySelfStoreBudgetEnv skit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (stk : Nat) (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_kp_shim : skit.kpShimStack ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (ret : BitVec 64) (st : M.σ) (s0 s6 : State) (sp : BitVec 64)
    (TailFrame : SepProp) (Q : State → SepProp → Prop) {Qp : State → SepProp → Prop}
    (coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr opkFutPtr
     pubCap pubPtr privCap privPtr opkIdWord u_ac8 v_98 v_a0 v_b0 : BitVec 64)
    (opkId : BitVec 32) (opkPubBytes opkPrivBytes : List (BitVec 8))
    (b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
     c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init : BitVec 8)
    (cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init : BitVec 64)
    (hfits_kp : FitsEnv M lim
      (M.stepEvents (p2OpkRecFreeEvents pkKit.getBoxSize pubCap.toNat privCap.toNat) st)
      (BoxAllocEnv skit.kpBoxSize))
    (hpub_len : opkPubBytes.length = 32) (hpriv_len : opkPrivBytes.length = 32)
    (hpub_le : (5#8 :: opkPubBytes).length ≤ pubCap.toNat)
    (hpub_nz : pubCap ≠ 0#64) (hpub_ne1 : pubCap ≠ 0xffffffffffffffff#64)
    (hCode6 : StoreKit.LibsignalCodeRoLoaded lsmpl s6.mem)
    (hpc6 : s6.pc = stageP1EntryPlaced + 0xe40#64)
    (hrun6 : s6.status = .Running) (hsp6 : s6.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hvregs6 : calleeSavedVRegs s6 = calleeSavedVRegs s0)
    (hx19_6 : s6.readReg64 .x19 = coroPtr) (hx21_6 : s6.readReg64 .x21 = opkFutPtr)
    (hx22_6 : s6.readReg64 .x22 = pubCap) (hx23_6 : s6.readReg64 .x23 = 33#64)
    (hx24_6 : s6.readReg64 .x24 = 0#64 + pkKit.getFutVtOff)
    (hx26_6 : s6.readReg64 .x26 = pubPtr) (hx27_6 : s6.readReg64 .x27 = opkIdWord)
    (hx28_6 : s6.readReg64 .x28 = sp + 0xa90#64)
    (hDone : ∀ (idKpFutPtr : BitVec 64)
      (b0 b1 b2 b3 b4 b5 b6 b63 c0 c1 c2 c3 c4 c5 c6 : BitVec 8)
      (w0 w1 w2 w3 w4 w5 w6 u0_kp u1_kp u2_kp u3_kp u4_kp u5_kp u6_kp u7_kp : BitVec 64)
      (sf : State),
      Steps (stageP1ProgPlaced ext) s6 sf →
      (∀ a : BitVec 64, (a ↦ₛ opkPubBytes) =
        (a ↦₆₄ u0_kp) ∗ ((a + 8#64) ↦₆₄ u1_kp) ∗ ((a + 16#64) ↦₆₄ u2_kp) ∗
          ((a + 24#64) ↦₆₄ u3_kp)) →
      (∀ a : BitVec 64, (a ↦ₛ clampBv8List opkPrivBytes) =
        (a ↦₆₄ u4_kp) ∗ ((a + 8#64) ↦₆₄ u5_kp) ∗ ((a + 16#64) ↦₆₄ u6_kp) ∗
          ((a + 24#64) ↦₆₄ u7_kp)) →
      (∀ a : BitVec 64,
        bytes7At a b0 b1 b2 b3 b4 b5 b6 ∗
        ((a + 7#64) ↦₆₄ w0) ∗ ((a + 15#64) ↦₆₄ w1) ∗ ((a + 23#64) ↦₆₄ w2) ∗ ((a + 31#64) ↦₆₄ w3) =
          (a ↦₆₄ u0_kp) ∗ ((a + 8#64) ↦₆₄ u1_kp) ∗ ((a + 16#64) ↦₆₄ u2_kp) ∗
            ((a + 24#64) ↦₆₄ u3_kp) ∗ bytes7At (a + 32#64) c0 c1 c2 c3 c4 c5 c6) →
      (∀ a : BitVec 64,
        bytes7At a c0 c1 c2 c3 c4 c5 c6 ∗
        ((a + 7#64) ↦₆₄ w4) ∗ ((a + 15#64) ↦₆₄ w5) ∗ ((a + 23#64) ↦₆₄ w6) ∗ ((a + 31#64) ↦₈ b63) =
          (a ↦₆₄ u4_kp) ∗ ((a + 8#64) ↦₆₄ u5_kp) ∗ ((a + 16#64) ↦₆₄ u6_kp) ∗
            ((a + 24#64) ↦₆₄ u7_kp)) →
      sf.pc = stageP1EntryPlaced + 0x36ac#64 →
      sf.status = .Running → sf.sp = sp → sf.trace = s6.trace →
      sf.readReg64 .x0 = idKpFutPtr → sf.readReg64 .x1 = 0#64 + skit.kpFutVtOff →
      idKpFutPtr ≠ 0#64 → idKpFutPtr.toNat % 8 = 0 →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x21 = v_b0 →
      sf.readReg64 .x23 = v_a0 → sf.readReg64 .x24 = sp + 0x370#64 →
      sf.readReg64 .x25 = s6.readReg64 .x25 → sf.readReg64 .x26 = v_98 →
      sf.readReg64 .x27 = ctxPtr → sf.readReg64 .x28 = sp + 0xa90#64 →
      sf.readReg64 .x29 = s6.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (stageP1ProgPlaced ext) ret sf
        (A.live idKpFutPtr skit.kpBoxSize 8 ∗
         skit.kpBoxAt idKpFutPtr idStorePtr 0#8 ∗
         ((sp + 0x98#64) ↦₆₄ v_98) ∗ ((sp + 0xa0#64) ↦₆₄ v_a0) ∗
         ((sp + 0xa8#64) ↦₆₄ 32#64) ∗ ((sp + 0xb0#64) ↦₆₄ v_b0) ∗
         ((sp + 0xb8#64) ↦₆₄ privCap) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
         ((sp + 0xd0#64) ↦₆₄ privPtr) ∗ memRegion (sp + 0x270#64) 9 ∗
         bytes7At (sp + 0x3b0#64) b0 b1 b2 b3 b4 b5 b6 ∗
         memRegion (sp + 0x3e0#64) 88 ∗ memRegion (sp + 0x930#64) 56 ∗
         memRegion (sp + 0xa90#64) 65 ∗
         ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
         ((coroPtr + 0x4b0#64) ↦₈ 1#8) ∗
         keyPair64UnalignedAt (coroPtr + 0x4b1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
         ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
         ((0#64 + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
         ((0#64 + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         A.pool lim
           (M.stepEvents
             (p2Sub4SomeTailEvents pkKit.getBoxSize pubCap.toNat privCap.toNat skit.kpBoxSize) st)
           sf ∗
         stackAt sp stk ∗ TailFrame)
        Q Qp) :
    SepWPp (stageP1ProgPlaced ext) ret s6
      (pkKit.getBoxAt opkFutPtr preKeyStorePtr opkId 1#8 ∗
       A.live opkFutPtr pkKit.getBoxSize 8 ∗
       preKeyRecordOut64At (sp + 0xa90#64) pubCap pubPtr 33#64 privCap privPtr 32#64 opkIdWord u_ac8 ∗
       memRegion (sp + 0xad0#64) 1 ∗
       A.live pubPtr pubCap.toNat 1 ∗ (pubPtr ↦ₛ (5#8 :: opkPubBytes)) ∗
       memRegion (pubPtr + BitVec.ofNat 64 (5#8 :: opkPubBytes).length)
         (pubCap.toNat - (5#8 :: opkPubBytes).length) ∗
       vecU8Buf A.repAlloc privCap privPtr opkPrivBytes ∗
       ((sp + 0x98#64) ↦₆₄ v_98) ∗ ((sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((sp + 0xa8#64) ↦₆₄ 32#64) ∗ ((sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((sp + 0xb8#64) ↦₆₄ privCap) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((sp + 0xd0#64) ↦₆₄ privPtr) ∗ memRegion (sp + 0x270#64) 9 ∗
       bytes7At (sp + 0x3b0#64) s0_b s1_b s2_b s3_b s4_b s5_b s6_b ∗
       memRegion (sp + 0x3e0#64) 88 ∗ memRegion (sp + 0x930#64) 56 ∗
       ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
       ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
       keyPair64UnalignedAt (coroPtr + 0x4b1#64) c0_init c1_init c2_init c3_init
         c4_init c5_init c6_init cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init
         cw6_init c63_init ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((0#64 + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
       ((0#64 + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.pool lim st s6 ∗ stackAt sp stk ∗ TailFrame)
      Q Qp :=
  stageP2_sub4_some_tail_kits_ext_placed ext hH hPure.to_4K pkKit ikit skit senv
    hskitVt hskitOk stk hstk_pure hstk_kp_shim hstk_lt ret st s0 s6 sp TailFrame Q (Qp := Qp)
    coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr opkFutPtr
    pubCap pubPtr privCap privPtr opkIdWord u_ac8 v_98 v_a0 v_b0
    opkId opkPubBytes opkPrivBytes b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
    c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init
    cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init
    hfits_kp hpub_len hpriv_len hpub_le hpub_nz hpub_ne1
    hCode6 hpc6 hrun6 hsp6 hsp_align hvregs6
    hx19_6 hx21_6 hx22_6 hx23_6 hx24_6 hx26_6 hx27_6 hx28_6 hDone

/-- `SeqEnv FreeOnlyEvs (BoxAllocEnv skit.kpBoxSize)` specialization of
`stageP2_sub4_some_tail_kits_ext_placed` (independent of `pubCap` and `privCap`). -/
theorem stageP2_sub4_some_tail_kits_seqEnv_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlaced4KOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (skit : IdentitySelfStoreSpec ikit)
    (senv : IdentitySelfStoreBudgetEnv skit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (stk : Nat) (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_kp_shim : skit.kpShimStack ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (ret : BitVec 64) (st : M.σ) (s0 s6 : State) (sp : BitVec 64)
    (TailFrame : SepProp) (Q : State → SepProp → Prop) {Qp : State → SepProp → Prop}
    (coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr opkFutPtr
     pubCap pubPtr privCap privPtr opkIdWord u_ac8 v_98 v_a0 v_b0 : BitVec 64)
    (opkId : BitVec 32) (opkPubBytes opkPrivBytes : List (BitVec 8))
    (b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
     c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init : BitVec 8)
    (cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init : BitVec 64)
    (hfits : FitsEnv M lim st (SeqEnv FreeOnlyEvs (BoxAllocEnv skit.kpBoxSize)))
    (hpub_len : opkPubBytes.length = 32) (hpriv_len : opkPrivBytes.length = 32)
    (hpub_le : (5#8 :: opkPubBytes).length ≤ pubCap.toNat)
    (hpub_nz : pubCap ≠ 0#64) (hpub_ne1 : pubCap ≠ 0xffffffffffffffff#64)
    (hCode6 : StoreKit.LibsignalCodeRoLoaded lsmpl s6.mem)
    (hpc6 : s6.pc = stageP1EntryPlaced + 0xe40#64)
    (hrun6 : s6.status = .Running) (hsp6 : s6.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hvregs6 : calleeSavedVRegs s6 = calleeSavedVRegs s0)
    (hx19_6 : s6.readReg64 .x19 = coroPtr) (hx21_6 : s6.readReg64 .x21 = opkFutPtr)
    (hx22_6 : s6.readReg64 .x22 = pubCap) (hx23_6 : s6.readReg64 .x23 = 33#64)
    (hx24_6 : s6.readReg64 .x24 = 0#64 + pkKit.getFutVtOff)
    (hx26_6 : s6.readReg64 .x26 = pubPtr) (hx27_6 : s6.readReg64 .x27 = opkIdWord)
    (hx28_6 : s6.readReg64 .x28 = sp + 0xa90#64)
    (hDone : ∀ (idKpFutPtr : BitVec 64)
      (b0 b1 b2 b3 b4 b5 b6 b63 c0 c1 c2 c3 c4 c5 c6 : BitVec 8)
      (w0 w1 w2 w3 w4 w5 w6 u0_kp u1_kp u2_kp u3_kp u4_kp u5_kp u6_kp u7_kp : BitVec 64)
      (sf : State),
      Steps (stageP1ProgPlaced ext) s6 sf →
      (∀ a : BitVec 64, (a ↦ₛ opkPubBytes) =
        (a ↦₆₄ u0_kp) ∗ ((a + 8#64) ↦₆₄ u1_kp) ∗ ((a + 16#64) ↦₆₄ u2_kp) ∗
          ((a + 24#64) ↦₆₄ u3_kp)) →
      (∀ a : BitVec 64, (a ↦ₛ clampBv8List opkPrivBytes) =
        (a ↦₆₄ u4_kp) ∗ ((a + 8#64) ↦₆₄ u5_kp) ∗ ((a + 16#64) ↦₆₄ u6_kp) ∗
          ((a + 24#64) ↦₆₄ u7_kp)) →
      (∀ a : BitVec 64,
        bytes7At a b0 b1 b2 b3 b4 b5 b6 ∗
        ((a + 7#64) ↦₆₄ w0) ∗ ((a + 15#64) ↦₆₄ w1) ∗ ((a + 23#64) ↦₆₄ w2) ∗ ((a + 31#64) ↦₆₄ w3) =
          (a ↦₆₄ u0_kp) ∗ ((a + 8#64) ↦₆₄ u1_kp) ∗ ((a + 16#64) ↦₆₄ u2_kp) ∗
            ((a + 24#64) ↦₆₄ u3_kp) ∗ bytes7At (a + 32#64) c0 c1 c2 c3 c4 c5 c6) →
      (∀ a : BitVec 64,
        bytes7At a c0 c1 c2 c3 c4 c5 c6 ∗
        ((a + 7#64) ↦₆₄ w4) ∗ ((a + 15#64) ↦₆₄ w5) ∗ ((a + 23#64) ↦₆₄ w6) ∗ ((a + 31#64) ↦₈ b63) =
          (a ↦₆₄ u4_kp) ∗ ((a + 8#64) ↦₆₄ u5_kp) ∗ ((a + 16#64) ↦₆₄ u6_kp) ∗
            ((a + 24#64) ↦₆₄ u7_kp)) →
      sf.pc = stageP1EntryPlaced + 0x36ac#64 →
      sf.status = .Running → sf.sp = sp → sf.trace = s6.trace →
      sf.readReg64 .x0 = idKpFutPtr → sf.readReg64 .x1 = 0#64 + skit.kpFutVtOff →
      idKpFutPtr ≠ 0#64 → idKpFutPtr.toNat % 8 = 0 →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x21 = v_b0 →
      sf.readReg64 .x23 = v_a0 → sf.readReg64 .x24 = sp + 0x370#64 →
      sf.readReg64 .x25 = s6.readReg64 .x25 → sf.readReg64 .x26 = v_98 →
      sf.readReg64 .x27 = ctxPtr → sf.readReg64 .x28 = sp + 0xa90#64 →
      sf.readReg64 .x29 = s6.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (stageP1ProgPlaced ext) ret sf
        (A.live idKpFutPtr skit.kpBoxSize 8 ∗
         skit.kpBoxAt idKpFutPtr idStorePtr 0#8 ∗
         ((sp + 0x98#64) ↦₆₄ v_98) ∗ ((sp + 0xa0#64) ↦₆₄ v_a0) ∗
         ((sp + 0xa8#64) ↦₆₄ 32#64) ∗ ((sp + 0xb0#64) ↦₆₄ v_b0) ∗
         ((sp + 0xb8#64) ↦₆₄ privCap) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
         ((sp + 0xd0#64) ↦₆₄ privPtr) ∗ memRegion (sp + 0x270#64) 9 ∗
         bytes7At (sp + 0x3b0#64) b0 b1 b2 b3 b4 b5 b6 ∗
         memRegion (sp + 0x3e0#64) 88 ∗ memRegion (sp + 0x930#64) 56 ∗
         memRegion (sp + 0xa90#64) 65 ∗
         ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
         ((coroPtr + 0x4b0#64) ↦₈ 1#8) ∗
         keyPair64UnalignedAt (coroPtr + 0x4b1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
         ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
         ((0#64 + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
         ((0#64 + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         A.pool lim
           (M.stepEvents
             (p2Sub4SomeTailEvents pkKit.getBoxSize pubCap.toNat privCap.toNat skit.kpBoxSize) st)
           sf ∗
         stackAt sp stk ∗ TailFrame)
        Q Qp) :
    SepWPp (stageP1ProgPlaced ext) ret s6
      (pkKit.getBoxAt opkFutPtr preKeyStorePtr opkId 1#8 ∗
       A.live opkFutPtr pkKit.getBoxSize 8 ∗
       preKeyRecordOut64At (sp + 0xa90#64) pubCap pubPtr 33#64 privCap privPtr 32#64 opkIdWord u_ac8 ∗
       memRegion (sp + 0xad0#64) 1 ∗
       A.live pubPtr pubCap.toNat 1 ∗ (pubPtr ↦ₛ (5#8 :: opkPubBytes)) ∗
       memRegion (pubPtr + BitVec.ofNat 64 (5#8 :: opkPubBytes).length)
         (pubCap.toNat - (5#8 :: opkPubBytes).length) ∗
       vecU8Buf A.repAlloc privCap privPtr opkPrivBytes ∗
       ((sp + 0x98#64) ↦₆₄ v_98) ∗ ((sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((sp + 0xa8#64) ↦₆₄ 32#64) ∗ ((sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((sp + 0xb8#64) ↦₆₄ privCap) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((sp + 0xd0#64) ↦₆₄ privPtr) ∗ memRegion (sp + 0x270#64) 9 ∗
       bytes7At (sp + 0x3b0#64) s0_b s1_b s2_b s3_b s4_b s5_b s6_b ∗
       memRegion (sp + 0x3e0#64) 88 ∗ memRegion (sp + 0x930#64) 56 ∗
       ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
       ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
       keyPair64UnalignedAt (coroPtr + 0x4b1#64) c0_init c1_init c2_init c3_init
         c4_init c5_init c6_init cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init
         cw6_init c63_init ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((0#64 + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
       ((0#64 + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.pool lim st s6 ∗ stackAt sp stk ∗ TailFrame)
      Q Qp :=
  stageP2_sub4_some_tail_kits_ext_placed ext hH hPure pkKit ikit skit senv
    hskitVt hskitOk stk hstk_pure hstk_kp_shim hstk_lt ret st s0 s6 sp TailFrame Q (Qp := Qp)
    coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr opkFutPtr
    pubCap pubPtr privCap privPtr opkIdWord u_ac8 v_98 v_a0 v_b0
    opkId opkPubBytes opkPrivBytes b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
    c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init
    cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init
    (hfits.seq_right (p2OpkRecFreeEvents_freeOnly pkKit.getBoxSize pubCap.toNat privCap.toNat))
    hpub_len hpriv_len hpub_le hpub_nz hpub_ne1
    hCode6 hpc6 hrun6 hsp6 hsp_align hvregs6
    hx19_6 hx21_6 hx22_6 hx23_6 hx24_6 hx26_6 hx27_6 hx28_6 hDone

abbrev stageP2_sub4_some_tail_kits_seqEnv_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlacedOfEnv P A lim F BobV1Env AcceptErrEnv ext) :=
  @stageP2_sub4_some_tail_kits_seqEnv_ext_placed _ M P A lim F BobV1Env AcceptErrEnv ext hH
    hPure.to_4K

theorem stageP2_sub4_some_tail_kits_ofTailEnv_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlaced4KOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (skit : IdentitySelfStoreSpec ikit)
    (senv : IdentitySelfStoreBudgetEnv skit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (stk : Nat) (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_kp_shim : skit.kpShimStack ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (ret : BitVec 64) (st : M.σ) (s0 s6 : State) (sp : BitVec 64)
    (TailFrame : SepProp) (Q : State → SepProp → Prop) {Qp : State → SepProp → Prop}
    (coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr opkFutPtr
     pubCap pubPtr privCap privPtr opkIdWord u_ac8 v_98 v_a0 v_b0 : BitVec 64)
    (opkId : BitVec 32) (opkPubBytes opkPrivBytes : List (BitVec 8))
    (b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
     c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init : BitVec 8)
    (cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init : BitVec 64)
    (hfits : FitsEnv M lim st
      (P2Sub4SomeTailEnv pkKit.getBoxSize pubCap.toNat privCap.toNat skit.kpBoxSize))
    (hpub_len : opkPubBytes.length = 32) (hpriv_len : opkPrivBytes.length = 32)
    (hpub_le : (5#8 :: opkPubBytes).length ≤ pubCap.toNat)
    (hpub_nz : pubCap ≠ 0#64) (hpub_ne1 : pubCap ≠ 0xffffffffffffffff#64)
    (hCode6 : StoreKit.LibsignalCodeRoLoaded lsmpl s6.mem)
    (hpc6 : s6.pc = stageP1EntryPlaced + 0xe40#64)
    (hrun6 : s6.status = .Running) (hsp6 : s6.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hvregs6 : calleeSavedVRegs s6 = calleeSavedVRegs s0)
    (hx19_6 : s6.readReg64 .x19 = coroPtr) (hx21_6 : s6.readReg64 .x21 = opkFutPtr)
    (hx22_6 : s6.readReg64 .x22 = pubCap) (hx23_6 : s6.readReg64 .x23 = 33#64)
    (hx24_6 : s6.readReg64 .x24 = 0#64 + pkKit.getFutVtOff)
    (hx26_6 : s6.readReg64 .x26 = pubPtr) (hx27_6 : s6.readReg64 .x27 = opkIdWord)
    (hx28_6 : s6.readReg64 .x28 = sp + 0xa90#64)
    (hDone : ∀ (idKpFutPtr : BitVec 64)
      (b0 b1 b2 b3 b4 b5 b6 b63 c0 c1 c2 c3 c4 c5 c6 : BitVec 8)
      (w0 w1 w2 w3 w4 w5 w6 u0_kp u1_kp u2_kp u3_kp u4_kp u5_kp u6_kp u7_kp : BitVec 64)
      (sf : State),
      Steps (stageP1ProgPlaced ext) s6 sf →
      (∀ a : BitVec 64, (a ↦ₛ opkPubBytes) =
        (a ↦₆₄ u0_kp) ∗ ((a + 8#64) ↦₆₄ u1_kp) ∗ ((a + 16#64) ↦₆₄ u2_kp) ∗
          ((a + 24#64) ↦₆₄ u3_kp)) →
      (∀ a : BitVec 64, (a ↦ₛ clampBv8List opkPrivBytes) =
        (a ↦₆₄ u4_kp) ∗ ((a + 8#64) ↦₆₄ u5_kp) ∗ ((a + 16#64) ↦₆₄ u6_kp) ∗
          ((a + 24#64) ↦₆₄ u7_kp)) →
      (∀ a : BitVec 64,
        bytes7At a b0 b1 b2 b3 b4 b5 b6 ∗
        ((a + 7#64) ↦₆₄ w0) ∗ ((a + 15#64) ↦₆₄ w1) ∗ ((a + 23#64) ↦₆₄ w2) ∗ ((a + 31#64) ↦₆₄ w3) =
          (a ↦₆₄ u0_kp) ∗ ((a + 8#64) ↦₆₄ u1_kp) ∗ ((a + 16#64) ↦₆₄ u2_kp) ∗
            ((a + 24#64) ↦₆₄ u3_kp) ∗ bytes7At (a + 32#64) c0 c1 c2 c3 c4 c5 c6) →
      (∀ a : BitVec 64,
        bytes7At a c0 c1 c2 c3 c4 c5 c6 ∗
        ((a + 7#64) ↦₆₄ w4) ∗ ((a + 15#64) ↦₆₄ w5) ∗ ((a + 23#64) ↦₆₄ w6) ∗ ((a + 31#64) ↦₈ b63) =
          (a ↦₆₄ u4_kp) ∗ ((a + 8#64) ↦₆₄ u5_kp) ∗ ((a + 16#64) ↦₆₄ u6_kp) ∗
            ((a + 24#64) ↦₆₄ u7_kp)) →
      sf.pc = stageP1EntryPlaced + 0x36ac#64 →
      sf.status = .Running → sf.sp = sp → sf.trace = s6.trace →
      sf.readReg64 .x0 = idKpFutPtr → sf.readReg64 .x1 = 0#64 + skit.kpFutVtOff →
      idKpFutPtr ≠ 0#64 → idKpFutPtr.toNat % 8 = 0 →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x21 = v_b0 →
      sf.readReg64 .x23 = v_a0 → sf.readReg64 .x24 = sp + 0x370#64 →
      sf.readReg64 .x25 = s6.readReg64 .x25 → sf.readReg64 .x26 = v_98 →
      sf.readReg64 .x27 = ctxPtr → sf.readReg64 .x28 = sp + 0xa90#64 →
      sf.readReg64 .x29 = s6.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (stageP1ProgPlaced ext) ret sf
        (A.live idKpFutPtr skit.kpBoxSize 8 ∗
         skit.kpBoxAt idKpFutPtr idStorePtr 0#8 ∗
         ((sp + 0x98#64) ↦₆₄ v_98) ∗ ((sp + 0xa0#64) ↦₆₄ v_a0) ∗
         ((sp + 0xa8#64) ↦₆₄ 32#64) ∗ ((sp + 0xb0#64) ↦₆₄ v_b0) ∗
         ((sp + 0xb8#64) ↦₆₄ privCap) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
         ((sp + 0xd0#64) ↦₆₄ privPtr) ∗ memRegion (sp + 0x270#64) 9 ∗
         bytes7At (sp + 0x3b0#64) b0 b1 b2 b3 b4 b5 b6 ∗
         memRegion (sp + 0x3e0#64) 88 ∗ memRegion (sp + 0x930#64) 56 ∗
         memRegion (sp + 0xa90#64) 65 ∗
         ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
         ((coroPtr + 0x4b0#64) ↦₈ 1#8) ∗
         keyPair64UnalignedAt (coroPtr + 0x4b1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
         ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
         ((0#64 + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
         ((0#64 + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         A.pool lim
           (M.stepEvents
             (p2Sub4SomeTailEvents pkKit.getBoxSize pubCap.toNat privCap.toNat skit.kpBoxSize) st)
           sf ∗
         stackAt sp stk ∗ TailFrame)
        Q Qp) :
    SepWPp (stageP1ProgPlaced ext) ret s6
      (pkKit.getBoxAt opkFutPtr preKeyStorePtr opkId 1#8 ∗
       A.live opkFutPtr pkKit.getBoxSize 8 ∗
       preKeyRecordOut64At (sp + 0xa90#64) pubCap pubPtr 33#64 privCap privPtr 32#64 opkIdWord u_ac8 ∗
       memRegion (sp + 0xad0#64) 1 ∗
       A.live pubPtr pubCap.toNat 1 ∗ (pubPtr ↦ₛ (5#8 :: opkPubBytes)) ∗
       memRegion (pubPtr + BitVec.ofNat 64 (5#8 :: opkPubBytes).length)
         (pubCap.toNat - (5#8 :: opkPubBytes).length) ∗
       vecU8Buf A.repAlloc privCap privPtr opkPrivBytes ∗
       ((sp + 0x98#64) ↦₆₄ v_98) ∗ ((sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((sp + 0xa8#64) ↦₆₄ 32#64) ∗ ((sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((sp + 0xb8#64) ↦₆₄ privCap) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((sp + 0xd0#64) ↦₆₄ privPtr) ∗ memRegion (sp + 0x270#64) 9 ∗
       bytes7At (sp + 0x3b0#64) s0_b s1_b s2_b s3_b s4_b s5_b s6_b ∗
       memRegion (sp + 0x3e0#64) 88 ∗ memRegion (sp + 0x930#64) 56 ∗
       ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
       ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
       keyPair64UnalignedAt (coroPtr + 0x4b1#64) c0_init c1_init c2_init c3_init
         c4_init c5_init c6_init cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init
         cw6_init c63_init ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((0#64 + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
       ((0#64 + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.pool lim st s6 ∗ stackAt sp stk ∗ TailFrame)
      Q Qp := by
  have hfits_all : FitsEvents M lim st
      (p2Sub4SomeTailEvents pkKit.getBoxSize pubCap.toNat privCap.toNat skit.kpBoxSize) :=
    (fitsEnv_p2Sub4SomeTailEnv_iff pkKit.getBoxSize pubCap.toNat privCap.toNat skit.kpBoxSize).mp
      hfits
  unfold p2Sub4SomeTailEvents at hfits_all
  rcases (fitsEvents_append M lim
      (p2OpkRecFreeEvents pkKit.getBoxSize pubCap.toNat privCap.toNat)
      (boxAllocEvents skit.kpBoxSize) st).mp hfits_all with ⟨_, hfits_box⟩
  exact stageP2_sub4_some_tail_kits_ext_placed ext hH hPure pkKit ikit skit senv
    hskitVt hskitOk stk hstk_pure hstk_kp_shim hstk_lt ret st s0 s6 sp TailFrame Q (Qp := Qp)
    coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr opkFutPtr
    pubCap pubPtr privCap privPtr opkIdWord u_ac8 v_98 v_a0 v_b0
    opkId opkPubBytes opkPrivBytes b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
    c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init
    cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init
    ((fitsEnv_boxAllocEnv_iff skit.kpBoxSize).mpr hfits_box)
    hpub_len hpriv_len hpub_le hpub_nz hpub_ne1
    hCode6 hpc6 hrun6 hsp6 hsp_align hvregs6
    hx19_6 hx21_6 hx22_6 hx23_6 hx24_6 hx26_6 hx27_6 hx28_6 hDone

abbrev stageP2_sub4_some_tail_kits_ofTailEnv_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlacedOfEnv P A lim F BobV1Env AcceptErrEnv ext) :=
  @stageP2_sub4_some_tail_kits_ofTailEnv_ext_placed _ M P A lim F BobV1Env AcceptErrEnv ext hH
    hPure.to_4K

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4AuxPlacedBudget
