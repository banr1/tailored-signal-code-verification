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
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA2PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3AuxPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3Placed
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Stage P2 Substage P2.3

Defines `P2Sub3DetPostPollEnv` and proves `RustCliAllocBudget M` / `VmPreserved` placed CPS
Substage P2.3 (`+0x1460 → +0x0d5c` on `Ok`, or `+0x0998` Arm 2) on Block `518`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.RecordCodecs (KyberPreKeyRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  KyberPreKeyStoreSpec LibsignalCodeRoLoaded PreKeyPollCall kpkGetPollOutAt withEnvPre
)
open CryptoVerification.E2E.Pqxdh.Initiator (AcceptKeysInput DRKey Primitives)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (decryptPrekeySavedRegsAt)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp (weaken_frame)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  p2_alloc_le_pure
  p2_kemStack_le_pure
  p2_memRegion_65_split_cells5
  p2_preKeyRecordOut64_tail_to_memRegion88
  p2_sepWPp_pure_elim_frame
  p2_sepWPp_weaken_eq
  p2_signedPreKeyStructAt_unpack
  p2_stackAt_kemKeyPair_eq
  p2_stackAt_split_of_le
  p2_vecU8Buf_dealloc_nonzero
  p2_vecU8Buf_nonempty
  p2_vecU8Buf_rejoin
  p2_vecU8Buf_zero
  stageP1EntryPlaced
  stageP1ProgPlaced
  stageP2PureAndErrStack
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FitsStep
  FreeOnlyEvs RustCliAllocBudget SeqEnv coarseCostModel coarseStep coarseStepReserve
  fitsEvents_append rustDeallocEvents
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesBudget (
  KemKeyPairFromPubPrivEnv kemKeyPairFromPubPrivEvents kemKeyPairFromPubPrivOkSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (futDropBudgetSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (
  KyberPreKeyStoreBudgetEnv kitKpkGetPollSpec kitKpkGetPollSpecE
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (KyberPreKeyStoreKitPlacedOk)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  StageP2ClosureHooksPlaced
  StageP2PureCalleesPlaced4KOfEnv
  StageP2PureCalleesPlacedOfEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA2PlacedBudget (
  p2_seg3a_ext_placed_wp
  p2_seg3b_gen_placed_wp
  p2_seg3c_hooks_placed_wp
  p2_seg3d1_sig0_hooks_placed_wp
  p2_seg3d1_sigNz_hooks_placed_wp
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget (
  p2_bind_sepWP_qp_frame_state_placed
  p2_call_lscl_nopanic_steps_frame_placed
  p2_call_rocl_nopanic_steps_frame_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2PlacedBudget (
  freeOnlyEvs_rustDeallocEvents
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3AuxPlacedBudget (
  P2Sub3TailAllocEnv
  fitsEnv_p2Sub3TailAllocEnv_iff
  p2KpkVecFreeEvents
  p2KpkVecFreeEvents_freeOnly
  p2Sub3TailAllocEvents
  p2_kpkGetPoll_pre_intro_placed
  stageP2_sub3_tail_kits_ext_placed
)

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  decryptPrekeySavedRegsAt

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

/-! ## 1. Substage P2.3 Post-Poll Event Lists, Envelope & Decomposition Lemmas -/

/-- Exact deterministic post-`kpkKit.getPoll` events prior to `+0x0d04` (`p2Sub3TailAllocEvents`):
`__rust_dealloc(kpkBoxSize, 8)` on the KPK poll future box, `kemKeyPairFromPubPrivEvents`
(`alloc 1568`, `alloc 3168`), and `p2KpkVecFreeEvents` freeing the cloned record buffers. -/
def p2Sub3PreTailEvents (kpkBoxSize pubCap privCap sigCap : Nat) : List AllocEvent :=
  rustDeallocEvents kpkBoxSize 8 ++ kemKeyPairFromPubPrivEvents ++
    p2KpkVecFreeEvents pubCap privCap sigCap

/-- Exact deterministic post-`kpkKit.getPoll` events up to `dropSpe2` (`p2Sub3PreTailEvents`
followed by the 21-byte `"missing pq ciphertext"` allocation `p2Sub3TailAllocEvents`). -/
def p2Sub3DetPostPollEvents (kpkBoxSize pubCap privCap sigCap : Nat) : List AllocEvent :=
  p2Sub3PreTailEvents kpkBoxSize pubCap privCap sigCap ++ p2Sub3TailAllocEvents

/-- Full post-`kpkKit.getPoll` `.ok`-branch event list including the `FreeOnlyEvs` deallocations
`evs_drop` performed by `dropSpe2` before reaching `+0x0d5c`. -/
def p2Sub3OkPostPollEvents (kpkBoxSize pubCap privCap sigCap : Nat)
    (evs_drop : List AllocEvent) : List AllocEvent :=
  p2Sub3DetPostPollEvents kpkBoxSize pubCap privCap sigCap ++ evs_drop

/-- Exact deterministic allocator event envelope for all post-`kpkKit.getPoll` allocations and
deallocations prior to `dropSpe2`'s `FreeOnlyEvs` drop. -/
def P2Sub3DetPostPollEnv (kpkBoxSize pubCap privCap sigCap : Nat)
    (evs : List AllocEvent) : Prop :=
  evs = p2Sub3DetPostPollEvents kpkBoxSize pubCap privCap sigCap

theorem fitsEnv_p2Sub3DetPostPollEnv_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (kpkBoxSize pubCap privCap sigCap : Nat) :
    FitsEnv M lim st (P2Sub3DetPostPollEnv kpkBoxSize pubCap privCap sigCap) ↔
      FitsEvents M lim st (p2Sub3DetPostPollEvents kpkBoxSize pubCap privCap sigCap) :=
  FitsEnv.eq_iff

theorem fitsEnv_kem_of_detPostPollEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {kpkBoxSize pubCap privCap sigCap : Nat}
    (h : FitsEnv M lim st (P2Sub3DetPostPollEnv kpkBoxSize pubCap privCap sigCap)) :
    FitsEnv M lim (M.stepEvents (rustDeallocEvents kpkBoxSize 8) st)
      KemKeyPairFromPubPrivEnv := by
  have hall : FitsEvents M lim st (p2Sub3DetPostPollEvents kpkBoxSize pubCap privCap sigCap) :=
    (fitsEnv_p2Sub3DetPostPollEnv_iff kpkBoxSize pubCap privCap sigCap).mp h
  unfold p2Sub3DetPostPollEvents p2Sub3PreTailEvents at hall
  rw [fitsEvents_append, fitsEvents_append, fitsEvents_append] at hall
  rintro _ rfl
  exact hall.1.1.2

theorem fitsEnv_tail_of_detPostPollEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {kpkBoxSize pubCap privCap sigCap : Nat}
    (h : FitsEnv M lim st (P2Sub3DetPostPollEnv kpkBoxSize pubCap privCap sigCap)) :
    FitsEnv M lim (M.stepEvents (p2Sub3PreTailEvents kpkBoxSize pubCap privCap sigCap) st)
      P2Sub3TailAllocEnv := by
  have hall : FitsEvents M lim st (p2Sub3DetPostPollEvents kpkBoxSize pubCap privCap sigCap) :=
    (fitsEnv_p2Sub3DetPostPollEnv_iff kpkBoxSize pubCap privCap sigCap).mp h
  unfold p2Sub3DetPostPollEvents at hall
  rw [fitsEvents_append] at hall
  exact fitsEnv_p2Sub3TailAllocEnv_iff.mpr hall.2

-- Concrete `FitsEnv` non-vacuity witness for `P2Sub3DetPostPollEnv 64 1569 3169 64` under `coarseCostModel`.
example :
    FitsEnv coarseCostModel
      { staticCount := 64, staticBytes := 67108864, physCap := 536870912, enforced := true }
      coarseCostModel.init
      (P2Sub3DetPostPollEnv 64 1569 3169 64) := by
  rw [fitsEnv_p2Sub3DetPostPollEnv_iff]
  have hevs : p2Sub3DetPostPollEvents 64 1569 3169 64 =
      [.free 8 64, .alloc 1568, .alloc 3168, .free 1 1569, .free 1 3169, .free 1 64,
       .alloc 21] := by decide
  rw [hevs]
  dsimp only [FitsEvents, FitsEvent, AllocEvent.withinMaxAlloc, FitsStep,
    AllocCostModel.step, coarseCostModel, coarseStep, coarseStepReserve]
  decide

/-! ## 2. Budget-Threaded Placed Substage P2.3 (`+0x1460 -> +0x0d5c` or `+0x0998` Arm 2) -/

set_option maxHeartbeats 1400000 in
/-- Budget-Threaded Placed Kit-Generic Substage P2.3 (`+0x1460 -> +0x0d5c` or `+0x0998` Arm 2)
in CPS form on `stageP1ProgPlaced ext`:
polls `kpkKit.getPoll`, delegates `.error e` at `+0x0998` to `hErr` with
`A.pool lim (M.stepEvents evs_poll st) s2`, and on `.ok r` drops/frees the KPK future,
deserializes the ML-KEM-1024 keypair (`kemKeyPairSerde`), frees the cloned record buffers,
allocates & drops the temporary `"missing pq ciphertext"` error, and reaches `+0x0d5c` (`hOk`)
with `A.pool lim (M.stepEvents (evs_poll ++ p2Sub3OkPostPollEvents kpkKit.getBoxSize pubCap.toNat privCap.toNat sigCap.toNat evs_drop) st) sf`. -/
theorem stageP2_sub3_kits_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlaced4KOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hkpkOk : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkEnv ext)
    (stk : Nat) (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_kpk_poll : kpkKit.getPollStack ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (ret : BitVec 64) (st : M.σ) (s0 s : State) (Frame : SepProp)
    (Q : State → SepProp → Prop) {Qp : State → SepProp → Prop}
    (coroPtr ctxPtr msgPtr kyberFutPtr kyberStorePtr kyberCtCap
     v_98 v_a0 v_b0 u_4f8 u_500 u_90 u_a8 u_b8 u_c0 u_d0
     u_3d8 u_3e0 u_3e8 u_3f0 : BitVec 64)
    (kyberPreKeyId : BitVec 32) (b_4f1 : BitVec 8) (stKpk : kpkKit.KpkState)
    (hfits_poll : FitsEnv M lim st (kpkEnv.getPollEnv stKpk kyberPreKeyId))
    (hfits_kem : ∀ (r : KyberPreKeyRecord) (evs_poll : List AllocEvent),
      kpkKit.getRel stKpk kyberPreKeyId (.ok r) → kpkKit.RecOk r →
      kpkEnv.getPollEnv stKpk kyberPreKeyId evs_poll →
      FitsEnv M lim
        (M.stepEvents (evs_poll ++ rustDeallocEvents kpkKit.getBoxSize 8) st)
        KemKeyPairFromPubPrivEnv)
    (hfits_tail : ∀ (r : KyberPreKeyRecord) (evs_poll : List AllocEvent)
      (pubCap privCap sigCap : Nat),
      kpkKit.getRel stKpk kyberPreKeyId (.ok r) → kpkKit.RecOk r →
      kpkEnv.getPollEnv stKpk kyberPreKeyId evs_poll →
      1569 ≤ pubCap → 3169 ≤ privCap →
      FitsEnv M lim
        (M.stepEvents
          (evs_poll ++ p2Sub3PreTailEvents kpkKit.getBoxSize pubCap privCap sigCap) st)
        P2Sub3TailAllocEnv)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem)
    (henv : ∀ s1 : State, Steps (stageP1ProgPlaced ext) s s1 →
      s1.trace = s.trace → kpkKit.envOk s1.fs.files)
    (hid_kpk : kpkKit.getIdOk kyberPreKeyId)
    (hrec_wf : ∀ r : KyberPreKeyRecord, kpkKit.getRel stKpk kyberPreKeyId (.ok r) →
      kpkKit.RecOk r →
      ∃ kyberPubBytes kyberPrivBytes : List (BitVec 8),
        kyberPubBytes.length = 1568 ∧ kyberPrivBytes.length = 3168 ∧
        r.signedPreKey.publicKey = 8#8 :: kyberPubBytes ∧
        r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes)
    (hpc : s.pc = stageP1EntryPlaced + 0x1460#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = kyberFutPtr) (hx1 : s.readReg64 .x1 = 0#64 + kpkKit.getFutVtOff)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = v_a0) (hx26 : s.readReg64 .x26 = v_98)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hErr : ∀ (e : kpkKit.GetErr) (evs_poll : List AllocEvent) (s2 : State),
      Steps (stageP1ProgPlaced ext) s s2 →
      kpkKit.getRel stKpk kyberPreKeyId (.error e) →
      kpkEnv.getPollEnv stKpk kyberPreKeyId evs_poll →
      s2.pc = stageP1EntryPlaced + 0x998#64 →
      s2.status = .Running → s2.sp = s.sp →
      s2.trace = s.trace ++ kpkKit.getEvs kyberPreKeyId (.error e) →
      s2.readReg64 .x19 = coroPtr → s2.readReg64 .x21 = v_b0 →
      s2.readReg64 .x23 = v_a0 → s2.readReg64 .x25 = s.readReg64 .x25 →
      s2.readReg64 .x26 = v_98 → s2.readReg64 .x27 = ctxPtr →
      s2.readReg64 .x28 = s.readReg64 .x28 → s2.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl s2.mem →
      SepWPp (stageP1ProgPlaced ext) ret s2
        (kpkGetPollOutAt kpkKit (s.sp + 0x3e0#64) (.error e) ∗
         kpkKit.getBoxAt kyberFutPtr kyberStorePtr kyberPreKeyId 1#8 ∗
         kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.error e)) ∗
         ((s.sp + 0x90#64) ↦₆₄ u_90) ∗ ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
         ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
         ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
         ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
         memRegion (s.sp + 0xa90#64) 65 ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ u_3d8) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ u_3e0) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ u_3e8) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ u_3f0) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
         ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
         ((coroPtr + 0x500#64) ↦₆₄ (0#64 + kpkKit.getFutVtOff)) ∗
         ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
         ((0#64 + kpkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + kpkKit.getFutDropOff)) ∗
         ((0#64 + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
         ((0#64 + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((0#64 + kpkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kpkKit.getPollOff)) ∗
         A.live kyberFutPtr kpkKit.getBoxSize 8 ∗
         A.pool lim (M.stepEvents evs_poll st) s2 ∗ stackAt s.sp stk ∗ Frame)
        Q Qp)
    (hOk : ∀ (r : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
      (evs_poll evs_drop : List AllocEvent)
      (pkBuf skBuf pubCap sigCap privCap privPtr : BitVec 64) (sf : State),
      Steps (stageP1ProgPlaced ext) s sf →
      kpkKit.getRel stKpk kyberPreKeyId (.ok r) → kpkKit.RecOk r →
      kpkEnv.getPollEnv stKpk kyberPreKeyId evs_poll →
      FreeOnlyEvs evs_drop →
      1569 ≤ pubCap.toNat → 3169 ≤ privCap.toNat →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      r.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      pkBuf ≠ 0#64 → skBuf ≠ 0#64 →
      sf.pc = stageP1EntryPlaced + 0xd5c#64 →
      sf.status = .Running → sf.sp = s.sp →
      sf.trace = s.trace ++ kpkKit.getEvs kyberPreKeyId (.ok r) →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x21 = msgPtr + 0x90#64 →
      sf.readReg64 .x22 = kyberCtCap → sf.readReg64 .x23 = v_a0 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = v_98 →
      sf.readReg64 .x27 = ctxPtr → sf.readReg64 .x28 = s.sp + 0xa90#64 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (stageP1ProgPlaced ext) ret sf
        (kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok r)) ∗
         (pkBuf ↦ₛ kyberPubBytes) ∗ A.live pkBuf 1568 1 ∗
         (skBuf ↦ₛ kyberPrivBytes) ∗ A.live skBuf 3168 1 ∗
         ((s.sp + 0x90#64) ↦₆₄ sigCap) ∗ ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
         ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xa8#64) ↦₆₄ 3169#64) ∗
         ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xb8#64) ↦₆₄ privCap) ∗
         ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ privPtr) ∗
         memRegion (s.sp + 0x3e0#64) 88 ∗ memRegion (s.sp + 0xa90#64) 65 ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
         ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
         ((coroPtr + 0x500#64) ↦₆₄ (0#64 + kpkKit.getFutVtOff)) ∗
         ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
         ((0#64 + kpkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + kpkKit.getFutDropOff)) ∗
         ((0#64 + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
         ((0#64 + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((0#64 + kpkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kpkKit.getPollOff)) ∗
         A.pool lim
           (M.stepEvents
             (evs_poll ++ p2Sub3OkPostPollEvents kpkKit.getBoxSize
               pubCap.toNat privCap.toNat sigCap.toNat evs_drop) st) sf ∗
         stackAt s.sp stk ∗ Frame)
        Q Qp) :
    SepWPp (stageP1ProgPlaced ext) ret s
      (((s.sp + 0x90#64) ↦₆₄ u_90) ∗ ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (s.sp + 0x3e0#64) 88 ∗ memRegion (s.sp + 0xa90#64) 65 ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ u_3d8) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ u_3e0) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ u_3e8) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ u_3f0) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗ ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
       ((0#64 + kpkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + kpkKit.getFutDropOff)) ∗
       ((0#64 + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
       ((0#64 + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((0#64 + kpkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kpkKit.getPollOff)) ∗
       A.live kyberFutPtr kpkKit.getBoxSize 8 ∗
       kpkKit.getBoxAt kyberFutPtr kyberStorePtr kyberPreKeyId 0#8 ∗
       kpkKit.storeAt kyberStorePtr stKpk ∗ A.pool lim st s ∗ stackAt s.sp stk ∗ Frame)
      Q Qp := by
  have hstep1 := p2_seg3a_ext_placed_wp (A := A) (lim := lim) ext st s coroPtr ctxPtr kyberFutPtr
    (0#64 + kpkKit.getFutVtOff) (0#64 + kpkKit.getPollOff) u_4f8 u_500
    hpc hrun hx0 hx1 hx19 hx27
  refine p2_bind_sepWP_qp_frame_state_placed hCode hstep1 (by sep_focus)
    fun s1 hst01 hpc1 hrun1 hCode1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, _, hx8_1, hx19_1, hx21_1, hx23_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  have hstk_poll := p2_stackAt_split_of_le s.sp stk kpkKit.getPollStack hstk_kpk_poll hstk_lt
  refine weaken_frame (Entails.of_eq hstk_poll) (by sep_focus) ?_
  sep_norm
  refine p2_call_rocl_nopanic_steps_frame_placed
    (x := (({ fut := kyberFutPtr, self := kyberStorePtr, out := s.sp + 0x3e0#64,
              id := kyberPreKeyId } : PreKeyPollCall), stKpk, st))
    hCode1 (hkpkOk.getPoll (by decide)) hpc1 hrun1 hsp1_al hx30_1
    (hsp1 ▸ p2_kpkGetPoll_pre_intro_placed (henv s1 hst01 htr1) hx0_1 hx8_1 hid_kpk hfits_poll)
    (by sep_focus)
    (hnext := fun s2 hst12 hpc2 hrun2 hsp2_1 _ hcs2 hCode2 => ?_)
  dsimp only [kitKpkGetPollSpecE, withEnvPre, kitKpkGetPollSpec]
  rcases hcs2 with ⟨hcs2_19, _, hcs2_21, _, hcs2_23, _, hcs2_25, hcs2_26, hcs2_27, hcs2_28,
    hcs2_29, hvregs2_1⟩
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
  rw [hsp1]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun ans => SepWPp.exists_elim fun evs_poll =>
    SepWPp.pure_elim fun ⟨hrel, htr2_1, hevs_poll⟩ => ?_
  refine weaken_frame (Entails.of_eq hstk_poll.symm) (by sep_focus) ?_
  have htr2 : s2.trace = s.trace ++ kpkKit.getEvs kyberPreKeyId ans := by rw [htr2_1, htr1]
  cases ans with
  | error e =>
    have herr := hErr e evs_poll s2 (hst01.trans hst12) hrel hevs_poll hpc2 hrun2 hsp2 htr2
      (hcs2_19.trans hx19_1) (by rw [hcs2_21, hx21_1, hx21]) (by rw [hcs2_23, hx23_1, hx23])
      (hcs2_25.trans hx25_1) (by rw [hcs2_26, hx26_1, hx26]) (hcs2_27.trans hx27_1)
      (hcs2_28.trans hx28_1) (hcs2_29.trans hx29_1)
      (by rw [hvregs2_1, hvregs1, hvregs]) hCode2
    exact p2_sepWPp_weaken_eq herr (by sep_focus)
  | ok r =>
    dsimp only [kpkGetPollOutAt]
    simp only [sepConj_assoc]
    refine p2_sepWPp_pure_elim_frame (kpkKit.RecOk r) (by sep_focus) fun hrec_ok => ?_
    obtain ⟨kyberPubBytes, kyberPrivBytes, hpub_len, hpriv_len, hpub_eq, hpriv_eq⟩ :=
      hrec_wf r hrel hrec_ok
    refine weaken_frame
      (p2_signedPreKeyStructAt_unpack A.repAlloc (s.sp + 0x3e0#64) r.signedPreKey)
      (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun pubCap => SepWPp.exists_elim fun pubPtr =>
      SepWPp.exists_elim fun privCap => SepWPp.exists_elim fun privPtr =>
      SepWPp.exists_elim fun sigCap => SepWPp.exists_elim fun sigPtr =>
      SepWPp.exists_elim fun pad32 => ?_
    have hpub_bv : BitVec.ofNat 64 r.signedPreKey.publicKey.length = 1569#64 := by
      rw [hpub_eq]; simp [hpub_len]
    have hpriv_bv : BitVec.ofNat 64 r.signedPreKey.privateKey.length = 3169#64 := by
      rw [hpriv_eq]; simp [hpriv_len]
    rw [hpub_bv, hpriv_bv, hpub_eq, hpriv_eq]
    refine weaken_frame
      (p2_vecU8Buf_nonempty A.repAlloc pubCap pubPtr (8#8 :: kyberPubBytes) (by simp))
      (by sep_focus) ?_
    simp only [sepConj_assoc, RustCliAllocBudget.repAlloc_live]
    refine SepWPp.pure_elim fun ⟨hpub_le, _, hpub_nz, hpub_ne2, hpub_ne1⟩ => ?_
    refine weaken_frame
      (p2_vecU8Buf_nonempty A.repAlloc privCap privPtr (8#8 :: kyberPrivBytes) (by simp))
      (by sep_focus) ?_
    simp only [sepConj_assoc, RustCliAllocBudget.repAlloc_live]
    refine SepWPp.pure_elim fun ⟨hpriv_le, _, hpriv_nz, _, _⟩ => ?_
    have hpub_cap : 1569 ≤ pubCap.toNat := by simpa [hpub_len] using hpub_le
    have hpriv_cap : 3169 ≤ privCap.toNat := by simpa [hpriv_len] using hpriv_le
    let st_poll := M.stepEvents evs_poll st
    have hstep3 := p2_seg3b_gen_placed_wp (A := A) (lim := lim) ext st_poll s2 coroPtr kyberFutPtr
      (0#64 + kpkKit.getFutVtOff) (0#64 + kpkKit.getFutDropOff)
      pubCap pubPtr privCap privPtr sigCap sigPtr
      v_98 v_a0 v_b0 u_90 v_98 v_a0 u_a8 v_b0 u_b8 u_d0
      hpc2 hrun2 hsp2_align hpub_ne2 (kpkKit.getFutDrop_ne_zero rfl)
      (hcs2_19.trans hx19_1) (by rw [hcs2_21, hx21_1, hx21])
      (by rw [hcs2_23, hx23_1, hx23]) (by rw [hcs2_26, hx26_1, hx26])
    have hvt0 : (0#64 + kpkKit.getFutVtOff) + 0x0#64 = 0#64 + kpkKit.getFutVtOff :=
      BitVec.add_zero _
    rw [hsp2, hvt0] at hstep3
    refine p2_bind_sepWP_qp_frame_state_placed hCode2 hstep3 (by sep_focus)
      fun s3 hst23 hpc3 hrun3 hCode3 hregs3 => ?_
    rcases hregs3 with ⟨hsp3, htr3_2, _, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3,
      hx26_3, hx27_3, hx28_3, hx29_3, hx30_3, hvregs3_2⟩
    have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3] using hsp_align
    refine p2_call_rocl_nopanic_steps_frame_placed (x := ()) (P_spec := emp)
      hCode3 (hkpkOk.getFutDrop (by decide)) hpc3 hrun3 hsp3_al hx30_3
      (Entails.refl emp) (emp_sepConj _).symm
      (hnext := fun s4 hst34 hpc4 hrun4 hsp4_3 _ hcs4 hCode4 => ?_)
    dsimp only [futDropBudgetSpec]
    refine SepWPp.pure_elim fun ⟨htr4_3, hvm34⟩ => ?_
    refine SepWPp.transport_budgetPool hvm34 (by sep_focus) ?_
    rcases hcs4 with ⟨hcs4_19, hcs4_20, hcs4_21, hcs4_22, hcs4_23, hcs4_24, hcs4_25, hcs4_26,
      hcs4_27, hcs4_28, hcs4_29, hvregs4_3⟩
    have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
    have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4]; exact hsp_align
    refine weaken_frame (kpkKit.getBoxAt_memRegion kyberFutPtr kyberStorePtr kyberPreKeyId 1#8)
      (by sep_focus) ?_
    refine weaken_frame
      (p2_preKeyRecordOut64_tail_to_memRegion88 (s.sp + 0x3e0#64)
        pubCap pubPtr 1569#64 privCap privPtr 3169#64 sigCap sigPtr
        (BitVec.ofNat 64 r.signedPreKey.signature.length)
        r.signedPreKey.timestamp (pad32 ++ r.signedPreKey.id))
      (by sep_focus) ?_
    have hstk_alloc := p2_stackAt_split_of_le s.sp stk allocHookStack
      (Nat.le_trans p2_alloc_le_pure hstk_pure) hstk_lt
    refine weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
    have hstep5 := p2_seg3c_hooks_placed_wp ext hH st_poll s4 coroPtr ctxPtr kyberFutPtr
      (0#64 + kpkKit.getFutVtOff) pubCap pubPtr privPtr sigPtr u_c0 kpkKit.getBoxSize
      hpc4 hrun4 hsp4_align hpub_ne1 kpkKit.getBoxSize_ne_zero kpkKit.getBoxSize_lt
      (hcs4_19.trans hx19_3) (hcs4_20.trans hx20_3) (hcs4_21.trans hx21_3)
      (hcs4_22.trans hx22_3) (hcs4_23.trans hx23_3) (hcs4_24.trans hx24_3)
      (by rw [hcs4_27, hx27_3, hcs2_27, hx27_1]) (hcs4_28.trans hx28_3)
    rw [hsp4] at hstep5
    refine p2_bind_sepWP_qp_frame_state_placed hCode4 hstep5 (by sep_focus)
      fun s5 hst45 hpc5 hrun5 hCode5 hregs5 => ?_
    rcases hregs5 with ⟨hsp5, htr5_4, hx0_5, hx1_5, hx2_5, hx3_5, hx8_5, hx19_5, hx20_5, _,
      hx23_5, hx25_5, hx26_5, hx27_5, hx28_5, hx29_5, hx30_5, hvregs5_4⟩
    simp only [arm64_norm] at hpc5
    have hsp5_al : s5.spAligned = true := by simpa only [State.spAligned, hsp5] using hsp_align
    refine weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
    have hstk_kem1 := p2_stackAt_split_of_le s.sp stk (64 + allocHookStack)
      (Nat.le_trans p2_kemStack_le_pure hstk_pure) hstk_lt
    have hstk_kem2 := p2_stackAt_kemKeyPair_eq s.sp
    have hmr65_split := p2_memRegion_65_split_cells5 (s.sp + 0xa90#64)
    refine weaken_frame (Entails.of_eq hstk_kem1) (by sep_focus) ?_
    refine weaken_frame (Entails.of_eq hstk_kem2) (by sep_focus) ?_
    refine weaken_frame (Entails.of_eq hmr65_split) (by sep_focus) ?_
    sep_norm
    let st_debox := M.stepEvents (rustDeallocEvents kpkKit.getBoxSize 8) st_poll
    have hfits_kem_debox : FitsEnv M lim st_debox KemKeyPairFromPubPrivEnv := by
      have hk := hfits_kem r evs_poll hrel hrec_ok hevs_poll
      simpa only [st_debox, st_poll, M.stepEvents_append] using hk
    refine p2_call_lscl_nopanic_steps_frame_placed
      (x := ((pubPtr, kyberPubBytes, privPtr, kyberPrivBytes, s.sp + 0xa90#64), st_debox))
      (P_spec := (pubPtr ↦ₛ (8#8 :: kyberPubBytes)) ∗ (privPtr ↦ₛ (8#8 :: kyberPrivBytes)) ∗
        cells (s.sp + 0xa90#64) 5 ∗
        (memRegion (s.sp - 4160#64) 64 ∗ stackAt s.sp allocHookStack) ∗
        A.pool lim st_debox s5)
      hCode5 hPure.kemKeyPairSerde hpc5 hrun5 hsp5_al hx30_5
      (by
        dsimp only [kemKeyPairFromPubPrivOkSpec,
          LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget.kemKeyPairFromPubPrivOkSpec,
          CryptoVerification.E2E.Pqxdh.ResponderStore.kemKeyPairFromPubPrivOkSpec,
          RustCliAllocBudget.atState_pool, RustCliAllocBudget.atState_live]
        rw [hsp5]
        have hlr5 : LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s5.readReg64 .lr) := by
          change LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s5.readReg64 .x30)
          rw [hx30_5]
          exact LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_blockPlacement_base_add
            518 0xc74#64 (by decide) (by decide)
        exact Entails.pure_right ⟨hfits_kem_debox, hlr5⟩
          (Entails.pure_right ⟨hx0_5, hx1_5, hx2_5, hx3_5, hx8_5, hpub_len, hpriv_len⟩
            (Entails.refl _)))
      (by sep_focus)
      (hnext := fun s6 hst56 hpc6 hrun6 hsp6_5 _ hcs6 hCode6 => ?_)
    dsimp only [kemKeyPairFromPubPrivOkSpec,
      LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget.kemKeyPairFromPubPrivOkSpec,
      CryptoVerification.E2E.Pqxdh.ResponderStore.kemKeyPairFromPubPrivOkSpec,
      RustCliAllocBudget.atState_pool, RustCliAllocBudget.atState_live]
    rcases hcs6 with ⟨hcs6_19, hcs6_20, _, _, hcs6_23, _, hcs6_25, hcs6_26, hcs6_27, hcs6_28,
      hcs6_29, hvregs6_5⟩
    have hsp6 : s6.sp = s.sp := hsp6_5.trans hsp5
    have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by rw [hsp6]; exact hsp_align
    rw [hsp5,
        show (s.sp + 0xa90#64) + 8#64 = s.sp + 0xa98#64 by bv_omega,
        show (s.sp + 0xa90#64) + 16#64 = s.sp + 0xaa0#64 by bv_omega,
        show (s.sp + 0xa90#64) + 24#64 = s.sp + 0xaa8#64 by bv_omega,
        show (s.sp + 0xa90#64) + 32#64 = s.sp + 0xab0#64 by bv_omega]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun pkBuf => SepWPp.exists_elim fun skBuf => ?_
    refine SepWPp.pure_elim fun ⟨htr6_5, hpk_nz, hsk_nz⟩ => ?_
    refine weaken_frame (Entails.of_eq hstk_kem2.symm) (by sep_focus) ?_
    refine weaken_frame (Entails.of_eq hstk_kem1.symm) (by sep_focus) ?_
    refine weaken_frame (p2_vecU8Buf_rejoin pubPtr pubCap (8#8 :: kyberPubBytes) hpub_le)
      (by sep_focus) ?_
    refine weaken_frame (p2_vecU8Buf_rejoin privPtr privCap (8#8 :: kyberPrivBytes) hpriv_le)
      (by sep_focus) ?_
    refine weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
    sep_norm
    let st_kem := M.stepEvents kemKeyPairFromPubPrivEvents st_debox
    have hst06 := hst01.trans (hst12.trans (hst23.trans (hst34.trans (hst45.trans hst56))))
    have hnext7 : ∀ (v90 : BitVec 64) (hv90 : v90 = sigCap) (st7 : M.σ)
        (hst7 : st7 = M.stepEvents
          (evs_poll ++ p2Sub3PreTailEvents kpkKit.getBoxSize
            pubCap.toNat privCap.toNat v90.toNat) st)
        (s7 : State),
        Steps (stageP1ProgPlaced ext) s6 s7 →
        s7.pc = stageP1EntryPlaced + 0xd04#64 →
        s7.status = .Running → LibsignalCodeRoLoaded lsmpl s7.mem →
        s7.sp = s.sp ∧ s7.trace = s6.trace ∧
        s7.readReg64 .x0 = 21#64 ∧ s7.readReg64 .x1 = 1#64 ∧
        s7.readReg64 .x19 = coroPtr ∧ s7.readReg64 .x21 = msgPtr + 0x90#64 ∧
        s7.readReg64 .x22 = kyberCtCap ∧ s7.readReg64 .x23 = v_a0 ∧
        s7.readReg64 .x25 = s6.readReg64 .x25 ∧ s7.readReg64 .x26 = v_98 ∧
        s7.readReg64 .x27 = s6.readReg64 .x27 ∧ s7.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s7.readReg64 .x29 = s6.readReg64 .x29 ∧ calleeSavedVRegs s7 = calleeSavedVRegs s6 →
        SepWPp (stageP1ProgPlaced ext) ret s7
          ((((s.sp + 0xa90#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
            ((s.sp + 0xa98#64) ↦₆₄ pkBuf) ∗ ((s.sp + 0xaa0#64) ↦₆₄ 0x620#64) ∗
            ((s.sp + 0xaa8#64) ↦₆₄ skBuf) ∗ ((s.sp + 0xab0#64) ↦₆₄ 0xc60#64) ∗
            ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
            ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
            ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗ ((s.sp + 0x90#64) ↦₆₄ v90) ∗
            ((s.sp + 0x98#64) ↦₆₄ v_98) ∗ ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
            ((s.sp + 0xb8#64) ↦₆₄ privCap) ∗ ((s.sp + 0xd0#64) ↦₆₄ privPtr) ∗
            A.pool lim st7 s7 ∗ stackAt s.sp allocHookStack ∗
            ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap)) ∗
           (kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok r)) ∗
            (pkBuf ↦ₛ kyberPubBytes) ∗ A.live pkBuf 1568 1 ∗
            (skBuf ↦ₛ kyberPrivBytes) ∗ A.live skBuf 3168 1 ∗
            ((s.sp + 0xa8#64) ↦₆₄ 3169#64) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
            ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ memRegion (s.sp + 0xab8#64) 25 ∗
            memRegion (s.sp + 0x3e0#64) 88 ∗
            ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
            ((coroPtr + 0x500#64) ↦₆₄ (0#64 + kpkKit.getFutVtOff)) ∗
            ((0#64 + kpkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + kpkKit.getFutDropOff)) ∗
            ((0#64 + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
            ((0#64 + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            ((0#64 + kpkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kpkKit.getPollOff)) ∗
            memRegion (s.sp - BitVec.ofNat 64 stk) (stk - allocHookStack) ∗ Frame))
          Q Qp := by
      intro v90 hv90 st7 hst7 s7 hst67 hpc7 hrun7 hCode7 hregs7
      subst hv90
      rcases hregs7 with ⟨hsp7, htr7_6, hx0_7, hx1_7, hx19_7, hx21_7, hx22_7, hx23_7, hx25_7,
        hx26_7, hx27_7, hx28_7, hx29_7, hvregs7_6⟩
      refine weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
      have htr7 : s7.trace = s.trace ++ kpkKit.getEvs kyberPreKeyId (.ok r) := by
        rw [htr7_6, htr6_5, htr5_4, htr4_3, htr3_2, htr2]
      have hvregs7 : calleeSavedVRegs s7 = calleeSavedVRegs s0 := by
        rw [hvregs7_6, hvregs6_5, hvregs5_4, hvregs4_3, hvregs3_2, hvregs2_1, hvregs1, hvregs]
      have hfits_st7 : FitsEnv M lim st7 P2Sub3TailAllocEnv := by
        rw [hst7]
        exact hfits_tail r evs_poll pubCap.toNat privCap.toNat v90.toNat
          hrel hrec_ok hevs_poll hpub_cap hpriv_cap
      let TailFrame : SepProp :=
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok r)) ∗
        (pkBuf ↦ₛ kyberPubBytes) ∗ A.live pkBuf 1568 1 ∗
        (skBuf ↦ₛ kyberPrivBytes) ∗ A.live skBuf 3168 1 ∗
        ((s.sp + 0x90#64) ↦₆₄ v90) ∗ ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
        ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xa8#64) ↦₆₄ 3169#64) ∗
        ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xb8#64) ↦₆₄ privCap) ∗
        ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ privPtr) ∗
        ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
        ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
        ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
        ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
        ((coroPtr + 0x500#64) ↦₆₄ (0#64 + kpkKit.getFutVtOff)) ∗
        ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
        ((0#64 + kpkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + kpkKit.getFutDropOff)) ∗
        ((0#64 + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
        ((0#64 + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + kpkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kpkKit.getPollOff)) ∗
        Frame
      have htail := stageP2_sub3_tail_kits_ext_placed hH hPure hstk_pure hstk_lt
        st7 s0 s7 ret s.sp coroPtr pkBuf skBuf kyberCtCap TailFrame Q (Qp := Qp)
        hfits_st7 hkyber_nz hCode7 hpc7 hrun7 hsp7 hsp_align hvregs7
        hx0_7 hx1_7 hx19_7 hx22_7
        (fun sf evs_drop hfree_drop hst7f hpcf hrunf hspf htrf_7
             hx19_f hx21_f hx22_f hx23_f hx25_f hx26_f hx27_f hx28_f hx29_f hvregsf hCodef => by
          have hpool_eq :
              M.stepEvents (p2Sub3TailAllocEvents ++ evs_drop) st7 =
                M.stepEvents
                  (evs_poll ++ p2Sub3OkPostPollEvents kpkKit.getBoxSize
                    pubCap.toNat privCap.toNat v90.toNat evs_drop) st := by
            rw [hst7]
            unfold p2Sub3OkPostPollEvents p2Sub3DetPostPollEvents
            simp only [M.stepEvents_append, List.append_assoc]
          have hok := hOk r kyberPubBytes kyberPrivBytes evs_poll evs_drop
            pkBuf skBuf pubCap v90 privCap privPtr sf
            (hst06.trans (hst67.trans hst7f)) hrel hrec_ok hevs_poll hfree_drop hpub_cap hpriv_cap
            hpub_len hpriv_len hpub_eq hpriv_eq
            hpk_nz hsk_nz hpcf hrunf hspf (htrf_7.trans htr7)
            hx19_f (hx21_f.trans hx21_7) hx22_f (hx23_f.trans hx23_7)
            (by rw [hx25_f, hx25_7, hcs6_25, hx25_5, hcs4_25, hx25_3, hcs2_25, hx25_1])
            (hx26_f.trans hx26_7)
            (by rw [hx27_f, hx27_7, hcs6_27, hx27_5])
            (hx28_f.trans hx28_7)
            (by rw [hx29_f, hx29_7, hcs6_29, hx29_5, hcs4_29, hx29_3, hcs2_29, hx29_1])
            hvregsf hCodef
          dsimp only [TailFrame]
          rw [hpool_eq]
          exact p2_sepWPp_weaken_eq hok (by sep_focus))
      dsimp only [TailFrame] at htail
      exact p2_sepWPp_weaken_eq htail (by sep_focus)
    by_cases hsig : sigCap = 0#64
    · rw [hsig]
      refine weaken_frame (p2_vecU8Buf_zero A.repAlloc sigPtr r.signedPreKey.signature)
        (by sep_focus) ?_
      sep_norm
      have hstep7 := p2_seg3d1_sig0_hooks_placed_wp ext hH st_kem s6 coroPtr msgPtr
        pubCap pubPtr privCap privPtr sigPtr pkBuf skBuf kyberCtCap v_98 v_a0
        u_3d8 u_3e0 u_3e8 u_3f0 b_4f1
        hpc6 hrun6 hsp6_align hpub_nz hpriv_nz
        (hcs6_19.trans hx19_5) (hcs6_20.trans hx20_5) (hcs6_23.trans hx23_5) (hcs6_28.trans hx28_5)
      rw [hsp6] at hstep7
      have hst7_0 :
          M.stepEvents
            (rustDeallocEvents pubCap.toNat 1 ++ rustDeallocEvents privCap.toNat 1) st_kem =
          M.stepEvents
            (evs_poll ++ p2Sub3PreTailEvents kpkKit.getBoxSize
              pubCap.toNat privCap.toNat (0#64).toNat) st := by
        dsimp only [st_kem, st_debox, st_poll, p2Sub3PreTailEvents, p2KpkVecFreeEvents]
        simp only [BitVec.toNat_ofNat, Nat.zero_mod, ↓reduceIte, M.stepEvents_append,
          List.append_assoc]
      exact p2_bind_sepWP_qp_frame_state_placed hCode6 hstep7 (by sep_focus)
        (hnext7 0#64 hsig.symm _ hst7_0)
    · refine weaken_frame
        (p2_vecU8Buf_dealloc_nonzero A.repAlloc sigCap sigPtr r.signedPreKey.signature hsig)
        (by sep_focus) ?_
      sep_norm
      have hstep7 := p2_seg3d1_sigNz_hooks_placed_wp ext hH st_kem s6 coroPtr msgPtr
        pubCap pubPtr privCap privPtr sigCap sigPtr pkBuf skBuf kyberCtCap v_98 v_a0
        u_3d8 u_3e0 u_3e8 u_3f0 b_4f1
        hpc6 hrun6 hsp6_align hpub_nz hpriv_nz hsig
        (hcs6_19.trans hx19_5) (hcs6_20.trans hx20_5) (hcs6_23.trans hx23_5) (hcs6_28.trans hx28_5)
      rw [hsp6] at hstep7
      have hsig_nat : sigCap.toNat ≠ 0 :=
        fun h => hsig (BitVec.eq_of_toNat_eq (by simpa using h))
      have hst7_nz :
          M.stepEvents
            (rustDeallocEvents pubCap.toNat 1 ++ rustDeallocEvents privCap.toNat 1 ++
              rustDeallocEvents sigCap.toNat 1) st_kem =
          M.stepEvents
            (evs_poll ++ p2Sub3PreTailEvents kpkKit.getBoxSize
              pubCap.toNat privCap.toNat sigCap.toNat) st := by
        dsimp only [st_kem, st_debox, st_poll, p2Sub3PreTailEvents]
        simp only [p2KpkVecFreeEvents, hsig_nat, ↓reduceIte, M.stepEvents_append, List.append_assoc]
      exact p2_bind_sepWP_qp_frame_state_placed hCode6 hstep7 (by sep_focus)
        (hnext7 sigCap rfl _ hst7_nz)

abbrev stageP2_sub3_kits_4k_placed := @stageP2_sub3_kits_ext_placed
abbrev stageP2_sub3_kits_hooks_placed := @stageP2_sub3_kits_ext_placed

theorem stageP2_sub3_kits_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlacedOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hkpkOk : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkEnv ext)
    (stk : Nat) (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_kpk_poll : kpkKit.getPollStack ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (ret : BitVec 64) (st : M.σ) (s0 s : State) (Frame : SepProp)
    (Q : State → SepProp → Prop) {Qp : State → SepProp → Prop}
    (coroPtr ctxPtr msgPtr kyberFutPtr kyberStorePtr kyberCtCap
     v_98 v_a0 v_b0 u_4f8 u_500 u_90 u_a8 u_b8 u_c0 u_d0
     u_3d8 u_3e0 u_3e8 u_3f0 : BitVec 64)
    (kyberPreKeyId : BitVec 32) (b_4f1 : BitVec 8) (stKpk : kpkKit.KpkState)
    (hfits_poll : FitsEnv M lim st (kpkEnv.getPollEnv stKpk kyberPreKeyId))
    (hfits_kem : ∀ (r : KyberPreKeyRecord) (evs_poll : List AllocEvent),
      kpkKit.getRel stKpk kyberPreKeyId (.ok r) → kpkKit.RecOk r →
      kpkEnv.getPollEnv stKpk kyberPreKeyId evs_poll →
      FitsEnv M lim
        (M.stepEvents (evs_poll ++ rustDeallocEvents kpkKit.getBoxSize 8) st)
        KemKeyPairFromPubPrivEnv)
    (hfits_tail : ∀ (r : KyberPreKeyRecord) (evs_poll : List AllocEvent)
      (pubCap privCap sigCap : Nat),
      kpkKit.getRel stKpk kyberPreKeyId (.ok r) → kpkKit.RecOk r →
      kpkEnv.getPollEnv stKpk kyberPreKeyId evs_poll →
      1569 ≤ pubCap → 3169 ≤ privCap →
      FitsEnv M lim
        (M.stepEvents
          (evs_poll ++ p2Sub3PreTailEvents kpkKit.getBoxSize pubCap privCap sigCap) st)
        P2Sub3TailAllocEnv)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem)
    (henv : ∀ s1 : State, Steps (stageP1ProgPlaced ext) s s1 →
      s1.trace = s.trace → kpkKit.envOk s1.fs.files)
    (hid_kpk : kpkKit.getIdOk kyberPreKeyId)
    (hrec_wf : ∀ r : KyberPreKeyRecord, kpkKit.getRel stKpk kyberPreKeyId (.ok r) →
      kpkKit.RecOk r →
      ∃ kyberPubBytes kyberPrivBytes : List (BitVec 8),
        kyberPubBytes.length = 1568 ∧ kyberPrivBytes.length = 3168 ∧
        r.signedPreKey.publicKey = 8#8 :: kyberPubBytes ∧
        r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes)
    (hpc : s.pc = stageP1EntryPlaced + 0x1460#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = kyberFutPtr) (hx1 : s.readReg64 .x1 = 0#64 + kpkKit.getFutVtOff)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = v_a0) (hx26 : s.readReg64 .x26 = v_98)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hErr : ∀ (e : kpkKit.GetErr) (evs_poll : List AllocEvent) (s2 : State),
      Steps (stageP1ProgPlaced ext) s s2 →
      kpkKit.getRel stKpk kyberPreKeyId (.error e) →
      kpkEnv.getPollEnv stKpk kyberPreKeyId evs_poll →
      s2.pc = stageP1EntryPlaced + 0x998#64 →
      s2.status = .Running → s2.sp = s.sp →
      s2.trace = s.trace ++ kpkKit.getEvs kyberPreKeyId (.error e) →
      s2.readReg64 .x19 = coroPtr → s2.readReg64 .x21 = v_b0 →
      s2.readReg64 .x23 = v_a0 → s2.readReg64 .x25 = s.readReg64 .x25 →
      s2.readReg64 .x26 = v_98 → s2.readReg64 .x27 = ctxPtr →
      s2.readReg64 .x28 = s.readReg64 .x28 → s2.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl s2.mem →
      SepWPp (stageP1ProgPlaced ext) ret s2
        (kpkGetPollOutAt kpkKit (s.sp + 0x3e0#64) (.error e) ∗
         kpkKit.getBoxAt kyberFutPtr kyberStorePtr kyberPreKeyId 1#8 ∗
         kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.error e)) ∗
         ((s.sp + 0x90#64) ↦₆₄ u_90) ∗ ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
         ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
         ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
         ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
         memRegion (s.sp + 0xa90#64) 65 ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ u_3d8) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ u_3e0) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ u_3e8) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ u_3f0) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
         ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
         ((coroPtr + 0x500#64) ↦₆₄ (0#64 + kpkKit.getFutVtOff)) ∗
         ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
         ((0#64 + kpkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + kpkKit.getFutDropOff)) ∗
         ((0#64 + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
         ((0#64 + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((0#64 + kpkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kpkKit.getPollOff)) ∗
         A.live kyberFutPtr kpkKit.getBoxSize 8 ∗
         A.pool lim (M.stepEvents evs_poll st) s2 ∗ stackAt s.sp stk ∗ Frame)
        Q Qp)
    (hOk : ∀ (r : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
      (evs_poll evs_drop : List AllocEvent)
      (pkBuf skBuf pubCap sigCap privCap privPtr : BitVec 64) (sf : State),
      Steps (stageP1ProgPlaced ext) s sf →
      kpkKit.getRel stKpk kyberPreKeyId (.ok r) → kpkKit.RecOk r →
      kpkEnv.getPollEnv stKpk kyberPreKeyId evs_poll →
      FreeOnlyEvs evs_drop →
      1569 ≤ pubCap.toNat → 3169 ≤ privCap.toNat →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      r.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      pkBuf ≠ 0#64 → skBuf ≠ 0#64 →
      sf.pc = stageP1EntryPlaced + 0xd5c#64 →
      sf.status = .Running → sf.sp = s.sp →
      sf.trace = s.trace ++ kpkKit.getEvs kyberPreKeyId (.ok r) →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x21 = msgPtr + 0x90#64 →
      sf.readReg64 .x22 = kyberCtCap → sf.readReg64 .x23 = v_a0 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = v_98 →
      sf.readReg64 .x27 = ctxPtr → sf.readReg64 .x28 = s.sp + 0xa90#64 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (stageP1ProgPlaced ext) ret sf
        (kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok r)) ∗
         (pkBuf ↦ₛ kyberPubBytes) ∗ A.live pkBuf 1568 1 ∗
         (skBuf ↦ₛ kyberPrivBytes) ∗ A.live skBuf 3168 1 ∗
         ((s.sp + 0x90#64) ↦₆₄ sigCap) ∗ ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
         ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xa8#64) ↦₆₄ 3169#64) ∗
         ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xb8#64) ↦₆₄ privCap) ∗
         ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ privPtr) ∗
         memRegion (s.sp + 0x3e0#64) 88 ∗ memRegion (s.sp + 0xa90#64) 65 ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
         ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
         ((coroPtr + 0x500#64) ↦₆₄ (0#64 + kpkKit.getFutVtOff)) ∗
         ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
         ((0#64 + kpkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + kpkKit.getFutDropOff)) ∗
         ((0#64 + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
         ((0#64 + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((0#64 + kpkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kpkKit.getPollOff)) ∗
         A.pool lim
           (M.stepEvents
             (evs_poll ++ p2Sub3OkPostPollEvents kpkKit.getBoxSize
               pubCap.toNat privCap.toNat sigCap.toNat evs_drop) st) sf ∗
         stackAt s.sp stk ∗ Frame)
        Q Qp) :
    SepWPp (stageP1ProgPlaced ext) ret s
      (((s.sp + 0x90#64) ↦₆₄ u_90) ∗ ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (s.sp + 0x3e0#64) 88 ∗ memRegion (s.sp + 0xa90#64) 65 ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ u_3d8) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ u_3e0) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ u_3e8) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ u_3f0) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗ ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
       ((0#64 + kpkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + kpkKit.getFutDropOff)) ∗
       ((0#64 + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
       ((0#64 + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((0#64 + kpkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kpkKit.getPollOff)) ∗
       A.live kyberFutPtr kpkKit.getBoxSize 8 ∗
       kpkKit.getBoxAt kyberFutPtr kyberStorePtr kyberPreKeyId 0#8 ∗
       kpkKit.storeAt kyberStorePtr stKpk ∗ A.pool lim st s ∗ stackAt s.sp stk ∗ Frame)
      Q Qp :=
  stageP2_sub3_kits_ext_placed ext hH hPure.to_4K
    kpkKit kpkEnv hkpkOk stk hstk_pure hstk_kpk_poll hstk_lt
    ret st s0 s Frame Q (Qp := Qp)
    coroPtr ctxPtr msgPtr kyberFutPtr kyberStorePtr kyberCtCap
    v_98 v_a0 v_b0 u_4f8 u_500 u_90 u_a8 u_b8 u_c0 u_d0 u_3d8 u_3e0 u_3e8 u_3f0
    kyberPreKeyId b_4f1 stKpk hfits_poll hfits_kem hfits_tail
    hkyber_nz hCode henv hid_kpk hrec_wf
    hpc hrun hsp_align hvregs hx0 hx1 hx19 hx21 hx23 hx26 hx27 hErr hOk

theorem stageP2_sub3_kits_seqEnv_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlaced4KOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hkpkOk : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkEnv ext)
    (stk : Nat) (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_kpk_poll : kpkKit.getPollStack ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (ret : BitVec 64) (st : M.σ) (s0 s : State) (Frame : SepProp)
    (Q : State → SepProp → Prop) {Qp : State → SepProp → Prop}
    (coroPtr ctxPtr msgPtr kyberFutPtr kyberStorePtr kyberCtCap
     v_98 v_a0 v_b0 u_4f8 u_500 u_90 u_a8 u_b8 u_c0 u_d0
     u_3d8 u_3e0 u_3e8 u_3f0 : BitVec 64)
    (kyberPreKeyId : BitVec 32) (b_4f1 : BitVec 8) (stKpk : kpkKit.KpkState)
    (hfits : FitsEnv M lim st
      (SeqEnv (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        (SeqEnv FreeOnlyEvs
          (SeqEnv KemKeyPairFromPubPrivEnv
            (SeqEnv FreeOnlyEvs P2Sub3TailAllocEnv)))))
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem)
    (henv : ∀ s1 : State, Steps (stageP1ProgPlaced ext) s s1 →
      s1.trace = s.trace → kpkKit.envOk s1.fs.files)
    (hid_kpk : kpkKit.getIdOk kyberPreKeyId)
    (hrec_wf : ∀ r : KyberPreKeyRecord, kpkKit.getRel stKpk kyberPreKeyId (.ok r) →
      kpkKit.RecOk r →
      ∃ kyberPubBytes kyberPrivBytes : List (BitVec 8),
        kyberPubBytes.length = 1568 ∧ kyberPrivBytes.length = 3168 ∧
        r.signedPreKey.publicKey = 8#8 :: kyberPubBytes ∧
        r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes)
    (hpc : s.pc = stageP1EntryPlaced + 0x1460#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = kyberFutPtr) (hx1 : s.readReg64 .x1 = 0#64 + kpkKit.getFutVtOff)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = v_a0) (hx26 : s.readReg64 .x26 = v_98)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hErr : ∀ (e : kpkKit.GetErr) (evs_poll : List AllocEvent) (s2 : State),
      Steps (stageP1ProgPlaced ext) s s2 →
      kpkKit.getRel stKpk kyberPreKeyId (.error e) →
      kpkEnv.getPollEnv stKpk kyberPreKeyId evs_poll →
      s2.pc = stageP1EntryPlaced + 0x998#64 →
      s2.status = .Running → s2.sp = s.sp →
      s2.trace = s.trace ++ kpkKit.getEvs kyberPreKeyId (.error e) →
      s2.readReg64 .x19 = coroPtr → s2.readReg64 .x21 = v_b0 →
      s2.readReg64 .x23 = v_a0 → s2.readReg64 .x25 = s.readReg64 .x25 →
      s2.readReg64 .x26 = v_98 → s2.readReg64 .x27 = ctxPtr →
      s2.readReg64 .x28 = s.readReg64 .x28 → s2.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl s2.mem →
      SepWPp (stageP1ProgPlaced ext) ret s2
        (kpkGetPollOutAt kpkKit (s.sp + 0x3e0#64) (.error e) ∗
         kpkKit.getBoxAt kyberFutPtr kyberStorePtr kyberPreKeyId 1#8 ∗
         kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.error e)) ∗
         ((s.sp + 0x90#64) ↦₆₄ u_90) ∗ ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
         ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
         ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
         ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
         memRegion (s.sp + 0xa90#64) 65 ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ u_3d8) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ u_3e0) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ u_3e8) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ u_3f0) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
         ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
         ((coroPtr + 0x500#64) ↦₆₄ (0#64 + kpkKit.getFutVtOff)) ∗
         ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
         ((0#64 + kpkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + kpkKit.getFutDropOff)) ∗
         ((0#64 + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
         ((0#64 + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((0#64 + kpkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kpkKit.getPollOff)) ∗
         A.live kyberFutPtr kpkKit.getBoxSize 8 ∗
         A.pool lim (M.stepEvents evs_poll st) s2 ∗ stackAt s.sp stk ∗ Frame)
        Q Qp)
    (hOk : ∀ (r : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
      (evs_poll evs_drop : List AllocEvent)
      (pkBuf skBuf pubCap sigCap privCap privPtr : BitVec 64) (sf : State),
      Steps (stageP1ProgPlaced ext) s sf →
      kpkKit.getRel stKpk kyberPreKeyId (.ok r) → kpkKit.RecOk r →
      kpkEnv.getPollEnv stKpk kyberPreKeyId evs_poll →
      FreeOnlyEvs evs_drop →
      1569 ≤ pubCap.toNat → 3169 ≤ privCap.toNat →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      r.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      pkBuf ≠ 0#64 → skBuf ≠ 0#64 →
      sf.pc = stageP1EntryPlaced + 0xd5c#64 →
      sf.status = .Running → sf.sp = s.sp →
      sf.trace = s.trace ++ kpkKit.getEvs kyberPreKeyId (.ok r) →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x21 = msgPtr + 0x90#64 →
      sf.readReg64 .x22 = kyberCtCap → sf.readReg64 .x23 = v_a0 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = v_98 →
      sf.readReg64 .x27 = ctxPtr → sf.readReg64 .x28 = s.sp + 0xa90#64 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (stageP1ProgPlaced ext) ret sf
        (kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok r)) ∗
         (pkBuf ↦ₛ kyberPubBytes) ∗ A.live pkBuf 1568 1 ∗
         (skBuf ↦ₛ kyberPrivBytes) ∗ A.live skBuf 3168 1 ∗
         ((s.sp + 0x90#64) ↦₆₄ sigCap) ∗ ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
         ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xa8#64) ↦₆₄ 3169#64) ∗
         ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xb8#64) ↦₆₄ privCap) ∗
         ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ privPtr) ∗
         memRegion (s.sp + 0x3e0#64) 88 ∗ memRegion (s.sp + 0xa90#64) 65 ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
         ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
         ((coroPtr + 0x500#64) ↦₆₄ (0#64 + kpkKit.getFutVtOff)) ∗
         ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
         ((0#64 + kpkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + kpkKit.getFutDropOff)) ∗
         ((0#64 + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
         ((0#64 + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((0#64 + kpkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kpkKit.getPollOff)) ∗
         A.pool lim
           (M.stepEvents
             (evs_poll ++ p2Sub3OkPostPollEvents kpkKit.getBoxSize
               pubCap.toNat privCap.toNat sigCap.toNat evs_drop) st) sf ∗
         stackAt s.sp stk ∗ Frame)
        Q Qp) :
    SepWPp (stageP1ProgPlaced ext) ret s
      (((s.sp + 0x90#64) ↦₆₄ u_90) ∗ ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (s.sp + 0x3e0#64) 88 ∗ memRegion (s.sp + 0xa90#64) 65 ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ u_3d8) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ u_3e0) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ u_3e8) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ u_3f0) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗ ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
       ((0#64 + kpkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + kpkKit.getFutDropOff)) ∗
       ((0#64 + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
       ((0#64 + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((0#64 + kpkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kpkKit.getPollOff)) ∗
       A.live kyberFutPtr kpkKit.getBoxSize 8 ∗
       kpkKit.getBoxAt kyberFutPtr kyberStorePtr kyberPreKeyId 0#8 ∗
       kpkKit.storeAt kyberStorePtr stKpk ∗ A.pool lim st s ∗ stackAt s.sp stk ∗ Frame)
      Q Qp :=
  stageP2_sub3_kits_ext_placed ext hH hPure
    kpkKit kpkEnv hkpkOk stk hstk_pure hstk_kpk_poll hstk_lt
    ret st s0 s Frame Q (Qp := Qp)
    coroPtr ctxPtr msgPtr kyberFutPtr kyberStorePtr kyberCtCap
    v_98 v_a0 v_b0 u_4f8 u_500 u_90 u_a8 u_b8 u_c0 u_d0 u_3d8 u_3e0 u_3e8 u_3f0
    kyberPreKeyId b_4f1 stKpk
    hfits.seq_left
    (fun _ evs_poll _ _ hevs_poll => by
      have h1 := ((hfits.seq_right hevs_poll).seq_right
        (freeOnlyEvs_rustDeallocEvents kpkKit.getBoxSize 8)).seq_left
      rwa [← M.stepEvents_append] at h1)
    (fun _ evs_poll pubCap privCap sigCap _ _ hevs_poll _ _ => by
      have hkem : KemKeyPairFromPubPrivEnv kemKeyPairFromPubPrivEvents := rfl
      have h1 := (((hfits.seq_right hevs_poll).seq_right
        (freeOnlyEvs_rustDeallocEvents kpkKit.getBoxSize 8)).seq_right hkem).seq_right
        (p2KpkVecFreeEvents_freeOnly pubCap privCap sigCap)
      simpa only [p2Sub3PreTailEvents, M.stepEvents_append, List.append_assoc] using h1)
    hkyber_nz hCode henv hid_kpk hrec_wf
    hpc hrun hsp_align hvregs hx0 hx1 hx19 hx21 hx23 hx26 hx27 hErr hOk

abbrev stageP2_sub3_kits_seqEnv_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlacedOfEnv P A lim F BobV1Env AcceptErrEnv ext) :=
  @stageP2_sub3_kits_seqEnv_ext_placed _ M P A lim F BobV1Env AcceptErrEnv ext hH hPure.to_4K

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3PlacedBudget
