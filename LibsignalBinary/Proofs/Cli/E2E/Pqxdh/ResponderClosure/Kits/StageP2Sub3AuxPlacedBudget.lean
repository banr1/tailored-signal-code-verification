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
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA3PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3AuxPlaced
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Stage P2 Substage P2.3 Helpers and Shared Tail

Defines `P2Sub3TailAllocEnv`, store-kit precondition helpers, and proves the budget-threaded placed
shared Substage P2.3 tail (`+0x0d04 → +0x0d5c`) on Block `518`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3AuxPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (speAt)
open CryptoVerification.LibsignalTripleRatchet.Getters (DropSpeGhost dropSpeStack)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  KyberPreKeyStoreSpec LibsignalCodeRoLoaded PreKeyPollCall withEnvPre
)
open CryptoVerification.E2E.Pqxdh.Initiator (AcceptKeysInput DRKey Primitives)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (decryptPrekeySavedRegsAt)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.SepWPp (weaken_frame)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  p2_alloc_le_pure
  p2_dropSpe_le_pure
  p2_drop_sep_frame
  p2_errStr_21_rejoin_entails
  p2_errStr_21_split16_eq
  p2_errStr_overlap13_entails
  p2_memRegion_88_spe_split_eq
  p2_missingKyber_ro0_sepWPp_placed
  p2_missingKyber_ro8_sepWPp_placed
  p2_missingKyber_ro13_sepWPp_placed
  p2_rocl_of_lscl_ro
  p2_sepWPp_weaken_eq
  p2_sp_a90_5words_entails_memRegion
  p2_speAt_badCiphertext_preKey_intro
  p2_stackAt_split_of_le
  stageP1EntryPlaced
  stageP1ProgPlaced
  stageP2PureAndErrStack
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FitsStep
  FreeOnlyEvs RustCliAllocBudget coarseCostModel coarseStep coarseStepReserve
  rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (
  KyberPreKeyStoreBudgetEnv kitKpkGetPollSpec kitKpkGetPollSpecE
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropSpeSpec)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  StageP2ClosureHooksPlaced
  StageP2PureCalleesPlaced4KOfEnv
  StageP2PureCalleesPlacedOfEnv
  p2_call_frame_cro_nopanic_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA2PlacedBudget (
  p2_seg3d2a_ext_placed_wp
  p2_seg3d2b_ext_placed_wp
  p2_seg3d2c_ext_placed_wp
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA3PlacedBudget (
  p2_seg3d2_alloc_cro_placed_ok
  p2_seg3d2_alloc_ext_placed_ok
  p2_seg3d2_alloc_hooks_placed_ok
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget (
  p2_bind_sepWP_qp_frame_state_placed
  p2_bind_sepWPp_steps_frame_state
  p2_call_rocl_nopanic_steps_frame_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2PlacedBudget (
  freeOnlyEvs_rustDeallocEvents
)

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  p2_missingKyber_ro0_sepWPp_placed
  p2_missingKyber_ro8_sepWPp_placed
  p2_missingKyber_ro13_sepWPp_placed
)
export LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA3PlacedBudget (
  p2_seg3d2_alloc_hooks_placed_ok
  p2_seg3d2_alloc_ext_placed_ok
  p2_seg3d2_alloc_cro_placed_ok
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

/-! ## 1. Substage P2.3 Deallocation & Tail-Allocation Event Lists and Envelope -/

/-- Exact deterministic deallocation events performed by `p2_seg3d1_sig0` / `p2_seg3d1_sigNz`
when freeing the cloned `KyberPreKeyRecord` `publicKey`, `privateKey`, and (when `sigCap ≠ 0`)
`signature` `Vec<u8>` buffers. -/
def p2KpkVecFreeEvents (pubCap privCap sigCap : Nat) : List AllocEvent :=
  if sigCap = 0 then
    rustDeallocEvents pubCap 1 ++ rustDeallocEvents privCap 1
  else
    rustDeallocEvents pubCap 1 ++ rustDeallocEvents privCap 1 ++
      rustDeallocEvents sigCap 1

theorem p2KpkVecFreeEvents_freeOnly (pubCap privCap sigCap : Nat) :
    FreeOnlyEvs (p2KpkVecFreeEvents pubCap privCap sigCap) := by
  unfold p2KpkVecFreeEvents
  split
  · exact FreeOnlyEvs.append (freeOnlyEvs_rustDeallocEvents pubCap 1)
      (freeOnlyEvs_rustDeallocEvents privCap 1)
  · exact FreeOnlyEvs.append
      (FreeOnlyEvs.append (freeOnlyEvs_rustDeallocEvents pubCap 1)
        (freeOnlyEvs_rustDeallocEvents privCap 1))
      (freeOnlyEvs_rustDeallocEvents sigCap 1)

/-- Exact deterministic allocation event list (`[AllocEvent.alloc 21]`) performed by
`p2_seg3d2_alloc` at `+0x0d04` for the 21-byte `"missing pq ciphertext"` error string. -/
def p2Sub3TailAllocEvents : List AllocEvent :=
  rustAllocEvents 21 1

/-- Exact allocator event envelope for the 21-byte error-string allocation at the start of
`stageP2_sub3_tail_kits_ext_placed` (`+0x0d04`). -/
def P2Sub3TailAllocEnv (evs : List AllocEvent) : Prop :=
  evs = p2Sub3TailAllocEvents

theorem fitsEnv_p2Sub3TailAllocEnv_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    FitsEnv M lim st P2Sub3TailAllocEnv ↔ FitsEvents M lim st p2Sub3TailAllocEvents :=
  FitsEnv.eq_iff

-- Concrete `FitsEnv` non-vacuity witness for `P2Sub3TailAllocEnv` under `coarseCostModel`.
example :
    FitsEnv coarseCostModel
      { staticCount := 64, staticBytes := 67108864, physCap := 536870912, enforced := true }
      coarseCostModel.init
      P2Sub3TailAllocEnv := by
  rw [fitsEnv_p2Sub3TailAllocEnv_iff]
  have hevs : p2Sub3TailAllocEvents = [.alloc 21] := by decide
  rw [hevs]
  dsimp only [FitsEvents, FitsEvent, AllocEvent.withinMaxAlloc, FitsStep,
    AllocCostModel.step, coarseCostModel, coarseStep, coarseStepReserve]
  decide

/-! ## 2. Budget-Threaded Precondition, Call-Framing, & `SignalProtocolError` Helpers -/

/-- Budget-threaded `kitKpkGetPollSpecE` precondition introduction at `b = 0#64`. -/
theorem p2_kpkGetPoll_pre_intro_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64}
    {kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit}
    {x : PreKeyPollCall} {st0 : kpkKit.KpkState} {st : M.σ} {s : State}
    (henv : kpkKit.envOk s.fs.files)
    (hx0 : s.readReg64 .x0 = x.fut) (hx8 : s.readReg64 .x8 = x.out)
    (hid : kpkKit.getIdOk x.id)
    (hfits : FitsEnv M lim st (kpkEnv.getPollEnv st0 x.id)) :
    kpkKit.getBoxAt x.fut x.self x.id 0#8 ∗ kpkKit.storeAt x.self st0 ∗
      memRegion x.out 88 ∗ A.pool lim st s ∗ stackAt s.sp kpkKit.getPollStack ⊢
        (kitKpkGetPollSpecE M A lim kpkKit kpkEnv).pre (x, st0, st) s := by
  dsimp only [kitKpkGetPollSpecE, withEnvPre, kitKpkGetPollSpec]
  exact Entails.pure_right henv (Entails.pure_right ⟨rfl, hx0, hx8, hid, hfits⟩ (Entails.refl _))

/-- Panic-free plain subroutine call-framing combinator preserving
`LibsignalCodeRoLoaded lsmpl`. -/
theorem p2_call_plain_nopanic_steps_frame_placed [LibsignalPlacement]
    {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State}
    {P F T : SepProp} {R_pure : Prop} {Q Qp : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : spec.pre x s = ⌜R_pure⌝ ∗ T)
    (hpure : R_pure)
    (hP : P = T ∗ F)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp :=
  p2_call_frame_cro_nopanic_placed hcrl hcall hpc hrun hsp hlr hpre hpure hP
    hpan_false hexit_false
    (fun sf hpcm hrunm hspm hsp_alm hcsm hcrl' hsteps =>
      hnext sf hsteps hpcm hrunm hspm hsp_alm hcsm hcrl')
    hoom_false

theorem p2_speAt_badCiphertext_preKey_intro_budget {M : AllocCostModel}
    (A : RustCliAllocBudget M) (sp errStrPtr : BitVec 64) (herr_nz : errStrPtr ≠ 0#64) :
    ((sp + 0x3e0#64) ↦₆₄ 0x8000000000000018#64) ∗
    ((sp + 0x3e8#64) ↦₆₄ 21#64) ∗
    ((sp + 0x3f0#64) ↦₆₄ errStrPtr) ∗
    ((sp + 0x3f8#64) ↦₆₄ 21#64) ∗
    ((sp + 0x400#64) ↦₈ 3#8) ∗
    memRegion (sp + 0x401#64) 15 ∗
    A.live errStrPtr 21 1 ∗
    memRegion errStrPtr 21 ⊢
      speAt A.repAlloc [] (sp + 0x3e0#64) (.invalidMessage .preKey .badCiphertext) :=
  p2_speAt_badCiphertext_preKey_intro A.repAlloc sp errStrPtr herr_nz

private theorem dropSpeSpec_post_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (g : DropSpeGhost) (st0 : M.σ) (s0 sf : State) :
    (dropSpeSpec M A lim).post (g, st0) s0 sf =
      ∃∗ evs : List AllocEvent,
        ⌜sf.trace = s0.trace⌝ ∗
          ⌜FreeOnlyEvs evs⌝ ∗
          memRegion g.a 48 ∗
          A.pool lim (M.stepEvents evs st0) sf ∗
          stackAt s0.sp dropSpeStack := by
  dsimp only [dropSpeSpec]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  congr 1; funext evs
  sep_ac_rfl

/-! ## 3. Budget-Threaded Placed Shared Substage P2.3 Tail (`+0x0d04 -> +0x0d5c`) -/

set_option maxHeartbeats 1200000 in
/-- Budget-Threaded Placed Shared Substage P2.3 Tail (`+0x0d04 -> +0x0d5c`) on
`stageP1ProgPlaced ext`: allocates the 21-byte `"missing pq ciphertext"` error string under
`FitsEnv M lim st P2Sub3TailAllocEnv`, builds `SignalProtocolError::InvalidMessage`, and drops it
via `hPure.dropSpe2` (`kyberCtCap ≠ 0#64`), threading
`A.pool lim (M.stepEvents (p2Sub3TailAllocEvents ++ evs_drop) st) sf` (`FreeOnlyEvs evs_drop`). -/
theorem stageP2_sub3_tail_kits_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {ext : String → Option (State → State)} {stk : Nat}
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlaced4KOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (hstk_pure : stageP2PureAndErrStack ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (st : M.σ) (s0 s : State) (ret sp coroPtr pkBuf skBuf kyberCtCap : BitVec 64)
    (Frame : SepProp) (Q : State → SepProp → Prop) {Qp : State → SepProp → Prop}
    (hfits : FitsEnv M lim st P2Sub3TailAllocEnv)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = stageP1EntryPlaced + 0xd04#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = 21#64) (hx1 : s.readReg64 .x1 = 1#64)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = kyberCtCap)
    (hOk : ∀ (sf : State) (evs_drop : List AllocEvent),
      FreeOnlyEvs evs_drop →
      Steps (stageP1ProgPlaced ext) s sf →
      sf.pc = stageP1EntryPlaced + 0xd5c#64 →
      sf.status = .Running → sf.sp = sp → sf.trace = s.trace →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x21 = s.readReg64 .x21 →
      sf.readReg64 .x22 = kyberCtCap → sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (stageP1ProgPlaced ext) ret sf
        (memRegion (sp + 0x3e0#64) 88 ∗ memRegion (sp + 0xa90#64) 65 ∗
         A.pool lim (M.stepEvents (p2Sub3TailAllocEvents ++ evs_drop) st) sf ∗
         stackAt sp stk ∗ Frame)
        Q Qp) :
    SepWPp (stageP1ProgPlaced ext) ret s
      (((sp + 0xa90#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((sp + 0xa98#64) ↦₆₄ pkBuf) ∗
       ((sp + 0xaa0#64) ↦₆₄ 0x620#64) ∗
       ((sp + 0xaa8#64) ↦₆₄ skBuf) ∗
       ((sp + 0xab0#64) ↦₆₄ 0xc60#64) ∗
       memRegion (sp + 0xab8#64) 25 ∗
       memRegion (sp + 0x3e0#64) 88 ∗
       A.pool lim st s ∗ stackAt sp stk ∗ Frame)
      Q Qp := by
  have hstk_alloc := p2_stackAt_split_of_le sp stk allocHookStack
    (Nat.le_trans p2_alloc_le_pure hstk_pure) hstk_lt
  refine weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
  have hs_align : (s.sp &&& 15#64 == 0#64) = true := by rw [hsp]; exact hsp_align
  have hfit21 : FitsEvents M lim st (rustAllocEvents 21 1) :=
    (fitsEnv_p2Sub3TailAllocEnv_iff (M := M) (lim := lim) (st := st)).mp hfits
  have hstep8 := p2_seg3d2_alloc_hooks_placed_ok (Qp := fun _ _ => False)
    ext hH st s hfit21 hCode hpc hrun hs_align hx0 hx1
  rw [hsp] at hstep8
  refine p2_bind_sepWPp_steps_frame_state hstep8 (by sep_focus)
    fun s8 hst08 hpc8 hrun8 hregs8 => ?_
  rcases hregs8 with ⟨hsp8, htr8, herr_nz, hx19_8, hx21_8, hx22_8, hx23_8, hx25_8, hx26_8, hx27_8,
    hx28_8, hx29_8, hvregs8, hCode8⟩
  refine weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
  refine weaken_frame
    (p2_sp_a90_5words_entails_memRegion (sp + 0xa90#64) 0xfffffffffffffffe#64 pkBuf 0x620#64 skBuf
      0xc60#64)
    (by rw [show (sp + 0xa90#64) + 8#64 = sp + 0xa98#64 by bv_omega,
            show (sp + 0xa90#64) + 16#64 = sp + 0xaa0#64 by bv_omega,
            show (sp + 0xa90#64) + 24#64 = sp + 0xaa8#64 by bv_omega,
            show (sp + 0xa90#64) + 32#64 = sp + 0xab0#64 by bv_omega,
            show (sp + 0xa90#64) + 40#64 = sp + 0xab8#64 by bv_omega]; sep_focus) ?_
  refine p2_missingKyber_ro0_sepWPp_placed hCode8 fun ro0 => ?_
  refine p2_missingKyber_ro8_sepWPp_placed hCode8 fun ro8 => ?_
  have hstep9 := p2_seg3d2a_ext_placed_wp (A := A) (lim := lim)
    ext (M.stepEvents p2Sub3TailAllocEvents st) s8 coroPtr (s8.readReg64 .x0) ro0 ro8
    herr_nz hpc8 hrun8 rfl (hx19_8.trans hx19)
  refine p2_bind_sepWP_qp_frame_state_placed hCode8 hstep9 (by sep_focus)
    fun s9 hst89 hpc9 hrun9 hCode9 hregs9 => ?_
  rcases hregs9 with ⟨hsp9_8, htr9_8, hx0_9, hx8_9, hx9_9, hq0_9, hx19_9, hx21_9, hx22_9, hx23_9,
    hx25_9, hx26_9, hx27_9, hx28_9, hx29_9, hvregs9_8⟩
  have hsp9 : s9.sp = sp := hsp9_8.trans hsp8
  have hsp9_align : (s9.sp &&& 15#64 == 0#64) = true := by rw [hsp9]; exact hsp_align
  refine p2_drop_sep_frame
    (Drop := ((lsρ "libsignal_cli_handshake:.rodata..Lanon.89") ↦₆₄ᵣ ro0) ∗
      ((lsρ "libsignal_cli_handshake:.rodata..Lanon.89" + 8#64) ↦₆₄ᵣ ro8))
    (by sep_focus) ?_
  refine weaken_frame (Entails.of_eq (p2_errStr_21_split16_eq (s8.readReg64 .x0)))
    (by sep_focus) ?_
  refine weaken_frame (Entails.of_eq (p2_memRegion_88_spe_split_eq sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u8_err => SepWPp.exists_elim fun u0_err =>
    SepWPp.exists_elim fun b_400_spe => SepWPp.exists_elim fun u_3f8_spe =>
    SepWPp.exists_elim fun u_3f0_spe => SepWPp.exists_elim fun u_3e8_spe =>
    SepWPp.exists_elim fun u_3e0_spe => ?_
  refine p2_missingKyber_ro13_sepWPp_placed hCode9 fun ro13 => ?_
  have hstep10 := p2_seg3d2b_ext_placed_wp (A := A) (lim := lim)
    ext (M.stepEvents p2Sub3TailAllocEvents st) s9 coroPtr (s8.readReg64 .x0)
    ro0 ro8 ro13 u0_err u8_err u_3f0_spe b_400_spe
    hpc9 hrun9 hsp9_align hx0_9 hx8_9 hx9_9 hq0_9 hx19_9
  rw [hsp9] at hstep10
  refine p2_bind_sepWP_qp_frame_state_placed hCode9 hstep10 (by sep_focus)
    fun s10 hst9_10 hpc10 hrun10 hCode10 hregs10 => ?_
  rcases hregs10 with ⟨hsp10_9, htr10_9, hx0_10, hx8_10, hx9_10, hx19_10, hx21_10, hx22_10, hx23_10,
    hx25_10, hx26_10, hx27_10, hx28_10, hx29_10, hvregs10_9⟩
  have hsp10 : s10.sp = sp := hsp10_9
  have hsp10_align : (s10.sp &&& 15#64 == 0#64) = true := by rw [hsp10]; exact hsp_align
  refine p2_drop_sep_frame
    (Drop := ((lsρ "libsignal_cli_handshake:.rodata..Lanon.89" + 13#64) ↦₆₄ᵣ ro13))
    (by sep_focus) ?_
  refine weaken_frame (p2_errStr_overlap13_entails (s8.readReg64 .x0) ro8) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u13_err => ?_
  have hx22_10' : s10.readReg64 .x22 = kyberCtCap := by
    rw [hx22_10, hx22_9, hx22_8, hx22]
  have hstep11 := p2_seg3d2c_ext_placed_wp (A := A) (lim := lim)
    ext (M.stepEvents p2Sub3TailAllocEvents st) s10 coroPtr (s8.readReg64 .x0)
    kyberCtCap ro13 u13_err u_3e0_spe u_3e8_spe u_3f8_spe
    hkyber_nz hpc10 hrun10 hsp10_align hx0_10 hx8_10 hx9_10 hx19_10 hx22_10'
  rw [hsp10] at hstep11
  refine p2_bind_sepWP_qp_frame_state_placed hCode10 hstep11 (by sep_focus)
    fun s11 hst10_11 hpc11 hrun11 hCode11 hregs11 => ?_
  rcases hregs11 with ⟨hsp11_10, htr11_10, hx0_11, hx19_11, _, hx21_11, hx22_11, hx23_11, hx25_11,
    hx26_11, hx27_11, hx28_11, hx29_11, hx30_11, hvregs11_10⟩
  simp only [arm64_norm] at hpc11
  have hsp11 : s11.sp = sp := hsp11_10
  have hsp11_al : s11.spAligned = true := by simpa only [State.spAligned, hsp11] using hsp_align
  refine weaken_frame (p2_errStr_21_rejoin_entails (s8.readReg64 .x0) ro0 ro13)
    (by sep_focus) ?_
  refine weaken_frame (p2_speAt_badCiphertext_preKey_intro_budget A sp (s8.readReg64 .x0) herr_nz)
    (by sep_focus) ?_
  have hstk_spe := p2_stackAt_split_of_le sp stk dropSpeStack
    (Nat.le_trans p2_dropSpe_le_pure hstk_pure) hstk_lt
  refine weaken_frame (Entails.of_eq hstk_spe) (by sep_focus) ?_
  sep_norm
  refine p2_call_rocl_nopanic_steps_frame_placed
    (x := ((⟨sp + 0x3e0#64, [], .invalidMessage .preKey .badCiphertext⟩ : DropSpeGhost),
      M.stepEvents p2Sub3TailAllocEvents st))
    (P_spec := speAt A.repAlloc [] (sp + 0x3e0#64) (.invalidMessage .preKey .badCiphertext) ∗
      A.pool lim (M.stepEvents p2Sub3TailAllocEvents st) s11 ∗
      stackAt sp dropSpeStack)
    hCode11 (p2_rocl_of_lscl_ro hPure.dropSpe2) hpc11 hrun11 hsp11_al hx30_11
    (by
      dsimp only [dropSpeSpec]; rw [hsp11]
      exact Entails.pure_right ⟨hx0_11, ⟨518, by decide, 0xd5c, by decide, hx30_11⟩⟩ (Entails.refl _))
    (by sep_focus)
    (hnext := fun sf hst11_f hpcf hrunf hspf_11 _ hcsf hCodef => ?_)
  rcases hcsf with ⟨hcsf_19, _, hcsf_21, hcsf_22, hcsf_23, _, hcsf_25, hcsf_26, hcsf_27, hcsf_28,
    hcsf_29, hvregsf_11⟩
  rw [dropSpeSpec_post_eq, hsp11]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun evs_drop =>
    SepWPp.pure_elim fun htrf_11 =>
    SepWPp.pure_elim fun hfree_drop => ?_
  rw [← M.stepEvents_append]
  refine weaken_frame (Entails.of_eq hstk_spe.symm) (by sep_focus) ?_
  have hmr88_rejoin :
      memRegion (sp + 0x3e0#64) 48 ∗ memRegion (sp + 0x410#64) 40 =
        memRegion (sp + 0x3e0#64) 88 :=
    (ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 48) (k := 40)
      (b' := sp + 0x410#64) rfl (by bv_omega) (by decide)).symm
  refine weaken_frame (Entails.of_eq hmr88_rejoin) (by sep_focus) ?_
  have hsteps_all :=
    hst08.trans (hst89.trans (hst9_10.trans (hst10_11.trans hst11_f)))
  have hok := hOk sf evs_drop hfree_drop hsteps_all hpcf hrunf (hspf_11.trans hsp11)
    (by rw [htrf_11, htr11_10, htr10_9, htr9_8, htr8])
    (hcsf_19.trans hx19_11)
    (by rw [hcsf_21, hx21_11, hx21_10, hx21_9, hx21_8])
    (hcsf_22.trans hx22_11)
    (by rw [hcsf_23, hx23_11, hx23_10, hx23_9, hx23_8])
    (by rw [hcsf_25, hx25_11, hx25_10, hx25_9, hx25_8])
    (by rw [hcsf_26, hx26_11, hx26_10, hx26_9, hx26_8])
    (by rw [hcsf_27, hx27_11, hx27_10, hx27_9, hx27_8])
    (by rw [hcsf_28, hx28_11, hx28_10, hx28_9, hx28_8])
    (by rw [hcsf_29, hx29_11, hx29_10, hx29_9, hx29_8])
    (by rw [hvregsf_11, hvregs11_10, hvregs10_9, hvregs9_8, hvregs8, hvregs])
    hCodef
  exact p2_sepWPp_weaken_eq hok (by sep_focus)

abbrev stageP2_sub3_tail_kits_4k_placed := @stageP2_sub3_tail_kits_ext_placed
abbrev stageP2_sub3_tail_kits_hooks_placed := @stageP2_sub3_tail_kits_ext_placed

theorem stageP2_sub3_tail_kits_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {ext : String → Option (State → State)} {stk : Nat}
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlacedOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (hstk_pure : stageP2PureAndErrStack ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (st : M.σ) (s0 s : State) (ret sp coroPtr pkBuf skBuf kyberCtCap : BitVec 64)
    (Frame : SepProp) (Q : State → SepProp → Prop) {Qp : State → SepProp → Prop}
    (hfits : FitsEnv M lim st P2Sub3TailAllocEnv)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = stageP1EntryPlaced + 0xd04#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = 21#64) (hx1 : s.readReg64 .x1 = 1#64)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = kyberCtCap)
    (hOk : ∀ (sf : State) (evs_drop : List AllocEvent),
      FreeOnlyEvs evs_drop →
      Steps (stageP1ProgPlaced ext) s sf →
      sf.pc = stageP1EntryPlaced + 0xd5c#64 →
      sf.status = .Running → sf.sp = sp → sf.trace = s.trace →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x21 = s.readReg64 .x21 →
      sf.readReg64 .x22 = kyberCtCap → sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (stageP1ProgPlaced ext) ret sf
        (memRegion (sp + 0x3e0#64) 88 ∗ memRegion (sp + 0xa90#64) 65 ∗
         A.pool lim (M.stepEvents (p2Sub3TailAllocEvents ++ evs_drop) st) sf ∗
         stackAt sp stk ∗ Frame)
        Q Qp) :
    SepWPp (stageP1ProgPlaced ext) ret s
      (((sp + 0xa90#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((sp + 0xa98#64) ↦₆₄ pkBuf) ∗ ((sp + 0xaa0#64) ↦₆₄ 0x620#64) ∗
       ((sp + 0xaa8#64) ↦₆₄ skBuf) ∗ ((sp + 0xab0#64) ↦₆₄ 0xc60#64) ∗
       memRegion (sp + 0xab8#64) 25 ∗ memRegion (sp + 0x3e0#64) 88 ∗
       A.pool lim st s ∗ stackAt sp stk ∗ Frame)
      Q Qp :=
  stageP2_sub3_tail_kits_ext_placed hH hPure.to_4K hstk_pure hstk_lt
    st s0 s ret sp coroPtr pkBuf skBuf kyberCtCap Frame Q (Qp := Qp) hfits hkyber_nz hCode
    hpc hrun hsp hsp_align hvregs hx0 hx1 hx19 hx22 hOk

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3AuxPlacedBudget
