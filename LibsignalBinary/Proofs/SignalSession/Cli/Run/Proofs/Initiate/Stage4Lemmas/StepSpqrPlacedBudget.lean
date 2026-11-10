/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.CellsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepSpqrPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Link
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Decode
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq

/-!
# Budget-Threaded Stage 4 Segment 2 (`[LibsignalPlacement]`): `spqr_chain_params` and `spqr::initial_state` (`+4576 → +4848`)

Executes `+4576 → +4848` on `initProgPlaced W` under `RustCliAllocBudget M`, transporting `A.pool`
across `spqr_chain_params` and advancing `st` by `InitStateEnv pSpqr evs` across
`spqr::initial_state`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false

noncomputable section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepSpqrPlacedBudget

open Arm64 Arm64.Obj Arm64.Process CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open ProofLib hiding pack32Pair
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.TopLevel
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  withLsCodeRoLoaded extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
open CryptoVerification.SpqrV1.Top.InitialState
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas
open CryptoVerification.CliHandshake.InitiatePlaced
open LibsignalBinary.Heap
  (VmPreserved AllocEvent AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (InitTraceFsSound traceFsSound_initPlaced)

attribute [local arm64_norm, local wp_norm] cliInitiateFrame_eq BitVec.toNat_zero
run_cmd Lean.Elab.Command.liftCoreM do
  for attrName in [`arm64_norm, `wp_norm] do
    let some ext ← Lean.Meta.Simp.getSimprocExtension? attrName
      | throwError "unknown simproc extension `{attrName}`"
    for declName in [``BitVec.reduceSub, ``BitVec.reduceNeg] do
      Lean.Meta.Simp.addSimprocAttrCore ext declName .local (post := true)

s4_clean_sp_attrs

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem sepWPp_step_cut_lscro_vm [LibsignalPlacement] {prog : Program} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Mid : State → SepProp → Prop}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P (fun sm Pm => VmPreserved s sm ∧ Mid sm Pm))
    (hcont : ∀ sm Pm, VmPreserved s sm →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      Mid sm Pm →
      SepWPp prog ret sm Pm Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases hstep.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hvm, hmid⟩ | ⟨_, hfalse⟩⟩
  · have hinv_m := hcrl.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', hout⟩ := hcont sm Pm hvm hinv_m hmid R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hfalse).elim

private theorem sepWP_done_tpidr {prog : Program} {target_pc : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = target_pc) (hrun : s.status = .Running)
    (htp : s.tpidrEl0 = s0.tpidrEl0) (hpost : Q s P) :
    SepWP prog target_pc s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ Q sm Pm) :=
  SepWP.done hpc hrun ⟨htp, hpost⟩

/-- Image-free budget-threaded inner `Spec` for `spqr::initial_state` (Block `327`) using `lsLogOff`. -/
def spqrInitialStateInnerSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (InitStateEnv : CryptoVerification.LibsignalSpqrV1.Params → List AllocEvent → Prop)
    (F : ShaCompress) :
    Spec (CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.pA ∧
      s.readReg64 .x8 = x.ret ∧
      x.akPtr ≠ 0#64 ∧
      x.p.authKey.length < 2 ^ 32 ∧
      FitsEnv M lim st (InitStateEnv x.p)⌝ ∗
      CryptoVerification.SpqrV1.Top.InitialState.paramsAt x.pA x.akPtr x.p ∗
      (x.akPtr ↦ₛ x.p.authKey) ∗
      memRegion x.ret 32 ∗
      FromRecordCallees.lsLogOff ∗
      A.pool lim st s ∗ stackAt s.sp CryptoVerification.SpqrV1.Top.InitialState.initialStateStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ InitStateEnv x.p evs⌝ ∗
        CryptoVerification.SpqrV1.Top.InitialState.paramsAt x.pA x.akPtr x.p ∗
        (x.akPtr ↦ₛ x.p.authKey) ∗
        CryptoVerification.SpqrV1.Top.InitialState.initialStateResultAt A.repAlloc x.ret
          (CryptoVerification.SpqrV1.Top.InitialState.initialStateValue F x.p) ∗
        FromRecordCallees.lsLogOff ∗
        A.pool lim (M.stepEvents evs st) sf ∗
        stackAt s0.sp CryptoVerification.SpqrV1.Top.InitialState.initialStateStack

set_option maxRecDepth 200000 in
set_option maxHeartbeats 1600000 in
theorem stage4_step_spqr_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitStateEnv : CryptoVerification.LibsignalSpqrV1.Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} [InitTraceFsSound mmpl gh W] {B : RunBudgets}
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) (_hstk64 : stk ≤ 2 ^ 63)
    {s0 : State} (hspk : stk ≤ s0.sp.toNat)
    {st : M.σ} {rk1 : RootKey} {ck1 : ChainKey} {pqrKey : BitVec 256}
    {Frame : SepProp}
    {Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hSpqrChainParams : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 74)
      (withLsCodeRoLoaded lsmpl (withVmPreserved spqrChainParamsSpec)))
    (hSpqrInit : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 327)
      (withLsCodeRoLoaded lsmpl (spqrInitialStateInnerSpec A lim InitStateEnv W.C.F)))
    (hFitsInit : FitsEnv M lim st
      (InitStateEnv (CryptoVerification.LibsignalSpqrV1.libsignalSpqrParams false .a2b pqrKey)))
    {s : State}
    (hctrl : InInitiatePlaced s0 s 4576)
    (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 2304#64)
    (hx25 : s.readReg64 (.gpr 25#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 5632#64)
    (hck1_idx : ck1.index = 0#32) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let pq : List (BitVec 8) := (pqxdhSpqrSession ⟨W.C, W.Q⟩).init .a2b pqrKey
    SepWPp (initProgPlaced mmpl gh W)
      (initPcPlaced 4848) s
      (((fsp + 0x459#64) ↦₈ 0#8) ∗
        ((fsp + 2304#64) ↦ₛ keyToBytes32 pqrKey) ∗
        memRegion (fsp + 2336#64) 36 ∗
        memRegion (fsp + 4064#64) 32 ∗
        ((fsp + 5632#64) ↦₃₂ 0#32) ∗
        ((fsp + 5636#64) ↦ₛ keyToBytes32 rk1) ∗
        ((fsp + 5668#64) ↦ₛ chainKeyBytes ck1) ∗
        memRegion (fsp + 7232#64) 32 ∗
        FromRecordCallees.lsLogOff ∗
        A.pool lim st s ∗
        stackAt fsp initialStateStack ∗
        Frame)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          InitStateEnv
            (CryptoVerification.LibsignalSpqrV1.libsignalSpqrParams false .a2b pqrKey) evs ∧
          sf.trace = s0.trace ∧
          InInitiatePlaced s0 sf 4848 ∧
          sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
          sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
          (Pf ⊢
            ((fsp + 0x459#64) ↦₈ 0#8) ∗
            ((fsp + 2304#64) ↦ₛ keyToBytes32 pqrKey) ∗
            ((fsp + 2336#64) ↦ₛ keyToBytes32 ck1.key) ∗
            ((fsp + 2368#64) ↦₃₂ 0#32) ∗
            ((fsp + 4064#64) ↦₆₄ 0#64) ∗
            RustHeap.vecU8 A.repAlloc (fsp + 4072#64) pq ∗
            memRegion (fsp + 5632#64) 72 ∗
            ((fsp + 7232#64) ↦ₛ keyToBytes32 rk1) ∗
            FromRecordCallees.lsLogOff ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt fsp initialStateStack ∗
            Frame))
      Qp oom := by
  intro fsp pq
  have hfsp_def : Hide (fsp = s0.sp - BitVec.ofNat 64 cliInitiateFrame) := ⟨rfl⟩
  have hfp_fsp : Hide (s0.sp - 0x60#64 = fsp + 7312#64) :=
    ⟨by dsimp only [fsp, cliInitiateFrame]; bv_omega⟩
  have hfsp_align : ∀ (stx : State), stx.sp = fsp → stx.spAligned = true :=
    fun stx hst => fsp_aligned_of_s0 hstk hspk hst hctrl.spAligned
  have hak_ne : fsp + 2304#64 ≠ 0#64 := fsp_add_ne_zero hstk hspk 2304 (by decide)
  have hsp0 : s.sp = fsp := hctrl.sp
  have hfp0 : s.readReg64 .fp = fsp + 7312#64 := hctrl.fp.trans hfp_fsp.val
  have hx20 : s.readReg64 (.gpr 20#5) = fsp + 0x348#64 := hx20
  have hx21 : s.readReg64 (.gpr 21#5) = fsp + 0x388#64 := hx21
  have hx22 : s.readReg64 (.gpr 22#5) = fsp + 2304#64 := hx22
  have hx25 : s.readReg64 (.gpr 25#5) = fsp + 5632#64 := hx25
  let pSpqr : CryptoVerification.LibsignalSpqrV1.Params :=
    CryptoVerification.LibsignalSpqrV1.libsignalSpqrParams false .a2b pqrKey
  have hpq_val : Hide (initialStateValue W.C.F pSpqr = pq) :=
    ⟨initialStateValue_libsignal W.C.F W.Q.K .a2b pqrKey⟩
  have hFitsInit' : FitsEnv M lim st (InitStateEnv pSpqr) := hFitsInit
  clear_value fsp pq
  have hrk_len : (keyToBytes32 rk1).length = 32 := by simp [keyToBytes32]
  have hck_len : (keyToBytes32 ck1.key).length = 32 := by simp [keyToBytes32]
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, hrk_d⟩ := exists_unpack32_8_of_length_32 hrk_len
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, hck_d⟩ := exists_unpack32_8_of_length_32 hck_len
  have hrk_5636 :
      ((fsp + 5636#64) ↦ₛ keyToBytes32 rk1) ∗
      ((fsp + 5668#64) ↦ₛ keyToBytes32 ck1.key) ∗
      ((fsp + 5700#64) ↦₃₂ 0#32) =
        ((fsp + 5636#64) ↦₃₂ r0) ∗
        ((fsp + 5640#64) ↦₆₄ pack32Pair r1 r2) ∗
        ((fsp + 5648#64) ↦₆₄ pack32Pair r3 r4) ∗
        ((fsp + 5656#64) ↦₆₄ pack32Pair r5 r6) ∗
        ((fsp + 5664#64) ↦₆₄ pack32Pair r7 c0) ∗
        ((fsp + 5672#64) ↦₆₄ pack32Pair c1 c2) ∗
        ((fsp + 5680#64) ↦₆₄ pack32Pair c3 c4) ∗
        ((fsp + 5688#64) ↦₆₄ pack32Pair c5 c6) ∗
        ((fsp + 5696#64) ↦₆₄ pack32Pair c7 0#32) := by
    rw [hrk_d (fsp + 5636#64), hck_d (fsp + 5668#64)]
    simp only [pointsTo64_pack32Pair, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have hrk_7232 :
      ((fsp + 7232#64) ↦ₛ keyToBytes32 rk1) =
        ((fsp + 7232#64) ↦₃₂ r0) ∗
        ((fsp + 7236#64) ↦₆₄ pack32Pair r1 r2) ∗
        ((fsp + 7244#64) ↦₆₄ pack32Pair r3 r4) ∗
        ((fsp + 7252#64) ↦₆₄ pack32Pair r5 r6) ∗
        ((fsp + 7260#64) ↦₃₂ r7) := by
    rw [hrk_d (fsp + 7232#64)]
    simp only [pointsTo64_pack32Pair, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have hck_2336 :
      ((fsp + 2336#64) ↦ₛ keyToBytes32 ck1.key) ∗ ((fsp + 2368#64) ↦₃₂ 0#32) =
        ((fsp + 2336#64) ↦₃₂ c0) ∗
        ((fsp + 2340#64) ↦₆₄ pack32Pair c1 c2) ∗
        ((fsp + 2348#64) ↦₆₄ pack32Pair c3 c4) ∗
        ((fsp + 2356#64) ↦₆₄ pack32Pair c5 c6) ∗
        ((fsp + 2364#64) ↦₆₄ pack32Pair c7 0#32) := by
    rw [hck_d (fsp + 2336#64)]
    simp only [pointsTo64_pack32Pair, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have hpc0 : s.pc = (blkPl_521).base + 4576#64 := hctrl.pc
  have hrun0 : s.status = .Running := hctrl.run
  have halign0 : s.spAligned = true := hfsp_align s hsp0
  have hx19_0 : s.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := hctrl.x19
  have hvr0 : calleeSavedVRegs s = calleeSavedVRegs s0 := hctrl.vregs
  apply sepWPp_steps_post (post := fun sf Pf =>
    ∃ evs : List AllocEvent,
      InitStateEnv pSpqr evs ∧
      sf.trace = s0.trace ∧
      sf.pc = initPcPlaced 4848 ∧
      sf.status = .Running ∧
      sf.sp = fsp ∧
      sf.readReg64 .fp = s0.sp - 0x60#64 ∧
      sf.readReg64 (.gpr 19#5) = s0.readReg64 .x8 ∧
      sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
      calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
      (Pf ⊢
        ((fsp + 0x459#64) ↦₈ 0#8) ∗
        ((fsp + 2304#64) ↦ₛ keyToBytes32 pqrKey) ∗
        ((fsp + 2336#64) ↦ₛ keyToBytes32 ck1.key) ∗
        ((fsp + 2368#64) ↦₃₂ 0#32) ∗
        ((fsp + 4064#64) ↦₆₄ 0#64) ∗
        RustHeap.vecU8 A.repAlloc (fsp + 4072#64) pq ∗
        memRegion (fsp + 5632#64) 72 ∗
        ((fsp + 7232#64) ↦ₛ keyToBytes32 rk1) ∗
        FromRecordCallees.lsLogOff ∗
        A.pool lim (M.stepEvents evs st) sf ∗
        stackAt fsp initialStateStack ∗
        Frame))
  · conv => arg 4; rw [pointsToBytes_chainKeyBytes_of_index_zero (fsp + 5668#64) hck1_idx]
    conv => arg 4; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    s4_rw_pre hrk_5636
    conv => arg 4; rw [memRegion36_2336_unaligned_split fsp,
        memRegion32_7232_unaligned_split fsp]
    s4_elim_exists u2336_0; s4_elim_exists u2336_1; s4_elim_exists u2336_2; s4_elim_exists u2336_3
    s4_elim_exists u2364
    s4_elim_exists u7232_0; s4_elim_exists u7232_1; s4_elim_exists u7232_2; s4_elim_exists u7232_3
    s4_elim_exists u7260
    conv => arg 4; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    let P1 : SepProp :=
      ((fsp + 0x459#64) ↦₈ 0#8) ∗
      ((fsp + 2304#64) ↦ₛ keyToBytes32 pqrKey) ∗
      ((fsp + 2336#64) ↦ₛ keyToBytes32 ck1.key) ∗
      ((fsp + 2368#64) ↦₃₂ 0#32) ∗
      memRegion (fsp + 4064#64) 32 ∗
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ d2 : BitVec 32,
       ∃∗ d3 : BitVec 32, ∃∗ w4 : BitVec 64, ∃∗ d6 : BitVec 32,
        ((fsp + 5632#64) ↦₆₄ w0) ∗ ((fsp + 5640#64) ↦₆₄ w1) ∗
        ((fsp + 5648#64) ↦₃₂ d2) ∗ ((fsp + 5652#64) ↦₃₂ d3) ∗
        ((fsp + 5656#64) ↦₆₄ w4) ∗ ((fsp + 5664#64) ↦₃₂ d6) ∗
        memRegion (fsp + 5668#64) 36) ∗
      ((fsp + 7232#64) ↦ₛ keyToBytes32 rk1) ∗
      FromRecordCallees.lsLogOff ∗
      A.pool lim st s ∗
      stackAt fsp initialStateStack ∗
      Frame
    refine sepWPp_step_cut_lscro_vm hctrl.inv (mid := lsmpl.base 74)
      (Mid := fun s1 Pm =>
        s1.pc = lsmpl.base 74 ∧
        s1.status = .Running ∧
        s1.sp = fsp ∧
        s1.readReg64 .lr = (blkPl_521).base + 4652#64 ∧
        s1.readReg32 .x0 = 0#32 ∧
        s1.readReg64 .fp = fsp + 7312#64 ∧
        s1.readReg64 (.gpr 19#5) = s0.readReg64 .x8 ∧
        s1.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
        s1.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        s1.readReg64 (.gpr 22#5) = fsp + 2304#64 ∧
        s1.readReg64 (.gpr 25#5) = fsp + 5632#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧
        s1.trace = s0.trace ∧
        Pm = P1) ?_ ?_
    · dsimp only [initProgPlaced, lsProg_521]
      by_vm_steps (
        wp_steps
        have hparams_cells := ccOk72_5632_to_spqrParams_unaligned fsp r0
          (pack32Pair r1 r2) (pack32Pair r3 r4) (pack32Pair r5 r6) (pack32Pair r7 c0)
          (pack32Pair c1 c2) (pack32Pair c3 c4) (pack32Pair c5 c6) (pack32Pair c7 0#32)
        refine SepWP.weaken_pre (P' := P1) (by
          dsimp only [P1]
          rw [← sepConj_assoc ((fsp + 2336#64) ↦ₛ keyToBytes32 ck1.key), hck_2336, hrk_7232]
          s4_fold_ent hparams_cells
          exact Entails.of_eq (by s4_ac_rfl)) ?_
        apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
          (by simp only [arm64_norm, wp_norm, *])
        refine ⟨by wp_norm_goal, by wp_norm_lhs, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by simp only [calleeSavedVRegs, arm64_norm]; exact hvr0,
          by simp only [arm64_norm]; exact htr, rfl⟩)
    rintro s1 _ hvm1 hs1_inv
      ⟨hs1_pc, hs1_run, hs1_sp, hs1_lr, hs1_x0, hs1_fp, hs1_x19, hs1_x20, hs1_x21,
       hs1_x22, hs1_x25, hs1_vr, hs1_tr, rfl⟩
    dsimp only [P1]
    clear P1
    s4_elim_exists p_w0; s4_elim_exists p_w1; s4_elim_exists p_d2
    s4_elim_exists p_d3; s4_elim_exists p_w4; s4_elim_exists p_d6
    conv => arg 4; simp only [sepConj_assoc]
    refine sepWPp_call_wpp_split_lscro hSpqrChainParams 0#32
      (T := emp)
      (F := ?_)
      hs1_inv
      hs1_pc hs1_run (hfsp_align s1 hs1_sp) rfl
      (by simp only [emp_sepConj]; rfl)
      ?_
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim) ?_
    · dsimp only [withVmPreserved, spqrChainParamsSpec]
      rw [← sepConj_emp (⌜_⌝)]
      exact Entails.pure_right hs1_x0 (Entails.refl _)
    intro s2 hs2_pc hs2_run hs2_sp hs2_cs hs2_inv
    dsimp only [withVmPreserved, spqrChainParamsSpec]
    conv => arg 4; simp only [sepConj_assoc]
    apply SepWPp.pure_elim
    intro hvm2
    apply SepWPp.pure_elim
    rintro ⟨hs2_tr_eq, hs2_w0, hs2_w1⟩
    simp only [beq_self_eq_true, ↓reduceIte] at hs2_w0
    have hpool2 : A.pool lim st s2 = A.pool lim st s :=
      A.pool_of_vmPreserved (hvm1.trans hvm2)
    conv => arg 4; rw [← hpool2]
    have hs2_sp' : s2.sp = fsp := hs2_sp.trans hs1_sp
    have hs2_align : s2.spAligned = true := hfsp_align s2 hs2_sp'
    have hs2_fp : s2.readReg64 .fp = fsp + 7312#64 :=
      (hs2_cs.gpr ⟨29, by decide⟩).trans hs1_fp
    have hs2_x19 : s2.readReg64 (.gpr 19#5) = s0.readReg64 .x8 :=
      (hs2_cs.gpr ⟨19, by decide⟩).trans hs1_x19
    have hs2_x20 : s2.readReg64 (.gpr 20#5) = fsp + 0x348#64 :=
      (hs2_cs.gpr ⟨20, by decide⟩).trans hs1_x20
    have hs2_x21 : s2.readReg64 (.gpr 21#5) = fsp + 0x388#64 :=
      (hs2_cs.gpr ⟨21, by decide⟩).trans hs1_x21
    have hs2_x22 : s2.readReg64 (.gpr 22#5) = fsp + 2304#64 :=
      (hs2_cs.gpr ⟨22, by decide⟩).trans hs1_x22
    have hs2_x25 : s2.readReg64 (.gpr 25#5) = fsp + 5632#64 :=
      (hs2_cs.gpr ⟨25, by decide⟩).trans hs1_x25
    have hs2_vr : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hs2_cs.vregs.trans hs1_vr
    have hs2_tr : s2.trace = s0.trace := hs2_tr_eq.trans hs1_tr
    have hs2_pc' : s2.pc = (blkPl_521).base + 4652#64 := hs2_pc.trans hs1_lr
    let P3 : SepProp :=
      ((fsp + 5632#64) ↦₆₄ (fsp + 2304#64)) ∗
      ((fsp + 5640#64) ↦₆₄ 32#64) ∗
      ((fsp + 5648#64) ↦₃₂ 25000#32) ∗
      ((fsp + 5652#64) ↦₃₂ 2000#32) ∗
      ((fsp + 5656#64) ↦₃₂ 0#32) ∗
      ((fsp + 5660#64) ↦₃₂ 1#32) ∗
      ((fsp + 5664#64) ↦₃₂ 1#32) ∗
      ((fsp + 2304#64) ↦ₛ keyToBytes32 pqrKey) ∗
      memRegion (fsp + 4064#64) 32 ∗
      FromRecordCallees.lsLogOff ∗
      A.pool lim st s2 ∗
      stackAt fsp initialStateStack ∗
      ((fsp + 0x459#64) ↦₈ 0#8) ∗
      ((fsp + 2336#64) ↦ₛ keyToBytes32 ck1.key) ∗
      ((fsp + 2368#64) ↦₃₂ 0#32) ∗
      memRegion (fsp + 5668#64) 36 ∗
      ((fsp + 7232#64) ↦ₛ keyToBytes32 rk1) ∗
      Frame
    refine sepWPp_step_cut_lscro_vm hs2_inv (mid := lsmpl.base 327)
      (Mid := fun s3 Pm =>
        s3.pc = lsmpl.base 327 ∧
        s3.status = .Running ∧
        s3.sp = fsp ∧
        s3.readReg64 .lr = (blkPl_521).base + 4716#64 ∧
        s3.readReg64 .x0 = fsp + 5632#64 ∧
        s3.readReg64 .x8 = fsp + 4064#64 ∧
        s3.readReg64 .fp = fsp + 7312#64 ∧
        s3.readReg64 (.gpr 19#5) = s0.readReg64 .x8 ∧
        s3.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
        s3.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        calleeSavedVRegs s3 = calleeSavedVRegs s0 ∧
        s3.trace = s0.trace ∧
        Pm = P3) ?_ ?_
    · dsimp only [initProgPlaced, lsProg_521]
      by_vm_steps (
        wp_steps
        refine SepWP.weaken_pre (P' := P3) (by
          dsimp only [P3]
          try simp only [arm64_norm, wp_norm, hs2_x22, hs2_x25, hs2_w0, hs2_w1]
          rw [pointsTo64_4294967296_eq_pair32 (fsp + 5656#64)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
          exact Entails.of_eq (by s4_ac_rfl)) ?_
        apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
          (by simp only [arm64_norm, wp_norm, *])
        refine ⟨by wp_norm_goal, by wp_norm_lhs, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal,
          by simp only [calleeSavedVRegs, arm64_norm]; exact hs2_vr,
          by simp only [arm64_norm]; exact hs2_tr, rfl⟩)
    rintro s3 _ hvm3 hs3_inv
      ⟨hs3_pc, hs3_run, hs3_sp, hs3_lr, hs3_x0, hs3_x8, hs3_fp, hs3_x19, hs3_x20,
       hs3_x21, hs3_vr, hs3_tr, rfl⟩
    dsimp only [P3]
    clear P3
    refine sepWPp_call_wpp_split_lscro hSpqrInit
      (⟨fsp + 5632#64, fsp + 4064#64, fsp + 2304#64, pSpqr⟩, st)
      (T := ((fsp + 5632#64) ↦₆₄ (fsp + 2304#64)) ∗
        ((fsp + 5640#64) ↦₆₄ 32#64) ∗
        ((fsp + 5648#64) ↦₃₂ 25000#32) ∗
        ((fsp + 5652#64) ↦₃₂ 2000#32) ∗
        ((fsp + 5656#64) ↦₃₂ 0#32) ∗
        ((fsp + 5660#64) ↦₃₂ 1#32) ∗
        ((fsp + 5664#64) ↦₃₂ 1#32) ∗
        ((fsp + 2304#64) ↦ₛ keyToBytes32 pqrKey) ∗
        memRegion (fsp + 4064#64) 32 ∗
        FromRecordCallees.lsLogOff ∗
        A.pool lim st s2 ∗
        stackAt fsp initialStateStack)
      (F := ?_)
      hs3_inv
      hs3_pc hs3_run (hfsp_align s3 hs3_sp) rfl
      (by s4_split_frame)
      ?_
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim) ?_
    · dsimp only [spqrInitialStateInnerSpec, paramsAt, pSpqr,
        CryptoVerification.LibsignalSpqrV1.libsignalSpqrParams,
        CryptoVerification.LibsignalSpqrV1.Direction.ofSpqrDirection,
        CryptoVerification.LibsignalSpqrV1.Direction.toI32,
        CryptoVerification.LibsignalSpqrV1.Version.toI32]
      have hs3_pool_eq : A.pool lim st s3 = A.pool lim st s2 :=
        A.pool_of_vmPreserved hvm3
      rw [hs3_sp, hs3_pool_eq]
      have hlen64 : BitVec.ofNat 64 (keyToBytes32 pqrKey).length = 32#64 := by
        simp [keyToBytes32]
      rw [hlen64]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      exact Entails.pure_right
        ⟨hs3_x0, hs3_x8, hak_ne, by simp [keyToBytes32], hFitsInit'⟩
        (Entails.of_eq (by s4_ac_rfl))
    intro s4 hs4_pc hs4_run hs4_sp hs4_cs hs4_inv
    dsimp only [spqrInitialStateInnerSpec, initialStateResultAt]
    conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
    s4_elim_exists evs
    conv => arg 4; rw [hpq_val.val]
    dsimp only [paramsAt, pSpqr, CryptoVerification.LibsignalSpqrV1.libsignalSpqrParams,
      CryptoVerification.LibsignalSpqrV1.Direction.ofSpqrDirection,
      CryptoVerification.LibsignalSpqrV1.Direction.toI32,
      CryptoVerification.LibsignalSpqrV1.Version.toI32]
    conv => arg 4; rw [hs3_sp]; simp only [sepConj_assoc]
    apply SepWPp.pure_elim
    rintro ⟨hs4_tr_eq, hevs⟩
    have hs4_tr : s4.trace = s0.trace := hs4_tr_eq.trans hs3_tr
    have hs4_sp' : s4.sp = fsp := hs4_sp.trans hs3_sp
    have hs4_align : s4.spAligned = true := hfsp_align s4 hs4_sp'
    have hs4_fp : s4.readReg64 .fp = fsp + 7312#64 :=
      (hs4_cs.gpr ⟨29, by decide⟩).trans hs3_fp
    have hs4_x19 : s4.readReg64 (.gpr 19#5) = s0.readReg64 .x8 :=
      (hs4_cs.gpr ⟨19, by decide⟩).trans hs3_x19
    have hs4_x20 : s4.readReg64 (.gpr 20#5) = fsp + 0x348#64 :=
      (hs4_cs.gpr ⟨20, by decide⟩).trans hs3_x20
    have hs4_x21 : s4.readReg64 (.gpr 21#5) = fsp + 0x388#64 :=
      (hs4_cs.gpr ⟨21, by decide⟩).trans hs3_x21
    have hs4_vr : calleeSavedVRegs s4 = calleeSavedVRegs s0 := hs4_cs.vregs.trans hs3_vr
    have hs4_pc' : s4.pc = (blkPl_521).base + 4716#64 := hs4_pc.trans hs3_lr
    have hcond := cond_ne_subs_0_1
    apply sepWPp_step_to_lscro hs4_inv (mid := (blkPl_521).base + 4848#64)
    dsimp only [initProgPlaced, lsProg_521]
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hinv'
    apply SepWPp.of_sepWP_ret
    apply SepWP.done (by wp_norm_goal; try rfl) (by wp_norm_lhs)
    have hmerge72 := spqrParams_5632_merge_72 fsp (fsp + 2304#64)
      (BitVec.ofNat 64 (keyToBytes32 pqrKey).length) 25000#32 2000#32 0#32 1#32 1#32
    refine ⟨evs, hevs, by wp_norm_goal, by wp_norm_goal; try rfl, by wp_norm_goal,
      by wp_norm_goal,
      by rw [hfp_fsp.val]; wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      hinv',
      by simp only [calleeSavedVRegs, arm64_norm]; exact hs4_vr, ?_⟩
    conv =>
      rhs
      rw [A.pool_of_vmPreserved (s0 := s4) ⟨⟨by try simp only [arm64_norm]; try rfl,
        by try simp only [arm64_norm]; try rfl,
        by try simp only [arm64_norm]; try rfl⟩,
        by try simp only [arm64_norm]; try rfl,
        fun _ => by try simp only [arm64_norm]; try rfl,
        LibsignalBinary.Heap.FdsHiFrame.of_fs_eq (by try simp only [arm64_norm]; try rfl)⟩]
    dsimp only [CryptoVerification.LibsignalSpqrV1.libsignalChainParams]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    s4_fold_ent hmerge72
    exact Entails.of_eq (by s4_ac_rfl)
  · intro sf Pf hsteps ⟨evs, hevs, htrf, hpcf, hrunf, hspf, hfpf, hx19f, hx20f, hx21f, hinvf, hvrf, hentf⟩
    have hfilesf : sf.fs.files = s0.fs.files :=
      (files_eq_of_steps_trace_eq (traceFsSound_initPlaced mmpl gh W) hsteps
        (htrf.trans htr.symm)).trans hctrl.files0
    exact ⟨evs, hevs, htrf,
      ⟨hpcf, hrunf, hfsp_def.val ▸ hspf, hfpf, hx19f, hfilesf, hinvf, hvrf, hctrl.spAligned⟩,
      hx20f, hx21f, hentf⟩

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepSpqrPlacedBudget
end
