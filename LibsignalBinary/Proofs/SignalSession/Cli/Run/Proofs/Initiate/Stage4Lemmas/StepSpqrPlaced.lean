/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.CellsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Link
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Decode
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq

/-!
# Stage 4 Segment 2 (`[LibsignalPlacement]`): `spqr_chain_params` and `spqr::initial_state` (`+4576 → +4848`)

Relocatable `[LibsignalPlacement]` proof of Stage 4 Segment 2 (`+4576 → +4848`).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas

open Arm64 Arm64.Obj Arm64.Process ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.TopLevel
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.Top.InitialState
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.CliHandshake.InitiatePlaced
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

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

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1600000 in
theorem stage4_step_spqr_placed [LibsignalPlacement]
    {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem}
    {B : RunBudgets}
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) (_hstk64 : stk ≤ 2 ^ 63)
    {x : InitGhost} {s0 : State} (hspk : stk ≤ s0.sp.toNat)
    {rk1 : RootKey} {ck1 : ChainKey} {pqrKey : BitVec 256}
    {Frame : SepProp}
    {_Q Qp : State → SepProp → Prop}
    [InitTraceFsSound mmpl gh W]
    (hLocal : InitLocalCalleesPlaced A mmpl gh W stk)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf)
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
        A.pool ∗
        stackAt fsp initialStateStack ∗
        Frame)
      (fun sf Pf =>
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
          RustHeap.vecU8 A (fsp + 4072#64) pq ∗
          memRegion (fsp + 5632#64) 72 ∗
          ((fsp + 7232#64) ↦ₛ keyToBytes32 rk1) ∗
          FromRecordCallees.lsLogOff ∗
          A.pool ∗
          stackAt fsp initialStateStack ∗
          Frame))
      Qp (initOom s0) := by
  intro fsp pq
  have hfsp_def : Hide (fsp = s0.sp - BitVec.ofNat 64 cliInitiateFrame) := ⟨rfl⟩
  have hfp_fsp : Hide (s0.sp - 0x60#64 = fsp + 7312#64) :=
    ⟨by dsimp only [fsp, cliInitiateFrame]; bv_omega⟩
  have hfsp_align : ∀ (st : State), st.sp = fsp → st.spAligned = true :=
    fun st hst => fsp_aligned_of_s0 hstk hspk hst hctrl.spAligned
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
  clear_value fsp pq
  have hcp := hLocal.spqrChainParams
  have his := hLocal.spqrInitialState
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
      RustHeap.vecU8 A (fsp + 4072#64) pq ∗
      memRegion (fsp + 5632#64) 72 ∗
      ((fsp + 7232#64) ↦ₛ keyToBytes32 rk1) ∗
      FromRecordCallees.lsLogOff ∗
      A.pool ∗
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
    apply sepWPp_step_to_lscro hctrl.inv (mid := lsmpl.base 74)
    dsimp only [initProgPlaced, lsProg_521]
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hs1_inv
    have hparams_cells := ccOk72_5632_to_spqrParams_unaligned fsp r0
      (pack32Pair r1 r2) (pack32Pair r3 r4) (pack32Pair r5 r6) (pack32Pair r7 c0)
      (pack32Pair c1 c2) (pack32Pair c3 c4) (pack32Pair c5 c6) (pack32Pair c7 0#32)
    refine sepWPp_mono_pre
      (P' := ((fsp + 0x459#64) ↦₈ 0#8) ∗
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
        A.pool ∗
        stackAt fsp initialStateStack ∗
        Frame) ?_ ?_
    · rw [← sepConj_assoc ((fsp + 2336#64) ↦ₛ keyToBytes32 ck1.key), hck_2336, hrk_7232]
      s4_fold_ent hparams_cells
      exact Entails.of_eq (by s4_ac_rfl)
    s4_elim_exists p_w0; s4_elim_exists p_w1; s4_elim_exists p_d2
    s4_elim_exists p_d3; s4_elim_exists p_w4; s4_elim_exists p_d6
    conv => arg 4; simp only [sepConj_assoc]
    refine sepWPp_call_wpp_split_lscro hcp 0#32
      (T := emp)
      (F := ?_)
      hs1_inv
      (by wp_norm_goal) (by wp_norm_lhs) (hfsp_align _ (by wp_norm_goal)) rfl
      (by simp only [emp_sepConj]; rfl)
      ?_
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim) ?_
    · dsimp only [spqrChainParamsSpec]
      rw [← sepConj_emp (⌜_⌝)]
      refine Entails.pure_right ?_ (Entails.refl _)
      wp_norm_goal
    intro s2 hs2_pc hs2_run hs2_sp hs2_cs hs2_inv
    dsimp only [spqrChainParamsSpec]
    have hs1_sp_eq := lscro_sp_eq hs1_inv fsp (by wp_norm_goal)
    s4_pure_elim
    rintro ⟨hs2_tr_eq, hs2_w0, hs2_w1⟩
    have hs2_sp' : s2.sp = fsp := hs2_sp.trans hs1_sp_eq
    have hs2_align : s2.spAligned = true := hfsp_align s2 hs2_sp'
    have hs2_fp : s2.readReg64 .fp = fsp + 7312#64 :=
      (hs2_cs.gpr ⟨29, by decide⟩).trans (by wp_norm_goal)
    have hs2_x19 : s2.readReg64 (.gpr 19#5) = s0.readReg64 .x8 :=
      (hs2_cs.gpr ⟨19, by decide⟩).trans (by wp_norm_goal)
    have hs2_x20 : s2.readReg64 (.gpr 20#5) = fsp + 0x348#64 :=
      (hs2_cs.gpr ⟨20, by decide⟩).trans (by wp_norm_goal)
    have hs2_x21 : s2.readReg64 (.gpr 21#5) = fsp + 0x388#64 :=
      (hs2_cs.gpr ⟨21, by decide⟩).trans (by wp_norm_goal)
    have hs2_x22 : s2.readReg64 (.gpr 22#5) = fsp + 2304#64 :=
      (hs2_cs.gpr ⟨22, by decide⟩).trans (by wp_norm_goal)
    have hs2_x25 : s2.readReg64 (.gpr 25#5) = fsp + 5632#64 :=
      (hs2_cs.gpr ⟨25, by decide⟩).trans (by wp_norm_goal)
    have hs2_vr : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hs2_cs.vregs.trans hvr0
    have hs2_tr : s2.trace = s0.trace := hs2_tr_eq.trans (by wp_norm_goal)
    have hs2_pc' : s2.pc = (blkPl_521).base + 4652#64 := by
      rw [hs2_pc]; wp_norm_goal
    apply sepWPp_step_to_lscro hs2_inv (mid := lsmpl.base 327)
    dsimp only [initProgPlaced, lsProg_521]
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hs3_inv
    conv => arg 4; rw [pointsTo64_4294967296_eq_pair32 (fsp + 5656#64)]
    conv => arg 4; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine sepWPp_call_wpp_split_lscro his
      ⟨fsp + 5632#64, fsp + 4064#64, fsp + 2304#64, pSpqr⟩
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
        A.pool ∗
        stackAt fsp initialStateStack)
      (F := ?_)
      hs3_inv
      (by wp_norm_goal) (by wp_norm_lhs) (hfsp_align _ (by wp_norm_goal)) rfl
      (by s4_split_frame)
      ?_
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (fun sm _ _ =>
        hpanic sm _ (by
          dsimp only [spqrInitialStateInnerSpec, initialStateOnPanic]
          exact panic_oom_entails_initOnPanic_placed A S x stk s0 _ sm _ _ (by wp_norm_goal))) ?_
    · dsimp only [spqrInitialStateInnerSpec, paramsAt, pSpqr,
        CryptoVerification.LibsignalSpqrV1.libsignalSpqrParams,
        CryptoVerification.LibsignalSpqrV1.Direction.ofSpqrDirection,
        CryptoVerification.LibsignalSpqrV1.Direction.toI32,
        CryptoVerification.LibsignalSpqrV1.Version.toI32]
      have hs3_sp_eq := lscro_sp_eq hs3_inv fsp (by wp_norm_goal)
      rw [hs3_sp_eq]
      have hlen64 : BitVec.ofNat 64 (keyToBytes32 pqrKey).length = 32#64 := by
        simp [keyToBytes32]
      rw [hlen64]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      exact Entails.pure_right
        ⟨by wp_norm_goal, by wp_norm_goal, hak_ne, by simp [keyToBytes32]⟩
        (Entails.of_eq (by s4_ac_rfl))
    intro s4 hs4_pc hs4_run hs4_sp hs4_cs hs4_inv
    dsimp only [spqrInitialStateInnerSpec, initialStateResultAt]
    conv => arg 4; rw [hpq_val.val]
    dsimp only [paramsAt, pSpqr, CryptoVerification.LibsignalSpqrV1.libsignalSpqrParams,
      CryptoVerification.LibsignalSpqrV1.Direction.ofSpqrDirection,
      CryptoVerification.LibsignalSpqrV1.Direction.toI32,
      CryptoVerification.LibsignalSpqrV1.Version.toI32]
    have hs3_sp_eq := lscro_sp_eq hs3_inv fsp (by wp_norm_goal)
    conv => arg 4; rw [hs3_sp_eq]
    s4_pure_elim
    intro hs4_tr_eq
    have hs4_tr : s4.trace = s0.trace := hs4_tr_eq.trans (by wp_norm_goal)
    have hs4_sp' : s4.sp = fsp := hs4_sp.trans hs3_sp_eq
    have hs4_align : s4.spAligned = true := hfsp_align s4 hs4_sp'
    have hs4_fp : s4.readReg64 .fp = fsp + 7312#64 :=
      (hs4_cs.gpr ⟨29, by decide⟩).trans (by wp_norm_goal)
    have hs4_x19 : s4.readReg64 (.gpr 19#5) = s0.readReg64 .x8 :=
      (hs4_cs.gpr ⟨19, by decide⟩).trans (by wp_norm_goal)
    have hs4_x20 : s4.readReg64 (.gpr 20#5) = fsp + 0x348#64 :=
      (hs4_cs.gpr ⟨20, by decide⟩).trans (by wp_norm_goal)
    have hs4_x21 : s4.readReg64 (.gpr 21#5) = fsp + 0x388#64 :=
      (hs4_cs.gpr ⟨21, by decide⟩).trans (by wp_norm_goal)
    have hs4_vr : calleeSavedVRegs s4 = calleeSavedVRegs s0 := hs4_cs.vregs.trans hs2_vr
    have hs4_pc' : s4.pc = (blkPl_521).base + 4716#64 := by rw [hs4_pc]; wp_norm_goal
    have hcond := cond_ne_subs_0_1
    apply sepWPp_step_to_lscro hs4_inv (mid := (blkPl_521).base + 4848#64)
    dsimp only [initProgPlaced, lsProg_521]
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hinv'
    apply SepWPp.of_sepWP_ret
    apply SepWP.done (by wp_norm_goal; rfl) (by wp_norm_lhs)
    have hmerge72 := spqrParams_5632_merge_72 fsp (fsp + 2304#64)
      (BitVec.ofNat 64 (keyToBytes32 pqrKey).length) 25000#32 2000#32 0#32 1#32 1#32
    refine ⟨by wp_norm_goal, by wp_norm_goal; rfl, by wp_norm_goal,
      by wp_norm_goal,
      by rw [hfp_fsp.val]; wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      hinv',
      by simp only [calleeSavedVRegs, arm64_norm]; exact hs4_vr, ?_⟩
    dsimp only [CryptoVerification.LibsignalSpqrV1.libsignalChainParams]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    s4_fold_ent hmerge72
    exact Entails.of_eq (by s4_ac_rfl)
  · intro sf Pf hsteps ⟨htrf, hpcf, hrunf, hspf, hfpf, hx19f, hx20f, hx21f, hinvf, hvrf, hentf⟩
    have hfilesf : sf.fs.files = s0.fs.files :=
      (files_eq_of_steps_trace_eq (traceFsSound_initPlaced mmpl gh W) hsteps
        (htrf.trans htr.symm)).trans hctrl.files0
    exact ⟨htrf, ⟨hpcf, hrunf, hfsp_def.val ▸ hspf, hfpf, hx19f, hfilesf, hinvf, hvrf, hctrl.spAligned⟩,
      hx20f, hx21f, hentf⟩

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas
