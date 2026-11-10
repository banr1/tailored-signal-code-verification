/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegA_Prep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.HelpersPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded Relocatable Stage 2 Prefix Steps (`0x0390 → 0x0464`)

Verifies `segA_step1_coins_placed`, `segA_step2_ek_placed`, and `segA_step3_poll_placed` on
`initProgPlaced` over `RustCliAllocBudget M` and `VmPreserved`.
-/

@[expose] public section
set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxRecDepth 200000

noncomputable section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegA_PrepPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  withLsCodeRoLoaded extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
  derivePublicKeyBytesSpec derivePublicKeyBytesStackSpec
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate hiding InitPanicPostPlaced
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas hiding initPanicPostPlaced_of_false
open CryptoVerification.CliHandshake.InitiatePlaced
open LibsignalBinary.Heap
  (VmPreserved AllocEvent AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (derivePublicKeyBytesBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitPanicPostPlaced initPanicPostPlaced_of_false)

private theorem sepWPp_of_sepWP_fs_vm {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hFs : TraceFsSound prog)
    (h : SepWP prog mid s P
      (fun sm Pm =>
        VmPreserved s sm ∧
          (sm.trace = s.trace ∧
            (VmPreserved s sm → s.mem.KeepsFrozen sm.mem → sm.fs.files = s.fs.files →
              SepWPp prog ret sm Pm Q Qp oom)))) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hvmp, htr, hcont⟩ | ⟨_, hfalse⟩⟩
  · have hfiles : sm.fs.files = s.fs.files :=
      hFs.files_eq hsteps (evs := []) (by simpa using htr) NoFsEv.nil
    obtain ⟨sf, hsteps', hout⟩ := hcont hvmp hsteps.keepsFrozen hfiles R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

private theorem sepWP_done_tpidr {prog : Program} {target_pc : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = target_pc) (hrun : s.status = .Running)
    (htp : s.tpidrEl0 = s0.tpidrEl0) (hpost : Q s P) :
    SepWP prog target_pc s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ Q sm Pm) :=
  SepWP.done hpc hrun ⟨htp, hpost⟩

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm ↓, local wp_norm ↓]
  CliStage2Norm.sp_setPC_pre CliStage2Norm.sp_setMem_setPC_pre CliStage2Norm.sp_writeVReg128_pre
  CliStage2Norm.fs_setPC_pre CliStage2Norm.fs_setMem_pre CliStage2Norm.fs_setPState_pre
  CliStage2Norm.fs_writeReg64_pre CliStage2Norm.fs_writeReg32_pre CliStage2Norm.fs_writeReg_pre
  CliStage2Norm.fs_writeVReg128_pre
  CliStage2Norm.trace_writeVReg128_pre CliStage2Norm.trace_writeReg32_pre
  CliStage2Norm.trace_writeReg_pre
  CliStage2Norm.readReg64_setPC_pre CliStage2Norm.readReg64_setMem_setPC_pre
  CliStage2Norm.readReg64_writeVReg128_pre
  CliStage2Norm.readReg32_setPC_pre CliStage2Norm.readReg32_setMem_setPC_pre
  CliStage2Norm.readReg32_writeVReg128_pre
  CliStage2Norm.readReg_setPC_pre CliStage2Norm.readReg_setMem_setPC_pre
  CliStage2Norm.readReg_writeVReg128_pre
  CliStage2Norm.readVReg128_setPC_pre CliStage2Norm.readVReg128_setMem_setPC_pre
  CliStage2Norm.readVReg128_setMem_pre CliStage2Norm.readVReg128_setPState_pre
  CliStage2Norm.readVReg128_writeReg64_pre CliStage2Norm.readVReg128_writeReg32_pre
  CliStage2Norm.readVReg128_writeReg_pre
  CliStage2Norm.extractLsb_append_lo CliStage2Norm.extractLsb_append_hi
  CliStage2Norm.extractLsb_pack32_0 CliStage2Norm.extractLsb_pack32_8
  CliStage2Norm.extractLsb_pack32_16 CliStage2Norm.extractLsb_pack32_24
  CliStage2Norm.extractLsb_pack32_0_16 CliStage2Norm.extractLsb_pack32_16_16
  symtab_setPC_pre symtab_setMem_pre symtab_setPState_pre
  symtab_writeReg64_pre symtab_writeReg32_pre symtab_writeReg_pre symtab_writeVReg128_pre

set_option maxHeartbeats 1200000 in
/-- Budget-threaded Stage 2 Step A1 (`+912 → +952`): fresh `SessionRecord` header and 32-byte `coins_fill`. -/
theorem segA_step1_coins_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} [InitTraceFsSound mmpl gh W] {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp} {F : SepProp}
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl (withVmPreserved (coinsFillSpecPlacedW3 cStk))))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hctrl : InInitiatePlaced s0 s 0x0390)
    (htrace : s.trace = s0.trace)
    (hx22 : s.readReg64 (.gpr 22#5) = 0#64)
    (hx23 : s.readReg64 (.gpr 23#5) = s.sp + 128#64)
    (hx25 : s.readReg64 (.gpr 25#5) = 0#64 - 1#64)
    (hx26 : s.readReg64 (.gpr 26#5) = 8#64)
    (hx27 : s.readReg64 (.gpr 27#5) = 0#64)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ sf : State,
      InInitiatePlaced s0 sf 0x03b8 →
      sf.trace = s0.trace →
      sf.readReg64 (.gpr 21#5) = s.sp + 664#64 →
      sf.readReg64 (.gpr 23#5) = s.sp + 128#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sf
        (A.pool lim st sf ∗
          initFreshRecAt s.sp ∗
          coinsCursorAtPlaced x.coinsP x.coins 32 ∗
          ((s.sp + 5632#64) ↦ₛ (padCoins x.coins).toList.take 32) ∗
          stackAt s.sp (stk - cliInitiateFrame) ∗ F)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (A.pool lim st s ∗
        coinsCursorAtPlaced x.coinsP x.coins 0 ∗
        memRegion (s.sp + 296#64) 32 ∗
        memRegion (s.sp + 5632#64) 32 ∗
        stackAt s.sp (stk - cliInitiateFrame) ∗ F)
      Q Qp oom := by
  rw [mr_32_eq_words4 (s.sp + 296#64), mr_32_eq_words4 (s.sp + 5632#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]
  iterate 8 (apply sepWPp_exists_left; intro _)
  have hpc0 : s.pc = (blkPl_521).base + 912#64 := hctrl.pc
  have hrun0 : s.status = .Running := hctrl.run
  have hsp_al : s.spAligned = true := spAligned_of_frame hctrl.sp hctrl.spAligned
  have hsp_mask : ((s.sp &&& 15#64) == 0#64) = true := hsp_al
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521] at hpc0 ⊢
  apply sepWPp_of_sepWP_fs_vm (traceFsSound_initPlaced mmpl gh W)
    (mid := lsmpl.base 618)
  by_vm_steps (
    wp_steps
    refine SepWP.weaken_pre (P' :=
      coinsCursorAtPlaced x.coinsP x.coins 0 ∗
        A.pool lim st s ∗
        initFreshRecAt s.sp ∗
        memRegion (s.sp + 5632#64) 32 ∗
        stackAt s.sp (stk - cliInitiateFrame) ∗ F) (by
      have hm5632 := words4_entails_mr32 (s.sp + 5632#64) 0#64 0#64 0#64 0#64
      rw [initFreshRecAt_eq_fsp s.sp]
      simp only [hx22, hx26, hx27, hx25, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
        at hm5632 ⊢
      refine entails_by_focus (by sep_frame) hm5632 ?_
      sep_frame) ?_
    apply sepWP_done_tpidr (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    refine ⟨by simp only [arm64_norm], fun hvm1 hkf1 hfiles1 => ?_⟩
    let cfG : CoinsFillGhost :=
      { dst := s.sp + 5632#64, len := 32, p₀ := x.coinsP, coins := x.coins, pos := 0 }
    refine sepWPp_call_cli_lscro (traceFsSound_initPlaced mmpl gh W)
      (hCoins (coinsFillStack_le_sub hstk) (sub_frame_le_63 hstk64))
      (x := cfG)
      (F := A.pool lim st s ∗ initFreshRecAt s.sp ∗ F)
      (ret_pc := initPcPlaced 0x03b8)
      (by simp only [arm64_norm, hpc0]; try rfl)
      (by simp only [arm64_norm, *])
      (by simpa only [arm64_norm] using hsp_al)
      (hctrl.inv.of_keepsFrozen hkf1)
      (by simp only [arm64_norm, initPcPlaced, initEntryPlaced, hpc0,
        show (blkPl_521).base = lsmpl.base 521 from rfl]; try bv_omega)
      (by
        dsimp only [withVmPreserved, coinsFillSpecPlacedW3,
          LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, cfG]
        simp only [sepConj_assoc]
        refine Entails.pure_right
          ⟨by simp only [arm64_norm]; try bv_omega,
           by simp only [arm64_norm],
           hcoinsLt, by decide⟩ ?_
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (Entails.pure_right (hctrl.inv.of_keepsFrozen hkf1) (Entails.refl _)))))
        try simp only [arm64_norm, sepConj_assoc]
        sep_frame)
      (fun sf => hpanic sf _ (initPanicPostPlaced_of_false A lim InitEnv S x st0 stk _))
      (fun _ _ => rfl)
      (fun _ => by
        dsimp only [withVmPreserved, coinsFillSpecPlacedW3]
        exact Entails.pure_left False.elim)
      fun s2 hpc2 hrun2 hsp2 hcs2 hkf2 _hsym2 hf2 => ?_
    dsimp only [withVmPreserved, coinsFillSpecPlacedW3, cfG]
    simp only [arm64_norm, Nat.zero_add, List.drop_zero, sepConj_assoc] at hsp2 ⊢
    apply sepWPp_pure_left; rintro ⟨hvm2, htr2, _⟩
    have hpool2 : A.pool lim st s2 = A.pool lim st s :=
      A.pool_of_vmPreserved (hvm1.trans hvm2)
    rw [← hpool2]
    have htr2_eq : s2.trace = s0.trace := by simpa only [arm64_norm, htrace] using htr2
    have hctrl2 : InInitiatePlaced s0 s2 0x03b8 :=
      inInitiatePlaced_after_call hctrl
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [calleeSavedVRegs, arm64_norm]) hkf1 hfiles1
        hpc2 hrun2 (by simp only [arm64_norm, *]) hcs2 hkf2 (hf2 htr2)
    rcases hcs2 with ⟨_, _, hx21_2, _, hx23_2, _, _, _, _, _, _, _⟩
    simp only [arm64_norm, hx23] at hx21_2 hx23_2
    refine sepWPp_weaken_pre ?_
      (hnext s2 hctrl2 htr2_eq (by bv_omega) hx23_2)
    try simp only [hsp2, sepConj_assoc]
    sep_frame)

set_option maxHeartbeats 1600000 in
/-- Budget-threaded Stage 2 Step A2 (`+952 → +1036`): `ekASk` clamping, `derive_public_key_bytes`, and `StaticSecret::drop`. -/
theorem segA_step2_ek_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} [InitTraceFsSound mmpl gh W] {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp} {F : SepProp}
    (hDerivePub : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 200)
      (withLsCodeRoLoaded lsmpl (derivePublicKeyBytesBudgetSpec W.C.pubKey)))
    (hZeroize : subroutine_ok (initProgPlaced mmpl gh W) (lsρ lsStaticSecretDropSym)
      (withVmPreserved zeroizeSecretSpec))
    (hctrl : InInitiatePlaced s0 s 0x03b8)
    (htrace : s.trace = s0.trace)
    (hx21 : s.readReg64 (.gpr 21#5) = s.sp + 664#64)
    (hx23 : s.readReg64 (.gpr 23#5) = s.sp + 128#64)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (sf : State) (ekASk ekAPk : List (BitVec 8)),
      InInitiatePlaced s0 sf 0x040c →
      sf.trace = s0.trace →
      (let ekKP := keyPairOf W.C ⟨(padCoins x.coins).toList.take 32, by simp; decide⟩
       ekASk = ekKP.privateKey.bytes.toList ∧ ekAPk = ekKP.publicKey.bytes.toList) →
      sf.readReg64 (.gpr 20#5) = s.sp + 4064#64 →
      sf.readReg64 (.gpr 21#5) = s.sp + 664#64 →
      sf.readReg64 (.gpr 23#5) = s.sp + 128#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sf
        (A.pool lim st sf ∗
          ((s.sp + 664#64) ↦ₛ ekAPk) ∗
          ((s.sp + 696#64) ↦ₛ ekASk) ∗
          memRegion (s.sp + 4064#64) 32 ∗
          memRegion (s.sp + 5632#64) 32 ∗ F)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (A.pool lim st s ∗
        memRegion (s.sp + 664#64) 32 ∗
        memRegion (s.sp + 696#64) 32 ∗
        memRegion (s.sp + 4064#64) 32 ∗
        ((s.sp + 5632#64) ↦ₛ (padCoins x.coins).toList.take 32) ∗ F)
      Q Qp oom := by
  let rawVec : List.Vector (BitVec 8) 32 :=
    ⟨(padCoins x.coins).toList.take 32, by simp; decide⟩
  let ekKP := keyPairOf W.C rawVec
  let ekASk := ekKP.privateKey.bytes.toList
  let ekAPk := ekKP.publicKey.bytes.toList
  have hkpEq := keyPairOf_eq W.C rawVec
  obtain ⟨b0, b31, mid, hmid, hraw, hclamp⟩ := clampScalar_split rawVec
  have hekSkLen : ekASk.length = 32 := ekKP.privateKey.bytes.property
  obtain ⟨eks0, eks1, eks2, eks3, heks⟩ := exists_keyWords4_of_len32 (bs := ekASk) hekSkLen
  have hrawList : (padCoins x.coins).toList.take 32 = [b0] ++ mid ++ [b31] := hraw
  have hclampSk : ekASk = [b0 &&& 0xf8#8] ++ mid ++ [(b31 &&& 0x7f#8) ||| 0x40#8] := by
    dsimp only [ekASk]; rw [hkpEq.1]; exact hclamp
  rw [hrawList, pointsToBytes_ends (s.sp + 5632#64) b0 b31 mid hmid,
      mr_32_eq_words4 (s.sp + 4064#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]
  apply sepWPp_exists_left; intro t3
  apply sepWPp_exists_left; intro t2
  apply sepWPp_exists_left; intro t1
  apply sepWPp_exists_left; intro t0
  have hpc0 : s.pc = (blkPl_521).base + 952#64 := hctrl.pc
  have hrun0 : s.status = .Running := hctrl.run
  have hsp_al : s.spAligned = true := spAligned_of_frame hctrl.sp hctrl.spAligned
  have hsp_mask : ((s.sp &&& 15#64) == 0#64) = true := hsp_al
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521] at hpc0 ⊢
  apply sepWPp_of_sepWP_fs_vm (traceFsSound_initPlaced mmpl gh W)
    (mid := lsmpl.base 200)
  by_vm_steps
    wp_steps
    refine SepWP.weaken_pre (P' :=
      A.pool lim st s ∗
        memRegion (s.sp + 664#64) 32 ∗
        memRegion (s.sp + 696#64) 32 ∗
        ((s.sp + 4064#64) ↦₆₄ t0) ∗ ((s.sp + 4072#64) ↦₆₄ t1) ∗
        ((s.sp + 4080#64) ↦₆₄ t2) ∗ ((s.sp + 4088#64) ↦₆₄ t3) ∗
        ((s.sp + 5632#64) ↦₆₄ eks0) ∗ ((s.sp + 5640#64) ↦₆₄ eks1) ∗
        ((s.sp + 5648#64) ↦₆₄ eks2) ∗ ((s.sp + 5656#64) ↦₆₄ eks3) ∗ F) (by
      have hends :
          ((s.sp + 5632#64) ↦₈ (b0 &&& 0xf8#8)) ∗
            (((s.sp + 5633#64) ↦ₛ mid) ∗
              ((s.sp + 5663#64) ↦₈ ((b31 &&& 0x7f#8) ||| 0x40#8))) ⊢
          ((s.sp + 5632#64) ↦₆₄ eks0) ∗
            (((s.sp + 5640#64) ↦₆₄ eks1) ∗
              (((s.sp + 5648#64) ↦₆₄ eks2) ∗ ((s.sp + 5656#64) ↦₆₄ eks3))) := by
        apply Entails.of_eq
        have h1 := (pointsToBytes_ends (s.sp + 5632#64) (b0 &&& 0xf8#8)
          ((b31 &&& 0x7f#8) ||| 0x40#8) mid hmid).symm
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h1
        rw [h1, ← hclampSk,
            heks (s.sp + 5632#64) (s.sp + 5640#64) (s.sp + 5648#64) (s.sp + 5656#64)
              (by bv_omega) (by bv_omega) (by bv_omega)]
      have hclamp0 :
          BitVec.zeroExtend 8 (BitVec.zeroExtend 64 b0 &&& 1065151889656#64) = b0 &&& 0xf8#8 := by
        bv_bits
      have hclamp31 :
          BitVec.zeroExtend 8 (64#64 ||| BitVec.zeroExtend 64 b31 >>> 0 &&& 63#64) =
            (b31 &&& 0x7f#8) ||| 0x40#8 := by
        bv_bits
      rw [hclamp0, hclamp31]
      try simp only [sepConj_assoc] at hends ⊢
      refine entails_by_focus (by sep_frame) hends ?_
      sep_frame) ?_
    wp_steps
    refine SepWP.weaken_pre (P' :=
      ((s.sp + 4064#64) ↦ₛ (Ratchet.clampScalar rawVec).toList) ∗
        memRegion (s.sp + 664#64) 32 ∗
        A.pool lim st s ∗
        memRegion (s.sp + 696#64) 32 ∗
        memRegion (s.sp + 5632#64) 32 ∗ F) (by
      have hm5632 := words4_entails_mr32 (s.sp + 5632#64) eks0 eks1 eks2 eks3
      rw [← hkpEq.1]
      change _ ⊢ ((s.sp + 4064#64) ↦ₛ ekASk) ∗ _
      rw [heks (s.sp + 4064#64) (s.sp + 4072#64) (s.sp + 4080#64) (s.sp + 4088#64)
        (by bv_omega) (by bv_omega) (by bv_omega)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hm5632 ⊢
      refine entails_by_focus (by sep_frame) hm5632 ?_
      sep_frame) ?_
    apply sepWP_done_tpidr (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    refine ⟨by simp only [arm64_norm], fun hvm1 hkf1 hfiles1 => ?_⟩
    refine sepWPp_call_cli_lscro (traceFsSound_initPlaced mmpl gh W)
      hDerivePub
      (x := { secret := s.sp + 4064#64, sec := Ratchet.clampScalar rawVec, out := s.sp + 664#64 })
      (F := A.pool lim st s ∗ memRegion (s.sp + 696#64) 32 ∗ memRegion (s.sp + 5632#64) 32 ∗ F)
      (ret_pc := initPcPlaced 0x03f4)
      (by simp only [arm64_norm, hpc0]; try rfl)
      (by simp only [arm64_norm, *])
      (by simpa only [arm64_norm] using hsp_al)
      (hctrl.inv.of_keepsFrozen hkf1)
      (by simp only [arm64_norm, initPcPlaced, initEntryPlaced, hpc0,
        show (blkPl_521).base = lsmpl.base 521 from rfl]; try bv_omega)
      (by
        dsimp only [derivePublicKeyBytesBudgetSpec]
        simp only [sepConj_assoc]
        refine Entails.pure_right
          ⟨by simp only [arm64_norm], by simp only [arm64_norm, hx23]; try bv_omega⟩ ?_
        try simp only [arm64_norm, sepConj_assoc]
        sep_frame)
      (fun sf => hpanic sf _ (initPanicPostPlaced_of_false A lim InitEnv S x st0 stk _))
      (fun _ _ => rfl)
      (fun _ => by dsimp only [derivePublicKeyBytesBudgetSpec]; exact Entails.pure_left False.elim)
      fun s2 hpc2 hrun2 hsp2 hcs2 hkf2 _hsym2 hf2 => ?_
    dsimp only [derivePublicKeyBytesBudgetSpec]
    simp only [arm64_norm, sepConj_assoc] at hsp2 ⊢
    apply sepWPp_pure_left; rintro ⟨htr2, hvm2⟩
    have hpool2 : A.pool lim st s2 = A.pool lim st s :=
      A.pool_of_vmPreserved (hvm1.trans hvm2)
    rw [← hpool2]
    have htr2_eq : s2.trace = s0.trace := by simpa only [arm64_norm, htrace] using htr2
    have hctrl2 : InInitiatePlaced s0 s2 0x03f4 :=
      inInitiatePlaced_after_call hctrl
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [calleeSavedVRegs, arm64_norm]) hkf1 hfiles1
        hpc2 hrun2 (by simp only [arm64_norm, *]) hcs2 hkf2 (hf2 htr2)
    rcases hcs2 with ⟨_, hx20_2, hx21_2, _, hx23_2, _, _, _, _, _, _, _⟩
    simp only [arm64_norm, hx21, hx23] at hx20_2 hx21_2 hx23_2
    have h4064_eq : ((s.sp + 4064#64) ↦ₛ (Ratchet.clampScalar rawVec).toList) =
        ((s.sp + 4064#64) ↦₆₄ eks0) ∗ ((s.sp + 4072#64) ↦₆₄ eks1) ∗
        ((s.sp + 4080#64) ↦₆₄ eks2) ∗ ((s.sp + 4088#64) ↦₆₄ eks3) := by
      rw [← hkpEq.1]
      exact heks (s.sp + 4064#64) (s.sp + 4072#64) (s.sp + 4080#64) (s.sp + 4088#64)
        (by bv_omega) (by bv_omega) (by bv_omega)
    have h664_eq : ((s.sp + 664#64) ↦ₛ (W.C.pubKey (Ratchet.clampScalar rawVec)).toList) =
        ((s.sp + 664#64) ↦ₛ ekAPk) := by
      dsimp only [ekAPk]; rw [hkpEq.2]
    rw [h4064_eq, h664_eq, mr_32_eq_words4 (s.sp + 696#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_assoc]
    iterate 4 (apply sepWPp_exists_left; intro _)
    rw [← hsp2] at hx20_2 hx21_2 hx23_2 ⊢
    replace hpc2 : s2.pc = (blkPl_521).base + 1012#64 := hpc2
    have hsp_al2 : s2.spAligned = true := by simpa only [arm64_norm, hsp2] using hsp_al
    have hsp_mask2 : ((s2.sp &&& 15#64) == 0#64) = true := hsp_al2
    dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521] at hpc2 ⊢
    apply sepWPp_of_sepWP_fs_vm (traceFsSound_initPlaced mmpl gh W)
      (mid := lsρ lsStaticSecretDropSym)
    by_vm_steps
      wp_steps
      refine SepWP.weaken_pre (P' :=
        memRegion (s2.sp + 4064#64) 32 ∗
          A.pool lim st s2 ∗
          ((s2.sp + 664#64) ↦ₛ ekAPk) ∗
          ((s2.sp + 696#64) ↦ₛ ekASk) ∗
          memRegion (s2.sp + 5632#64) 32 ∗ F) (by
        have hm4064 := words4_entails_mr32 (s2.sp + 4064#64) eks0 eks1 eks2 eks3
        rw [heks (s2.sp + 696#64) (s2.sp + 704#64) (s2.sp + 712#64) (s2.sp + 720#64)
          (by bv_omega) (by bv_omega) (by bv_omega)]
        simp only [hx20_2, hx23_2, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
          at hm4064 ⊢
        refine entails_by_focus (by sep_frame) hm4064 ?_
        sep_frame) ?_
      apply sepWP_done_tpidr (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      refine ⟨by simp only [arm64_norm], fun hvm3 hkf3 hfiles3 => ?_⟩
      rw [hsp2] at hx20_2 hx21_2 hx23_2 ⊢
      refine sepWPp_call_cli (traceFsSound_initPlaced mmpl gh W)
        hZeroize
        (x := s.sp + 4064#64)
        (F := A.pool lim st s2 ∗ ((s.sp + 664#64) ↦ₛ ekAPk) ∗ ((s.sp + 696#64) ↦ₛ ekASk) ∗
          memRegion (s.sp + 5632#64) 32 ∗ F)
        (ret_pc := initPcPlaced 0x040c)
        (by simp only [arm64_norm, hpc2]; try rfl)
        (by simp only [arm64_norm, *])
        (by simpa only [arm64_norm, hsp2] using hsp_al)
        (by simp only [arm64_norm, initPcPlaced, initEntryPlaced, hpc2,
          show (blkPl_521).base = lsmpl.base 521 from rfl]; try bv_omega)
        (by
          dsimp only [withVmPreserved, zeroizeSecretSpec]
          simp only [sepConj_assoc]
          refine Entails.pure_right (by simp only [arm64_norm, hx20_2, hsp2]) ?_
          try simp only [sepConj_assoc]
          sep_frame)
        (fun sf => hpanic sf _ (initPanicPostPlaced_of_false A lim InitEnv S x st0 stk _))
        (fun _ _ => rfl)
        (fun _ => by dsimp only [withVmPreserved, zeroizeSecretSpec]; exact Entails.pure_left False.elim)
        fun s4 hpc4 hrun4 hsp4 hcs4 hkf4 _hsym4 hf4 => ?_
      dsimp only [withVmPreserved, zeroizeSecretSpec]
      simp only [arm64_norm, hsp2, sepConj_assoc] at hsp4 ⊢
      apply sepWPp_pure_left; rintro ⟨hvm4, htr4⟩
      have hpool4 : A.pool lim st s4 = A.pool lim st s2 :=
        A.pool_of_vmPreserved (hvm3.trans hvm4)
      rw [← hpool4]
      have htr4_eq : s4.trace = s0.trace := by simpa only [arm64_norm, htr2_eq] using htr4
      have hctrl4 : InInitiatePlaced s0 s4 0x040c :=
        inInitiatePlaced_after_call hctrl2
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
          (by simp only [arm64_norm])
          (by simp only [calleeSavedVRegs, arm64_norm]) hkf3 hfiles3
          hpc4 hrun4 (by simp only [arm64_norm, *]) hcs4 hkf4 (hf4 htr4)
      rcases hcs4 with ⟨_, hx20_4, hx21_4, _, hx23_4, _, _, _, _, _, _, _⟩
      simp only [arm64_norm, hx20_2, hx21_2, hx23_2] at hx20_4 hx21_4 hx23_4
      apply sepWPp_weaken_pre (P' :=
        A.pool lim st s4 ∗
          ((s.sp + 664#64) ↦ₛ ekAPk) ∗
          ((s.sp + 696#64) ↦ₛ ekASk) ∗
          memRegion (s.sp + 4064#64) 32 ∗
          memRegion (s.sp + 5632#64) 32 ∗ F) (by
        have hmZero : ((s.sp + 4064#64) ↦ₛ List.replicate 32 0#8) ⊢ memRegion (s.sp + 4064#64) 32 :=
          mr_of_bytes _ _ 32 (by simp)
        refine entails_by_focus (by sep_frame) hmZero ?_
        sep_frame)
      exact hnext s4 ekASk ekAPk hctrl4 htr4_eq ⟨rfl, rfl⟩ hx20_4 hx21_4 hx23_4

set_option maxHeartbeats 1600000 in
/-- Budget-threaded Stage 2 Step A3 (`+1036 → +1124`): `get_identity_key_pair` shim and poll (`evs1 ++ evs2`). -/
theorem segA_step3_poll_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {PollEnv : FsFiles → IdOwnPollGhostPlaced → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} [InitTraceFsSound mmpl gh W] {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {opkId : BitVec 32} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp} {F : SepProp}
    (hRoKeyPairSlot : ∀ {m : Memory} {P : SepProp},
      LibsignalRoLoaded lsmpl m → (m ⊨ P) →
      (m ⊨ ((lsρ cliIdentityVtSym + 24#64) ↦₆₄ᵣ lsmpl.base 602) ∗ P))
    (hIdKeyPairShim : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 602)
      (LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.idOwnShimSpecPlaced
        idKeyPairFutVtSym A lim (stk - cliInitiateFrame)))
    (hIdKeyPairPoll : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 567)
      (LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.idKeyPairPollSpecPlaced
        cliIo.rd cliWrOk A lim PollEnv (stk - cliInitiateFrame)))
    (hFitsShim : FitsEnv M lim st (BoxAllocEnv 16))
    (hFitsPoll : ∀ (evs1 : List AllocEvent) (box : BitVec 64),
      BoxAllocEnv 16 evs1 → box ≠ 0#64 →
      FitsEnv M lim (M.stepEvents evs1 st)
        (PollEnv x.F
          { fut := box
            out := s.sp + 5632#64
            self := x.stores
            own := StoresGhost.opened.identity.own }))
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hctrl : InInitiatePlaced s0 s 0x040c)
    (htrace : s.trace = s0.trace)
    (hfiles : s0.fs.files = x.F)
    (hx20 : s.readReg64 (.gpr 20#5) = s.sp + 4064#64)
    (hx21 : s.readReg64 (.gpr 21#5) = s.sp + 664#64)
    (hx23 : s.readReg64 (.gpr 23#5) = s.sp + 128#64)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (sf : State) (box : BitVec 64) (ans : Except Unit IdentityKeyPair)
        (evs1 evs2 : List AllocEvent),
      InInitiatePlaced s0 sf 0x0464 →
      sf.trace = s0.trace →
      box ≠ 0#64 →
      ans = StoresGhost.opened.identity.keyPair cliIo.rd x.F →
      BoxAllocEnv 16 evs1 →
      PollEnv x.F
        { fut := box
          out := s.sp + 5632#64
          self := x.stores
          own := StoresGhost.opened.identity.own } evs2 →
      sf.readReg64 (.gpr 20#5) = s.sp + 4064#64 →
      sf.readReg64 (.gpr 21#5) = s.sp + 664#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sf
        (storesAt A.repAlloc x.stores StoresGhost.opened ∗
          cliBundleBodyAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr opkId ∗
          FromRecordCallees.lsLogOff ∗ A.pool lim (M.stepEvents (evs1 ++ evs2) st) sf ∗
          initArgsAtPlaced s.sp x s0 ∗
          ((s.sp + 728#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
          ((s.sp + 760#64) ↦₆₄ (x.bundleA + 88#64)) ∗
          ((s.sp + 768#64) ↦₃₂ (if x.bundle.opk.isSome then 1#32 else 0#32)) ∗
          ((s.sp + 772#64) ↦₃₂ opkId) ∗
          A.live box 16 8 ∗ StoreDefs.idOwnFutBoxAt box x.stores 1#8 ∗
          ((s.sp + 1472#64) ↦₆₄ box) ∗
          ((s.sp + 1480#64) ↦₆₄ lsρ idKeyPairFutVtSym) ∗
          StoreDefs.idKeyPairOutAt A.repAlloc (s.sp + 5632#64) ans ∗
          stackAt s.sp (stk - cliInitiateFrame) ∗ F)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (storesAt A.repAlloc x.stores StoresGhost.opened ∗
        cliBundleBodyAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr opkId ∗
        FromRecordCallees.lsLogOff ∗ A.pool lim st s ∗ initArgsAtPlaced s.sp x s0 ∗
        memRegion (s.sp + 728#64) 48 ∗
        memRegion (s.sp + 1472#64) 16 ∗
        memRegion (s.sp + 5632#64) 72 ∗
        stackAt s.sp (stk - cliInitiateFrame) ∗ F)
      Q Qp oom := by
  obtain ⟨spk0, spk1, spk2, spk3, hspk⟩ :=
    exists_keyWords4_of_len32 (bs := x.bundle.spk.bytes.toList) x.bundle.spk.bytes.property
  apply sepWPp_with_rodata (fun _ hP => hRoKeyPairSlot hctrl.inv.2 hP)
  unfold cliBundleBodyAt initArgsAtPlaced
  rw [hspk (x.bundleA + 24#64) (x.bundleA + 32#64) (x.bundleA + 40#64) (x.bundleA + 48#64)
        (by bv_omega) (by bv_omega) (by bv_omega),
      mr_split (s.sp + 728#64) (s.sp + 760#64) 32 16 48 rfl (by bv_omega),
      mr_split (s.sp + 760#64) (s.sp + 768#64) 8 8 16 rfl (by bv_omega),
      mr_split (s.sp + 768#64) (s.sp + 772#64) 4 4 8 rfl (by bv_omega),
      mr_32_eq_words4 (s.sp + 728#64),
      memRegion_8_eq_exists (s.sp + 760#64),
      memRegion_4_eq_exists (s.sp + 768#64),
      memRegion_4_eq_exists (s.sp + 772#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]
  iterate 7 (apply sepWPp_exists_left; intro _)
  have hpc0 : s.pc = (blkPl_521).base + 1036#64 := hctrl.pc
  have hrun0 : s.status = .Running := hctrl.run
  have hsp_al : s.spAligned = true := spAligned_of_frame hctrl.sp hctrl.spAligned
  have hsp_mask : ((s.sp &&& 15#64) == 0#64) = true := hsp_al
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521] at hpc0 ⊢
  apply sepWPp_of_sepWP_fs_vm (traceFsSound_initPlaced mmpl gh W)
    (mid := lsmpl.base 602)
  by_vm_steps
    generalize hshim : lsmpl.base 602 = shimAddr
    wp_steps
    apply sepWP_drop_left
    refine SepWP.weaken_pre (P' :=
      A.pool lim st s ∗ stackAt s.sp (stk - cliInitiateFrame) ∗
        storesAt A.repAlloc x.stores StoresGhost.opened ∗
        cliBundleBodyAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr opkId ∗
        FromRecordCallees.lsLogOff ∗ initArgsAtPlaced s.sp x s0 ∗
        ((s.sp + 728#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((s.sp + 760#64) ↦₆₄ (x.bundleA + 88#64)) ∗
        ((s.sp + 768#64) ↦₃₂ (if x.bundle.opk.isSome then 1#32 else 0#32)) ∗
        ((s.sp + 772#64) ↦₃₂ opkId) ∗
        memRegion (s.sp + 1472#64) 16 ∗
        memRegion (s.sp + 5632#64) 72 ∗ F) (by
      unfold cliBundleBodyAt initArgsAtPlaced
      dsimp only
      rw [hspk (x.bundleA + 24#64) (x.bundleA + 32#64) (x.bundleA + 40#64) (x.bundleA + 48#64)
            (by bv_omega) (by bv_omega) (by bv_omega),
          hspk (s.sp + 728#64) (s.sp + 736#64) (s.sp + 744#64) (s.sp + 752#64)
            (by bv_omega) (by bv_omega) (by bv_omega)]
      simp only [Option.isSome, hx23, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      sep_frame) ?_
    apply sepWP_done_tpidr (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    refine ⟨by simp only [arm64_norm], fun hvm1 hkf1 hfiles1 => ?_⟩
    refine sepWPp_call_cli_lscro (traceFsSound_initPlaced mmpl gh W)
      hIdKeyPairShim
      (x := (x.stores, st))
      (F := storesAt A.repAlloc x.stores StoresGhost.opened ∗
        cliBundleBodyAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr opkId ∗
        FromRecordCallees.lsLogOff ∗ initArgsAtPlaced s.sp x s0 ∗
        ((s.sp + 728#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((s.sp + 760#64) ↦₆₄ (x.bundleA + 88#64)) ∗
        ((s.sp + 768#64) ↦₃₂ (if x.bundle.opk.isSome then 1#32 else 0#32)) ∗
        ((s.sp + 772#64) ↦₃₂ opkId) ∗
        memRegion (s.sp + 1472#64) 16 ∗
        memRegion (s.sp + 5632#64) 72 ∗ F)
      (ret_pc := initPcPlaced 0x0448)
      (by simp only [arm64_norm, hshim])
      (by simp only [arm64_norm, *])
      (by simpa only [arm64_norm] using hsp_al)
      (hctrl.inv.of_keepsFrozen hkf1)
      (by simp only [arm64_norm, initPcPlaced, initEntryPlaced, hpc0,
        show (blkPl_521).base = lsmpl.base 521 from rfl]; try bv_omega)
      (by
        dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.idOwnShimSpecPlaced]
        rw [A.pool_of_vmPreserved hvm1]
        simp only [sepConj_assoc]
        refine Entails.pure_right ⟨by simp only [arm64_norm], hFitsShim⟩ ?_
        simp only [arm64_norm, sepConj_assoc]
        sep_frame)
      (fun sf => hpanic sf _ (initPanicPostPlaced_of_false A lim InitEnv S x st0 stk _))
      (fun _ _ => rfl)
      (fun _ => by
        dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.idOwnShimSpecPlaced]
        exact Entails.pure_left False.elim)
      fun s2 hpc2 hrun2 hsp2 hcs2 hkf2 _hsym2 hf2 => ?_
    dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.idOwnShimSpecPlaced,
      idOwnFutBoxAtPlaced]
    simp only [arm64_norm, sepExists_sepConj_left, sepConj_assoc] at hsp2 ⊢
    apply sepWPp_exists_left; intro evs1
    apply sepWPp_pure_left; rintro ⟨hx1_2, hbox_ne, _, htr2, hevs1⟩
    set box := s2.readReg64 .x0
    have htr2_eq : s2.trace = s0.trace := by simpa only [arm64_norm, htrace] using htr2
    have hctrl2 : InInitiatePlaced s0 s2 0x0448 :=
      inInitiatePlaced_after_call hctrl
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        (by simp only [calleeSavedVRegs, arm64_norm]) hkf1 hfiles1
        hpc2 hrun2 (by simp only [arm64_norm, *]) hcs2 hkf2 (hf2 htr2)
    rcases hcs2 with ⟨_, hx20_2, hx21_2, _, _, _, _, _, _, _, _, _⟩
    simp only [arm64_norm, hx20, hx21] at hx20_2 hx21_2
    apply sepWPp_with_rodata (fun _ => rodata_idKeyPairFutPoll_placed hctrl2.inv)
    rw [mr_split (s.sp + 1472#64) (s.sp + 1480#64) 8 8 16 rfl (by bv_omega),
        memRegion_8_eq_exists (s.sp + 1472#64),
        memRegion_8_eq_exists (s.sp + 1480#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    iterate 2 (apply sepWPp_exists_left; intro _)
    have hpc2' : s2.pc = (blkPl_521).base + 1096#64 := hpc2
    dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521] at hpc2' ⊢
    apply sepWPp_of_sepWP_fs_vm (traceFsSound_initPlaced mmpl gh W)
      (mid := lsmpl.base 567)
    by_vm_steps
      generalize hpoll : lsmpl.base 567 = pollAddr
      wp_steps
      apply sepWP_drop_left
      refine SepWP.weaken_pre (P' :=
        StoreDefs.idOwnFutBoxAt box x.stores 0#8 ∗
          dirAt A.repAlloc x.stores StoresGhost.opened.identity.own ∗
          memRegion (s.sp + 5632#64) 72 ∗
          FromRecordCallees.lsLogOff ∗ A.pool lim (M.stepEvents evs1 st) s2 ∗
          stackAt s.sp (stk - cliInitiateFrame) ∗
          storesRestAt A.repAlloc x.stores StoresGhost.opened ∗
          cliBundleBodyAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr opkId ∗
          initArgsAtPlaced s.sp x s0 ∗
          ((s.sp + 728#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
          ((s.sp + 760#64) ↦₆₄ (x.bundleA + 88#64)) ∗
          ((s.sp + 768#64) ↦₃₂ (if x.bundle.opk.isSome then 1#32 else 0#32)) ∗
          ((s.sp + 772#64) ↦₃₂ opkId) ∗
          A.live box 16 8 ∗
          ((s.sp + 1472#64) ↦₆₄ box) ∗
          ((s.sp + 1480#64) ↦₆₄ lsρ idKeyPairFutVtSym) ∗ F) (by
        rw [storesAt_eq_own_sep]
        simp only [Option.isSome, hsp2, hx1_2, StoreDefs.idOwnFutBoxAt, sepConj_assoc]
        sep_frame) ?_
      apply sepWP_done_tpidr (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      refine ⟨by simp only [arm64_norm], fun hvm3 hkf3 hfiles3 => ?_⟩
      obtain ⟨hownLen, hownWr, hownGetLt, hownEq⟩ := idKeyPairPoll_own_facts hinitOk
      let pollG : IdOwnPollGhostPlaced :=
        { fut := box
          out := s.sp + 5632#64
          self := x.stores
          own := StoresGhost.opened.identity.own }
      refine sepWPp_call_cli_lscro (traceFsSound_initPlaced mmpl gh W)
        hIdKeyPairPoll
        (x := (pollG, M.stepEvents evs1 st))
        (F := storesRestAt A.repAlloc x.stores StoresGhost.opened ∗
          cliBundleBodyAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr opkId ∗
          initArgsAtPlaced s.sp x s0 ∗
          ((s.sp + 728#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
          ((s.sp + 760#64) ↦₆₄ (x.bundleA + 88#64)) ∗
          ((s.sp + 768#64) ↦₃₂ (if x.bundle.opk.isSome then 1#32 else 0#32)) ∗
          ((s.sp + 772#64) ↦₃₂ opkId) ∗
          A.live box 16 8 ∗
          ((s.sp + 1472#64) ↦₆₄ box) ∗
          ((s.sp + 1480#64) ↦₆₄ lsρ idKeyPairFutVtSym) ∗ F)
        (ret_pc := initPcPlaced 0x0464)
        (by simp only [arm64_norm, hpoll])
        (by simp only [arm64_norm, *])
        (by simpa only [arm64_norm, hsp2] using hsp_al)
        (hctrl2.inv.of_keepsFrozen hkf3)
        (by simp only [arm64_norm, initPcPlaced, initEntryPlaced, hpc2',
          show (blkPl_521).base = lsmpl.base 521 from rfl]; try bv_omega)
        (by
          have hf3_x := hfiles3.trans (hctrl2.files0.trans hfiles)
          dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.idKeyPairPollSpecPlaced,
            idOwnFutBoxAtPlaced, StoreDefs.idOwnFutBoxAt, pollG]
          rw [A.pool_of_vmPreserved hvm3]
          simp only [sepConj_assoc]
          refine Entails.pure_right
            ⟨by simp only [arm64_norm]; try rfl,
             by simp only [arm64_norm, hsp2]; try bv_omega,
             hownLen, hownWr, by rw [hf3_x]; exact hownGetLt,
             by rw [hf3_x]; exact hFitsPoll evs1 box hevs1 hbox_ne⟩ ?_
          dsimp only [FromRecordCallees.lsLogOff]
          try simp only [arm64_norm, hsp2, sepConj_assoc]
          sep_frame)
        (fun sf => hpanic sf _ (initPanicPostPlaced_of_false A lim InitEnv S x st0 stk _))
        (fun _ _ => rfl)
        (fun _ => by
          dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.idKeyPairPollSpecPlaced]
          exact Entails.pure_left False.elim)
        fun s4 hpc4 hrun4 hsp4 hcs4 hkf4 _hsym4 hf4 => ?_
      dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.idKeyPairPollSpecPlaced, pollG]
      rw [PollCommon.idOwnFutBoxAtPlaced_eq]
      simp only [arm64_norm, hsp2, sepExists_sepConj_left, sepConj_assoc] at hsp4 ⊢
      apply sepWPp_exists_left; intro evs2
      apply sepWPp_exists_left; intro ans
      apply sepWPp_pure_left; rintro ⟨hans, htr4, hevs2⟩
      rw [PollCommon.idKeyPairOutAtPlaced_eq]
      have htr4_eq : s4.trace = s0.trace := by simpa only [arm64_norm, htr2_eq] using htr4
      have hf2_x : s2.fs.files = x.F := hctrl2.files0.trans hfiles
      have hans_eq : ans = StoresGhost.opened.identity.keyPair cliIo.rd x.F := by
        simpa only [hf2_x, hownEq] using hans
      have hevs2_x : PollEnv x.F pollG evs2 := by
        dsimp only [pollG]
        simpa only [hf2_x] using hevs2
      have hctrl4 : InInitiatePlaced s0 s4 0x0464 :=
        inInitiatePlaced_after_call hctrl2
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
          (by simp only [arm64_norm])
          (by simp only [calleeSavedVRegs, arm64_norm]) hkf3 hfiles3
          hpc4 hrun4 (by simp only [arm64_norm, *]) hcs4 hkf4 (hf4 htr4)
      rcases hcs4 with ⟨_, hx20_4, hx21_4, _, _, _, _, _, _, _, _, _⟩
      simp only [arm64_norm, hx20_2, hx21_2] at hx20_4 hx21_4
      rw [← M.stepEvents_append evs1 evs2 st]
      refine sepWPp_weaken_pre ?_
        (hnext s4 box ans evs1 evs2 hctrl4 htr4_eq hbox_ne hans_eq hevs1 hevs2_x hx20_4 hx21_4)
      rw [storesAt_eq_own_sep]
      dsimp only [FromRecordCallees.lsLogOff]
      try simp only [Option.isSome, sepConj_assoc]
      sep_frame

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegA_PrepPlacedBudget
end
