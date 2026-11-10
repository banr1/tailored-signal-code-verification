/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueTrustPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegSigsPlaced
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# Budget-Threaded Stage 1 Segment 2 (`0x0154 → 0x01b4`): Signed Pre-Key XEdDSA Signature Check

Provides the non-nested `VmPreserved` basic-block stepper `sepWPp_step_entails_vm_placed` and proves
the budget-threaded signed pre-key XEdDSA signature check `stage1_spk_sig_placed_ok`
(`0x0154 → 0x01b4` and `0x0280 → 0x0350`) over `spkSigEvents`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegSigsPlacedBudgetAux

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)

noncomputable section

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.CliHandshake.InitiatePlaced (blkPl_521 lsProg_521)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives modelPrims vecU8)
open CryptoVerification.E2E.Pqxdh.Shared (bytesToBv8)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (Params)
open CryptoVerification.LibsignalTripleRatchet (PublicKeySerializeCall)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (protocolAddressAt speWord)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo storesAt)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunSem cliBundleAt)
open CryptoVerification.SignalSession.Cli.RunProofs (cliInitiateFrame cliInitiateNeed initDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (InInitiatePlaced VerifySignatureGhost coinsCursorAtPlaced initArgsAtPlaced initLocalsSize
   initPcPlaced initProgExtPlaced initProgPlaced initSaved)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
  (boxU8Buf_serialize_unpack bundleEOf_eq_some_mkBundleE bytes32_eq_exists_words4 bytesToBv8_vecU8
   cliBundleAt_unpack cliBundleBody cliBundleBody_pack cs_fp cs_vregs cs_x19 cs_x20 cs_x21 cs_x22
   false_entails initDef_eq_some_none_of_sigsOk_false memRegion_32_words mkBundleE
   pure_sepConj_intro sepWPp_exists_left sepWPp_exists_pos2 sepWPp_mono_pre sepWPp_pure_elim
   sigsOk_false_of_spk_false spAligned_of_sp_eq sp_sub_4192_sub_3216 sp_sub_96_add_96
   sp_sub_96_sub_4096 spkSerialize_eq_encodeEC verifySigAtStkSpec words4_to_bytes32)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas.Stage1Norm
  (extractLsb_append_hi extractLsb_append_lo extractLsb_pack32_0 extractLsb_pack32_0_16
   extractLsb_pack32_8 extractLsb_pack32_16 extractLsb_pack32_16_16 extractLsb_pack32_24
   fs_setMem_pre fs_setPC_pre fs_setPState_pre fs_writeReg32_pre fs_writeReg64_pre fs_writeReg_pre
   fs_writeVReg128_pre readReg32_setMem_setPC_pre readReg32_setPC_pre readReg32_writeVReg128_pre
   readReg64_setMem_setPC_pre readReg64_setPC_pre readReg64_writeVReg128_pre
   readReg_setMem_setPC_pre readReg_setPC_pre readReg_writeVReg128_pre readVReg128_setMem_pre
   readVReg128_setMem_setPC_pre readVReg128_setPC_pre readVReg128_setPState_pre
   readVReg128_writeReg32_pre readVReg128_writeReg64_pre readVReg128_writeReg_pre
   sp_setMem_setPC_pre sp_setPC_pre sp_writeVReg128_pre trace_writeReg32_pre trace_writeReg_pre
   trace_writeVReg128_pre)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAllocBudget VmPreserved
   rustAllocEvents rustCliDeallocBudgetExternSpecWithStack rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitExitPostPlaced InitPanicPostPlaced stage2MemPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
  (InitLocalCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.CalleesPlacedBudget
  (init_dealloc_placed_ok_at init_pubKeySerialize_placed_ok_at init_verifySig_vm_placed_ok_at
   pubKeySerializeAtStkSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.ModelAndLayoutPlacedBudget
  (initCallLscro)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueHelpersPlacedBudget
  (sepWP_done_tpidr sepWPp_step_to_vm_placed stage1_plain11_exit_placed_ok_of_st)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueTrustPlacedBudget
  (stage2MemPlaced_of_vmPreserved)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm]
  cliInitiateFrame initLocalsSize
  bv_sub_add_lit sp_sub_96_sub_4096 sp_sub_4192_sub_3216 sp_sub_96_add_96 BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre sp_writeVReg128_pre
  fs_setPC_pre fs_setMem_pre fs_setPState_pre
  fs_writeReg64_pre fs_writeReg32_pre fs_writeReg_pre
  fs_writeVReg128_pre
  trace_writeVReg128_pre trace_writeReg32_pre trace_writeReg_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre readReg64_writeVReg128_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg32_writeVReg128_pre
  readReg_setPC_pre readReg_setMem_setPC_pre readReg_writeVReg128_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre
  readVReg128_setMem_pre readVReg128_setPState_pre
  readVReg128_writeReg64_pre readVReg128_writeReg32_pre readVReg128_writeReg_pre
  extractLsb_append_lo extractLsb_append_hi
  extractLsb_pack32_0 extractLsb_pack32_8
  extractLsb_pack32_16 extractLsb_pack32_24
  extractLsb_pack32_0_16 extractLsb_pack32_16_16

/-- Two-goal `VmPreserved` basic-block stepper over `SepWP` keeping `by_vm_steps` isolated to `hstep`. -/
theorem sepWPp_step_entails_vm_placed [LibsignalPlacement] {prog : Program} (mid : BitVec 64)
    {ret : BitVec 64} {s : State} {P P_post : SepProp} (R_st : State → Prop)
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P
      (fun sm Pm => VmPreserved s sm ∧ R_st sm ∧ (Pm ⊢ P_post)))
    (hcont : ∀ sm : State,
      sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      VmPreserved s sm → R_st sm →
      SepWPp prog ret sm P_post Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  refine sepWPp_step_to_vm_placed mid hinv ?_
  exact SepWP.mono hstep fun sm Pm _ _ ⟨hvm, hr, hent⟩ =>
    ⟨hvm, fun sNext hEq hpc' hrun' hinv' hvm' => by
      subst hEq
      exact sepWPp_mono_pre hent (hcont sm hpc' hrun' hinv' hvm' hr)⟩

/-- Heap `AllocEvent` trace of Segment 2 (`rustAllocEvents 33 1 ++ rustDeallocEvents 33 1`). -/
abbrev spkSigEvents : List AllocEvent :=
  rustAllocEvents 33 1 ++ rustDeallocEvents 33 1

set_option maxHeartbeats 3200000 in
/-- Budget-threaded signed pre-key XEdDSA signature check (`0x0154 → 0x01b4` and `0x0280 → 0x0350`). -/
theorem stage1_spk_sig_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {stk : Nat} {s0 s1 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (h1 : x.bundle.spkSig.length = 64)
    (h2 : x.bundle.kpkSig.length = 64)
    (h3 : x.bundle.kpk.length = 1568)
    (hctrl : InInitiatePlaced s0 s1 0x0154)
    (htr : s1.trace = s0.trace)
    (hfs : s1.fs.files = x.F)
    (_htrust : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true)
    (hFitsSer : FitsEvents M lim st (rustAllocEvents 33 1))
    (hEnvBadSpk :
      (modelPrims X ⟨W.C, W.Q⟩).sigVerify
        (vecU8 (mkBundleE x.bundle h1 h2 h3).idPub)
        (SignalPqxdh.encodeEC (vecU8 (mkBundleE x.bundle h1 h2 h3).spkPub))
        (vecU8 (mkBundleE x.bundle h1 h2 h3).spkSig) = false →
      ∃ evs, InitEnv x evs ∧ M.stepEvents spkSigEvents st = M.stepEvents evs st0)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s2 : State),
      InInitiatePlaced s0 s2 0x01b4 →
      s2.trace = s0.trace →
      s2.fs.files = x.F →
      (modelPrims X ⟨W.C, W.Q⟩).sigVerify
        (vecU8 (mkBundleE x.bundle h1 h2 h3).idPub)
        (SignalPqxdh.encodeEC (vecU8 (mkBundleE x.bundle h1 h2 h3).spkPub))
        (vecU8 (mkBundleE x.bundle h1 h2 h3).spkSig) = true →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s2
        (stage2MemPlaced A lim (M.stepEvents spkSigEvents st) x stk s0 s2) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s1
      (stage2MemPlaced A lim st x stk s0 s1) Q Qp oom := by
  have hpc1 : s1.pc = (blkPl_521).base + 340#64 := hctrl.pc
  have hrun1 := hctrl.run; have hsp1 := hctrl.sp
  have hfp1 := hctrl.fp; have hx19_1 := hctrl.x19; have hfs10 := hctrl.files0
  have hvregs1 := hctrl.vregs; have hal0 := hctrl.spAligned
  have hal1 :=
    CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas.InInitiatePlaced.spAligned_cur hctrl
  let be := mkBundleE x.bundle h1 h2 h3
  unfold stage2MemPlaced; dsimp only
  generalize hfsp : s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp at hsp1 ⊢
  have hfspAl : (fsp &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp1] using hal1
  have hsplit5ba :
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) =
        memRegion (fsp + 0x5ba#64) (0x1600 - 0x5ba) ∗
          memRegion (fsp + 0x1600#64) 32 ∗
          memRegion (fsp + 0x1620#64) (initLocalsSize - 0x1620) := by
    rw [show initLocalsSize - 0x5ba = (0x1600 - 0x5ba) + (32 + (initLocalsSize - 0x1620)) by decide,
      memRegion_split (fsp + 0x5ba#64) (0x1600 - 0x5ba) _ (by decide),
      memRegion_split _ 32 _ (by decide)]
    simp only [Nat.reduceSub, BitVec.add_assoc, BitVec.reduceAdd]
  rw [hsplit5ba]
  refine sepWPp_mono_pre (P' :=
      cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        memRegion (fsp + 0x1600#64) 32 ∗
        storesAt A.repAlloc x.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
        coinsCursorAtPlaced x.coinsP x.coins 0 ∗
        tokenInitPlacedAt ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        lsLogOff ∗ A.pool lim st s1 ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) (0x1600 - 0x5ba) ∗
        memRegion (fsp + 0x1620#64) (initLocalsSize - 0x1620) ∗
        stackAt fsp (stk - cliInitiateFrame))
    (by sep_frame) ?_
  rw [cliBundleAt_unpack]
  refine sepWPp_exists_left fun opkId => ?_
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun ⟨_, _, _, hopk⟩ => ?_
  rw [memRegion_32_words (fsp + 0x1600#64)]
  refine sepWPp_exists_pos2 fun d3 => ?_; refine sepWPp_exists_pos2 fun d2 => ?_
  refine sepWPp_exists_pos2 fun d1 => ?_; refine sepWPp_exists_pos2 fun d0 => ?_
  refine sepWPp_mono_pre (P' :=
      ((x.bundleA + 24#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        (x.bundleA ↦₆₄ 64#64) ∗ ((x.bundleA + 8#64) ↦₆₄ x.spkSigPtr) ∗
        ((x.bundleA + 16#64) ↦₆₄ 64#64) ∗ (x.spkSigPtr ↦ₛ x.bundle.spkSig) ∗
        ((x.bundleA + 56#64) ↦₃₂ x.bundle.spkId) ∗ memRegion (x.bundleA + 60#64) 4 ∗
        ((x.bundleA + 64#64) ↦₆₄ 64#64) ∗ ((x.bundleA + 72#64) ↦₆₄ x.kpkSigPtr) ∗
        ((x.bundleA + 80#64) ↦₆₄ 64#64) ∗ (x.kpkSigPtr ↦ₛ x.bundle.kpkSig) ∗
        ((x.bundleA + 88#64) ↦₆₄ x.kpkPtr) ∗ ((x.bundleA + 96#64) ↦₆₄ 1568#64) ∗
        (x.kpkPtr ↦ₛ x.bundle.kpk) ∗
        ((x.bundleA + 104#64) ↦₃₂ x.bundle.kpkId) ∗ memRegion (x.bundleA + 108#64) 4 ∗
        ((x.bundleA + 112#64) ↦₃₂ (if x.bundle.opk.isSome then 1#32 else 0#32)) ∗
        ((x.bundleA + 116#64) ↦₃₂ opkId) ∗
        ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((x.bundleA + 152#64) ↦₃₂ x.bundle.regId) ∗
        ((x.bundleA + 156#64) ↦₈ (if x.bundle.opk.isSome then 1#32 else 0#32).truncate 8) ∗
        (match x.bundle.opk with
         | some (_, k) => (x.bundleA + 157#64) ↦ₛ k.bytes.toList
         | none => memRegion (x.bundleA + 157#64) 32) ∗
        ((x.bundleA + 189#64) ↦₈ x.bundle.device) ∗ memRegion (x.bundleA + 190#64) 2 ∗
        ((fsp + 0x1600#64) ↦₆₄ d0) ∗ ((fsp + 0x1608#64) ↦₆₄ d1) ∗
        ((fsp + 0x1610#64) ↦₆₄ d2) ∗ ((fsp + 0x1618#64) ↦₆₄ d3) ∗
        storesAt A.repAlloc x.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
        coinsCursorAtPlaced x.coinsP x.coins 0 ∗
        tokenInitPlacedAt ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        lsLogOff ∗ A.pool lim st s1 ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) (0x1600 - 0x5ba) ∗
        memRegion (fsp + 0x1620#64) (initLocalsSize - 0x1620) ∗
        stackAt fsp (stk - cliInitiateFrame))
    (by unfold cliBundleBody; rcases x.bundle.opk with _ | ⟨_, _⟩ <;> (dsimp only; sep_frame)) ?_
  refine sepWPp_mono_pre
    (sepConj_mono_left (bytes32_eq_exists_words4 (x.bundleA + 24#64) (by simp))) ?_
  refine sepWPp_exists_left fun w0 => ?_; refine sepWPp_exists_left fun w1 => ?_
  refine sepWPp_exists_left fun w2 => ?_; refine sepWPp_exists_left fun w3 => ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [sepConj_assoc]; refine sepWPp_pure_elim fun hbs => ?_
  let bundleRestSpk : SepProp :=
    ((x.bundleA + 24#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
      (x.bundleA ↦₆₄ 64#64) ∗ ((x.bundleA + 8#64) ↦₆₄ x.spkSigPtr) ∗
      ((x.bundleA + 16#64) ↦₆₄ 64#64) ∗
      ((x.bundleA + 56#64) ↦₃₂ x.bundle.spkId) ∗ memRegion (x.bundleA + 60#64) 4 ∗
      ((x.bundleA + 64#64) ↦₆₄ 64#64) ∗ ((x.bundleA + 72#64) ↦₆₄ x.kpkSigPtr) ∗
      ((x.bundleA + 80#64) ↦₆₄ 64#64) ∗ (x.kpkSigPtr ↦ₛ x.bundle.kpkSig) ∗
      ((x.bundleA + 88#64) ↦₆₄ x.kpkPtr) ∗ ((x.bundleA + 96#64) ↦₆₄ 1568#64) ∗
      (x.kpkPtr ↦ₛ x.bundle.kpk) ∗
      ((x.bundleA + 104#64) ↦₃₂ x.bundle.kpkId) ∗ memRegion (x.bundleA + 108#64) 4 ∗
      ((x.bundleA + 112#64) ↦₃₂ (if x.bundle.opk.isSome then 1#32 else 0#32)) ∗
      ((x.bundleA + 116#64) ↦₃₂ opkId) ∗
      ((x.bundleA + 152#64) ↦₃₂ x.bundle.regId) ∗
      ((x.bundleA + 156#64) ↦₈ (if x.bundle.opk.isSome then 1#32 else 0#32).truncate 8) ∗
      (match x.bundle.opk with
       | some (_, k) => (x.bundleA + 157#64) ↦ₛ k.bytes.toList
       | none => memRegion (x.bundleA + 157#64) 32) ∗
      ((x.bundleA + 189#64) ↦₈ x.bundle.device) ∗ memRegion (x.bundleA + 190#64) 2
  let preSerMem : SepProp :=
    ((fsp + 0x1600#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
      A.pool lim st s1 ∗
      stackAt fsp (stk - cliInitiateFrame) ∗
      (bundleRestSpk ∗
        (x.spkSigPtr ↦ₛ x.bundle.spkSig) ∗
        ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        storesAt A.repAlloc x.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
        coinsCursorAtPlaced x.coinsP x.coins 0 ∗
        tokenInitPlacedAt ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        lsLogOff ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) (0x1600 - 0x5ba) ∗
        memRegion (fsp + 0x1620#64) (initLocalsSize - 0x1620))
  unfold initArgsAtPlaced
  refine sepWPp_step_entails_vm_placed (lsmpl.base 205) (P_post := preSerMem)
    (fun sSer =>
      sSer.sp = fsp ∧
      sSer.readReg64 .x0 = fsp + 0x1600#64 ∧
      sSer.readReg64 (.gpr 22#5) = x.bundleA + 120#64 ∧
      sSer.readReg64 .lr = initPcPlaced 0x017c ∧
      sSer.readReg64 .fp = s0.sp - 0x60#64 ∧
      sSer.readReg64 (.gpr 19#5) = s0.readReg64 .x8 ∧
      calleeSavedVRegs sSer = calleeSavedVRegs s0 ∧
      sSer.trace = s0.trace ∧
      sSer.fs.files = s0.fs.files)
    hctrl.inv ?_ ?_
  · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
    by_vm_steps (
      wp_steps
      refine sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm]) ⟨?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [wp_norm, arm64_norm, hsp1]
        · simp [wp_norm, arm64_norm]; try bv_omega
        · simp [wp_norm, arm64_norm]
        · change _ = (blkPl_521).base + 380#64
          simp [wp_norm, arm64_norm]; try bv_omega
        · simp [wp_norm, arm64_norm, hfp1]
        · simp [wp_norm, arm64_norm, hx19_1]
        · simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregs1]
        · simp [wp_norm, arm64_norm, htr]
        · simp [wp_norm, arm64_norm, hfs10]
      · dsimp only [preSerMem, bundleRestSpk]
        unfold initArgsAtPlaced
        try rw [hsp1]
        have hwSrc :
            ((x.bundleA + 24#64) ↦₆₄ w0) ∗ ((x.bundleA + 32#64) ↦₆₄ w1) ∗
              ((x.bundleA + 40#64) ↦₆₄ w2) ∗ ((x.bundleA + 48#64) ↦₆₄ w3) ⊢
              ((x.bundleA + 24#64) ↦ₛ x.bundle.spk.bytes.toList) := by
          simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
            words4_to_bytes32 (x.bundleA + 24#64) hbs
        have hwDst :
            ((fsp + 0x1600#64) ↦₆₄ w0) ∗
              ((fsp + 0x1608#64) ↦₆₄ w1) ∗
              ((fsp + 0x1610#64) ↦₆₄ w2) ∗
              ((fsp + 0x1618#64) ↦₆₄ w3) ⊢
              ((fsp + 0x1600#64) ↦ₛ x.bundle.spk.bytes.toList) := by
          simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
            words4_to_bytes32 (fsp + 0x1600#64) hbs
        refine Entails.trans ?_
          (sepConj_mono hwDst
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (sepConj_mono_left hwSrc)))))
        sep_frame)
  intro sSer hpcS hrunS hinvS hvmS
    ⟨hspS, hx0S, hx22S, hlrS, hfpS, hx19S, hvregsS, htrS, hfsS⟩
  have halS : sSer.spAligned = true := spAligned_of_sp_eq hal1 (hspS.trans hsp1.symm)
  have hpoolS : A.pool lim st s1 = A.pool lim st sSer := (A.pool_of_vmPreserved hvmS).symm
  have hser := init_pubKeySerialize_placed_ok_at (mmpl := mmpl) (gh := gh) (W := W) (B := B) hh hstk hstk64
  let serCall : PublicKeySerializeCall := { self := fsp + 0x1600#64, pk := x.bundle.spk }
  dsimp only [preSerMem]
  rw [hpoolS]
  refine sepWPp_mono_pre (P' :=
      ((pubKeySerializeAtStkSpec M A lim (stk - cliInitiateFrame)).pre (serCall, st) sSer) ∗
      (bundleRestSpk ∗
        (x.spkSigPtr ↦ₛ x.bundle.spkSig) ∗
        ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        storesAt A.repAlloc x.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
        coinsCursorAtPlaced x.coinsP x.coins 0 ∗
        tokenInitPlacedAt ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        lsLogOff ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) (0x1600 - 0x5ba) ∗
        memRegion (fsp + 0x1620#64) (initLocalsSize - 0x1620))) ?_ ?_
  · unfold pubKeySerializeAtStkSpec
    dsimp only [serCall]
    rw [hspS]
    repeat rw [sepConj_assoc]
    refine pure_sepConj_intro ⟨hx0S, hFitsSer⟩ ?_
    sep_frame
  refine initCallLscro hh hpanic hser hpcS hrunS halS hinvS htrS hfsS hlrS
    (Entails.refl _) (fun _ => false_entails _) ?_
  intro sAS hpcAS hrunAS hspAS hcsAS hinvAS hfsAS
  unfold pubKeySerializeAtStkSpec; dsimp only [serCall]
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun ⟨hx1AS, htrAS⟩ => ?_
  have htrAS' : sAS.trace = s0.trace := htrAS.trans htrS
  have hfsAS' : sAS.fs.files = s0.fs.files := hfsAS htrAS'
  have hspAS' : sAS.sp = fsp := hspAS.trans hspS
  have hx22AS : sAS.readReg64 (.gpr 22#5) = x.bundleA + 120#64 := (cs_x22 hcsAS).trans hx22S
  let bufPtr := sAS.readReg64 .x0
  let st1 := M.stepEvents (rustAllocEvents 33 1) st
  have hmerge5ba :
      ((fsp + 0x1600#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        memRegion (fsp + 0x5ba#64) (0x1600 - 0x5ba) ∗
        memRegion (fsp + 0x1620#64) (initLocalsSize - 0x1620) ⊢
        memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) := by
    have hm32 : ((fsp + 0x1600#64) ↦ₛ x.bundle.spk.bytes.toList) ⊢ memRegion (fsp + 0x1600#64) 32 := by
      simpa using pointsToBytes_entails_memRegion (fsp + 0x1600#64) x.bundle.spk.bytes.toList
    rw [hsplit5ba]
    refine Entails.trans (sepConj_mono_left hm32) ?_
    sep_frame
  refine sepWPp_mono_pre (P' :=
      (⌜bufPtr ≠ 0#64⌝ ∗ A.live bufPtr 33 1 ∗ (bufPtr ↦ₛ x.bundle.spk.serialize)) ∗
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
      ((x.spkSigPtr ↦ₛ x.bundle.spkSig) ∗
        ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        bundleRestSpk ∗
        A.pool lim st1 sAS ∗ stackAt fsp (stk - cliInitiateFrame) ∗
        storesAt A.repAlloc x.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
        coinsCursorAtPlaced x.coinsP x.coins 0 ∗
        tokenInitPlacedAt ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        lsLogOff ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8))) ?_ ?_
  · rw [hspS]
    dsimp only [st1]
    refine Entails.trans ?_
      (sepConj_mono (boxU8Buf_serialize_unpack A.repAlloc bufPtr x.bundle.spk)
        (sepConj_mono_left hmerge5ba))
    sep_frame
  repeat rw [sepConj_assoc]
  refine sepWPp_pure_elim fun _hbufNZ => ?_
  let preVerMem : SepProp :=
    A.live bufPtr 33 1 ∗
      (bufPtr ↦ₛ x.bundle.spk.serialize) ∗
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
      (x.spkSigPtr ↦ₛ x.bundle.spkSig) ∗
      ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
      bundleRestSpk ∗
      A.pool lim st1 sAS ∗ stackAt fsp (stk - cliInitiateFrame) ∗
      storesAt A.repAlloc x.stores StoresGhost.opened ∗
      protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
      coinsCursorAtPlaced x.coinsP x.coins 0 ∗
      tokenInitPlacedAt ∗
      (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
      lsLogOff ∗ initSaved s0 ∗
      memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗
      memRegion (fsp + 0x128#64) 0x490 ∗
      ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8)
  change sAS.pc = (blkPl_521).base + 380#64 at hpcAS
  refine sepWPp_step_entails_vm_placed (lsmpl.base 203) (P_post := preVerMem)
    (fun sVer =>
      sVer.sp = fsp ∧
      sVer.readReg64 .x0 = x.bundleA + 120#64 ∧
      sVer.readReg64 .x1 = bufPtr ∧
      sVer.readReg64 .x2 = 33#64 ∧
      sVer.readReg64 .x3 = x.spkSigPtr ∧
      sVer.readReg64 .x4 = 64#64 ∧
      sVer.readReg64 (.gpr 20#5) = bufPtr ∧
      sVer.readReg64 (.gpr 21#5) = 33#64 ∧
      sVer.readReg64 .lr = initPcPlaced 0x019c ∧
      sVer.readReg64 .fp = s0.sp - 0x60#64 ∧
      sVer.readReg64 (.gpr 19#5) = s0.readReg64 .x8 ∧
      calleeSavedVRegs sVer = calleeSavedVRegs s0 ∧
      sVer.trace = s0.trace ∧
      sVer.fs.files = s0.fs.files)
    hinvAS ?_ ?_
  · unfold initArgsAtPlaced; dsimp only [bundleRestSpk, initProgPlaced, initProgExtPlaced, lsProg_521]
    by_vm_steps (
      wp_steps
      refine sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm]) ⟨?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [wp_norm, arm64_norm, hspAS']
        · simp [wp_norm, arm64_norm]
        · simp [bufPtr, wp_norm, arm64_norm]
        · simp [wp_norm, arm64_norm]
        · simp [wp_norm, arm64_norm]
        · simp [wp_norm, arm64_norm]
        · simp [bufPtr, wp_norm, arm64_norm]
        · simp [wp_norm, arm64_norm]
        · change _ = (blkPl_521).base + 412#64
          simp [wp_norm, arm64_norm]; try bv_omega
        · simp [wp_norm, arm64_norm, cs_fp hcsAS, hfpS]
        · simp [wp_norm, arm64_norm, cs_x19 hcsAS, hx19S]
        · simp [calleeSavedVRegs, wp_norm, arm64_norm, cs_vregs hcsAS, hvregsS]
        · simp [wp_norm, arm64_norm, htrAS']
        · simp [wp_norm, arm64_norm, hfsAS']
      · dsimp only [preVerMem, bundleRestSpk]
        unfold initArgsAtPlaced
        sep_frame)
  intro sVer hpcV hrunV hinvV hvmV
    ⟨hspV, hx0V, hx1V, hx2V, hx3V, hx4V, hx20V, hx21V, hlrV, hfpV, hx19V, hvregsV, htrV, hfsV⟩
  have halV : sVer.spAligned = true := spAligned_of_sp_eq hal1 (hspV.trans hsp1.symm)
  have hpoolV : A.pool lim st1 sAS = A.pool lim st1 sVer := (A.pool_of_vmPreserved hvmV).symm
  have hvCall := init_verifySig_vm_placed_ok_at (X := X) (B := B) hLocal hstk hstk64
  let vg : VerifySignatureGhost :=
    { pkPtr := x.bundleA + 120#64
      msgPtr := bufPtr
      sigPtr := x.spkSigPtr
      pk := vecU8 be.idPub
      m := SignalPqxdh.encodeEC (vecU8 be.spkPub)
      sig := vecU8 be.spkSig }
  have hmlen : vg.m.length = 33 := by simp [vg, SignalPqxdh.encodeEC, vecU8]
  have hpkEq : bytesToBv8 vg.pk = x.bundle.idKey.publicKey.bytes.toList :=
    bytesToBv8_vecU8 be.idPub
  have hmEq : bytesToBv8 vg.m = x.bundle.spk.serialize :=
    (spkSerialize_eq_encodeEC x.bundle h1 h2 h3).symm
  have hsigEq : bytesToBv8 vg.sig = x.bundle.spkSig :=
    bytesToBv8_vecU8 be.spkSig
  dsimp only [preVerMem]
  rw [hpoolV]
  refine sepWPp_mono_pre (P' :=
      ((withVmPreserved (verifySigAtStkSpec (modelPrims X ⟨W.C, W.Q⟩) (stk - cliInitiateFrame))).pre
        vg sVer) ∗
      (A.live bufPtr 33 1 ∗ A.pool lim st1 sVer ∗
        bundleRestSpk ∗
        storesAt A.repAlloc x.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
        coinsCursorAtPlaced x.coinsP x.coins 0 ∗
        tokenInitPlacedAt ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        lsLogOff ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba))) ?_ ?_
  · unfold withVmPreserved verifySigAtStkSpec initArgsAtPlaced
    try dsimp only [vg, bundleRestSpk, bufPtr, Reg.x0]
    try dsimp only [Reg.x0]
    rw [hspV, hpkEq, hmEq, hsigEq, hmlen]
    repeat rw [sepConj_assoc]
    refine pure_sepConj_intro
      ⟨hx0V, hx1V, hx2V, hx3V, hx4V, by simp [be, mkBundleE, vecU8], Or.inl rfl,
        by simp [be, mkBundleE, vecU8, h1]⟩ ?_
    rcases x.bundle.opk with _ | ⟨_, _⟩ <;> (dsimp only; sep_frame)
  refine initCallLscro hh hpanic hvCall hpcV hrunV halV hinvV htrV hfsV hlrV
    (Entails.refl _) (fun _ => false_entails _) ?_
  intro sAV hpcAV hrunAV hspAV hcsAV hinvAV hfsAV
  unfold withVmPreserved verifySigAtStkSpec; dsimp only
  rw [sepConj_assoc, sepConj_assoc]
  refine sepWPp_pure_elim fun hvmAV => ?_
  refine sepWPp_pure_elim fun ⟨hx0AV, htrAV⟩ => ?_
  have htrAV' : sAV.trace = s0.trace := htrAV.trans htrV
  have hfsAV' : sAV.fs.files = s0.fs.files := hfsAV htrAV'
  have hspAV' : sAV.sp = fsp := hspAV.trans hspV
  have hx20AV : sAV.readReg64 (.gpr 20#5) = bufPtr := (cs_x20 hcsAV).trans hx20V
  have hx21AV : sAV.readReg64 (.gpr 21#5) = 33#64 := (cs_x21 hcsAV).trans hx21V
  have hpoolAV : A.pool lim st1 sVer = A.pool lim st1 sAV := (A.pool_of_vmPreserved hvmAV).symm
  let frameNoPool : SepProp :=
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
      storesAt A.repAlloc x.stores StoresGhost.opened ∗
      protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
      coinsCursorAtPlaced x.coinsP x.coins 0 ∗
      tokenInitPlacedAt ∗
      (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
      lsLogOff ∗ initSaved s0 ∗
      memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗
      memRegion (fsp + 0x128#64) 0x490 ∗
      ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba)
  let preDeallocMem : SepProp :=
    A.pool lim st1 sAV ∗ A.live bufPtr 33 1 ∗ memRegion bufPtr 33 ∗
      stackAt fsp (stk - cliInitiateFrame) ∗ frameNoPool
  refine sepWPp_mono_pre (P' := preDeallocMem) ?_ ?_
  · rw [hspV, hpkEq, hmEq, hsigEq, hpoolAV]
    dsimp only [vg, preDeallocMem, frameNoPool]
    have hbufMem : (bufPtr ↦ₛ x.bundle.spk.serialize) ⊢ memRegion bufPtr 33 := by
      have hm := pointsToBytes_entails_memRegion bufPtr x.bundle.spk.serialize
      have hl : x.bundle.spk.serialize.length = 33 := by simp [PublicKey.serialize]
      rwa [hl] at hm
    have hpackB :
        ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
          (x.spkSigPtr ↦ₛ x.bundle.spkSig) ∗ bundleRestSpk ⊢
          cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr := by
      refine Entails.trans ?_
        (cliBundleBody_pack (a := x.bundleA) (b := x.bundle)
          (spkSigPtr := x.spkSigPtr) (kpkSigPtr := x.kpkSigPtr) (kpkPtr := x.kpkPtr)
          (opkId := opkId) h1 h2 h3 hopk)
      unfold cliBundleBody; dsimp only [bundleRestSpk]
      rcases x.bundle.opk with _ | ⟨_, _⟩ <;> (dsimp only; sep_frame)
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hbufMem (sepConj_mono_right (sepConj_mono_left hpackB)))))
    sep_frame
  have hdealloc := init_dealloc_placed_ok_at (mmpl := mmpl) (gh := gh) (W := W) (B := B) hh hstk hstk64
  change sAV.pc = (blkPl_521).base + 412#64 at hpcAV
  cases hv : (modelPrims X ⟨W.C, W.Q⟩).sigVerify vg.pk vg.m vg.sig
  · -- Invalid SPK signature (`hv = false`)
    rw [hv] at hx0AV
    simp only [Bool.false_eq_true, ↓reduceIte, Reg.x0] at hx0AV
    refine sepWPp_step_entails_vm_placed (lsρ lsRustDeallocSymCli) (P_post := preDeallocMem)
      (fun sD =>
        sD.sp = fsp ∧
        sD.readReg64 .x0 = bufPtr ∧
        (sD.readReg64 .x1).toNat = 33 ∧
        (sD.readReg64 .x2).toNat = 1 ∧
        sD.readReg64 .lr = initPcPlaced 0x0294 ∧
        sD.readReg64 .fp = s0.sp - 0x60#64 ∧
        sD.readReg64 (.gpr 19#5) = s0.readReg64 .x8 ∧
        calleeSavedVRegs sD = calleeSavedVRegs s0 ∧
        sD.trace = s0.trace ∧
        sD.fs.files = s0.fs.files)
      hinvAV ?_ ?_
    · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
      by_vm_steps (
        wp_steps
        refine sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
          (by simp only [arm64_norm, wp_norm]) ⟨?_, Entails.refl _⟩
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [wp_norm, arm64_norm, hspAV']
        · simp [wp_norm, arm64_norm]
        · simp [wp_norm, arm64_norm]
        · simp [wp_norm, arm64_norm]
        · change _ = (blkPl_521).base + 660#64
          simp [wp_norm, arm64_norm]; try bv_omega
        · simp [wp_norm, arm64_norm, cs_fp hcsAV, hfpV]
        · simp [wp_norm, arm64_norm, cs_x19 hcsAV, hx19V]
        · simp [calleeSavedVRegs, wp_norm, arm64_norm, cs_vregs hcsAV, hvregsV]
        · simp [wp_norm, arm64_norm, htrAV']
        · simp [wp_norm, arm64_norm, hfsAV'])
    intro sD hpcD hrunD hinvD hvmD
      ⟨hspD, hx0D, hx1D, hx2D, hlrD, hfpD, hx19D, hvregsD, htrD, hfsD⟩
    have halD : sD.spAligned = true := spAligned_of_sp_eq hal1 (hspD.trans hsp1.symm)
    have hpoolD : A.pool lim st1 sAV = A.pool lim st1 sD := (A.pool_of_vmPreserved hvmD).symm
    have hpcD' : sD.pc = lsρ lsRustDeallocSymCli := hpcD
    dsimp only [preDeallocMem]
    rw [hpoolD]
    refine initCallLscro hh hpanic hdealloc (gx := (bufPtr, 33, 1, st1))
      hpcD' hrunD halD hinvD htrD hfsD hlrD
      (by
        unfold rustCliDeallocBudgetExternSpecWithStack; dsimp only; rw [hspD]
        repeat rw [sepConj_assoc]
        exact pure_sepConj_intro
          ⟨hx0D, hx1D, hx2D, ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩,
            by rw [hlrD]; exact lsRetAddr624_blockPlacement_base_add 521 _ (by decide) (by decide)⟩
          (by sep_frame))
      (fun _ => false_entails _) ?_
    intro sAD hpcAD hrunAD hspAD hcsAD hinvAD hfsAD
    unfold rustCliDeallocBudgetExternSpecWithStack; dsimp only
    rw [sepConj_assoc]; refine sepWPp_pure_elim fun htrAD => ?_
    have htrAD' : sAD.trace = s0.trace := htrAD.trans htrD
    have hfsAD' : sAD.fs.files = s0.fs.files := hfsAD htrAD'
    have hspAD' : sAD.sp = fsp := hspAD.trans hspD
    have hstEq : M.stepEvents (rustDeallocEvents 33 1) st1 = M.stepEvents spkSigEvents st := by
      dsimp only [st1, spkSigEvents]
      exact (M.stepEvents_append (rustAllocEvents 33 1) (rustDeallocEvents 33 1) st).symm
    refine sepWPp_mono_pre
      (P' := stage2MemPlaced A lim (M.stepEvents spkSigEvents st) x stk s0 sAD)
      (by unfold stage2MemPlaced; dsimp only [frameNoPool]; rw [hspD, ← hfsp, hstEq]; sep_frame) ?_
    change sAD.pc = (blkPl_521).base + 660#64 at hpcAD
    refine sepWPp_step_entails_vm_placed ((blkPl_521).base + 848#64)
      (P_post := stage2MemPlaced A lim (M.stepEvents spkSigEvents st) x stk s0 sAD)
      (fun sErr =>
        sErr.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame ∧
        sErr.readReg64 .fp = s0.sp - 0x60#64 ∧
        sErr.readReg64 (.gpr 19#5) = s0.readReg64 .x8 ∧
        calleeSavedVRegs sErr = calleeSavedVRegs s0 ∧
        sErr.trace = s0.trace ∧
        sErr.fs.files = s0.fs.files ∧
        sErr.readReg64 (.gpr 26#5) = speWord 11)
      hinvAD ?_ ?_
    · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
      by_vm_steps (
        wp_steps
        refine sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
          (by simp only [arm64_norm, wp_norm]) ⟨?_, Entails.refl _⟩
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hfsp]; simp [wp_norm, arm64_norm, hspAD']
        · simp [wp_norm, arm64_norm, cs_fp hcsAD, hfpD]
        · simp [wp_norm, arm64_norm, cs_x19 hcsAD, hx19D]
        · simp [calleeSavedVRegs, wp_norm, arm64_norm, cs_vregs hcsAD, hvregsD]
        · simp [wp_norm, arm64_norm, htrAD']
        · simp [wp_norm, arm64_norm, hfsAD']
        · simp [wp_norm, arm64_norm]; rfl)
    intro sErr hpcErr hrunErr hinvErr hvmErr
      ⟨hspErr, hfpErr, hx19Err, hvregsErr, htrErr, hfsErr, hx26Err⟩
    rw [stage2MemPlaced_of_vmPreserved A lim (M.stepEvents spkSigEvents st) x stk s0 hvmErr]
    have hctrlErr : InInitiatePlaced s0 sErr 0x0350 :=
      ⟨hpcErr, hrunErr, hspErr, hfpErr, hx19Err, hfsErr, hinvErr, hvregsErr, hal0⟩
    have hans : S.initiate x.F x.peer.val x.me.val x.bundle x.coins = some none := by
      rw [hS]
      exact initDef_eq_some_none_of_sigsOk_false X ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val
        x.bundle be x.coins (bundleEOf_eq_some_mkBundleE x.bundle h1 h2 h3)
        (sigsOk_false_of_spk_false X ⟨W.C, W.Q⟩ be hv)
    exact stage1_plain11_exit_placed_ok_of_st (hEnvBadSpk hv) hstk hstk64 hx8 hctrlErr htrErr hans
      hpost hx26Err
  · -- Valid SPK signature (`hv = true`)
    rw [hv] at hx0AV
    simp only [↓reduceIte, Reg.x0] at hx0AV
    refine sepWPp_step_entails_vm_placed (lsρ lsRustDeallocSymCli) (P_post := preDeallocMem)
      (fun sD =>
        sD.sp = fsp ∧
        sD.readReg64 .x0 = bufPtr ∧
        (sD.readReg64 .x1).toNat = 33 ∧
        (sD.readReg64 .x2).toNat = 1 ∧
        sD.readReg64 .lr = initPcPlaced 0x01b4 ∧
        sD.readReg64 .fp = s0.sp - 0x60#64 ∧
        sD.readReg64 (.gpr 19#5) = s0.readReg64 .x8 ∧
        calleeSavedVRegs sD = calleeSavedVRegs s0 ∧
        sD.trace = s0.trace ∧
        sD.fs.files = s0.fs.files)
      hinvAV ?_ ?_
    · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
      by_vm_steps (
        wp_steps
        refine sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
          (by simp only [arm64_norm, wp_norm]) ⟨?_, Entails.refl _⟩
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [wp_norm, arm64_norm, hspAV']
        · simp [wp_norm, arm64_norm]
        · simp [wp_norm, arm64_norm]
        · simp [wp_norm, arm64_norm]
        · change _ = (blkPl_521).base + 436#64
          simp [wp_norm, arm64_norm]; try bv_omega
        · simp [wp_norm, arm64_norm, cs_fp hcsAV, hfpV]
        · simp [wp_norm, arm64_norm, cs_x19 hcsAV, hx19V]
        · simp [calleeSavedVRegs, wp_norm, arm64_norm, cs_vregs hcsAV, hvregsV]
        · simp [wp_norm, arm64_norm, htrAV']
        · simp [wp_norm, arm64_norm, hfsAV'])
    intro sD hpcD hrunD hinvD hvmD
      ⟨hspD, hx0D, hx1D, hx2D, hlrD, hfpD, hx19D, hvregsD, htrD, hfsD⟩
    have halD : sD.spAligned = true := spAligned_of_sp_eq hal1 (hspD.trans hsp1.symm)
    have hpoolD : A.pool lim st1 sAV = A.pool lim st1 sD := (A.pool_of_vmPreserved hvmD).symm
    have hpcD' : sD.pc = lsρ lsRustDeallocSymCli := hpcD
    dsimp only [preDeallocMem]
    rw [hpoolD]
    refine initCallLscro hh hpanic hdealloc (gx := (bufPtr, 33, 1, st1))
      hpcD' hrunD halD hinvD htrD hfsD hlrD
      (by
        unfold rustCliDeallocBudgetExternSpecWithStack; dsimp only; rw [hspD]
        repeat rw [sepConj_assoc]
        exact pure_sepConj_intro
          ⟨hx0D, hx1D, hx2D, ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩,
            by rw [hlrD]; exact lsRetAddr624_blockPlacement_base_add 521 _ (by decide) (by decide)⟩
          (by sep_frame))
      (fun _ => false_entails _) ?_
    intro s2 hpc2 hrun2 hsp2 hcs2 hinv2 hfs2
    unfold rustCliDeallocBudgetExternSpecWithStack; dsimp only
    rw [sepConj_assoc]; refine sepWPp_pure_elim fun htr2 => ?_
    have htr2' : s2.trace = s0.trace := htr2.trans htrD
    have hfs20 : s2.fs.files = s0.fs.files := hfs2 htr2'
    have hfs2F : s2.fs.files = x.F := by rw [hfs20, ← hfs10, hfs]
    have hctrl2 : InInitiatePlaced s0 s2 0x01b4 :=
      ⟨hpc2, hrun2, (hsp2.trans hspD).trans hfsp.symm, (cs_fp hcs2).trans hfpD,
        (cs_x19 hcs2).trans hx19D, hfs20, hinv2, (cs_vregs hcs2).trans hvregsD, hal0⟩
    have hstEq : M.stepEvents (rustDeallocEvents 33 1) st1 = M.stepEvents spkSigEvents st := by
      dsimp only [st1, spkSigEvents]
      exact (M.stepEvents_append (rustAllocEvents 33 1) (rustDeallocEvents 33 1) st).symm
    refine sepWPp_mono_pre
      (P' := stage2MemPlaced A lim (M.stepEvents spkSigEvents st) x stk s0 s2)
      (by unfold stage2MemPlaced; dsimp only [frameNoPool]; rw [hspD, ← hfsp, hstEq]; sep_frame) ?_
    exact hnext s2 hctrl2 htr2' hfs2F hv

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegSigsPlacedBudgetAux
