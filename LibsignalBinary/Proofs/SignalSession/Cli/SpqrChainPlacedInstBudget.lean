/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.ContractsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrChainPlacedInst
public import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrowBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.NewBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.ProofPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.ProofPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixed
import LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixedGen
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceGen
import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlacedBudget
import ProofLib.OpcodeExclusion
import VerifiedLibraries.RustStd.Proofs.ExecSegSym

/-!
# Budget-Threaded Placed Chain Contracts for CLI Send & Recv

Proves code-loaded (`withLsCodeLoaded` / `withLsCodeRoLoaded` / `withLsCallInv`) placed budget
contracts for `hkdf_to_slice` (Block 379, strengthened to `withAllocVmPreserved`), epoch-slice
drops (Blocks 287, 288), `VecDeque::grow` (Block 353), `Chain::{new,from_pb,into_pb}` (Blocks 363,
364, 365), `chain_from_version_negotiation` (Block 328), and `Chain::from` (Block 323), lifted to
`spqrSendPlacedProg` and `spqrRecvPlacedProg`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrChainPlacedInstBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.HKDF (hkdfExpand)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
   blkLib_379 blkLib_402 blkLib_425 blkLib_eq_379 blkLib_eq_402 blkLib_eq_425
   blkPC_353 blkPl_353 blkPC_363 blkPl_363 blkPC_364 blkPl_364 blkPC_365 blkPl_365
   blkPC_379 blkPl_379 blkPC_402 blkPl_402 blkPC_425 blkPl_425
   libsignalMutatedBlocks libsignalSessionLib
   ls_blockPlacement_base ls_externAt?_blockProgram_eq_of_externs_eq
   ls_subroutine_ok_of_block lsmpl lsρ prog_eq_blockProgram
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.Cli.SpqrV1.Top.Send (spqrSendPlacedProg)
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook returnToLinkRegister)
open CryptoVerification.LibsignalHmac (compress256Hook readShaState)
open CryptoVerification.LibsignalSession.CryptoHmacSha256 (disjointRegions_of_ro_rw length_hmacWith)
open CryptoVerification.LibsignalSpqrV1 (hkdfExtractBytes spqrHkdfWith)
open CryptoVerification.LibsignalTripleRatchet
  (CalleeSaved CallingConventionPreserved_of_calleeSaved Frame HkdfPlacedHooks
   RunsTo TraceEq extHookStack extract_withLsCodeRoLoaded
   hookMemcpy_eq_memcpyHook hookMemset_eq_memsetHook keys_ls_subroutine_ok_of_block_cro
   lsCompress256Sym lsMemcpySym lsMemsetSym ro_outside_rw_shared_lb withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Expand
  (KeepsFrozenNoAnon t1_length t2_length t3_length)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced lsRustAllocSymCli lsRustDeallocSymCli
   lsRustNoAllocShimSymCli lsRustReallocSymCli)
open CryptoVerification.SignalSession.Cli.MainHops
  (allocHookStack_le_extHookStack extHookStack_le)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_alloc
   cliGhostExterns_other cliGhostExterns_shim hookSat_of_eq withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots
  (cliGhostExterns_panic_handle_error cliGhostExterns_sat_of_cliExternsPlaced
   lsRngFillSym memmove_row_placed trTrapExternsPlaced)
open CryptoVerification.SpqrV1.Alloc (growOneStack spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt hkdfToSliceSpec hkdfToSliceSpqrSpec)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts
  (ls_subroutine_ok_callInv_of_block subroutine_ok_withLsCallInv_of_withLsCodeLoaded withLsCallInv)
open CryptoVerification.SpqrV1.Kdf
  (FinPre3 FinPre3Pfx FinPre3PfxGen
   effectiveHmacKey effectiveHmacKey_length_le fin3PlacedFakeB fin3PlacedFakeB_off_0
   hmacWith_effectiveHmacKey new_from_slice3_gen_placed_runsTo)
open CryptoVerification.SpqrV1.Kdf.FinalizeFixed3GenProof
  (finalize_fixed3_pfx_lt64_placed_runsTo)
open CryptoVerification.SpqrV1.Kdf.FinalizeFixed3Proof
  (finalize_fixed3_placed_runsTo finalize_fixed3_pfx_placed_runsTo)
open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof
  (HCommon HExpCommon HFrame HPost HPre Nfs3GenRunsToProg
   StateB1Done StateB1Fin StateB1RetFin
   StateEFin StateERetFin StateExtractDone StateLoop StateLoopC StateLoopFin
   b1_done_32_placed_runsTo b1_to_loop_placed_runsTo
   epilogue_placed_runsTo hkdfCodeFakeB hkdfExpand_32_eq hkdfExpand_64_eq hkdfExpand_96_eq
   hsp hsp_aligned iter_a1_placed_runsTo iter_a2_placed_runsTo iter_b_placed_runsTo
   iter_d_continue_placed_runsTo iter_d_done_placed_runsTo
   nfs1_runsTo nfs2_runsTo rodata_sha256IV_placed
   seg_b1a_placed_runsTo seg_b1b_placed_runsTo seg_b1d_placed_runsTo
   seg_e0_placed_runsTo seg_e1_placed_runsTo seg_e1d_placed_runsTo
   seg_e2_placed_runsTo seg_e3_placed_runsTo)
open CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof
  (nfs3PlacedFakeB nfs3PlacedFakeB_add_iv spqrSha256IVAddr)
open CryptoVerification.SpqrV1.Kdf.SpqrKdfExt (disjointRegions_of_outside)
open CryptoVerification.SpqrV1.States.Leaves
  (subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
   subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv)
open CryptoVerification.SpqrV1.Top.Placed (blkPC_323 blkPl_323 blkPC_328 blkPl_328)
open CryptoVerification.SpqrV1.Top.Recv
  (ls_subroutine_ok_callInv_of_callInv ls_subroutine_ok_cro_of_callInv
   ls_subroutine_ok_cro_of_cl spqrRecvPlacedProg)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
   rustCliAllocBudgetSpec rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps
  (vmPreserved_refl_iff vmPreserved_setMem_writeBytes vmPreserved_setPC)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
  (hookOk_rustAllocWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks cliExternsPlaced_alloc_budget_sat
   cliExternsPlaced_dealloc_budget_sat cliExternsPlaced_framelessMemcpyAcp_budget_sat
   cliExternsPlaced_realloc_budget_sat)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux
  (framelessMemcpyAcpSpec hookMemcpy_framelessMemcpyAcp_ok hookNoop_rustAllocShimVm_ok)
open LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrowBudget (vec_deque_grow_spec_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrowBudgetAux
  (hookMemmove_sessionMemmoveAcp_ok sessionMemmoveAcpSpec)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (chainNewSpecX vecDequeGrowSpec)
open LibsignalBinary.Proofs.SpqrV1.Chain.FromPbClPlacedBudget (chain_from_pb_cl_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbClPlacedBudget (chain_into_pb_cl_placed_ok_X)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget (chainIntoPbSpecX)
open LibsignalBinary.Proofs.SpqrV1.Chain.NewBudget (chainNew_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget
  (allocCallPreserved_trans withAllocVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget
  (dropChainEpochSliceSpec drop_chain_epoch_slice_local2_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget
  (dropProtoEpochSliceSpec drop_proto_epoch_slice_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (checkBlockSafeVm placedLib_rebase_allInstrs_safeVm stripS_calleeSavedVRegs
   stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget (chainFromPbSpecX chainFromSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.ProofPlacedBudget
  (chainFrom_placed_ok_of_contracts_x)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.DefsBudget
  (chainFromVersionNegotiationSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.ProofPlacedBudget
  (chainFromVersionNegotiation_placed_ok_of_contracts_x)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (rustAllocSpecWithStack subroutine_ok_withStack_of_subroutine_ok withStack)

/-! ## 0. Block `379` (`spqr::kdf::hkdf_to_slice`) Strengthened to `withAllocVmPreserved` -/

private def projOracle (s : State) := s.oracle
private theorem projOracle_adv (s : State) : projOracle s.advancePC = projOracle s := by
  cases s; rfl
private theorem projOracle_pc (s : State) (p : BitVec 64) :
    projOracle (s.setPC p) = projOracle s := by cases s; rfl
private theorem projOracle_w64 (s : State) (r : Reg) (v : BitVec 64) :
    projOracle (s.writeReg64 r v) = projOracle s := by cases s; cases r <;> rfl
private theorem projOracle_w32 (s : State) (r : Reg) (v : BitVec 32) :
    projOracle (s.writeReg32 r v) = projOracle s := projOracle_w64 s r _
private theorem projOracle_w (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    projOracle (s.writeReg w r v) = projOracle s := projOracle_w64 s r _
private theorem projOracle_v128 (s : State) (r : BitVec 5) (v : BitVec 128) :
    projOracle (s.writeVReg128 r v) = projOracle s := by cases s; rfl
private theorem projOracle_v64 (s : State) (r : BitVec 5) (v : BitVec 64) :
    projOracle (s.writeVReg64 r v) = projOracle s := projOracle_v128 s r _
private theorem projOracle_v32 (s : State) (r : BitVec 5) (v : BitVec 32) :
    projOracle (s.writeVReg32 r v) = projOracle s := projOracle_v128 s r _
private theorem projOracle_ps (s : State) (p : PState) :
    projOracle (s.setPState p) = projOracle s := by cases s; rfl
private theorem projOracle_fp (s : State) (f : BitVec 32) :
    projOracle (s.setFpsr f) = projOracle s := by cases s; rfl
private theorem projOracle_ofp (s : State) (f : BitVec 32) :
    projOracle (s.orFpsr f) = projOracle s := by cases s; rfl
private theorem projOracle_st (s : State) (st : ExecStatus) :
    projOracle (s.setStatus st) = projOracle s := by cases s; rfl
private theorem projOracle_wst (s : State) (st : ExecStatus) :
    projOracle { s with status := st } = projOracle s := by cases s; rfl
private theorem projOracle_mem (s : State) (m : Memory) :
    projOracle (s.setMem m) = projOracle s := by cases s; rfl
private theorem projOracle_tp (s : State) (v : BitVec 64) :
    projOracle (setTpidrEl0 s v) = projOracle s := by cases s; rfl
private theorem projOracle_ex (s : State) :
    projOracle s.stepExclOracle = projOracle s := by cases s; rfl
private theorem projOracle_as (s : State) (rd : BitVec 5) (r : Except String (BitVec 128)) :
    projOracle (applySimdResult s rd r) = projOracle s := by cases s; cases r <;> rfl
private theorem projOracle_ass (s : State) (rd : BitVec 5) (r : Except String (BitVec 128))
    (sat : Option (BitVec 32)) :
    projOracle (applySimdSatResult s rd r sat) = projOracle s := by
  cases s; cases r <;> cases sat <;> rfl
private theorem projOracle_slr (sz : SimdMemSize) (m : Memory) :
    ∀ (n : Nat) (vt : BitVec 5) (ea : BitVec 64) (s : State),
      projOracle (simdLoadRegs sz m n vt ea s) = projOracle s
  | 0, _, _, _ => rfl
  | n + 1, _, _, s => (projOracle_slr sz m n _ _ _).trans (projOracle_v128 s _ _)

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
private theorem execInst_projOracle_of_not_isSvc0 {inst : Instr}
    (h : inst.isSvc0 = false) (s : State) :
    (execInst inst s).oracle = s.oracle := by
  change projOracle (execInst inst s) = projOracle s
  cases inst
  case system isHalt imm =>
    cases isHalt
    · by_cases himm : imm == 0#16
      · have heq : imm = 0#16 := of_decide_eq_true himm; subst heq; simp [Instr.isSvc0] at h
      · dsimp only [execInst, execInstWithSvc]; simp [himm, projOracle_st]
    · dsimp only [execInst, execInstWithSvc]; by_cases himm : imm == 1#16 <;> simp [himm, projOracle_st]
  case simdThreeSame q u size rm opcode rn rd =>
    dsimp only [execInst, execInstWithSvc]
    by_cases hop : opcode == 0b00011#5
    · simp only [hop, ↓reduceIte]
      rcases size with ⟨_ | _ | _ | _ | _, _⟩ <;> try omega
      all_goals (cases u <;> first
        | exact (projOracle_adv _).trans (projOracle_v128 _ _ _)
        | exact projOracle_ass _ _ _ _)
    · simp only [hop, Bool.false_eq_true, ↓reduceIte, projOracle_adv, projOracle_v128,
        projOracle_st, projOracle_wst, projOracle_as, projOracle_ass,
        apply_ite projOracle, ite_self]
  case ldpSimd _ _ _ addr | stpSimd _ _ _ addr | ldrSimd _ _ addr | strSimd _ _ addr =>
    dsimp only [execInst, execInstWithSvc]
    rcases evalAddrMode s addr with ⟨_, _ | ⟨_, _⟩⟩ <;>
      simp [projOracle_adv, projOracle_mem, projOracle_v128, projOracle_w64, projOracle_st,
        apply_ite projOracle]
  case ldr | ldrLit | str | ldp | stp | ldnp | stnp | addSubImm | logicalImm | moveWide | bitfield
     | logicalShift | addSubShift | addSubExt | addSubCarry | condCompareReg | condCompareImm
     | condSelect | dataProc1 | dataProc2 | dataProc3 =>
    cases s; dsimp only [execInst, execInstWithSvc, execLdr, execLdrLit, execStr, execLdp, execStp,
      execAddSubImm, execLogicalImm, execMoveWide, execBitfield, execLogicalShift, execAddSubShift,
      execAddSubExt, execAddSubCarry, execCondCompare, execCondSelect, execDataProc1, execDataProc2,
      execDataProc3]; (repeat' split) <;> rfl
  all_goals
    dsimp only [execInst, execInstWithSvc]
    simp only [projOracle_adv, projOracle_pc, projOracle_w64, projOracle_w32, projOracle_w,
      projOracle_v128, projOracle_v64, projOracle_v32, projOracle_ps, projOracle_fp,
      projOracle_ofp, projOracle_st, projOracle_wst, projOracle_mem, projOracle_tp,
      projOracle_ex, projOracle_as, projOracle_ass, projOracle_slr,
      apply_ite projOracle, ite_self]
    try (cases s; (repeat' split) <;> rfl)

private theorem findSome?_symbols_none {α : Type} :
    ∀ (syms : List (String × Nat)) {off : Nat},
      (syms.findSome? fun x => if x.2 == off then (none : Option α) else none) = none
  | [], _ => rfl
  | _ :: rest, _ => by
    rw [List.findSome?_cons, ite_self]
    exact findSome?_symbols_none rest

private theorem bytesAt_read {ro : Bool} {p : BitVec 64} {bs : List (BitVec 8)}
    {R : SepProp} {m : Memory} (hle : bs.length ≤ 2 ^ 64)
    (hsep : m ⊨ bytesAt ro p bs ∗ R) :
    m.readBytes p bs.length = bs := by
  cases ro
  · exact ((IsBlock.pointsToBytes p bs).read hsep).2
  · exact (IsBlockRO.pointsToBytesRO p bs hle).read hsep

private theorem bytesAt_outside_rw {ro : Bool} {p b_rw : BitVec 64} {bs : List (BitVec 8)}
    {n_rw : Nat} {Q R : SepProp} {Φ_rw : Memory → Prop} {m : Memory}
    (hle : bs.length ≤ 2 ^ 64) (hrw_pos : 0 < n_rw)
    (hrw : IsBlock Q b_rw n_rw Φ_rw)
    (hsep : m ⊨ bytesAt ro p bs ∗ (Q ∗ R)) :
    ∀ a, InRegion p bs.length a → OutsideRegion b_rw n_rw a := by
  cases ro
  · intro a ha
    have hpos : 0 < bs.length := by unfold InRegion at ha; omega
    have hd := (IsBlock.pointsToBytes p bs).disjoint hrw hpos hrw_pos hsep
    unfold DisjointRegions at hd
    unfold InRegion at ha
    unfold OutsideRegion
    bv_omega
  · exact ro_outside_rw_shared_lb (IsBlockRO.pointsToBytesRO p bs hle) hrw hsep

private theorem stackAt_hkdfToSlice (s₀ : State) :
    stackAt s₀.sp extHookStack =
      memRegion (s₀.sp - 16384#64) 15152 ∗ memRegion (hsp s₀ - 544#64) 1232 := by
  have h1 : stackAt s₀.sp extHookStack =
      memRegion (s₀.sp - 16384#64) 15152 ∗ stackAt s₀.sp 1232 :=
    ProofLib.stackAt_split_bottom s₀.sp 1232 15152 (by decide)
  have h2 : stackAt s₀.sp 1232 = memRegion (hsp s₀ - 544#64) 1232 := by
    simp only [stackAt, hsp]
    congr 1
    bv_lin
  rw [h1, h2]

private def kdfOnlyHooks (H : LibsignalHooks) : LibsignalHooks :=
  fun n =>
    if n == lsMemsetSym || n == lsMemcpySym || n == lsCompress256Sym then H n
    else (H n).map (fun _ s => s.setStatus (.Exception "ext"))

private instance instHkdfPlacedHooks_kdfOnly (C : Crypto) {H : LibsignalHooks}
    [hH : HkdfPlacedHooks C.F H] : HkdfPlacedHooks C.F (kdfOnlyHooks H) where
  memset := by simp [kdfOnlyHooks, hH.memset]
  memcpy := by simp [kdfOnlyHooks, hH.memcpy]
  compress256 := by simp [kdfOnlyHooks, hH.compress256]

private theorem blk379_safeVm : checkBlockSafeVm blkLib_379.text = true := by decide
private theorem blk402_safeVm : checkBlockSafeVm blkLib_402.text = true := by decide
private theorem blk425_safeVm : checkBlockSafeVm blkLib_425.text = true := by decide

private noncomputable def keepKdf [LibsignalPlacement] (a : BitVec 64) : Bool :=
  ProofLib.progKeep ((blkPC_379).rebase (blkPl_379).base vmTrapHooks) a ||
  ProofLib.progKeep ((blkPC_402).rebase (blkPl_402).base vmTrapHooks) a ||
  ProofLib.progKeep ((blkPC_425).rebase (blkPl_425).base vmTrapHooks) a

private def KdfCodeLoaded [LibsignalPlacement] (m : Memory) : Prop :=
  ∀ (H : LibsignalHooks),
    ((blkPC_379).rebase (blkPl_379).base H).CodeLoaded m ∧
    ((blkPC_402).rebase (blkPl_402).base H).CodeLoaded m ∧
    ((blkPC_425).rebase (blkPl_425).base H).CodeLoaded m

private theorem KdfCodeLoaded.of_keepsFrozenNoAnon [LibsignalPlacement] {m m' : Memory}
    (hcl : KdfCodeLoaded m) (hk : KeepsFrozenNoAnon m m') : KdfCodeLoaded m' :=
  fun H =>
    let ⟨h1, h2, h3⟩ := hcl H
    ⟨CryptoVerification.LibsignalTripleRatchet.Expand.Program.CodeLoaded.of_keepsFrozenNoAnon h1 hk,
     CryptoVerification.LibsignalTripleRatchet.Expand.Program.CodeLoaded.of_keepsFrozenNoAnon h2 hk,
     CryptoVerification.LibsignalTripleRatchet.Expand.Program.CodeLoaded.of_keepsFrozenNoAnon h3 hk⟩

private theorem strip_codeLoaded_of_keep_sub {R : Program} {keep : BitVec 64 → Bool} {m : Memory}
    (hsub : ∀ a, ProofLib.progKeep R a = true → keep a = true)
    (hL : R.CodeLoaded m) : R.CodeLoaded (ProofLib.stripExecOutside keep m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hno := hL.no_wrap
  have hsub_add : R.base + BitVec.ofNat 64 i - R.base = BitVec.ofNat 64 i := by bv_omega
  have hkeep : keep (R.base + BitVec.ofNat 64 i) = true := by
    apply hsub
    unfold ProofLib.progKeep
    rw [hsub_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true hi
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

private theorem kdfCodeLoaded_of_ls [LibsignalPlacement] {m : Memory}
    (hcl : LibsignalCodeLoaded lsmpl m) : KdfCodeLoaded m := by
  intro H
  have hI379 : IsLsBlockProg ((blkPC_379).rebase (blkPl_379).base H) 379 H := inferInstance
  have hI402 : IsLsBlockProg ((blkPC_402).rebase (blkPl_402).base H) 402 H := inferInstance
  have hI425 : IsLsBlockProg ((blkPC_425).rebase (blkPl_425).base H) 425 H := inferInstance
  exact ⟨hI379.eq_blockProgram ▸ hcl 379 (by decide) (by decide) H (fun _ => none) Syscall.standard,
    hI402.eq_blockProgram ▸ hcl 402 (by decide) (by decide) H (fun _ => none) Syscall.standard,
    hI425.eq_blockProgram ▸ hcl 425 (by decide) (by decide) H (fun _ => none) Syscall.standard⟩

private theorem kdfCodeLoaded_strip [LibsignalPlacement] {m : Memory}
    (hcl : LibsignalCodeLoaded lsmpl m) :
    KdfCodeLoaded (ProofLib.stripExecOutside keepKdf m) := by
  intro H
  have hI379 : IsLsBlockProg ((blkPC_379).rebase (blkPl_379).base H) 379 H := inferInstance
  have hI402 : IsLsBlockProg ((blkPC_402).rebase (blkPl_402).base H) 402 H := inferInstance
  have hI425 : IsLsBlockProg ((blkPC_425).rebase (blkPl_425).base H) 425 H := inferInstance
  have hL379 : ((blkPC_379).rebase (blkPl_379).base H).CodeLoaded m :=
    hI379.eq_blockProgram ▸ hcl 379 (by decide) (by decide) H (fun _ => none) Syscall.standard
  have hL402 : ((blkPC_402).rebase (blkPl_402).base H).CodeLoaded m :=
    hI402.eq_blockProgram ▸ hcl 402 (by decide) (by decide) H (fun _ => none) Syscall.standard
  have hL425 : ((blkPC_425).rebase (blkPl_425).base H).CodeLoaded m :=
    hI425.eq_blockProgram ▸ hcl 425 (by decide) (by decide) H (fun _ => none) Syscall.standard
  refine ⟨strip_codeLoaded_of_keep_sub (fun a ha => ?_) hL379,
    strip_codeLoaded_of_keep_sub (fun a ha => ?_) hL402,
    strip_codeLoaded_of_keep_sub (fun a ha => ?_) hL425⟩
  · have ha' : ProofLib.progKeep ((blkPC_379).rebase (blkPl_379).base vmTrapHooks) a = true := ha
    simp [keepKdf, ha']
  · have ha' : ProofLib.progKeep ((blkPC_402).rebase (blkPl_402).base vmTrapHooks) a = true := ha
    simp [keepKdf, ha']
  · have ha' : ProofLib.progKeep ((blkPC_425).rebase (blkPl_425).base vmTrapHooks) a = true := ha
    simp [keepKdf, ha']

private theorem runsTo_of_kdf_402 [LibsignalPlacement] {H : LibsignalHooks}
    {s : State} {P_post : State → Prop}
    (hcl : KdfCodeLoaded s.mem)
    (h : RunsTo ((blkPC_402).rebase (blkPl_402).base H) s P_post) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s P_post := by
  intro hL_caller
  have hcaller : IsLsBlockProg ((blkPC_379).rebase (blkPl_379).base H) 379 H := inferInstance
  have hcallee : IsLsBlockProg ((blkPC_402).rebase (blkPl_402).base H) 402 H := inferInstance
  obtain ⟨s', hst_callee, htr, hP, _⟩ := h (hcl H).2.1
  have hext : ∀ pc, ((blkPC_402).rebase (blkPl_402).base H).externAt? pc =
      ((blkPC_379).rebase (blkPl_379).base H).externAt? pc := fun pc => by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : ((blkPC_402).rebase (blkPl_402).base H).svc =
      ((blkPC_379).rebase (blkPl_379).base H).svc := by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  have hst_caller := Steps.of_sameHooks hext hsvc hst_callee
  exact ⟨s', hst_caller, htr, hP, hst_caller.codeLoaded hL_caller⟩

private theorem runsTo_of_kdf_425 [LibsignalPlacement] {H : LibsignalHooks}
    {s : State} {P_post : State → Prop}
    (hcl : KdfCodeLoaded s.mem)
    (h : RunsTo ((blkPC_425).rebase (blkPl_425).base H) s P_post) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s P_post := by
  intro hL_caller
  have hcaller : IsLsBlockProg ((blkPC_379).rebase (blkPl_379).base H) 379 H := inferInstance
  have hcallee : IsLsBlockProg ((blkPC_425).rebase (blkPl_425).base H) 425 H := inferInstance
  obtain ⟨s', hst_callee, htr, hP, _⟩ := h (hcl H).2.2
  have hext : ∀ pc, ((blkPC_425).rebase (blkPl_425).base H).externAt? pc =
      ((blkPC_379).rebase (blkPl_379).base H).externAt? pc := fun pc => by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : ((blkPC_425).rebase (blkPl_425).base H).svc =
      ((blkPC_379).rebase (blkPl_379).base H).svc := by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  have hst_caller := Steps.of_sameHooks hext hsvc hst_callee
  exact ⟨s', hst_caller, htr, hP, hst_caller.codeLoaded hL_caller⟩

private theorem fin_extract_kdf_runsTo [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_memset : H lsMemsetSym = some memsetHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook C.F))
    {b_iv : BitVec 64} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : Nat} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv
      (KdfCodeLoaded s₀.mem))
    (hx : StateEFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀ s (blkPl_425).base) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateERetFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀) := by
  have : HkdfPlacedHooks C.F H :=
    { memset := h_memset, memcpy := h_memcpy, compress256 := h_compress }
  rcases hx.hmac_32 with ⟨pfx, tail, hpt, _hmod, hlt, hhm⟩
  have hrw_hsp := HFrame.rw_hsp hpre hx.common.frame
  have hrw_sub := HFrame.rw_sub_544 hpre hx.common.frame
  have hfin_pre : FinPre3PfxGen fin3PlacedFakeB C.F (effectiveHmacKey C.F salt) pfx tail s :=
    { pc_eq := by rw [fin3PlacedFakeB_off_0]; exact hx.pc_eq
      status := hx.common.status
      key_le := effectiveHmacKey_length_le C.F salt
      tail_lt := hlt
      hmac_st := by rw [hx.x1_eq]; exact hhm
      rw_out := by rw [hx.x0_eq]; exact hrw_hsp.sub (by bv_omega)
      rw_hm := by rw [hx.x1_eq]; exact hrw_hsp.sub (by bv_omega)
      rw_fsp := by rw [hx.common.sp_eq]; exact hrw_sub.sub (by bv_omega)
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq]; unfold DisjointRegions; bv_omega
      disj_out_fsp := by rw [hx.x0_eq, hx.common.sp_eq]; unfold DisjointRegions; bv_omega
      disj_hm_fsp := by rw [hx.x1_eq, hx.common.sp_eq]; unfold DisjointRegions; bv_omega
      sp_aligned := by rw [hx.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).2.1 }
  have hcl_s : KdfCodeLoaded s.mem :=
    hpre.base_al.of_keepsFrozenNoAnon (HFrame.keepsFrozen hpre hx.common.frame)
  refine (runsTo_of_kdf_425 hcl_s
    (finalize_fixed3_pfx_lt64_placed_runsTo (C := C) hfin_pre)).mono
    fun s' ⟨hpc', hrun', hcs, hout, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.x0_eq, hpt, hmacWith_effectiveHmacKey] at hout
  rw [hx.x0_eq, hx.x1_eq, hx.common.sp_eq] at hfr
  have hm16' : s'.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length := by
    refine (CryptoVerification.LibsignalTripleRatchet.Expand.Frame.read64_eq hfr fun r hr => ?_).trans hx.m16_eq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  exact ⟨hpc', HCommon.of_fin_frame (outOff := 507#64) hx.common hrun' hcs hfr (by decide),
    (CalleeSaved.x19 hcs).trans hx.x19_eq, (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x25 hcs).trans hx.x25_eq, (CalleeSaved.x26 hcs).trans hx.x26_eq,
    (CalleeSaved.x27 hcs).trans hx.x27_eq, hm16', hout⟩

private theorem fin_b1_kdf_runsTo [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_memset : H lsMemsetSym = some memsetHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook C.F))
    {b_iv : BitVec 64} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : Nat} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv
      (KdfCodeLoaded s₀.mem))
    (hx : StateB1Fin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀ s (blkPl_425).base) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateB1RetFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀) := by
  have : HkdfPlacedHooks C.F H :=
    { memset := h_memset, memcpy := h_memcpy, compress256 := h_compress }
  have hrw_hsp := HFrame.rw_hsp hpre hx.exp.common.frame
  have hrw_sub := HFrame.rw_sub_544 hpre hx.exp.common.frame
  have hfin_pre : FinPre3 fin3PlacedFakeB C.F (hkdfExtractBytes C.F salt ikm) (info ++ [1#8]) s :=
    { pc_eq := by rw [fin3PlacedFakeB_off_0]; exact hx.pc_eq
      status := hx.exp.common.status
      key_le := by rw [hkdfExtractBytes, length_hmacWith]; decide
      msg_lt := by have := hpre.info_lt; simp; omega
      hmac_st := by rw [hx.x1_eq]; exact hx.hmac_32
      rw_out := by rw [hx.x0_eq]; exact hrw_hsp.sub (by bv_omega)
      rw_hm := by rw [hx.x1_eq]; exact hrw_hsp.sub (by bv_omega)
      rw_fsp := by rw [hx.exp.common.sp_eq]; exact hrw_sub.sub (by bv_omega)
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq]; unfold DisjointRegions; bv_omega
      disj_out_fsp := by rw [hx.x0_eq, hx.exp.common.sp_eq]; unfold DisjointRegions; bv_omega
      disj_hm_fsp := by rw [hx.x1_eq, hx.exp.common.sp_eq]; unfold DisjointRegions; bv_omega
      sp_aligned := by rw [hx.exp.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).2.1 }
  have hcl_s : KdfCodeLoaded s.mem :=
    hpre.base_al.of_keepsFrozenNoAnon (HFrame.keepsFrozen hpre hx.exp.common.frame)
  refine (runsTo_of_kdf_425 hcl_s
    (finalize_fixed3_placed_runsTo (C := C) hfin_pre)).mono
    fun s' ⟨hpc', hrun', hcs, ht1, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.x0_eq] at ht1
  rw [hx.x0_eq, hx.x1_eq, hx.exp.common.sp_eq] at hfr
  exact ⟨hpc', HExpCommon.of_fin_frame hx.exp hrun' hcs hfr,
    (CalleeSaved.x21 hcs).trans hx.x21_eq, (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x24 hcs).trans hx.x24_eq, (CalleeSaved.x25 hcs).trans hx.x25_eq,
    (CalleeSaved.x26 hcs).trans hx.x26_eq, (CalleeSaved.x28 hcs).trans hx.x28_eq, ht1⟩

private theorem iter_fin_kdf_runsTo [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_memset : H lsMemsetSym = some memsetHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook C.F))
    {b_iv : BitVec 64} {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i rem dstOff : Nat} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv
      (KdfCodeLoaded s₀.mem))
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoopC hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s (blkPl_425).base) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateLoopFin hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀) := by
  have : HkdfPlacedHooks C.F H :=
    { memset := h_memset, memcpy := h_memcpy, compress256 := h_compress }
  have hrw_hsp := HFrame.rw_hsp hpre hx.exp.common.frame
  have hrw_sub := HFrame.rw_sub_544 hpre hx.exp.common.frame
  have hfin_pre : FinPre3Pfx fin3PlacedFakeB C.F (hkdfExtractBytes C.F salt ikm)
      (tPrev ++ info.take 32) (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)]) s :=
    { pc_eq := by rw [fin3PlacedFakeB_off_0]; exact hx.pc_eq
      status := hx.exp.common.status
      key_le := by rw [hkdfExtractBytes, length_hmacWith]; decide
      tail_lt := by have := hpre.info_lt; simp; omega
      hmac_st := by rw [hx.x1_eq]; exact hx.hmac_32
      rw_out := by rw [hx.x0_eq]; exact hrw_hsp.sub (by bv_omega)
      rw_hm := by rw [hx.x1_eq]; exact hrw_hsp.sub (by bv_omega)
      rw_fsp := by rw [hx.exp.common.sp_eq]; exact hrw_sub.sub (by bv_omega)
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq]; unfold DisjointRegions; bv_omega
      disj_out_fsp := by rw [hx.x0_eq, hx.exp.common.sp_eq]; unfold DisjointRegions; bv_omega
      disj_hm_fsp := by rw [hx.x1_eq, hx.exp.common.sp_eq]; unfold DisjointRegions; bv_omega
      sp_aligned := by rw [hx.exp.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).2.1 }
  have hcl_s : KdfCodeLoaded s.mem :=
    hpre.base_al.of_keepsFrozenNoAnon (HFrame.keepsFrozen hpre hx.exp.common.frame)
  refine (runsTo_of_kdf_425 hcl_s
    (finalize_fixed3_pfx_placed_runsTo (C := C) hfin_pre)).mono
    fun s' ⟨hpc', hrun', hcs, hout, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.x0_eq] at hout; rw [hx.x0_eq, hx.x1_eq, hx.exp.common.sp_eq] at hfr
  have hmsg_eq : (tPrev ++ info.take 32) ++ (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)]) =
      tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)] := by
    rw [List.append_assoc tPrev (info.take 32), ← List.append_assoc (info.take 32),
      List.take_append_drop, ← List.append_assoc]
  rw [hmsg_eq] at hout
  have hokm' : s'.mem.readBytes okmA dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hokm_len := hpre.okm_len
      refine (CryptoVerification.LibsignalTripleRatchet.Expand.Frame.readBytes_eq hfr (fun r hr => ?_) (by omega)).trans hx.okm_pre
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> dsimp only
      · exact (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 540#64) ⟨by decide, by bv_omega⟩).sub_right
          okmA ⟨by omega, by bv_omega⟩
      · exact (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 32#64) ⟨by decide, by bv_omega⟩).sub_right
          okmA ⟨by omega, by bv_omega⟩
      · exact (hpre.disj_okm_stk.symm.sub_left (hsp s₀ - 144#64) ⟨by decide, by bv_omega⟩).sub_right
          okmA ⟨by omega, by bv_omega⟩
  exact ⟨hpc', HExpCommon.of_fin_frame hx.exp hrun' hcs hfr,
    (CalleeSaved.x20 hcs).trans hx.x20_eq, (CalleeSaved.x21 hcs).trans hx.x21_eq,
    (CalleeSaved.x22 hcs).trans hx.x22_eq, (CalleeSaved.x24 hcs).trans hx.x24_eq,
    (CalleeSaved.x25 hcs).trans hx.x25_eq, (CalleeSaved.x26 hcs).trans hx.x26_eq,
    (CalleeSaved.x27 hcs).trans hx.x27_eq, (CalleeSaved.x28 hcs).trans hx.x28_eq, hout, hokm'⟩

private theorem hkdf_to_slice_kdf_runsTo [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_memset : H lsMemsetSym = some memsetHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook C.F))
    (hNfs : Nfs3GenRunsToProg ((blkPC_379).rebase (blkPl_379).base H)
      nfs3PlacedFakeB (blkPl_402).base KdfCodeLoaded C.F)
    {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : Nat} {s₀ : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀
      nfs3PlacedFakeB (KdfCodeLoaded s₀.mem)) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s₀ (HPost C.F salt ikm info okmA okmLen s₀) := by
  have hextract : RunsTo ((blkPC_379).rebase (blkPl_379).base H) s₀
      (StateExtractDone hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀) :=
    (seg_e0_placed_runsTo hpre).trans fun _ hs0 =>
    (nfs1_runsTo hNfs hpre hs0
      (fun hkf => hpre.base_al.of_keepsFrozenNoAnon hkf)).trans fun _ hs1 =>
    (seg_e1_placed_runsTo h_memcpy h_compress hpre hs1).trans fun _ hs2 =>
    (seg_e1d_placed_runsTo hpre hs2).trans fun _ hs3 =>
    (fin_extract_kdf_runsTo (C := C) h_memcpy h_memset h_compress hpre hs3).trans fun _ hs4 =>
    (seg_e2_placed_runsTo hpre hs4).trans fun _ hs5 =>
    (nfs2_runsTo hNfs hpre hs5
      (fun hkf => hpre.base_al.of_keepsFrozenNoAnon hkf)).trans fun _ hs6 =>
    seg_e3_placed_runsTo hpre hs6
  have hb1 : RunsTo ((blkPC_379).rebase (blkPl_379).base H) s₀
      (StateB1Done hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀) :=
    hextract.trans fun _ hs0 =>
    (seg_b1a_placed_runsTo hpre hs0).trans fun _ hs1 =>
    (seg_b1b_placed_runsTo h_memcpy hpre hs1).trans fun _ hs2 =>
    (fin_b1_kdf_runsTo (C := C) h_memcpy h_memset h_compress hpre hs2).trans fun _ hs3 =>
    seg_b1d_placed_runsTo h_memcpy hpre hs3
  have hiter_step : ∀ {tPrev okmSoFar : List (BitVec 8)} {i rem dstOff : Nat} {s : State},
      tPrev.length = 32 → (i = 1 ∨ i = 2) → (rem = 32 ∨ rem = 64) → dstOff + 32 ≤ okmLen →
      StateLoop hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s →
      RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
        (StateLoopFin hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀) :=
    fun ht_len hi hrem hdst hx =>
      (iter_a1_placed_runsTo hpre ht_len hrem (by omega) hx).trans fun _ hs1 =>
      (iter_a2_placed_runsTo h_memcpy h_compress hpre ht_len (by omega) hs1).trans fun _ hs2 =>
      (iter_b_placed_runsTo h_memcpy hpre ht_len hi hrem hdst hs2).trans fun _ hs3 =>
      iter_fin_kdf_runsTo (C := C) h_memcpy h_memset h_compress hpre (by omega) hs3
  refine hb1.trans fun s₁ hs₁ => ?_
  rcases hpre.okm_len with rfl | rfl | rfl
  · exact (b1_done_32_placed_runsTo hpre hs₁).trans fun _ hdone =>
      epilogue_placed_runsTo hpre hdone
  · refine (b1_to_loop_placed_runsTo (Or.inl rfl) hs₁).trans fun _ hloop1 => ?_
    refine (hiter_step (t1_length _ _ _) (Or.inl rfl) (Or.inl rfl) (by decide) hloop1).trans
      fun _ hfin1 => ?_
    refine (iter_d_done_placed_runsTo h_memcpy hpre (by decide) rfl ?_ hfin1).trans
      fun _ hdone => epilogue_placed_runsTo hpre hdone
    exact (hkdfExpand_64_eq C.F (hkdfExtractBytes C.F salt ikm) info).symm
  · refine (b1_to_loop_placed_runsTo (Or.inr rfl) hs₁).trans fun _ hloop1 => ?_
    refine (hiter_step (t1_length _ _ _) (Or.inl rfl) (Or.inr rfl) (by decide) hloop1).trans
      fun _ hfin1 => ?_
    refine (iter_d_continue_placed_runsTo h_memcpy hpre rfl hfin1).trans fun _ hloop2 => ?_
    refine (hiter_step (length_hmacWith _ _ _) (Or.inr rfl) (Or.inl rfl) (by decide)
      hloop2).trans fun _ hfin2 => ?_
    refine (iter_d_done_placed_runsTo h_memcpy hpre (by decide) rfl ?_ hfin2).trans
      fun _ hdone => epilogue_placed_runsTo hpre hdone
    exact (hkdfExpand_96_eq C.F (hkdfExtractBytes C.F salt ikm) info).symm

private theorem strip_readBytes (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    ∀ n, (ProofLib.stripExecOutside keep m).readBytes a n = m.readBytes a n
  | 0 => rfl
  | n + 1 => by
    simp [Memory.readBytes, ProofLib.strip_read8, strip_readBytes keep m (a + 1#64) n]

private theorem strip_read32 (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    (ProofLib.stripExecOutside keep m).read32 a = m.read32 a := by
  simp [Memory.read32, ProofLib.strip_read8]

private theorem strip_readShaState (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    readShaState (ProofLib.stripExecOutside keep m) a = readShaState m a := by
  unfold readShaState
  congr 1; funext i
  exact strip_read32 keep m _

private theorem strip_writeBytes_comm (keep : BitVec 64 → Bool) :
    ∀ (bs : List (BitVec 8)) (m : Memory) (a : BitVec 64),
      (ProofLib.stripExecOutside keep m).writeBytes a bs =
        ProofLib.stripExecOutside keep (m.writeBytes a bs)
  | [], _, _ => rfl
  | b :: bs, m, a => by
    simp only [Memory.writeBytes]
    rw [ProofLib.strip_write8, strip_writeBytes_comm keep bs (m.write8 a b) (a + 1#64)]

private theorem strip_permNoLazy_rw {keep : BitVec 64 → Bool} {m : Memory} {a : BitVec 64}
    (h : m.permNoLazy a = some Perm.rw) :
    (ProofLib.stripExecOutside keep m).permNoLazy a = some Perm.rw := by
  dsimp only [ProofLib.stripExecOutside, Memory.permNoLazy] at h ⊢
  rcases hc : m.cells a with _ | ⟨_ | ⟨r, w, x, lf, an⟩, _⟩ <;> simp [hc, Perm.rw] at h ⊢
  rcases h with ⟨rfl, rfl, rfl, rfl⟩; cases keep a <;> exact ⟨rfl, rfl, rfl, rfl⟩

private theorem hook_writeBytes_strip_allocVm (keep : BitVec 64 → Bool) (s : State)
    (bs : List (BitVec 8)) :
    returnToLinkRegister ((ProofLib.stripS keep s).setMem
        ((ProofLib.stripS keep s).mem.writeBytes ((ProofLib.stripS keep s).readReg64 .x0) bs)) =
      ProofLib.stripS keep
        (returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 .x0) bs))) ∧
    AllocCallPreserved s (returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 .x0) bs))) ∧
    VmPreserved s (returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 .x0) bs))) := by
  refine ⟨?_, ?_, ?_⟩
  · cases s
    dsimp only [ProofLib.stripS, returnToLinkRegister, State.setMem, State.setPC, State.readReg64]
    rw [strip_writeBytes_comm]
  · unfold returnToLinkRegister
    cases s
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · unfold returnToLinkRegister
    simp only [vmPreserved_setPC, vmPreserved_setMem_writeBytes, vmPreserved_refl_iff]

private theorem kdfOnlyHooks_findSome?_active_allocVm [LibsignalPlacement] {C : Crypto}
    {H : LibsignalHooks} [hH : HkdfPlacedHooks C.F H] :
    ∀ (l : List (String × Nat)) {off : Nat} {f : State → State},
      (l.findSome? fun (n, o) => if o == off then kdfOnlyHooks H n else none) = some f →
      ∀ s : State,
        (f (ProofLib.stripS keepKdf s)).status = .Running →
        (l.findSome? fun (n, o) => if o == off then H n else none) = some f ∧
        f (ProofLib.stripS keepKdf s) = ProofLib.stripS keepKdf (f s) ∧
        AllocCallPreserved s (f s) ∧
        VmPreserved s (f s)
  | [], _, _, h => by simp at h
  | (n, o) :: tl, off, f, h => by
    dsimp only [List.findSome?] at h ⊢
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte] at h ⊢
      by_cases hn : (n == lsMemsetSym || n == lsMemcpySym || n == lsCompress256Sym) = true
      · have hk_eq : kdfOnlyHooks H n = H n := by simp [kdfOnlyHooks, hn]
        rw [hk_eq] at h
        intro s _hrun
        simp only [Bool.or_eq_true, beq_iff_eq] at hn
        rcases hn with (rfl | rfl) | rfl
        · rw [hH.memset] at h ⊢; dsimp only at h ⊢; injection h with hf; subst hf
          refine ⟨rfl, ?_⟩
          unfold memsetHook
          simp only [stripS_readReg64]
          exact hook_writeBytes_strip_allocVm keepKdf s _
        · rw [hH.memcpy] at h ⊢; dsimp only at h ⊢; injection h with hf; subst hf
          refine ⟨rfl, ?_⟩
          unfold memcpyHook
          simp only [stripS_readReg64]
          have hrd : (ProofLib.stripS keepKdf s).mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat =
              s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat := by
            cases s; exact strip_readBytes keepKdf _ _ _
          rw [hrd]
          exact hook_writeBytes_strip_allocVm keepKdf s _
        · rw [hH.compress256] at h ⊢; dsimp only at h ⊢; injection h with hf; subst hf
          refine ⟨rfl, ?_⟩
          unfold compress256Hook
          dsimp only []
          simp only [stripS_readReg64]
          have hst : readShaState (ProofLib.stripS keepKdf s).mem (s.readReg64 .x0) =
              readShaState s.mem (s.readReg64 .x0) := by
            cases s; exact strip_readShaState keepKdf _ _
          have hbs : (ProofLib.stripS keepKdf s).mem.readBytes (s.readReg64 .x1)
                (64 * (s.readReg64 .x2).toNat) =
              s.mem.readBytes (s.readReg64 .x1) (64 * (s.readReg64 .x2).toNat) := by
            cases s; exact strip_readBytes keepKdf _ _ _
          rw [hst, hbs]
          exact hook_writeBytes_strip_allocVm keepKdf s _
      · simp only [Bool.not_eq_true] at hn
        cases hHn : H n with
        | none =>
          have hk_n : kdfOnlyHooks H n = none := by unfold kdfOnlyHooks; rw [hn]; simp [hHn]
          rw [hk_n] at h; dsimp only at h ⊢
          exact kdfOnlyHooks_findSome?_active_allocVm (C := C) tl h
        | some g =>
          have hk_g : kdfOnlyHooks H n = some (fun s => s.setStatus (.Exception "ext")) := by
            unfold kdfOnlyHooks; rw [hn]; simp [hHn]
          rw [hk_g] at h; dsimp only at h
          injection h with hf; subst hf; intro s hrun; cases s; cases hrun
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact kdfOnlyHooks_findSome?_active_allocVm (C := C) tl h

private theorem kdfOnlyHooks_findSome?_none {H : LibsignalHooks} :
    ∀ (l : List (String × Nat)) {off : Nat},
      (l.findSome? fun (n, o) => if o == off then kdfOnlyHooks H n else none) = none →
      (l.findSome? fun (n, o) => if o == off then H n else none) = none
  | [], _, _ => rfl
  | (n, o) :: tl, off, h => by
    dsimp only [List.findSome?] at h ⊢
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte] at h ⊢
      cases hHn : H n with
      | none =>
        have hk : kdfOnlyHooks H n = none := by
          unfold kdfOnlyHooks; split <;> simp [hHn]
        rw [hk] at h
        exact kdfOnlyHooks_findSome?_none tl h
      | some g =>
        have hk : ∃ g', kdfOnlyHooks H n = some g' := by
          unfold kdfOnlyHooks
          split
          · exact ⟨g, hHn⟩
          · exact ⟨_, by rw [hHn]; rfl⟩
        rcases hk with ⟨g', hg'⟩
        rw [hg'] at h
        cases h
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact kdfOnlyHooks_findSome?_none tl h

private theorem kdfOnlyHooks_externAt?_active_allocVm [LibsignalPlacement] {C : Crypto}
    {H : LibsignalHooks} [HkdfPlacedHooks C.F H] {pc : BitVec 64} {f : State → State}
    (hext : ((blkPC_379).rebase (blkPl_379).base (kdfOnlyHooks H)).externAt? pc = some f)
    {s : State} (hrun : (f (ProofLib.stripS keepKdf s)).status = .Running) :
    ((blkPC_379).rebase (blkPl_379).base H).externAt? pc = some f ∧
    f (ProofLib.stripS keepKdf s) = ProofLib.stripS keepKdf (f s) ∧
    AllocCallPreserved s (f s) ∧
    VmPreserved s (f s) := by
  unfold Program.externAt? Program.hookAtOff? Program.rebase at hext ⊢
  dsimp only at hext ⊢
  rw [findSome?_symbols_none] at hext ⊢
  cases hm : ((blkPC_379).stubs.findSome? fun (n, o) =>
      if o == (pc - (blkPl_379).base).toNat then kdfOnlyHooks H n else none) with
  | none => rw [hm] at hext; cases hext
  | some g =>
    rw [hm] at hext; injection hext with hgf; subst hgf
    obtain ⟨hhk, hcomm, hacp, hvm⟩ :=
      kdfOnlyHooks_findSome?_active_allocVm (C := C) (blkPC_379).stubs hm s hrun
    rw [hhk]
    exact ⟨rfl, hcomm, hacp, hvm⟩

private theorem kdfOnlyHooks_externAt?_none [LibsignalPlacement] {H : LibsignalHooks}
    {pc : BitVec 64}
    (hext : ((blkPC_379).rebase (blkPl_379).base (kdfOnlyHooks H)).externAt? pc = none) :
    ((blkPC_379).rebase (blkPl_379).base H).externAt? pc = none := by
  unfold Program.externAt? Program.hookAtOff? Program.rebase at hext ⊢
  dsimp only at hext ⊢
  rw [findSome?_symbols_none] at hext ⊢
  have h1 : ((blkPC_379).stubs.findSome? fun (n, o) =>
      if o == (pc - (blkPl_379).base).toNat then kdfOnlyHooks H n else none) = none := by
    cases hm : ((blkPC_379).stubs.findSome? fun (n, o) =>
        if o == (pc - (blkPl_379).base).toNat then kdfOnlyHooks H n else none) with
    | none => rfl
    | some g => rw [hm] at hext; cases hext
  rw [kdfOnlyHooks_findSome?_none (blkPC_379).stubs h1]
  rfl

private theorem safeVm_of_block_progKeep
    (lib : Obj.PlacedLib) (pl : Obj.Placement)
    (hchk : checkBlockSafeVm lib.text = true)
    {m : Memory} {pc : BitVec 64} {inst : Instr}
    (hL : ((lib.program pl).rebase pl.base vmTrapHooks).CodeLoaded m)
    (hkeep : ProofLib.progKeep ((lib.program pl).rebase pl.base vmTrapHooks) pc = true)
    (hal_pc : pc.toNat % 4 = 0)
    (hdec : Arm64.decode (m.read32 pc) = some inst) :
    inst.isSvc0 = false ∧ inst.isMsrTpidrEl0 = false := by
  let Q := (lib.program pl).rebase pl.base (fun _ => none)
  have hall : Q.allInstrs (fun i => !(i.isSvc0 || i.isMsrTpidrEl0)) = true :=
    placedLib_rebase_allInstrs_safeVm lib pl (fun _ => none) hchk
  have hLQ : Q.CodeLoaded m := hL.of_base_code rfl rfl
  have hlen_mod4 : Q.code.length % 4 = 0 := by
    have hcode : Q.code = lib.text.patched pl := rfl
    rw [hcode, Obj.CodeBlock.length_patched]
    omega
  have hoff_lt : (pc - Q.base).toNat < Q.code.length := by
    unfold ProofLib.progKeep at hkeep
    exact of_decide_eq_true hkeep
  have hbase_al : Q.base.toNat % 4 = 0 := hLQ.aligned
  have hno_wrap : Q.base.toNat + Q.code.length ≤ 2 ^ 64 := hLQ.no_wrap
  have hpc_eq : pc = Q.base + BitVec.ofNat 64 (pc - Q.base).toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm Q.base, BitVec.sub_add_cancel]
  have hpc_nat : pc.toNat = Q.base.toNat + (pc - Q.base).toNat := by
    conv_lhs => rw [hpc_eq]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := (pc - Q.base).toNat) (by omega), Nat.mod_eq_of_lt (by omega)]
  have hin : (pc - Q.base).toNat + 4 ≤ Q.code.length := by omega
  have hfe_Q : Q.fetchMem m pc = some inst := by
    have hext_Q : Q.externAt? pc = none := by
      unfold Q Program.externAt? Program.hookAtOff? Program.rebase
      dsimp only
      rw [findSome?_symbols_none, findSome?_symbols_none]
      rfl
    have hce_Q : m.canExec pc 4 = true := by
      unfold Memory.canExec; rw [Memory.allPerm_iff]; intro k hk
      have hk_lt : (pc - Q.base).toNat + k < Q.code.length := by omega
      have heq_addr : pc + BitVec.ofNat 64 k =
          Q.base + BitVec.ofNat 64 ((pc - Q.base).toNat + k) := by
        conv_lhs => rw [hpc_eq]
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      rw [heq_addr, hLQ.perm_eq _ hk_lt]
      rfl
    unfold Program.fetchMem
    rw [hext_Q]
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hal_pc, ne_eq,
      not_true_eq_false, hce_Q, Bool.not_true]
    exact hdec
  have hboth := Program.fetchMem_of_allInstrs_holdsBytes_in_code hall hbase_al hno_wrap
    (fun k hk => ⟨hLQ.byte_eq k hk, hLQ.perm_eq k hk, hLQ.isLazyFree_eq k hk⟩) hin hfe_Q
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff] at hboth
  exact hboth

private theorem steps_kdf_lockstep_allocVm [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [HkdfPlacedHooks C.F H] {s1 sf0 sf' : State}
    (hsteps0 : Steps ((blkPC_379).rebase (blkPl_379).base (kdfOnlyHooks H)) s1 sf0)
    (hrun0 : sf0.status = .Running) :
    ∀ {s1' : State},
      s1' = ProofLib.stripS keepKdf s1 →
      Steps ((blkPC_379).rebase (blkPl_379).base (kdfOnlyHooks H)) s1' sf' →
      sf'.status = .Running →
      LibsignalCodeLoaded lsmpl s1.mem →
      ∃ sf : State,
        (sf = sf0 ∨ sf' = ProofLib.stripS keepKdf sf) ∧
        Steps ((blkPC_379).rebase (blkPl_379).base H) s1 sf ∧
        AllocCallPreserved s1 sf ∧
        VmPreserved s1 sf := by
  induction hsteps0 with
  | refl =>
    intro s1' _ _ _ _
    exact ⟨_, Or.inl rfl, .refl _, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, VmPreserved.refl _⟩
  | @step s1 s2 sf0 h1_0 hrest0 ih =>
    intro s1' hs1' hsteps' hrun_f hcl1
    cases hsteps' with
    | refl =>
      exact ⟨s1, Or.inr hs1', .refl s1, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, VmPreserved.refl s1⟩
    | @step _ s2' _ h1' hrest' =>
      subst hs1'
      have hr2_0 : s2.status = .Running := by
        cases hrest0 with
        | refl => exact hrun0
        | step hs _ => cases hs <;> assumption
      have hr2' : s2'.status = .Running := by
        cases hrest' with
        | refl => exact hrun_f
        | step hs _ => cases hs <;> assumption
      cases h1_0 with
      | halt_unmapped _ _ _ => cases s1; cases hr2_0
      | extern_fault _ _ _ => cases s1; cases hr2_0
      | @extern f hr1 hext0 hkf_s1 hsym_s1 =>
        cases h1' with
        | halt_unmapped _ _ _ => cases s1; cases hr2'
        | extern_fault _ _ _ => cases s1; cases hr2'
        | @exec inst' _ hfe' =>
          have hpc_eq : (ProofLib.stripS keepKdf s1).pc = s1.pc := by cases s1; rfl
          unfold Program.fetchMem at hfe'
          rw [hpc_eq, hext0] at hfe'
          simp at hfe'
        | @extern f' _ hext' _ _ =>
          have hpc_eq : (ProofLib.stripS keepKdf s1).pc = s1.pc := by cases s1; rfl
          rw [hpc_eq, hext0] at hext'
          injection hext' with hff'
          subst hff'
          obtain ⟨hext_H, hcomm, hacp1, hvm1⟩ :=
            kdfOnlyHooks_externAt?_active_allocVm (C := C) hext0 hr2'
          have hstep_H : Step ((blkPC_379).rebase (blkPl_379).base H) s1 (f s1) :=
            Step.extern hr1 hext_H hkf_s1 hsym_s1
          have hcl2 : LibsignalCodeLoaded lsmpl (f s1).mem := hcl1.of_keepsFrozen hkf_s1
          obtain ⟨sf, hor, hsteps_H, hacp_rest, hvm_rest⟩ := ih hrun0 hcomm hrest' hrun_f hcl2
          exact ⟨sf, hor, .step hstep_H hsteps_H,
            allocCallPreserved_trans hacp1 hacp_rest, hvm1.trans hvm_rest⟩
      | @exec inst hr1 hfe0 =>
        let P_H := (blkPC_379).rebase (blkPl_379).base H
        have hext_kdf :
            ((blkPC_379).rebase (blkPl_379).base (kdfOnlyHooks H)).externAt? s1.pc = none := by
          cases he : ((blkPC_379).rebase (blkPl_379).base (kdfOnlyHooks H)).externAt? s1.pc with
          | none => rfl
          | some g => unfold Program.fetchMem at hfe0; rw [he] at hfe0; simp at hfe0
        cases h1' with
        | halt_unmapped _ _ _ => cases s1; cases hr2'
        | extern_fault _ _ _ => cases s1; cases hr2'
        | @extern f' _ hext' _ _ =>
          have hpc_eq : (ProofLib.stripS keepKdf s1).pc = s1.pc := by cases s1; rfl
          rw [hpc_eq, hext_kdf] at hext'; cases hext'
        | @exec inst' _ hfe' =>
          have hpc_eq : (ProofLib.stripS keepKdf s1).pc = s1.pc := by cases s1; rfl
          have hmem_eq : (ProofLib.stripS keepKdf s1).mem =
              ProofLib.stripExecOutside keepKdf s1.mem := by cases s1; rfl
          rw [hpc_eq, hmem_eq] at hfe'
          have hext_H : P_H.externAt? s1.pc = none := kdfOnlyHooks_externAt?_none hext_kdf
          have ⟨hal_pc, hce', hdec⟩ : s1.pc.toNat % 4 = 0 ∧
              (ProofLib.stripExecOutside keepKdf s1.mem).canExec s1.pc 4 = true ∧
              Arm64.decode (s1.mem.read32 s1.pc) = some inst' := by
            unfold Program.fetchMem at hfe'
            rw [hext_kdf] at hfe'
            simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfe'
            by_cases hal : s1.pc.toNat % 4 = 0
            · simp only [hal, ne_eq, not_true_eq_false, ↓reduceIte] at hfe'
              split at hfe'
              · contradiction
              · rename_i hce_neg
                simp only [Bool.not_eq_true', Bool.not_eq_false] at hce_neg
                rw [strip_read32] at hfe'; exact ⟨hal, hce_neg, hfe'⟩
            · simp only [hal, ne_eq, not_false_eq_true, ↓reduceIte] at hfe'; contradiction
          have hce : s1.mem.canExec s1.pc 4 = true := by
            unfold Memory.canExec at hce' ⊢; rw [Memory.allPerm_iff] at hce' ⊢; intro k hk
            have hxk := hce' k hk
            rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
          have hfe0' := hfe0
          unfold Program.fetchMem at hfe0'
          rw [hext_kdf] at hfe0'
          simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hal_pc, ne_eq,
            not_true_eq_false, hce, Bool.not_true] at hfe0'
          have hinst_eq : inst' = inst := Option.some.inj (hdec.symm.trans hfe0')
          subst hinst_eq
          have hfe_H : P_H.fetchMem s1.mem s1.pc = some inst' := by
            unfold Program.fetchMem
            rw [hext_H]
            simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hal_pc, ne_eq,
              not_true_eq_false, hce, Bool.not_true]
            exact hdec
          have hkeep_pc : keepKdf s1.pc = true := by
            unfold Memory.canExec at hce'; rw [Memory.allPerm_iff] at hce'
            have hx0 := hce' 0 (by omega)
            simpa using (ProofLib.strip_perm_x_imp hx0).2
          have ⟨hnsvc0, hnmsr⟩ : inst'.isSvc0 = false ∧ inst'.isMsrTpidrEl0 = false := by
            unfold keepKdf at hkeep_pc
            simp only [Bool.or_eq_true] at hkeep_pc
            rcases hkeep_pc with (hk379 | hk402) | hk425
            · have hI : IsLsBlockProg ((blkPC_379).rebase (blkPl_379).base vmTrapHooks) 379 vmTrapHooks :=
                inferInstance
              have hL : ((blkPC_379).rebase (blkPl_379).base vmTrapHooks).CodeLoaded s1.mem :=
                hI.eq_blockProgram ▸ hcl1 379 (by decide) (by decide) vmTrapHooks (fun _ => none) Syscall.standard
              have hEq : (blkPC_379).rebase (blkPl_379).base vmTrapHooks =
                  (blkLib_379.program blkPl_379).rebase (blkPl_379).base vmTrapHooks :=
                hI.eq_blockProgram.trans (prog_eq_blockProgram blkLib_eq_379).symm
              exact safeVm_of_block_progKeep blkLib_379 blkPl_379 blk379_safeVm
                (hEq ▸ hL) (hEq ▸ hk379) hal_pc hdec
            · have hI : IsLsBlockProg ((blkPC_402).rebase (blkPl_402).base vmTrapHooks) 402 vmTrapHooks :=
                inferInstance
              have hL : ((blkPC_402).rebase (blkPl_402).base vmTrapHooks).CodeLoaded s1.mem :=
                hI.eq_blockProgram ▸ hcl1 402 (by decide) (by decide) vmTrapHooks (fun _ => none) Syscall.standard
              have hEq : (blkPC_402).rebase (blkPl_402).base vmTrapHooks =
                  (blkLib_402.program blkPl_402).rebase (blkPl_402).base vmTrapHooks :=
                hI.eq_blockProgram.trans (prog_eq_blockProgram blkLib_eq_402).symm
              exact safeVm_of_block_progKeep blkLib_402 blkPl_402 blk402_safeVm
                (hEq ▸ hL) (hEq ▸ hk402) hal_pc hdec
            · have hI : IsLsBlockProg ((blkPC_425).rebase (blkPl_425).base vmTrapHooks) 425 vmTrapHooks :=
                inferInstance
              have hL : ((blkPC_425).rebase (blkPl_425).base vmTrapHooks).CodeLoaded s1.mem :=
                hI.eq_blockProgram ▸ hcl1 425 (by decide) (by decide) vmTrapHooks (fun _ => none) Syscall.standard
              have hEq : (blkPC_425).rebase (blkPl_425).base vmTrapHooks =
                  (blkLib_425.program blkPl_425).rebase (blkPl_425).base vmTrapHooks :=
                hI.eq_blockProgram.trans (prog_eq_blockProgram blkLib_eq_425).symm
              exact safeVm_of_block_progKeep blkLib_425 blkPl_425 blk425_safeVm
                (hEq ▸ hL) (hEq ▸ hk425) hal_pc hdec
          have hev0 : ((blkPC_379).rebase (blkPl_379).base (kdfOnlyHooks H)).evalInst inst' s1 =
              execInst inst' s1 :=
            Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0 s1
          have hev_kdf : ((blkPC_379).rebase (blkPl_379).base (kdfOnlyHooks H)).evalInst inst'
              (ProofLib.stripS keepKdf s1) =
              ProofLib.stripS keepKdf
                (((blkPC_379).rebase (blkPl_379).base (kdfOnlyHooks H)).evalInst inst' s1) := by
            rw [hev0, Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
          have hstep_H : Step P_H s1
              (((blkPC_379).rebase (blkPl_379).base (kdfOnlyHooks H)).evalInst inst' s1) := by
            rw [hev0]
            have := Step.exec (prog := P_H) hr1 hfe_H
            rwa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] at this
          have hcl2 : LibsignalCodeLoaded lsmpl
              (((blkPC_379).rebase (blkPl_379).base (kdfOnlyHooks H)).evalInst inst' s1).mem :=
            hcl1.of_keepsFrozen hstep_H.keepsFrozen
          have hacp1 : AllocCallPreserved s1
              (((blkPC_379).rebase (blkPl_379).base (kdfOnlyHooks H)).evalInst inst' s1) := by
            have hsym : (((blkPC_379).rebase (blkPl_379).base (kdfOnlyHooks H)).evalInst inst' s1).symtab =
                s1.symtab := hstep_H.symtab_eq
            rw [hev0] at hsym ⊢
            have hbo := ProofLib.execInst_brk_oracle_of_not_isSvc0 hnsvc0 s1
            have hnsp := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1
            exact ⟨hbo.2.2.2.2.2, hnsp.1, hbo.1,
              Arm64.execInst_tpidrEl0_of_not_isMsrTpidrEl0 hnmsr s1,
              hbo.2.2.1, execInst_projOracle_of_not_isSvc0 hnsvc0 s1, hsym⟩
          have hvm1 : VmPreserved s1
              (((blkPC_379).rebase (blkPl_379).base (kdfOnlyHooks H)).evalInst inst' s1) := by
            rw [hev0]
            exact VmPreserved.of_vm_tpidr
              (VerifiedLibraries.RustStd.nonSyscallPreserved_toVmFields
                (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1))
              (Arm64.execInst_tpidrEl0_of_not_isMsrTpidrEl0 hnmsr s1)
              (LibsignalBinary.Heap.FdsHiFrame.of_fs_eq
                (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1).2.2.2.2.2.2)
          obtain ⟨sf, hor, hsteps_H, hacp_rest, hvm_rest⟩ := ih hrun0 hev_kdf hrest' hrun_f hcl2
          exact ⟨sf, hor, .step hstep_H hsteps_H,
            allocCallPreserved_trans hacp1 hacp_rest, hvm1.trans hvm_rest⟩

/-- Block `379` (`spqr::kdf::hkdf_to_slice`, 473 instructions) meets
`withLsCodeRoLoaded lsmpl (withAllocVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith C.F)))` on
`(blkPC_379).rebase (blkPl_379).base H`. -/
theorem hkdf_to_slice_spqr_allocVm_placed_ok [LibsignalPlacement] (C : Crypto)
    {H : LibsignalHooks} [HkdfPlacedHooks C.F H] :
    subroutine_ok ((blkPC_379).rebase (blkPl_379).base H) (blkPl_379).base
      (withLsCodeRoLoaded lsmpl
        (withAllocVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith C.F)))) := by
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp_al => ?_
  obtain ⟨⟨hcl, hro⟩, hpre⟩ := extract_withLsCodeRoLoaded hpre
  change s0.mem ⊨ (hkdfToSliceSpqrSpec (spqrHkdfWith C.F)).pre x s0 ∗ R at hpre
  rw [hkdfToSliceSpqrSpec, hkdfToSliceSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7,
    hsalt_lt, hikm_len, hinfo_ge, hinfo_lt, hokm_len⟩, hsep⟩
  rw [stackAt_hkdfToSlice s0] at hsep
  have hb_okm := IsBlock.memRegion x.okmA x.okmLen
  have hb_stk := IsBlock.memRegion (hsp s0 - 544#64) 1232
  let R_inv : SepProp :=
    bytesAt x.saltRO x.saltA x.salt ∗
      bytesAt x.ikmRO x.ikmA x.ikm ∗
      bytesAt x.infoRO x.infoA x.info ∗
      memRegion (s0.sp - 16384#64) 15152 ∗ R
  have hsep_okm_stk : s0.mem ⊨ memRegion x.okmA x.okmLen ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗ R_inv) :=
    Satisfies.mono (Entails.of_eq (by dsimp only [R_inv]; sep_ac_rfl)) hsep
  have hsep_stk : s0.mem ⊨ memRegion (hsp s0 - 544#64) 1232 ∗
      (memRegion x.okmA x.okmLen ∗ R_inv) :=
    Satisfies.mono (Entails.of_eq (by dsimp only [R_inv]; sep_ac_rfl)) hsep
  have hsep_salt_stk : s0.mem ⊨ bytesAt x.saltRO x.saltA x.salt ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗
        (bytesAt x.ikmRO x.ikmA x.ikm ∗ bytesAt x.infoRO x.infoA x.info ∗
          memRegion x.okmA x.okmLen ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hsep_salt_okm : s0.mem ⊨ bytesAt x.saltRO x.saltA x.salt ∗
      (memRegion x.okmA x.okmLen ∗
        (memRegion (hsp s0 - 544#64) 1232 ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
          bytesAt x.infoRO x.infoA x.info ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hsep_ikm_stk : s0.mem ⊨ bytesAt x.ikmRO x.ikmA x.ikm ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗
        (bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.infoRO x.infoA x.info ∗
          memRegion x.okmA x.okmLen ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hsep_ikm_okm : s0.mem ⊨ bytesAt x.ikmRO x.ikmA x.ikm ∗
      (memRegion x.okmA x.okmLen ∗
        (memRegion (hsp s0 - 544#64) 1232 ∗ bytesAt x.saltRO x.saltA x.salt ∗
          bytesAt x.infoRO x.infoA x.info ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hsep_info_stk : s0.mem ⊨ bytesAt x.infoRO x.infoA x.info ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗
        (bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
          memRegion x.okmA x.okmLen ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hsep_info_okm : s0.mem ⊨ bytesAt x.infoRO x.infoA x.info ∗
      (memRegion x.okmA x.okmLen ∗
        (memRegion (hsp s0 - 544#64) 1232 ∗ bytesAt x.saltRO x.saltA x.salt ∗
          bytesAt x.ikmRO x.ikmA x.ikm ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hokm_pos : 0 < x.okmLen := by omega
  have hokm_le : x.okmLen ≤ 2 ^ 64 := by omega
  have hrw_okm : s0.mem.RW x.okmA x.okmLen := fun a ha => hb_okm.permNoLazy_rw hsep_okm_stk ha
  have hrw_stk : s0.mem.RW (hsp s0 - 544#64) 1232 := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  obtain ⟨hro_iv, hiv_eq⟩ := rodata_sha256IV_placed hro
  let s0' := ProofLib.stripS keepKdf s0
  have hs0'_mem : s0'.mem = ProofLib.stripExecOutside keepKdf s0.mem := by cases s0; rfl
  have hrw_strip : ∀ {base : BitVec 64} {len : Nat}, s0.mem.RW base len → s0'.mem.RW base len := by
    intro base len hrw a ha
    rw [hs0'_mem]
    exact strip_permNoLazy_rw (hrw a ha)
  have hread_iv0 : s0.mem.Readable spqrSha256IVAddr 32 := by
    intro a ha
    obtain ⟨hp, hlf⟩ := hro_iv a ha
    exact ⟨by rw [hp]; rfl, hlf⟩
  have hread_iv0_fake : s0.mem.Readable
      (nfs3PlacedFakeB + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 := by
    rw [nfs3PlacedFakeB_add_iv]
    exact hread_iv0
  have hread_iv' : s0'.mem.Readable spqrSha256IVAddr 32 := by
    intro a ha
    obtain ⟨hp, hlf⟩ := hro_iv a ha
    rw [hs0'_mem]
    refine ⟨?_, by rwa [ProofLib.strip_isLazyFree]⟩
    rw [ProofLib.strip_perm, hp]
    cases keepKdf a <;> rfl
  have hread_iv_fake : s0'.mem.Readable
      (nfs3PlacedFakeB + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 := by
    rw [nfs3PlacedFakeB_add_iv]
    exact hread_iv'
  have hout_salt_stk : ∀ a, InRegion x.saltA x.salt.length a →
      OutsideRegion (hsp s0 - 544#64) 1232 a :=
    bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_salt_stk
  have hhsp_eq : hsp s0' = hsp s0 := by unfold hsp; simp [s0', stripS_sp]
  have h_hpre0 : HPre hkdfCodeFakeB x.salt x.ikm x.info x.saltA x.ikmA x.infoA x.okmA x.okmLen s0
      nfs3PlacedFakeB (KdfCodeLoaded s0.mem) :=
    { pc_eq         := by rw [hkdfCodeFakeB, BitVec.sub_add_cancel]; exact hpc
      status        := hrun
      x0_eq         := hx0
      x1_eq         := hx1
      x2_eq         := hx2
      x3_eq         := hx3
      x4_eq         := hx4
      x5_eq         := hx5
      x6_eq         := hx6
      x7_eq         := hx7
      salt_lt       := hsalt_lt
      ikm_len       := hikm_len
      info_ge       := hinfo_ge
      info_lt       := hinfo_lt
      okm_len       := hokm_len
      base_al       := kdfCodeLoaded_of_ls hcl
      ro_iv_bytes   := by rw [nfs3PlacedFakeB_add_iv]; exact hiv_eq
      ro_iv_read    := hread_iv0_fake
      disj_iv_stk   := by
        rw [nfs3PlacedFakeB_add_iv]
        exact disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_stk
      disj_iv_okm   := by
        rw [nfs3PlacedFakeB_add_iv]
        exact disjointRegions_of_ro_rw (by decide) hokm_pos hro_iv hrw_okm
      salt_bytes    := bytesAt_read (by omega) hsep_salt_stk
      ikm_bytes     := bytesAt_read (by omega) hsep_ikm_stk
      info_bytes    := bytesAt_read (by omega) hsep_info_stk
      rw_okm        := hrw_okm
      rw_stack      := hrw_stk
      disj_okm_stk  := hb_okm.disjoint hb_stk hokm_pos (by decide) hsep_okm_stk
      disj_salt_stk := by
        by_cases h0 : x.salt.length = 0
        · exact Or.inl h0
        · exact Or.inr (disjointRegions_of_outside (by omega) (by decide) hout_salt_stk)
      out_salt_stk  := hout_salt_stk
      out_salt_okm  := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_salt_okm
      out_ikm_stk   := bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_ikm_stk
      out_ikm_okm   := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_ikm_okm
      out_info_stk  := bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_info_stk
      out_info_okm  := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_info_okm
      sp_aligned    := by simpa [State.spAligned] using hsp_al }
  have h_hpre : HPre hkdfCodeFakeB x.salt x.ikm x.info x.saltA x.ikmA x.infoA x.okmA x.okmLen s0'
      nfs3PlacedFakeB (KdfCodeLoaded s0'.mem) :=
    { pc_eq         := by
        rw [hkdfCodeFakeB, BitVec.sub_add_cancel]
        simpa [s0', stripS_pc] using hpc
      status        := by simpa [s0', stripS_status] using hrun
      x0_eq         := by simpa [s0', stripS_readReg64] using hx0
      x1_eq         := by simpa [s0', stripS_readReg64] using hx1
      x2_eq         := by simpa [s0', stripS_readReg64] using hx2
      x3_eq         := by simpa [s0', stripS_readReg64] using hx3
      x4_eq         := by simpa [s0', stripS_readReg64] using hx4
      x5_eq         := by simpa [s0', stripS_readReg64] using hx5
      x6_eq         := by simpa [s0', stripS_readReg64] using hx6
      x7_eq         := by simpa [s0', stripS_readReg64] using hx7
      salt_lt       := hsalt_lt
      ikm_len       := hikm_len
      info_ge       := hinfo_ge
      info_lt       := hinfo_lt
      okm_len       := hokm_len
      base_al       := hs0'_mem ▸ kdfCodeLoaded_strip hcl
      ro_iv_bytes   := by
        rw [nfs3PlacedFakeB_add_iv, hs0'_mem, strip_readBytes]
        exact hiv_eq
      ro_iv_read    := hread_iv_fake
      disj_iv_stk   := by
        rw [nfs3PlacedFakeB_add_iv, hhsp_eq]
        exact disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_stk
      disj_iv_okm   := by
        rw [nfs3PlacedFakeB_add_iv]
        exact disjointRegions_of_ro_rw (by decide) hokm_pos hro_iv hrw_okm
      salt_bytes    := by rw [hs0'_mem, strip_readBytes]; exact bytesAt_read (by omega) hsep_salt_stk
      ikm_bytes     := by rw [hs0'_mem, strip_readBytes]; exact bytesAt_read (by omega) hsep_ikm_stk
      info_bytes    := by rw [hs0'_mem, strip_readBytes]; exact bytesAt_read (by omega) hsep_info_stk
      rw_okm        := hrw_strip hrw_okm
      rw_stack      := by rw [hhsp_eq]; exact hrw_strip hrw_stk
      disj_okm_stk  := by rw [hhsp_eq]; exact hb_okm.disjoint hb_stk hokm_pos (by decide) hsep_okm_stk
      disj_salt_stk := by
        rw [hhsp_eq]
        by_cases h0 : x.salt.length = 0
        · exact Or.inl h0
        · exact Or.inr (disjointRegions_of_outside (by omega) (by decide) hout_salt_stk)
      out_salt_stk  := by rw [hhsp_eq]; exact hout_salt_stk
      out_salt_okm  := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_salt_okm
      out_ikm_stk   := by rw [hhsp_eq]; exact bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_ikm_stk
      out_ikm_okm   := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_ikm_okm
      out_info_stk  := by rw [hhsp_eq]; exact bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_info_stk
      out_info_okm  := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_info_okm
      sp_aligned    := by simpa [State.spAligned, s0', stripS_sp] using hsp_al }
  let H' := kdfOnlyHooks H
  have hH' : HkdfPlacedHooks C.F H' := inferInstance
  have hNfs : Nfs3GenRunsToProg ((blkPC_379).rebase (blkPl_379).base H')
      nfs3PlacedFakeB (blkPl_402).base KdfCodeLoaded C.F := by
    intro s_nfs hpc_nfs hstat_nfs hlen_nfs hiv_nfs hcl_nfs hread_iv_nfs hdisj_iv_nfs
      h_out_nfs h_stk_nfs h_out_stk_nfs h_key_stk_nfs _ hal_nfs
    rw [nfs3PlacedFakeB_add_iv] at hiv_nfs hread_iv_nfs hdisj_iv_nfs
    exact runsTo_of_kdf_402 hcl_nfs
      (new_from_slice3_gen_placed_runsTo C H' hpc_nfs hstat_nfs hlen_nfs hiv_nfs
        hread_iv_nfs hdisj_iv_nfs h_out_nfs h_stk_nfs h_out_stk_nfs h_key_stk_nfs hal_nfs)
  have hRuns0 := hkdf_to_slice_kdf_runsTo (C := C) (H := H')
    hH'.memcpy hH'.memset hH'.compress256 hNfs h_hpre0
  have hRuns := hkdf_to_slice_kdf_runsTo (C := C) (H := H')
    hH'.memcpy hH'.memset hH'.compress256 hNfs h_hpre
  intro _hL0
  have hL0_kdf : ((blkPC_379).rebase (blkPl_379).base H').CodeLoaded s0.mem :=
    (kdfCodeLoaded_of_ls hcl) H' |>.1
  have hL0' : ((blkPC_379).rebase (blkPl_379).base H').CodeLoaded s0'.mem :=
    (hs0'_mem ▸ kdfCodeLoaded_strip hcl) H' |>.1
  obtain ⟨sf0, hsteps0, htr0, hpost0, _⟩ := hRuns0 hL0_kdf
  obtain ⟨sf', hsteps', htr', hpost', _⟩ := hRuns hL0'
  obtain ⟨sf, hor, hsteps_H, hacp, hvm⟩ :=
    steps_kdf_lockstep_allocVm (C := C) (H := H) hsteps0 hpost0.2.1 rfl hsteps' hpost'.2.1 hcl
  have ⟨htr, hpc_sf, hstat_sf, hcallee, hokm_sf, hframe_sf⟩ :
      TraceEq s0 sf ∧ HPost C.F x.salt x.ikm x.info x.okmA x.okmLen s0 sf := by
    rcases hor with rfl | hsf_eq
    · exact ⟨htr0, hpost0⟩
    · subst hsf_eq
      rcases hpost' with ⟨hpc_sf', hstat_sf', hcallee', hokm_sf', hframe_sf'⟩
      have hpc_sf : sf.pc = s0.readReg64 .x30 := by
        simpa [s0', stripS_pc, stripS_readReg64] using hpc_sf'
      have hstat_sf : sf.status = .Running := by
        simpa [stripS_status] using hstat_sf'
      have hcallee : CalleeSaved s0 sf := by
        refine ⟨by simpa [s0', stripS_sp] using hcallee'.1, fun r hr => ?_⟩
        simpa [s0', stripS_readReg64] using hcallee'.2 r hr
      have htr : TraceEq s0 sf :=
        ⟨by simpa [s0', stripS_trace] using htr'.1,
         by simpa [s0', stripS_calleeSavedVRegs] using htr'.2⟩
      have hsf_mem : (ProofLib.stripS keepKdf sf).mem = ProofLib.stripExecOutside keepKdf sf.mem := by
        cases sf; rfl
      have hokm_sf : sf.mem.readBytes x.okmA x.okmLen =
          hkdfExpand C.F (hkdfExtractBytes C.F x.salt x.ikm) x.info x.okmLen := by
        rwa [hsf_mem, strip_readBytes] at hokm_sf'
      have hframe_sf : HFrame x.okmLen s0 sf.mem := by
        unfold HFrame Frame at hframe_sf' ⊢
        rcases hframe_sf' with ⟨hfr1, _hfr2, hfr3, hfr4, hfr5⟩
        have hx6_s0' : s0'.readReg64 .x6 = s0.readReg64 .x6 :=
          stripS_readReg64 keepKdf s0 .x6
        refine ⟨?_, funext hvm.perm_eq, ?_, ?_, ?_⟩
        · intro a hout
          have h1 := hfr1 a (by rwa [hx6_s0', hhsp_eq])
          rwa [hsf_mem, hs0'_mem, ProofLib.strip_read8, ProofLib.strip_read8] at h1
        · intro a hout
          have h3 := hfr3 a (by rwa [hx6_s0', hhsp_eq])
          rwa [hsf_mem, hs0'_mem, ProofLib.strip_isLazyFree, ProofLib.strip_isLazyFree] at h3
        · intro a hlf
          have h4 := hfr4 a (by rwa [hs0'_mem, ProofLib.strip_isLazyFree])
          rwa [hsf_mem, ProofLib.strip_isLazyFree] at h4
        · intro a han
          have h5 := hfr5 a (by rwa [hs0'_mem, ProofLib.strip_isAnon])
          rwa [hsf_mem, ProofLib.strip_isAnon] at h5
      exact ⟨htr, hpc_sf, hstat_sf, hcallee, hokm_sf, hframe_sf⟩
  refine ⟨sf, hsteps_H, Or.inl ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩⟩
  dsimp only [withLsCodeRoLoaded, withAllocVmPreserved]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hacp, hvm⟩, ?_⟩
  rw [hkdfToSliceSpqrSpec, hkdfToSliceSpec]
  dsimp only []
  rw [sepConj_assoc, satisfies_pure_sepConj]
  have h_spqr_eq : spqrHkdfWith C.F x.salt x.ikm x.info x.okmLen =
      hkdfExpand C.F (hkdfExtractBytes C.F x.salt x.ikm) x.info x.okmLen := rfl
  have h_exp_len : (spqrHkdfWith C.F x.salt x.ikm x.info x.okmLen).length = x.okmLen := by
    rw [h_spqr_eq]
    rcases hokm_len with h32 | h64 | h96
    · rw [h32, hkdfExpand_32_eq, t1_length]
    · rw [h64, hkdfExpand_64_eq]; simp [t1_length, t2_length]
    · rw [h96, hkdfExpand_96_eq]; simp [t1_length, t2_length, t3_length]
  refine ⟨⟨h_exp_len, htr.1⟩, ?_⟩
  unfold HFrame at hframe_sf
  rw [hx6] at hframe_sf
  rw [← h_spqr_eq] at hokm_sf
  have hb_okm' := IsBlock.pointsToBytes_len (a := x.okmA) h_exp_len
  have hpost_sep : sf.mem ⊨ (x.okmA ↦ₛ spqrHkdfWith C.F x.salt x.ikm x.info x.okmLen) ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗ R_inv) :=
    Frame.update_two_blocks hb_okm hb_okm' hb_stk hb_stk hsep_okm_stk hframe_sf
      ⟨by rw [h_exp_len]; exact hokm_le, by rwa [h_exp_len]⟩ trivial
  rw [stackAt_hkdfToSlice s0]
  exact Satisfies.mono (Entails.of_eq (by dsimp only [R_inv]; sep_ac_rfl)) hpost_sep

theorem hkdf_to_slice_spqr_allocVm_placed_ok_of_other_block [LibsignalPlacement] (C : Crypto)
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooks C.F H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 379)
      (withLsCodeRoLoaded lsmpl
        (withAllocVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith C.F)))) :=
  keys_ls_subroutine_ok_of_block_cro (hkdf_to_slice_spqr_allocVm_placed_ok C) hi

/-! ## 1. CLI Allocator Hook Bridges & Budget Drop / `VecDeque::grow` / `Chain::new` Callees -/

private theorem hExt_withPanics
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      Rust.withPanics ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym := by
  intro sym hne
  have h1 : Rust.withPanics ext sym =
      Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym := by
    simp only [Rust.withPanics, hExt sym hne]
  exact h1.trans (congrFun (withPanics_cliGhostExterns mmpl gh W) sym)

theorem cliExternsPlaced_rustAllocShimVm_sat
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hShim : gh.shim = hookNoop := by rfl) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W))
      lsRustNoAllocShimSymCli rustAllocShimVmSpec :=
  ⟨hookNoop, (cliGhostExterns_shim gh _).trans (congrArg some hShim), hookNoop_rustAllocShimVm_ok⟩

theorem cliExternsPlaced_framelessMemcpyAcp_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memcpy" framelessMemcpyAcpSpec :=
  cliExternsPlaced_framelessMemcpyAcp_budget_sat mmpl gh W hA

theorem cliExternsPlaced_sessionMemmoveAcp_sat
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (stk : Nat := 4096) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memmove" (sessionMemmoveAcpSpec stk) :=
  cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
    ⟨hookMemmove, cliExternsPlaced_row mmpl W (memmove_row_placed mmpl W),
      hookMemmove_sessionMemmoveAcp_ok stk⟩

theorem cliExternsPlaced_alloc_budget_withStack_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsRustAllocSymCli
      (rustAllocSpecWithStack M A lim false extHookStack) :=
  ⟨gh.alloc, cliGhostExterns_alloc gh _,
    hookOk_rustAllocWithStack hA.alloc allocHookStack_le_extHookStack extHookStack_le⟩

private theorem cliRustAllocShimVm_at_block [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {prog : Program} {i : Nat} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [IsLsBlockProg prog i H]
    (hShim : gh.shim = hookNoop := by rfl)
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      rustAllocShimVmSpec :=
  spqr_hook_ok_of_mem
    (hookSat_of_eq (hExt lsRustNoAllocShimSymCli (by decide))
      (cliExternsPlaced_rustAllocShimVm_sat mmpl gh W hShim))
    (by decide) hi hunmut

private theorem cliRustAllocShimVmWithStack_at_block [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {prog : Program} {i : Nat} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [IsLsBlockProg prog i H] (stk : Nat := extHookStack)
    (hShim : gh.shim = hookNoop := by rfl)
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack rustAllocShimVmSpec stk) :=
  subroutine_ok_withStack_of_subroutine_ok
    (cliRustAllocShimVm_at_block mmpl gh W hExt hShim hi hunmut) stk

theorem cliAllocBudget_at_block [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    {prog : Program} {i : Nat} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [IsLsBlockProg prog i H]
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false) :=
  spqr_hook_ok_of_mem
    (hookSat_of_eq (hExt lsRustAllocSymCli (by decide))
      (cliExternsPlaced_alloc_budget_sat mmpl gh W hA))
    (by decide) hi hunmut

theorem cliAllocBudgetWithStack_at_block [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    {prog : Program} {i : Nat} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [IsLsBlockProg prog i H]
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack M A lim false extHookStack) :=
  spqr_hook_ok_of_mem
    (hookSat_of_eq (hExt lsRustAllocSymCli (by decide))
      (cliExternsPlaced_alloc_budget_withStack_sat mmpl gh W hA))
    (by decide) hi hunmut

theorem cliDeallocBudget_at_block [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    {prog : Program} {i : Nat} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [IsLsBlockProg prog i H]
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim) :=
  spqr_hook_ok_of_mem
    (hookSat_of_eq (hExt lsRustDeallocSymCli (by decide))
      (cliExternsPlaced_dealloc_budget_sat mmpl gh W hA))
    (by decide) hi hunmut

/-- Budget-threaded Block `287` (`drop_glue::<[spqr::chain::ChainEpoch]> [local#2]`) under `cliGhostExterns`. -/
theorem cliDrop_287 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      ((CryptoVerification.SpqrV1.Drop.Blk337_338.blkPC_287).rebase
        (CryptoVerification.SpqrV1.Drop.Blk337_338.blkPl_287).base H)
      (CryptoVerification.SpqrV1.Drop.Blk337_338.blkPl_287).base
      (dropChainEpochSliceSpec M A lim) :=
  drop_chain_epoch_slice_local2_placed_ok (cliDeallocBudget_at_block mmpl gh W hA hExt)

/-- Code-loaded Block `287` (`drop_glue::<[spqr::chain::ChainEpoch]> [local#2]`) under `cliGhostExterns`. -/
theorem cliDrop_287_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      ((CryptoVerification.SpqrV1.Drop.Blk337_338.blkPC_287).rebase
        (CryptoVerification.SpqrV1.Drop.Blk337_338.blkPl_287).base H)
      (lsmpl.base 287)
      (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)) := by
  rw [← ls_blockPlacement_base (i := 287)]
  exact subroutine_ok_withLsCodeLoaded_of_plain (cliDrop_287 mmpl gh W hA hExt)

/-- Budget-threaded Block `288` (`drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>`) under `cliGhostExterns`. -/
theorem cliDrop_288 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      ((CryptoVerification.SpqrV1.Drop.Blk337_338.blkPC_288).rebase
        (CryptoVerification.SpqrV1.Drop.Blk337_338.blkPl_288).base H)
      (CryptoVerification.SpqrV1.Drop.Blk337_338.blkPl_288).base
      (dropProtoEpochSliceSpec M A lim) :=
  drop_proto_epoch_slice_placed_ok (cliDeallocBudget_at_block mmpl gh W hA hExt)

/-- Code-loaded Block `288` (`drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>`) under `cliGhostExterns`. -/
theorem cliDrop_288_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      ((CryptoVerification.SpqrV1.Drop.Blk337_338.blkPC_288).rebase
        (CryptoVerification.SpqrV1.Drop.Blk337_338.blkPl_288).base H)
      (lsmpl.base 288)
      (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec M A lim)) := by
  rw [← ls_blockPlacement_base (i := 288)]
  exact subroutine_ok_withLsCodeLoaded_of_plain (cliDrop_288 mmpl gh W hA hExt)

/-- Budget-threaded Block `353` (`<VecDeque<spqr::chain::ChainEpoch>>::grow`) under `cliGhostExterns`. -/
theorem cliVecDequeGrow_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok ((blkPC_353).rebase (blkPl_353).base H)
      (blkPl_353).base
      (withLsCodeLoaded lsmpl (vecDequeGrowSpec M A lim)) :=
  vec_deque_grow_spec_placed_ok
    ((hExt "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" (by decide)).trans
      (cliGhostExterns_panic_handle_error mmpl gh W))
    (hookSat_of_eq (hExt lsRustNoAllocShimSymCli (by decide))
      (cliExternsPlaced_rustAllocShimVm_sat mmpl gh W hA.shim_eq))
    (hookSat_of_eq (hExt lsRustAllocSymCli (by decide))
      (cliExternsPlaced_alloc_budget_sat mmpl gh W hA))
    (hookSat_of_eq (hExt lsRustReallocSymCli (by decide))
      (cliExternsPlaced_realloc_budget_sat mmpl gh W hA))
    (hookSat_of_eq (hExt "memcpy" (by decide))
      (cliExternsPlaced_framelessMemcpyAcp_sat mmpl gh W hA))
    (hookSat_of_eq (hExt "memmove" (by decide))
      (cliExternsPlaced_sessionMemmoveAcp_sat mmpl gh W growOneStack))

private theorem cliExternsPlaced_sessionMemsetRegion_allocVm_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hA : CliGhostAllocHooks M A lim gh) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved CryptoVerification.LibsignalTripleRatchet.sessionMemsetRegionSpec) := by
  obtain ⟨f, hf, _, _, _, hok, hvm, hfs, _⟩ := hA.memset
  have hacp := hA.memset_acp f hf
  refine ⟨f,
    CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_memset_some gh _ hf,
    fun x R s0 hrun hpre hsp_al => ?_⟩
  obtain ⟨hkf, hsym, hout⟩ := hok x R s0 hrun hpre hsp_al
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have htr : (f s0).trace = s0.trace := by
      rcases x with ⟨ptr, c, len⟩
      dsimp only [CryptoVerification.LibsignalTripleRatchet.sessionMemsetRegionSpec] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
      exact hpost.1.2
    dsimp only [withAllocVmPreserved]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨⟨hfs s0, htr, (hacp s0).1, (hvm s0).1.2.2, (hvm s0).1.1, (hacp s0).2, hsym⟩, hvm s0⟩, hpost⟩
  · exact Or.inr hrest

private theorem hookSat_sessionMemsetRegionBudget_of_allocVm_priv
    {H : String → Option (State → State)} {sym : String}
    (h : HookSat H sym
      (withAllocVmPreserved CryptoVerification.LibsignalTripleRatchet.sessionMemsetRegionSpec)) :
    HookSat H sym
      LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemsetRegionBudgetSpec := by
  refine ProofLib.HookSat.mono h fun x R s0 hpre => ⟨x, R, hpre, fun sf hpost => ?_⟩
  dsimp only [withAllocVmPreserved,
    LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemsetRegionBudgetSpec] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1.2, hpost.2⟩

private theorem hkdf_to_slice_spqr_allocVm_placed_ok_sat_priv [LibsignalPlacement] (C : Crypto)
    {H : LibsignalHooks}
    [LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat C.F H]
    (hMemset : HookSat H lsMemsetSym
      (withAllocVmPreserved CryptoVerification.LibsignalTripleRatchet.sessionMemsetRegionSpec)) :
    subroutine_ok ((blkPC_379).rebase (blkPl_379).base H) (blkPl_379).base
      (withLsCodeRoLoaded lsmpl
        (withAllocVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith C.F)))) := by
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp_al => ?_
  obtain ⟨⟨hcl, hro⟩, hpre⟩ := extract_withLsCodeRoLoaded hpre
  change s0.mem ⊨ (hkdfToSliceSpqrSpec (spqrHkdfWith C.F)).pre x s0 ∗ R at hpre
  rw [hkdfToSliceSpqrSpec, hkdfToSliceSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7,
    hsalt_lt, hikm_len, hinfo_ge, hinfo_lt, hokm_len⟩, hsep⟩
  rw [LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat.stackAt_hkdfToSlice s0] at hsep
  have hb_okm := IsBlock.memRegion x.okmA x.okmLen
  have hb_stk := IsBlock.memRegion (hsp s0 - 544#64) 1232
  let R_inv : SepProp :=
    bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
      bytesAt x.infoRO x.infoA x.info ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R
  have hsep_okm_stk : s0.mem ⊨ memRegion x.okmA x.okmLen ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗ R_inv) := by dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (hsp s0 - 544#64) 1232 ∗
      (memRegion x.okmA x.okmLen ∗ R_inv) := by dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_salt_stk : s0.mem ⊨ bytesAt x.saltRO x.saltA x.salt ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗
        (bytesAt x.ikmRO x.ikmA x.ikm ∗ bytesAt x.infoRO x.infoA x.info ∗
          memRegion x.okmA x.okmLen ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_salt_okm : s0.mem ⊨ bytesAt x.saltRO x.saltA x.salt ∗
      (memRegion x.okmA x.okmLen ∗
        (memRegion (hsp s0 - 544#64) 1232 ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
          bytesAt x.infoRO x.infoA x.info ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_ikm_stk : s0.mem ⊨ bytesAt x.ikmRO x.ikmA x.ikm ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗
        (bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.infoRO x.infoA x.info ∗
          memRegion x.okmA x.okmLen ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_ikm_okm : s0.mem ⊨ bytesAt x.ikmRO x.ikmA x.ikm ∗
      (memRegion x.okmA x.okmLen ∗
        (memRegion (hsp s0 - 544#64) 1232 ∗ bytesAt x.saltRO x.saltA x.salt ∗
          bytesAt x.infoRO x.infoA x.info ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_info_stk : s0.mem ⊨ bytesAt x.infoRO x.infoA x.info ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗
        (bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
          memRegion x.okmA x.okmLen ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_info_okm : s0.mem ⊨ bytesAt x.infoRO x.infoA x.info ∗
      (memRegion x.okmA x.okmLen ∗
        (memRegion (hsp s0 - 544#64) 1232 ∗ bytesAt x.saltRO x.saltA x.salt ∗
          bytesAt x.ikmRO x.ikmA x.ikm ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by ac_nf at hsep ⊢
  have hokm_pos : 0 < x.okmLen := by omega
  have hokm_le : x.okmLen ≤ 2 ^ 64 := by omega
  have hrw_okm : s0.mem.RW x.okmA x.okmLen := fun a ha => hb_okm.permNoLazy_rw hsep_okm_stk ha
  have hrw_stk : s0.mem.RW (hsp s0 - 544#64) 1232 := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  obtain ⟨hro_iv, hiv_eq⟩ := rodata_sha256IV_placed hro
  have hread_iv : s0.mem.Readable spqrSha256IVAddr 32 := fun a ha =>
    let ⟨hp, hlf⟩ := hro_iv a ha; ⟨by rw [hp]; rfl, hlf⟩
  have hout_salt_stk :=
    LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat.bytesAt_outside_rw
      (by omega) (by decide) hb_stk hsep_salt_stk
  have hb : LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat.HPreBase
      x.salt x.ikm x.info x.saltA x.ikmA x.infoA x.okmA x.okmLen s0 :=
    { pre :=
        { pc_eq := by rw [hkdfCodeFakeB, BitVec.sub_add_cancel]; exact hpc,
          status := hrun,
          x0_eq := hx0, x1_eq := hx1, x2_eq := hx2, x3_eq := hx3,
          x4_eq := hx4, x5_eq := hx5, x6_eq := hx6, x7_eq := hx7,
          salt_lt := hsalt_lt, ikm_len := hikm_len, info_ge := hinfo_ge,
          info_lt := hinfo_lt, okm_len := hokm_len, base_al := trivial,
          ro_iv_bytes := by rw [nfs3PlacedFakeB_add_iv]; exact hiv_eq,
          ro_iv_read := by rw [nfs3PlacedFakeB_add_iv]; exact hread_iv,
          disj_iv_stk := by
            rw [nfs3PlacedFakeB_add_iv]
            exact disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_stk,
          disj_iv_okm := by
            rw [nfs3PlacedFakeB_add_iv]
            exact disjointRegions_of_ro_rw (by decide) hokm_pos hro_iv hrw_okm,
          salt_bytes := LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat.bytesAt_read
            (by omega) hsep_salt_stk,
          ikm_bytes := LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat.bytesAt_read
            (by omega) hsep_ikm_stk,
          info_bytes := LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat.bytesAt_read
            (by omega) hsep_info_stk,
          rw_okm := hrw_okm, rw_stack := hrw_stk,
          disj_okm_stk := hb_okm.disjoint hb_stk hokm_pos (by decide) hsep_okm_stk,
          disj_salt_stk := by
            by_cases h0 : x.salt.length = 0; · exact Or.inl h0
            · exact Or.inr (disjointRegions_of_outside (by omega) (by decide) hout_salt_stk),
          out_salt_stk := hout_salt_stk,
          out_salt_okm :=
            LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat.bytesAt_outside_rw
              (by omega) hokm_pos hb_okm hsep_salt_okm,
          out_ikm_stk :=
            LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat.bytesAt_outside_rw
              (by omega) (by decide) hb_stk hsep_ikm_stk,
          out_ikm_okm :=
            LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat.bytesAt_outside_rw
              (by omega) hokm_pos hb_okm hsep_ikm_okm,
          out_info_stk :=
            LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat.bytesAt_outside_rw
              (by omega) (by decide) hb_stk hsep_info_stk,
          out_info_okm :=
            LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat.bytesAt_outside_rw
              (by omega) hokm_pos hb_okm hsep_info_okm,
          sp_aligned := by simpa [State.spAligned] using hsp_al },
      read_salt := LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat.bytesAt_readable
        (by omega) hsep_salt_stk,
      read_ikm := LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat.bytesAt_readable
        (by omega) hsep_ikm_stk,
      read_info := LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat.bytesAt_readable
        (by omega) hsep_info_stk }
  intro hL0
  obtain ⟨sf, hsteps_H, hvm, hacp_imp, htr, _hvregs,
    ⟨hpc_sf, hstat_sf, hcallee, hokm_sf, hframe_sf⟩, _⟩ :=
    LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat.hkdf_to_slice_kdf_vm_sat (C := C)
      (hookSat_sessionMemsetRegionBudget_of_allocVm_priv hMemset) hcl hb hL0
  have hpma : LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetVmSat.ProgMemsetAllocVm
      ((blkPC_379).rebase (blkPl_379).base H) := by
    obtain ⟨f, hfH, hfOk⟩ := hMemset
    refine ⟨f, ?_, hfOk⟩
    rw [CryptoVerification.ls_externAt?_of_mem (by decide) (by decide) (by decide), hfH]
  have _ : TraceEq s0 sf := ⟨htr, _hvregs⟩
  refine ⟨sf, hsteps_H, Or.inl ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩⟩
  dsimp only [withLsCodeRoLoaded, withAllocVmPreserved]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hacp_imp hpma, hvm⟩, ?_⟩
  rw [hkdfToSliceSpqrSpec, hkdfToSliceSpec]; dsimp only []
  rw [sepConj_assoc, satisfies_pure_sepConj]
  have h_spqr_eq : spqrHkdfWith C.F x.salt x.ikm x.info x.okmLen =
      hkdfExpand C.F (hkdfExtractBytes C.F x.salt x.ikm) x.info x.okmLen := rfl
  have h_exp_len : (spqrHkdfWith C.F x.salt x.ikm x.info x.okmLen).length = x.okmLen := by
    rw [h_spqr_eq]
    rcases hokm_len with h32 | h64 | h96
    · rw [h32, hkdfExpand_32_eq, t1_length]
    · rw [h64, hkdfExpand_64_eq]; simp [t1_length, t2_length]
    · rw [h96, hkdfExpand_96_eq]; simp [t1_length, t2_length, t3_length]
  refine ⟨⟨h_exp_len, htr⟩, ?_⟩
  unfold LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat.HFrameS2 at hframe_sf
  rw [hx6] at hframe_sf
  rw [← h_spqr_eq] at hokm_sf
  have hb_okm' := IsBlock.pointsToBytes_len (a := x.okmA) h_exp_len
  have hpost_sep : sf.mem ⊨ (x.okmA ↦ₛ spqrHkdfWith C.F x.salt x.ikm x.info x.okmLen) ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗ R_inv) :=
    CryptoVerification.LibsignalTripleRatchet.Extract.S2Frame.update_two_blocks
      hb_okm hb_okm' hb_stk hb_stk hsep_okm_stk hframe_sf
      ⟨by rw [h_exp_len]; exact hokm_le, by rwa [h_exp_len]⟩ trivial
  rw [LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat.stackAt_hkdfToSlice s0]
  dsimp only [R_inv] at hpost_sep
  ac_nf at hpost_sep ⊢

private theorem hkdf_to_slice_spqr_allocVm_placed_ok_of_other_block_sat_priv [LibsignalPlacement]
    (C : Crypto) {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    [LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat C.F H]
    (hMemset : HookSat H lsMemsetSym
      (withAllocVmPreserved CryptoVerification.LibsignalTripleRatchet.sessionMemsetRegionSpec))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 379)
      (withLsCodeRoLoaded lsmpl
        (withAllocVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith C.F)))) :=
  keys_ls_subroutine_ok_of_block_cro (hkdf_to_slice_spqr_allocVm_placed_ok_sat_priv C hMemset) hi

/-- Budget-threaded Block `363` (`<spqr::chain::Chain>::new`) under `cliGhostExterns`. -/
theorem cliChainNew_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok ((blkPC_363).rebase (blkPl_363).base H)
      (blkPl_363).base
      (withLsCallInv lsmpl (chainNewSpecX (spqrHkdfWith W.C.F) M A lim)) := by
  let _ : LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat W.C.F H :=
    LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat.of_allocHooks_ext
      (mmpl := mmpl) (W := W) hA hExt
  have hMemsetH : HookSat H lsMemsetSym
      (withAllocVmPreserved CryptoVerification.LibsignalTripleRatchet.sessionMemsetRegionSpec) :=
    hookSat_of_eq (hExt lsMemsetSym (by decide))
      (cliExternsPlaced_sessionMemsetRegion_allocVm_sat mmpl gh W hA)
  have hhkdf_363 : subroutine_ok
      ((blkPC_363).rebase (blkPl_363).base H)
      (lsmpl.base 379)
      (withLsCallInv lsmpl (withAllocVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith W.C.F)))) :=
    subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
      (hkdf_to_slice_spqr_allocVm_placed_ok_of_other_block_sat_priv W.C hMemsetH)
  have hgrow_363 : subroutine_ok
      ((blkPC_363).rebase (blkPl_363).base H)
      (lsmpl.base 353)
      (withLsCallInv lsmpl (vecDequeGrowSpec M A lim)) :=
    subroutine_ok_withLsCallInv_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block (i := 363) (j := 353)
        (cliVecDequeGrow_placed_ok mmpl gh W hA hExt))
  exact chainNew_placed_ok
    hhkdf_363 hgrow_363
    (cliRustAllocShimVmWithStack_at_block mmpl gh W hExt extHookStack hA.shim_eq)
    (cliAllocBudgetWithStack_at_block mmpl gh W hA hExt)

/-! ## (a) Own-Block `withLsCodeLoaded` Contracts for Blocks `364` and `365` -/

/-- Block `364` (`<spqr::chain::Chain>::from_pb`) with `withLsCodeLoaded lsmpl` under `cliGhostExterns`. -/
theorem cliChainFromPb_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 364)
      (withLsCodeLoaded lsmpl (chainFromPbSpecX M A lim)) := by
  rw [← ls_blockPlacement_base (i := 364)]
  exact chain_from_pb_cl_placed_ok
    (cliDeallocBudget_at_block mmpl gh W hA hExt)
    (ls_subroutine_ok_of_block (i := 364) (j := 287) (cliDrop_287_cl mmpl gh W hA hExt))
    (ls_subroutine_ok_of_block (i := 364) (j := 288) (cliDrop_288_cl mmpl gh W hA hExt))

/-- Block `365` (`<spqr::chain::Chain>::into_pb`) with `withLsCodeLoaded lsmpl` under `cliGhostExterns`. -/
theorem cliChainIntoPb_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 365)
      (withLsCodeLoaded lsmpl (chainIntoPbSpecX M A lim)) := by
  rw [← ls_blockPlacement_base (i := 365)]
  exact chain_into_pb_cl_placed_ok_X
    (cliRustAllocShimVm_at_block mmpl gh W hExt hA.shim_eq)
    (cliAllocBudget_at_block mmpl gh W hA hExt)
    (cliDeallocBudget_at_block mmpl gh W hA hExt)
    (ls_subroutine_ok_of_block (i := 365) (j := 287) (cliDrop_287_cl mmpl gh W hA hExt))

/-- Own-block `blockProgram` form of Block `364` (`Chain::from_pb`) under `Rust.withPanics ext`. -/
theorem cliChainFromPb_blockProgram_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 364 (Rust.withPanics ext))
      (lsmpl.base 364)
      (withLsCodeLoaded lsmpl (chainFromPbSpecX M A lim)) := by
  rw [← IsLsBlockProg.eq_blockProgram
    (prog := (blkPC_364).rebase (blkPl_364).base (Rust.withPanics ext))]
  exact cliChainFromPb_cl mmpl gh W hA (hExt_withPanics mmpl gh W hExt)

/-- Own-block `blockProgram` form of Block `365` (`Chain::into_pb`) under `Rust.withPanics ext`. -/
theorem cliChainIntoPb_blockProgram_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 365 (Rust.withPanics ext))
      (lsmpl.base 365)
      (withLsCodeLoaded lsmpl (chainIntoPbSpecX M A lim)) := by
  rw [← IsLsBlockProg.eq_blockProgram
    (prog := (blkPC_365).rebase (blkPl_365).base (Rust.withPanics ext))]
  exact cliChainIntoPb_cl mmpl gh W hA (hExt_withPanics mmpl gh W hExt)

/-- Own-block `blockProgram` form of Block `328` (`spqr::chain_from_version_negotiation`)
    under `Rust.withPanics ext`. -/
theorem cliChainFromVn_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 328 (Rust.withPanics ext))
      (lsmpl.base 328)
      (withLsCodeRoLoaded lsmpl
        (chainFromVersionNegotiationSpecX (spqrHkdfWith W.C.F) M A lim)) := by
  have hnew_328 : subroutine_ok
      ((blkPC_328).rebase (blkPl_328).base (Rust.withPanics ext))
      (lsmpl.base 363)
      (withLsCallInv lsmpl (chainNewSpecX (spqrHkdfWith W.C.F) M A lim)) :=
    ls_subroutine_ok_callInv_of_block (i := 328) (j := 363)
      (cliChainNew_placed_ok mmpl gh W hA (hExt_withPanics mmpl gh W hExt))
  have hraw := chainFromVersionNegotiation_placed_ok_of_contracts_x hnew_328
  rw [← IsLsBlockProg.eq_blockProgram
    (prog := (blkPC_328).rebase (blkPl_328).base (Rust.withPanics ext))]
  exact subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv hraw

/-! ## (b) `spqrSendPlacedProg` Contracts -/

/-- Block `364` (`Chain::from_pb`) lifted to `spqrSendPlacedProg ext` (`Block 427`). -/
theorem cliSpqrSend_chainFromPb_ok_ext [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 364)
      (withLsCodeRoLoaded lsmpl (chainFromPbSpecX M A lim)) :=
  ls_subroutine_ok_cro_of_cl (i := 427) (j := 364)
    (cliChainFromPb_cl mmpl gh W hA (H := Rust.withPanics ext) (hExt_withPanics mmpl gh W hExt))

/-- Block `365` (`Chain::into_pb`) lifted to `spqrSendPlacedProg ext` (`Block 427`). -/
theorem cliSpqrSend_chainIntoPb_ok_ext [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 365)
      (withLsCodeRoLoaded lsmpl (chainIntoPbSpecX M A lim)) :=
  ls_subroutine_ok_cro_of_cl (i := 427) (j := 365)
    (cliChainIntoPb_cl mmpl gh W hA (H := Rust.withPanics ext) (hExt_withPanics mmpl gh W hExt))

/-- Block `328` (`spqr::chain_from_version_negotiation`) lifted to `spqrSendPlacedProg ext` (`Block 427`). -/
theorem cliSpqrSend_chainFromVn_ok_ext [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 328)
      (withLsCodeRoLoaded lsmpl
        (chainFromVersionNegotiationSpecX (spqrHkdfWith W.C.F) M A lim)) := by
  have hnew_328 : subroutine_ok
      ((blkPC_328).rebase (blkPl_328).base (Rust.withPanics ext))
      (lsmpl.base 363)
      (withLsCallInv lsmpl (chainNewSpecX (spqrHkdfWith W.C.F) M A lim)) :=
    ls_subroutine_ok_callInv_of_block (i := 328) (j := 363)
      (cliChainNew_placed_ok mmpl gh W hA
        (H := Rust.withPanics ext) (hExt_withPanics mmpl gh W hExt))
  exact ls_subroutine_ok_cro_of_callInv (i := 427) (j := 328)
    (chainFromVersionNegotiation_placed_ok_of_contracts_x hnew_328)

/-- Exact `hChainFromPb` hypothesis of `spqrSendPlacedContractsTight_of_okX` at
`cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem cliSpqrSend_chainFromPb_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 364)
      (withLsCodeRoLoaded lsmpl (chainFromPbSpecX M A lim)) :=
  cliSpqrSend_chainFromPb_ok_ext mmpl gh W hA (fun _ _ => rfl)

/-- Exact `hChainIntoPb` hypothesis of `spqrSendPlacedContractsTight_of_okX` at
`cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem cliSpqrSend_chainIntoPb_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 365)
      (withLsCodeRoLoaded lsmpl (chainIntoPbSpecX M A lim)) :=
  cliSpqrSend_chainIntoPb_ok_ext mmpl gh W hA (fun _ _ => rfl)

/-- Exact `hChainFromVn` hypothesis of `spqrSendPlacedContractsTight_of_okX` at
`cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem cliSpqrSend_chainFromVn_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 328)
      (withLsCodeRoLoaded lsmpl
        (chainFromVersionNegotiationSpecX (spqrHkdfWith W.C.F) M A lim)) :=
  cliSpqrSend_chainFromVn_ok_ext mmpl gh W hA (fun _ _ => rfl)

/-!
## (c) `spqrRecvPlacedProg` Contracts (`SpqrRecvPlacedContracts` Fields at `Top/Recv/DefsPlacedBudget.lean:232-295`)
-/

/-- Lift a code-loaded Block `364` budget contract (generic in `M`, `A`, `lim`, `ext`)
    to `spqrRecvPlacedProg ext`. -/
theorem spqrRecv_chainFromPb_ok_of_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hChainFromPb : subroutine_ok ((blkPC_364).rebase (blkPl_364).base (Rust.withPanics ext))
      (lsmpl.base 364) (withLsCodeLoaded lsmpl (chainFromPbSpecX M A lim))) :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 364) (withLsCodeRoLoaded lsmpl (chainFromPbSpecX M A lim)) :=
  ls_subroutine_ok_cro_of_cl (i := 329) (j := 364) hChainFromPb

/-- Lift a code-loaded Block `365` budget contract (generic in `M`, `A`, `lim`, `ext`)
    to `spqrRecvPlacedProg ext`. -/
theorem spqrRecv_chainIntoPb_ok_of_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hChainIntoPb : subroutine_ok ((blkPC_365).rebase (blkPl_365).base (Rust.withPanics ext))
      (lsmpl.base 365) (withLsCodeLoaded lsmpl (chainIntoPbSpecX M A lim))) :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 365) (withLsCodeRoLoaded lsmpl (chainIntoPbSpecX M A lim)) :=
  ls_subroutine_ok_cro_of_cl (i := 329) (j := 365) hChainIntoPb

/-- Exact `dropEpochSlice_ok` field of `SpqrRecvPlacedContracts`
    for any `ext` matching `cliGhostExterns gh (cliExternsPlaced mmpl W)` off RNG. -/
theorem cliSpqrRecv_dropEpochSlice_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec M A lim)) :=
  ls_subroutine_ok_of_block (i := 329) (j := 288)
    (cliDrop_288_cl mmpl gh W hA (H := Rust.withPanics ext) (hExt_withPanics mmpl gh W hExt))

/-- Exact `chainFromPb_ok` field of `SpqrRecvPlacedContracts`
    for any `ext` matching `cliGhostExterns gh (cliExternsPlaced mmpl W)` off RNG. -/
theorem cliSpqrRecv_chainFromPb_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 364) (withLsCodeRoLoaded lsmpl (chainFromPbSpecX M A lim)) :=
  spqrRecv_chainFromPb_ok_of_cl (cliChainFromPb_cl mmpl gh W hA (hExt_withPanics mmpl gh W hExt))

/-- Exact `chainNew_ok` field of `SpqrRecvPlacedContracts`
    for any `ext` matching `cliGhostExterns gh (cliExternsPlaced mmpl W)` off RNG. -/
theorem cliSpqrRecv_chainNew_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 363) (withLsCodeRoLoaded lsmpl (chainNewSpecX (spqrHkdfWith W.C.F) M A lim)) :=
  ls_subroutine_ok_cro_of_callInv (i := 329) (j := 363)
    (cliChainNew_placed_ok mmpl gh W hA
      (H := Rust.withPanics ext) (hExt_withPanics mmpl gh W hExt))

/-- Exact `chainIntoPb_ok` field of `SpqrRecvPlacedContracts`
    for any `ext` matching `cliGhostExterns gh (cliExternsPlaced mmpl W)` off RNG. -/
theorem cliSpqrRecv_chainIntoPb_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 365) (withLsCodeRoLoaded lsmpl (chainIntoPbSpecX M A lim)) :=
  spqrRecv_chainIntoPb_ok_of_cl (cliChainIntoPb_cl mmpl gh W hA (hExt_withPanics mmpl gh W hExt))

/-- Exact `chainFrom_ok` field of `SpqrRecvPlacedContracts`
    proved from code-loaded Block `364` + `cliChainNew_placed_ok` for `cliGhostExterns`. -/
theorem cliSpqrRecv_chainFrom_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 323) (withLsCodeRoLoaded lsmpl (chainFromSpecX (spqrHkdfWith W.C.F) M A lim)) := by
  have h_fpb_323 : subroutine_ok ((blkPC_323).rebase (blkPl_323).base (Rust.withPanics ext))
      (lsmpl.base 364) (withLsCallInv lsmpl (chainFromPbSpecX M A lim)) :=
    ls_subroutine_ok_callInv_of_callInv (i := 323) (j := 364)
      (subroutine_ok_withLsCallInv_of_withLsCodeLoaded
        (cliChainFromPb_cl mmpl gh W hA
          (H := Rust.withPanics ext) (hExt_withPanics mmpl gh W hExt)))
  have h_new_323 : subroutine_ok ((blkPC_323).rebase (blkPl_323).base (Rust.withPanics ext))
      (lsmpl.base 363) (withLsCallInv lsmpl (chainNewSpecX (spqrHkdfWith W.C.F) M A lim)) :=
    ls_subroutine_ok_callInv_of_callInv (i := 323) (j := 363)
      (cliChainNew_placed_ok mmpl gh W hA
        (H := Rust.withPanics ext) (hExt_withPanics mmpl gh W hExt))
  exact ls_subroutine_ok_cro_of_callInv (i := 329) (j := 323)
    (chainFrom_placed_ok_of_contracts_x h_fpb_323 h_new_323)

theorem cliSpqrRecv_dropEpochSlice_ok_trTrap [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh) :
    subroutine_ok
      (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec M A lim)) :=
  cliSpqrRecv_dropEpochSlice_ok mmpl gh W hA
    (fun sym hne => by simp [trTrapExternsPlaced, lsRngFillSym, ProofLib.Variant.trapAt, hne])

theorem cliSpqrRecv_chainFromPb_ok_trTrap [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh) :
    subroutine_ok
      (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 364) (withLsCodeRoLoaded lsmpl (chainFromPbSpecX M A lim)) :=
  cliSpqrRecv_chainFromPb_ok mmpl gh W hA
    (fun sym hne => by simp [trTrapExternsPlaced, lsRngFillSym, ProofLib.Variant.trapAt, hne])

theorem cliSpqrRecv_chainNew_ok_trTrap [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh) :
    subroutine_ok
      (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 363) (withLsCodeRoLoaded lsmpl (chainNewSpecX (spqrHkdfWith W.C.F) M A lim)) :=
  cliSpqrRecv_chainNew_ok mmpl gh W hA
    (fun sym hne => by simp [trTrapExternsPlaced, lsRngFillSym, ProofLib.Variant.trapAt, hne])

theorem cliSpqrRecv_chainIntoPb_ok_trTrap [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh) :
    subroutine_ok
      (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 365) (withLsCodeRoLoaded lsmpl (chainIntoPbSpecX M A lim)) :=
  cliSpqrRecv_chainIntoPb_ok mmpl gh W hA
    (fun sym hne => by simp [trTrapExternsPlaced, lsRngFillSym, ProofLib.Variant.trapAt, hne])

theorem cliSpqrRecv_chainFrom_ok_trTrap [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh) :
    subroutine_ok
      (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 323) (withLsCodeRoLoaded lsmpl (chainFromSpecX (spqrHkdfWith W.C.F) M A lim)) :=
  cliSpqrRecv_chainFrom_ok mmpl gh W hA
    (fun sym hne => by simp [trTrapExternsPlaced, lsRngFillSym, ProofLib.Variant.trapAt, hne])

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrChainPlacedInstBudget
