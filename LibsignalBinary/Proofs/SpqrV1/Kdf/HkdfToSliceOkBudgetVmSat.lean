/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixedGen -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixed
import LibsignalBinary.Proofs.SpqrV1.Kdf.FrameROExt
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSlice
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceGen
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedExt
import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
import ProofLib.SepLogic.HeapIntro
import VerifiedLibraries.RustStd.Proofs.ExecSegSym

/-!
# `RunsToVm` & `stripS` Lifting Helpers for `HkdfToSliceOkBudgetSat` (`HkdfToSliceOkBudgetVmSat`)

Provides `RunsToVm`, single-block `memset`-free lifting onto Block `379` (`lift_block_to_379_vm`),
and `stripS` / `unstrip` frame invariance lemmas shared across `HkdfToSliceOkBudgetFinSat` and
`HkdfToSliceOkBudgetSat`.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetVmSat

open Arm64 ProofLib
open Arm64.Obj (MultiPlacedLib MultiPlacement PlacedLib)
open CryptoGames.HKDF (hkdfExpand)
open CryptoGames.HMAC (ShaState chunks64 hmacWith sha256IV toBEBytes)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
   blkLib_379 blkLib_402 blkLib_425 blkLib_eq_379 blkLib_eq_402 blkLib_eq_425
   blkPC_378 blkPC_379 blkPC_402 blkPC_425 blkPl_378 blkPl_379 blkPl_402 blkPl_425
   libsignalMutatedBlocks libsignalSessionLib
   lsProg_402 ls_externAt?_blockProgram_eq_of_externs_eq ls_externAt?_of_mem lsmpl lsρ)
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run.Bytes
  (readBytes_add readBytes_writeBytes_disjoint readBytes_writeBytes_same)
open CryptoVerification.LibsignalHmac (compress256Hook readShaState shaStateBytes)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
  (disjointRegions_of_ro_rw length_hmacWith)
open CryptoVerification.LibsignalSpqrV1 (hkdfExtractBytes spqrHkdfWith)
open CryptoVerification.LibsignalTripleRatchet
  (CalleeSaved CallingConventionPreserved_of_calleeSaved FinSaved Frame
   HkdfPlacedHooks HmacSt LibsignalCodeRoLoaded RW RunsTo RunsToFrom TraceEq
   agreesOutside_seg2a agreesOutside_seg3a agreesOutside_seg4a
   digestBytes digestBytes_eq_append extHookStack extract_withLsCodeRoLoaded
   finSaved_seg3a finSaved_seg4a frame_seg2a frame_seg3a frame_seg4a fsp_aligned
   hmacInnerInit hmacOuterInit keys_ls_subroutine_ok_of_block_cro
   compress256Hook_eq lsCompress256Sym lsMemcpySym lsMemsetSym noAllocShimSpec
   outerBlock outerBlock_digestBytes_length
   read32_words_at_104_of_shaStateBytes read32_words_at_64_of_shaStateBytes
   read64_seg2a_mid read64_seg3a_pad_32 read64_seg3a_pad_40
   readBytes_56_eq_append_8 readBytes_56_of_buf_eq readBytes_fsp_64_seg2 readBytes_fsp_64_seg3
   readBytes_write32_8_digestBytes ro_outside_rw_shared_lb rw_of_perm_eq
   sessionMemsetRegionSpec shaStateBytes_length
   toLEBytes_4_rev32 toLEBytes_8_read64 toLEBytes_8_rev32_append toLEBytes_8_rev64
   truncate8_truncate32 ult_7_of_lt_56 withLsCodeRoLoaded xor_63_of_lt_64
   zeroExtend64_ofNat8 zeroExtend64_truncate32_ofNat64)
open CryptoVerification.LibsignalTripleRatchet.Expand
  (hkdfExpand_64_eq t1_length t2_length t3_length)
open CryptoVerification.LibsignalTripleRatchet.Extract
  (CallingConventionPreserved.x19 CallingConventionPreserved.x20
   CallingConventionPreserved.x21 CallingConventionPreserved.x22
   CallingConventionPreserved.x27 CallingConventionPreserved.x29 S2Frame
   disjoint_fullComplementHeap fullComplementHeap matches_fullComplementHeap)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt
  (AgreesOn AgreesOn.finSaved_of AgreesOn.read64_eq AgreesOn.readBytes_eq)
open CryptoVerification.SpqrV1.Alloc (spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt hkdfToSliceSpec hkdfToSliceSpqrSpec)
open CryptoVerification.SpqrV1.Kdf
  (FinPre3 FinPre3Pfx FinPre3PfxGen HmacStN
   bit_len_innerN_eq bit_len_innerN_eq_lt64 effectiveHmacKey effectiveHmacKey_length_le
   effectiveHmacKey_of_le fin3PlacedFakeB fin3PlacedFakeB_off_0
   hmacWith_effectiveHmacKey hmacWith_pfx_short hmacWith_pfx_two_blocks
   innerLastBlockN innerLastBlockN_length innerPadBlock1 innerPadBlock1_length
   innerPadBlock2 innerPadBlock2_length read64_fsp32_hm readBytes_64_eq_append_8
   readBytes_fsp_64_copy spqrRustAllocZeroedSym toLEBytes_8_zero_7 ult_7_of_ge_56)
open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof
  (HCommon HExpCommon HFrame HPost HPre HSaved
   StateB1Done StateB1Fin StateB1RetFin StateDone
   StateEFin StateENfs1 StateENfs2 StateERet1 StateERet2 StateERetFin StateExtractDone
   StateLoop StateLoopC StateLoopFin
   b1_done_32_placed_runsTo b1_to_loop_placed_runsTo epilogue_placed_runsTo
   hkdfCodeFakeB hkdfExpand_32_eq hkdfExpand_96_eq hsp hsp_aligned
   iter_a1_placed_runsTo iter_a2_placed_runsTo iter_b_placed_runsTo
   iter_d_continue_placed_runsTo iter_d_done_placed_runsTo rodata_sha256IV_placed
   seg_b1a_placed_runsTo seg_b1b_placed_runsTo seg_b1d_placed_runsTo
   seg_e0_placed_runsTo seg_e1_placed_runsTo seg_e1d_placed_runsTo
   seg_e2_placed_runsTo seg_e3_placed_runsTo)
open CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof
  (new_from_slice3_placed_run nfs3PlacedFakeB nfs3PlacedFakeB_add_iv spqrSha256IVAddr)
open CryptoVerification.SpqrV1.Kdf.SpqrKdfExt (disjointRegions_of_outside)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.MuslMemOpsRunsTo (MemcpyClobber applyMemcpyClobber)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
  (stripExecOutside_readBytes stripExecOutside_readable stripExecOutside_rw unstrip_frame)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat
  (blockProgram_allInstrs_not_isMsrTpidrEl0 checkBlockNoMsrTpidrEl0
   hookOk_sessionMemsetRegionBudget_elim)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps
  (vmPreserved_refl_iff vmPreserved_setMem_writeBytes vmPreserved_setPC)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore
  (HookExactMemcpy HookSatExactMemcpy applyMemcpyClobber_ofState_eq)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget
  (allocCallPreserved_trans withAllocVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (CallingConventionPreserved.x23 CallingConventionPreserved.x24
   CallingConventionPreserved.x25 CallingConventionPreserved.x26
   CallingConventionPreserved.x28 HkdfPlacedHooksExactSat HkdfPlacedHooksSat
   vmPreserved_applyMemcpyClobber_writeBytes)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSat (FinPostSat)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemsetRegionBudgetSpec)
open VerifiedLibraries.RustStd (blockProgram_rebase_allInstrs_not_isSvc0)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

open CryptoVerification.LibsignalTripleRatchet.FinalizeFixedProof (FinCommon FinPost)

/-! ## 2. `RunsToVm` & Single-Block `memset`-Free Lifting onto Block `379` -/

abbrev ProgMemsetAllocVm [LibsignalPlacement] (P : Program) : Prop :=
  ∃ f : State → State,
    P.externAt? (lsρ lsMemsetSym) = some f ∧
    HookOk f (withAllocVmPreserved sessionMemsetRegionSpec)

theorem allocCallPreserved_refl (s : State) : AllocCallPreserved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

abbrev RunsToVm [LibsignalPlacement] (P : Program) (s : State) (Q : State → Prop) : Prop :=
  P.CodeLoaded s.mem →
  ∃ sf : State,
    Steps P s sf ∧ VmPreserved s sf ∧
    (ProgMemsetAllocVm P → AllocCallPreserved s sf) ∧
    sf.trace = s.trace ∧
    calleeSavedVRegs sf = calleeSavedVRegs s ∧ Q sf ∧ P.CodeLoaded sf.mem

theorem RunsToVm.refl [LibsignalPlacement] {P : Program} {s : State} {Q : State → Prop}
    (hq : Q s) : RunsToVm P s Q :=
  fun hL => ⟨s, .refl s, VmPreserved.refl s, fun _ => allocCallPreserved_refl s, rfl, rfl, hq, hL⟩

theorem RunsToVm.mono [LibsignalPlacement] {P : Program} {s : State} {Q1 Q2 : State → Prop}
    (h : RunsToVm P s Q1) (himp : ∀ sf, Q1 sf → Q2 sf) :
    RunsToVm P s Q2 :=
  fun hL =>
    let ⟨sf, hst, hvm, hacp, htr, hv, hq, hLf⟩ := h hL
    ⟨sf, hst, hvm, hacp, htr, hv, himp sf hq, hLf⟩

theorem RunsToVm.trans_full [LibsignalPlacement] {P : Program} {s : State} {Q1 Q2 : State → Prop}
    (h1 : RunsToVm P s Q1)
    (h2 : ∀ s1, Q1 s1 → s.mem.KeepsFrozen s1.mem → RunsToVm P s1 Q2) :
    RunsToVm P s Q2 :=
  fun hL =>
    let ⟨s1, hst1, hvm1, hacp1, htr1, hv1, hq1, hL1⟩ := h1 hL
    let ⟨s2, hst2, hvm2, hacp2, htr2, hv2, hq2, hL2⟩ := h2 s1 hq1 hst1.keepsFrozen hL1
    ⟨s2, hst1.trans hst2, hvm1.trans hvm2,
      fun hms => allocCallPreserved_trans (hacp1 hms) (hacp2 hms),
      htr2.trans htr1, hv2.trans hv1, hq2, hL2⟩

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

private theorem stripExecOutside_writeBytes_vm (p : BitVec 64 → Bool) (m : Memory) :
    ∀ (a : BitVec 64) (bs : List (BitVec 8)),
      (ProofLib.stripExecOutside p m).writeBytes a bs = ProofLib.stripExecOutside p (m.writeBytes a bs)
  | _, [] => rfl
  | a, b :: bs => by
    simp only [Memory.writeBytes, ProofLib.strip_write8,
      stripExecOutside_writeBytes_vm p (m.write8 a b) (a + 1#64) bs]

private theorem stripExecOutside_readShaState_vm (p : BitVec 64 → Bool) (m : Memory)
    (a : BitVec 64) :
    readShaState (ProofLib.stripExecOutside p m) a = readShaState m a := by
  simp [readShaState, Memory.read32, ProofLib.strip_read8]

private theorem stripS_applyMemcpyClobber_vm (kp : BitVec 64 → Bool) (s : State) (m' : Memory)
    (pc' : BitVec 64) (c : MemcpyClobber) :
    ProofLib.stripS kp (applyMemcpyClobber s m' pc' c) =
      applyMemcpyClobber (ProofLib.stripS kp s) (ProofLib.stripExecOutside kp m') pc' c := by
  cases s; rfl

private theorem allocCallPreserved_applyMemcpyClobber_vm (s : State) (m' : Memory)
    (pc' : BitVec 64) (c : MemcpyClobber) :
    AllocCallPreserved s (applyMemcpyClobber s m' pc' c) := by
  cases s; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private def restorePerm (m₀ m : Memory) : Memory :=
  ⟨fun a => match m.cells a, m₀.perm a with
    | some (some p, b), some p₀ =>
        some (some { p with r := p₀.r, w := p₀.w, x := p₀.x }, b)
    | other, _ => other⟩

private theorem restorePerm_isLazyFree (m₀ m : Memory) (a : BitVec 64) :
    (restorePerm m₀ m).isLazyFree a = m.isLazyFree a := by
  dsimp only [restorePerm, Memory.isLazyFree]
  rcases m.cells a with _ | ⟨_ | p, _⟩
  · rfl
  · rfl
  · cases m₀.perm a <;> rfl

private theorem restorePerm_read8 (m₀ m : Memory) (a : BitVec 64) :
    (restorePerm m₀ m).read8 a = m.read8 a := by
  dsimp only [restorePerm, Memory.read8]
  rcases m.cells a with _ | ⟨_ | p, _⟩
  · rfl
  · rfl
  · cases m₀.perm a <;> rfl

private theorem restorePerm_readBytes (m₀ m : Memory) (a : BitVec 64) (n : Nat) :
    (restorePerm m₀ m).readBytes a n = m.readBytes a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => exact congrArg₂ List.cons (restorePerm_read8 m₀ m a) (ih (a + 1#64))

private theorem restorePerm_perm {m₀ m : Memory} {kp : BitVec 64 → Bool}
    (hperm : ∀ a, m.perm a = (ProofLib.stripExecOutside kp m₀).perm a) (a : BitVec 64) :
    (restorePerm m₀ m).perm a = m₀.perm a := by
  have ha := (hperm a).trans (ProofLib.strip_perm kp m₀ a)
  show (match (restorePerm m₀ m).cells a with
    | some (some p, _) => some p.rwx | _ => none) = m₀.perm a
  dsimp only [restorePerm]
  rcases hc : m.cells a with _ | ⟨_ | p, b⟩
  · have hm : m.perm a = none := by simp [Memory.perm, hc]
    rw [hm] at ha; cases hm₀ : m₀.perm a <;> simp [hm₀] at ha ⊢
  · have hm : m.perm a = none := by simp [Memory.perm, hc]
    rw [hm] at ha; cases hm₀ : m₀.perm a <;> simp [hm₀] at ha ⊢
  · have hm : m.perm a = some p.rwx := by simp [Memory.perm, hc]
    rw [hm] at ha
    cases hm₀ : m₀.perm a with
    | none => simp [hm₀] at ha
    | some p₀ =>
      unfold Memory.perm at hm₀
      rcases hc₀ : m₀.cells a with _ | ⟨_ | q₀, _⟩ <;> simp [hc₀] at hm₀
      subst hm₀; rfl

private theorem restorePerm_readable {m₀ m : Memory} {kp : BitVec 64 → Bool}
    (hperm : ∀ a, m.perm a = (ProofLib.stripExecOutside kp m₀).perm a)
    {a : BitVec 64} {n : Nat} (h : m.Readable a n) :
    (restorePerm m₀ m).Readable a n := by
  intro x hx
  obtain ⟨hr, hnl⟩ := h x hx
  rw [restorePerm_perm hperm x, restorePerm_isLazyFree]
  rw [hperm x, (ProofLib.strip_perm_props kp m₀ x).1] at hr
  exact ⟨hr, hnl⟩

private theorem restorePerm_rw {m₀ m : Memory} {kp : BitVec 64 → Bool}
    (hperm : ∀ a, m.perm a = (ProofLib.stripExecOutside kp m₀).perm a)
    {a : BitVec 64} {n : Nat} (h : Memory.RW m a n) :
    Memory.RW (restorePerm m₀ m) a n := fun x hx => by
  rw [Memory.permNoLazy_eq_some_rw_iff]
  have ⟨hrw, hnl⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (h x hx)
  rw [restorePerm_perm hperm x, restorePerm_isLazyFree]
  rw [hperm x, (ProofLib.strip_perm_props kp m₀ x).2.2.2] at hrw
  exact ⟨hrw, hnl⟩

private theorem stripExecOutside_restorePerm {m₀ m : Memory} {kp : BitVec 64 → Bool}
    (hperm : ∀ a, m.perm a = (ProofLib.stripExecOutside kp m₀).perm a) :
    ProofLib.stripExecOutside kp (restorePerm m₀ m) = m := by
  ext a
  have ha := (hperm a).trans (ProofLib.strip_perm kp m₀ a)
  dsimp only [ProofLib.stripExecOutside, restorePerm]
  rcases hc : m.cells a with _ | ⟨_ | p, b⟩
  · rfl
  · rfl
  · have hm : m.perm a = some p.rwx := by simp [Memory.perm, hc]
    rw [hm] at ha
    cases hm₀ : m₀.perm a with
    | none => simp [hm₀] at ha
    | some p₀ =>
      simp only [hm₀, Option.map_some, Option.some.injEq] at ha
      rcases p with ⟨r, w, x, lf, an⟩
      rcases p₀ with ⟨r₀, w₀, x₀, lf₀, an₀⟩
      cases hkp : kp a <;> cases x₀ <;>
        simp_all [ProofLib.stripPerm, Perm.rwx]

private theorem restorePerm_stripExecOutside_self {m₀ m₁ : Memory} (kp : BitVec 64 → Bool)
    (hperm : ∀ a, m₁.perm a = m₀.perm a) :
    restorePerm m₀ (ProofLib.stripExecOutside kp m₁) = m₁ := by
  ext a
  have ha := (hperm a).symm
  dsimp only [restorePerm, ProofLib.stripExecOutside]
  rcases hc₁ : m₁.cells a with _ | ⟨_ | p, b⟩
  · rfl
  · rfl
  · have hp₁ : m₁.perm a = some p.rwx := by simp [Memory.perm, hc₁]
    rw [ha, hp₁]
    rcases p with ⟨r, w, x, lf, an⟩
    cases kp a <;> cases x <;> rfl

private def MemcpyPre (u : State) : Prop :=
  u.status = .Running ∧
  u.spAligned = true ∧
  u.mem.RW (u.readReg64 .x0) (u.readReg64 .x2).toNat ∧
  u.mem.Readable (u.readReg64 .x1) (u.readReg64 .x2).toNat ∧
  ((u.readReg64 .x2).toNat = 0 ∨
    DisjointRegions (u.readReg64 .x0) (u.readReg64 .x2).toNat
      (u.readReg64 .x1) (u.readReg64 .x2).toNat)

private noncomputable def coupledMemcpy (f_mc : State → State) (m₀ : Memory)
    (kp : BitVec 64 → Bool) (u : State) : State :=
  open Classical in
  if MemcpyPre u then
    if ∀ a, u.mem.perm a = (ProofLib.stripExecOutside kp m₀).perm a then
      ProofLib.stripS kp (f_mc (u.setMem (restorePerm m₀ u.mem)))
    else
      (u.setMem (u.mem.writeBytes (u.readReg64 .x0)
        (u.mem.readBytes (u.readReg64 .x1) (u.readReg64 .x2).toNat))).setPC (u.readReg64 .lr)
  else
    u.setStatus (.Exception "ext")

private theorem coupledMemcpy_exact {f_mc : State → State} (hf : HookExactMemcpy f_mc)
    (m₀ : Memory) (kp : BitVec 64 → Bool) :
    HookExactMemcpy (coupledMemcpy f_mc m₀ kp) := by
  intro u dst src lr len bs hrun hsp hx0 hx1 hx2 hlr hbs hrw hread hdisj
  have hpre : MemcpyPre u := by
    refine ⟨hrun, hsp, ?_, ?_, ?_⟩
    · rwa [hx0, hx2]
    · rwa [hx1, hx2]
    · rwa [hx0, hx1, hx2]
  unfold coupledMemcpy
  simp only [hpre, ↓reduceIte]
  by_cases hperm : ∀ a, u.mem.perm a = (ProofLib.stripExecOutside kp m₀).perm a
  · simp only [eq_true hperm, ↓reduceIte]
    let s1 := u.setMem (restorePerm m₀ u.mem)
    have hs1_run : s1.status = .Running := by cases u; exact hrun
    have hs1_sp : s1.spAligned = true := by cases u; exact hsp
    have hs1_x0 : s1.readReg64 .x0 = dst := by cases u; exact hx0
    have hs1_x1 : s1.readReg64 .x1 = src := by cases u; exact hx1
    have hs1_x2 : (s1.readReg64 .x2).toNat = len := by cases u; exact hx2
    have hs1_lr : s1.readReg64 .lr = lr := by cases u; exact hlr
    have hs1_bs : s1.mem.readBytes src len = bs := by
      change (restorePerm m₀ u.mem).readBytes src len = bs
      rwa [restorePerm_readBytes]
    have hs1_rw : s1.mem.RW dst len := restorePerm_rw hperm hrw
    have hs1_read : s1.mem.Readable src len := restorePerm_readable hperm hread
    obtain ⟨c, hfc⟩ :=
      hf hs1_run hs1_sp hs1_x0 hs1_x1 hs1_x2 hs1_lr hs1_bs hs1_rw hs1_read hdisj
    refine ⟨c, ?_⟩
    rw [hfc, stripS_applyMemcpyClobber_vm]
    have hu_eq : ProofLib.stripS kp s1 = u := by
      dsimp only [s1, ProofLib.stripS, State.setMem]
      rw [stripExecOutside_restorePerm hperm]
    have hm_eq : ProofLib.stripExecOutside kp (s1.mem.writeBytes dst bs) =
        u.mem.writeBytes dst bs := by
      change ProofLib.stripExecOutside kp ((restorePerm m₀ u.mem).writeBytes dst bs) = _
      rw [← stripExecOutside_writeBytes_vm, stripExecOutside_restorePerm hperm]
    rw [hu_eq, hm_eq]
  · simp only [hperm, ↓reduceIte]
    refine ⟨MemcpyClobber.ofState u, ?_⟩
    rw [hx0, hx1, hx2, hbs, hlr, applyMemcpyClobber_ofState_eq]

private theorem coupledMemcpy_running_step {f_mc : State → State} (hf : HookExactMemcpy f_mc)
    {m₀ : Memory} {kp : BitVec 64 → Bool} {s1 : State}
    (hperm1 : ∀ a, s1.mem.perm a = m₀.perm a)
    (hrb' : (coupledMemcpy f_mc m₀ kp (ProofLib.stripS kp s1)).status = .Running) :
    coupledMemcpy f_mc m₀ kp (ProofLib.stripS kp s1) = ProofLib.stripS kp (f_mc s1) ∧
    VmPreserved s1 (f_mc s1) ∧
    AllocCallPreserved s1 (f_mc s1) := by
  let u := ProofLib.stripS kp s1
  have hperm_u : ∀ a, u.mem.perm a = (ProofLib.stripExecOutside kp m₀).perm a := fun a => by
    have hm : u.mem = ProofLib.stripExecOutside kp s1.mem := by cases s1; rfl
    rw [hm, ProofLib.strip_perm, ProofLib.strip_perm, hperm1 a]
  have hs1_eq : u.setMem (restorePerm m₀ u.mem) = s1 := by
    cases s1; dsimp only [u, ProofLib.stripS, State.setMem]
    rw [restorePerm_stripExecOutside_self kp hperm1]
  have hpre : MemcpyPre u := by
    by_contra hnpre
    have hstat : (coupledMemcpy f_mc m₀ kp u).status = .Exception "ext" := by
      unfold coupledMemcpy; simp only [hnpre, ↓reduceIte]; cases u; rfl
    rw [hstat] at hrb'; cases hrb'
  have hc_eq : coupledMemcpy f_mc m₀ kp u = ProofLib.stripS kp (f_mc s1) := by
    unfold coupledMemcpy
    simp only [eq_true hpre, eq_true hperm_u, ↓reduceIte, hs1_eq]
  rcases hpre with ⟨hrun_u, hsp_u, hrw_u, hread_u, hdisj_u⟩
  have hrun1 : s1.status = .Running := by cases s1; exact hrun_u
  have hsp1 : s1.spAligned = true := by cases s1; exact hsp_u
  have hr64 : ∀ r, u.readReg64 r = s1.readReg64 r := fun _ => by cases s1; rfl
  rw [hr64, hr64] at hrw_u hread_u
  rw [hr64, hr64, hr64] at hdisj_u
  have hm_rest : restorePerm m₀ u.mem = s1.mem := by
    have hm : u.mem = ProofLib.stripExecOutside kp s1.mem := by cases s1; rfl
    rw [hm, restorePerm_stripExecOutside_self kp hperm1]
  have hrw1 : s1.mem.RW (s1.readReg64 .x0) (s1.readReg64 .x2).toNat :=
    hm_rest ▸ restorePerm_rw hperm_u hrw_u
  have hread1 : s1.mem.Readable (s1.readReg64 .x1) (s1.readReg64 .x2).toNat :=
    hm_rest ▸ restorePerm_readable hperm_u hread_u
  obtain ⟨c, hfc⟩ := hf hrun1 hsp1 rfl rfl rfl rfl rfl hrw1 hread1 hdisj_u
  refine ⟨hc_eq, ?_, ?_⟩
  · rw [hfc]; exact vmPreserved_applyMemcpyClobber_writeBytes s1 _ _ _ c
  · rw [hfc]; exact allocCallPreserved_applyMemcpyClobber_vm s1 _ _ c

private theorem stripS_compress256Hook_vm (F : ShaState → List (BitVec 8) → ShaState)
    (p : BitVec 64 → Bool) (s : State) :
    compress256Hook F (ProofLib.stripS p s) = ProofLib.stripS p (compress256Hook F s) := by
  cases s
  dsimp only [ProofLib.stripS, compress256Hook, returnToLinkRegister,
    State.setMem, State.setPC, State.readReg64]
  rw [stripExecOutside_readShaState_vm, stripExecOutside_readBytes, stripExecOutside_writeBytes_vm]

private theorem vmPreserved_compress256Hook_vm (F : ShaState → List (BitVec 8) → ShaState)
    (s : State) : VmPreserved s (compress256Hook F s) := by
  dsimp only [compress256Hook, returnToLinkRegister]
  simp only [vmPreserved_setPC, vmPreserved_setMem_writeBytes, vmPreserved_refl_iff]

private theorem allocCallPreserved_compress256Hook_vm (F : ShaState → List (BitVec 8) → ShaState)
    (s : State) : AllocCallPreserved s (compress256Hook F s) := by
  cases s; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem option_or_isSome_vm {α : Type} (o₁ o₂ : Option α) :
    (o₁.or o₂).isSome = (o₁.isSome || o₂.isSome) := by cases o₁ <;> rfl

private theorem findSome?_isSome_congr_vm {α β γ : Type} (l : List α)
    (f : α → Option β) (g : α → Option γ) (h : ∀ x, (f x).isSome = (g x).isSome) :
    (l.findSome? f).isSome = (l.findSome? g).isSome := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.findSome?]
    cases hf : f x <;> cases hg : g x
    · exact ih
    · have hx := h x; rw [hf, hg] at hx; cases hx
    · have hx := h x; rw [hf, hg] at hx; cases hx
    · rfl

noncomputable def hmacNoMemsetExcHooks (F : ShaState → List (BitVec 8) → ShaState)
    (H : LibsignalHooks) (m₀ : Memory) (kp : BitVec 64 → Bool) :
    LibsignalHooks :=
  fun n =>
    if n = lsMemcpySym then (H lsMemcpySym).map (fun f_mc => coupledMemcpy f_mc m₀ kp)
    else if n = lsCompress256Sym then some (compress256Hook F)
    else (H n).map (fun _ s => s.setStatus (.Exception "ext"))

theorem hmacNoMemsetExcHooks_memcpy {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (m₀ : Memory) (kp : BitVec 64 → Bool) :
    HookSatExactMemcpy (hmacNoMemsetExcHooks F H m₀ kp) lsMemcpySym := by
  rcases h_mc with ⟨f_mc, hfH, hfEx⟩
  exact ⟨coupledMemcpy f_mc m₀ kp, by simp [hmacNoMemsetExcHooks, hfH],
    coupledMemcpy_exact hfEx m₀ kp⟩

theorem hmacNoMemsetExcHooks_compress (F : ShaState → List (BitVec 8) → ShaState)
    (H : LibsignalHooks) (m₀ : Memory) (kp : BitVec 64 → Bool) :
    hmacNoMemsetExcHooks F H m₀ kp lsCompress256Sym = some (compress256Hook F) := by
  have hne : lsCompress256Sym ≠ lsMemcpySym := by decide
  simp [hmacNoMemsetExcHooks, hne]

private theorem hmacNoMemsetExcHooks_isSome_vm {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks}
    (h_c256 : H lsCompress256Sym = some (compress256Hook F))
    (m₀ : Memory) (kp : BitVec 64 → Bool)
    (n : String) :
    (hmacNoMemsetExcHooks F H m₀ kp n).isSome = (H n).isSome := by
  unfold hmacNoMemsetExcHooks
  by_cases h1 : n = lsMemcpySym
  · subst h1; simp
  · by_cases h2 : n = lsCompress256Sym
    · subst h2; simp [h1, h_c256]
    · simp [h1, h2]

private theorem blockProgram_hmacNoMemsetExcHooks_externAt?_isSome_vm
    (lib : MultiPlacedLib) (pl : MultiPlacement) (i : Nat)
    {F : ShaState → List (BitVec 8) → ShaState} {H : LibsignalHooks}
    (h_c256 : H lsCompress256Sym = some (compress256Hook F))
    (m₀ : Memory) (kp : BitVec 64 → Bool)
    (pc : BitVec 64) :
    ((lib.blockProgram pl i (hmacNoMemsetExcHooks F H m₀ kp)).externAt? pc).isSome =
      ((lib.blockProgram pl i H).externAt? pc).isSome := by
  unfold Program.externAt? Program.hookAtOff? MultiPlacedLib.blockProgram PlacedLib.program
  dsimp only
  rw [option_or_isSome_vm, option_or_isSome_vm]
  rw [findSome?_isSome_congr_vm _
    (fun x : String × Nat =>
      if (x.2 == (pc - (lib.blockPlacement pl i).base).toNat) = true then
        hmacNoMemsetExcHooks F H m₀ kp x.1
      else none)
    (fun x : String × Nat =>
      if (x.2 == (pc - (lib.blockPlacement pl i).base).toNat) = true then H x.1 else none)]
  intro x
  cases h : (x.2 == (pc - (lib.blockPlacement pl i).base).toNat) <;>
    simp [hmacNoMemsetExcHooks_isSome_vm h_c256 m₀ kp]

private theorem findSome?_hmacNoMemsetExcHooks_cases_vm {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} {f_mc : State → State}
    (h_mc : H lsMemcpySym = some f_mc)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F))
    (m₀ : Memory) (kp : BitVec 64 → Bool) :
    ∀ (l : List (String × Nat)) {off : Nat} {f : State → State},
      (l.findSome? fun (n, o) => if o == off then hmacNoMemsetExcHooks F H m₀ kp n else none) =
        some f →
      (∀ s, (f s).status = .Exception "ext") ∨
      (f = coupledMemcpy f_mc m₀ kp ∧
        (l.findSome? fun (n, o) => if o == off then H n else none) = some f_mc) ∨
      (f = compress256Hook F ∧
        (l.findSome? fun (n, o) => if o == off then H n else none) = some (compress256Hook F))
  | [], _, _, h => by simp at h
  | (n, o) :: tl, off, f, h => by
    simp only [List.findSome?_cons] at h ⊢
    cases ho : o == off
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact findSome?_hmacNoMemsetExcHooks_cases_vm h_mc h_c256 m₀ kp tl h
    · simp only [ho, ↓reduceIte] at h ⊢
      unfold hmacNoMemsetExcHooks at h
      by_cases h1 : n = lsMemcpySym
      · subst h1; simp only [↓reduceIte, h_mc, Option.map, Option.some.injEq] at h; subst h
        rw [h_mc]; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · by_cases h2 : n = lsCompress256Sym
        · subst h2; simp only [h1, ↓reduceIte, Option.some.injEq] at h; subst h
          rw [h_c256]; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        · simp only [h1, h2, ↓reduceIte] at h
          cases hHn : H n with
          | none =>
            rw [hHn] at h; dsimp only [Option.map] at h ⊢
            exact findSome?_hmacNoMemsetExcHooks_cases_vm h_mc h_c256 m₀ kp tl h
          | some _ =>
            rw [hHn] at h; simp only [Option.map, Option.some.injEq] at h; subst h
            exact Or.inl fun s => by cases s; rfl

private theorem blockProgram_hmacNoMemsetExcHooks_externAt?_cases_vm
    {lib : MultiPlacedLib} {pl : MultiPlacement} {i : Nat}
    {F : ShaState → List (BitVec 8) → ShaState} {H : LibsignalHooks} {f_mc : State → State}
    (h_mc : H lsMemcpySym = some f_mc)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F))
    {m₀ : Memory} {kp : BitVec 64 → Bool}
    {pc : BitVec 64} {f : State → State}
    (h : (lib.blockProgram pl i (hmacNoMemsetExcHooks F H m₀ kp)).externAt? pc = some f) :
    (∀ s, (f s).status = .Exception "ext") ∨
    (f = coupledMemcpy f_mc m₀ kp ∧ (lib.blockProgram pl i H).externAt? pc = some f_mc) ∨
    (f = compress256Hook F ∧ (lib.blockProgram pl i H).externAt? pc = some (compress256Hook F)) := by
  unfold Program.externAt? Program.hookAtOff? MultiPlacedLib.blockProgram PlacedLib.program at h ⊢
  dsimp only at h ⊢
  have hnone : ∀ (l : List (String × Nat)),
      (l.findSome? fun (_ : String × Nat) => (none : Option (State → State))) = none := by
    intro l; induction l with | nil => rfl | cons _ _ ih => exact ih
  simp only [ite_self, hnone, Option.or_none] at h ⊢
  exact findSome?_hmacNoMemsetExcHooks_cases_vm h_mc h_c256 m₀ kp _ h

private theorem strip_codeLoaded_of_keep_vm {prog : Program} {m : Memory} (hL : prog.CodeLoaded m) :
    prog.CodeLoaded (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun k hk => ?_
  have hno := hL.no_wrap
  have hsub : prog.base + BitVec.ofNat 64 k - prog.base = BitVec.ofNat 64 k := by bv_omega
  have hkeep : ProofLib.progKeep prog (prog.base + BitVec.ofNat 64 k) = true := by
    unfold ProofLib.progKeep
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true hk
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]
  exact ⟨hL.byte_eq k hk, hL.perm_eq k hk, hL.isLazyFree_eq k hk⟩

private theorem strip_execOnlyIn_of_keep_vm (prog : Program) (m : Memory) :
    prog.ExecOnlyIn (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) := fun _ hpx =>
  of_decide_eq_true (ProofLib.strip_perm_x_imp hpx).2

private theorem steps_start_running_vm {Q : Program} {s sf : State}
    (h : Steps Q s sf) (hr : sf.status = .Running) : s.status = .Running := by
  cases h with
  | refl => exact hr
  | step h1 _ => cases h1 <;> assumption

private theorem step_P_extern_eq_vm {P : Program} {s1 s2 : State} {f : State → State}
    (hstep : Step P s1 s2) (hrun2 : s2.status = .Running)
    (heP : P.externAt? s1.pc = some f) :
    s2 = f s1 ∧ s1.mem.KeepsFrozen (f s1).mem ∧ (f s1).symtab = s1.symtab := by
  cases hstep with
  | @exec _ _ hfe => unfold Program.fetchMem at hfe; rw [heP] at hfe; simp at hfe
  | halt_unmapped _ _ he => rw [heP] at he; cases he
  | extern _ he hkf hsym =>
    rw [heP] at he; injection he with hff; subst hff; exact ⟨rfl, hkf, hsym⟩
  | extern_fault _ _ _ => cases s1; cases hrun2

private theorem step_P_exec_eq_vm {P : Program} {s1 s2 : State} {inst : Instr}
    (hstep : Step P s1 s2)
    (hfeP : P.fetchMem s1.mem s1.pc = some inst)
    (hnsvc0 : inst.isSvc0 = false) :
    s2 = execInst inst s1 := by
  have heP_none : P.externAt? s1.pc = none := by
    unfold Program.fetchMem at hfeP
    cases he : P.externAt? s1.pc with | none => rfl | some _ => simp [he] at hfeP
  cases hstep with
  | @exec _ _ hfe' =>
    rw [hfeP] at hfe'; injection hfe' with hi; subst hi
    exact Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0 s1
  | halt_unmapped _ hfe' _ => rw [hfeP] at hfe'; cases hfe'
  | extern _ he _ _ => rw [heP_none] at he; cases he
  | extern_fault _ he _ => rw [heP_none] at he; cases he

private theorem steps_hmacNoMemsetExc_lift_strip_allocVm
    (lib : MultiPlacedLib) (pl : MultiPlacement) (i : Nat)
    {F : ShaState → List (BitVec 8) → ShaState} {H : LibsignalHooks}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F))
    (m₀ : Memory)
    (hall_svc :
      (lib.blockProgram pl i
        (hmacNoMemsetExcHooks F H m₀ (ProofLib.progKeep (lib.blockProgram pl i H)))).allInstrs
      (fun ins => !ins.isSvc0) = true)
    (hall_msr :
      (lib.blockProgram pl i
        (hmacNoMemsetExcHooks F H m₀ (ProofLib.progKeep (lib.blockProgram pl i H)))).allInstrs
      (fun ins => !ins.isMsrTpidrEl0) = true)
    {s1' sf' : State}
    (hsteps : Steps
      (lib.blockProgram pl i
        (hmacNoMemsetExcHooks F H m₀ (ProofLib.progKeep (lib.blockProgram pl i H)))) s1' sf')
    (hrun_f : sf'.status = .Running) :
    let P := lib.blockProgram pl i H
    let Q := lib.blockProgram pl i (hmacNoMemsetExcHooks F H m₀ (ProofLib.progKeep P))
    ∀ (s1 sfP : State),
      s1' = ProofLib.stripS (ProofLib.progKeep Q) s1 →
      (∀ a, s1.mem.perm a = m₀.perm a) →
      Q.CodeLoaded s1.mem →
      Steps P s1 sfP →
      sfP.status = .Running →
      ∃ sf : State,
        Steps P s1 sf ∧
        VmPreserved s1 sf ∧
        AllocCallPreserved s1 sf ∧
        (sf' = ProofLib.stripS (ProofLib.progKeep Q) sf ∨ sf = sfP) := by
  rcases h_mc with ⟨f_mc, hfH, hfEx⟩
  intro P Q
  have hkp : ProofLib.progKeep Q = ProofLib.progKeep P := rfl
  induction hsteps with
  | refl =>
    intro s1 _ hs1 _ _ _ _
    exact ⟨s1, .refl s1, VmPreserved.refl s1, allocCallPreserved_refl s1, Or.inl hs1⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro s1 sfP hsa hperm1 hL1 hstepsP hrun_sfP
    cases hstepsP with
    | refl =>
      exact ⟨s1, .refl s1, VmPreserved.refl s1, allocCallPreserved_refl s1, Or.inr rfl⟩
    | @step _ s2P _ h1_P hrest_P =>
      have hr2P : s2P.status = .Running := steps_start_running_vm hrest_P hrun_sfP
      have hrb' : sb'.status = .Running := steps_start_running_vm hrest hrun_f
      subst hsa
      cases h1 with
      | halt_unmapped _ _ _ => cases s1; cases hrb'
      | extern_fault _ _ _ => cases s1; cases hrb'
      | extern hr1' he _ _ =>
        have hr1 : s1.status = .Running := by cases s1; exact hr1'
        have hpc_eq : (ProofLib.stripS (ProofLib.progKeep Q) s1).pc = s1.pc := by cases s1; rfl
        rw [hpc_eq] at he
        rcases blockProgram_hmacNoMemsetExcHooks_externAt?_cases_vm hfH h_c256 he with
          htrap | ⟨rfl, heP⟩ | ⟨rfl, heP⟩
        · rw [htrap] at hrb'; cases hrb'
        · obtain ⟨hs2P, hkf1, hsym1⟩ := step_P_extern_eq_vm h1_P hr2P heP
          rw [hs2P] at hrest_P
          have hstepP := Step.extern hr1 heP hkf1 hsym1
          rw [hkp] at hrb' ⊢
          obtain ⟨hc_eq, hvm1, hacp1⟩ := coupledMemcpy_running_step hfEx hperm1 hrb'
          have hperm2 : ∀ a, (f_mc s1).mem.perm a = m₀.perm a :=
            fun a => (hvm1.2.2.1 a).trans (hperm1 a)
          obtain ⟨sf, hsteps_rest, hvm_rest, hacp_rest, hor⟩ :=
            ih hrun_f (f_mc s1) sfP (by rw [hkp]; exact hc_eq) hperm2
              (hL1.of_keepsFrozen hkf1) hrest_P hrun_sfP
          rw [hkp] at hor
          exact ⟨sf, .step hstepP hsteps_rest, hvm1.trans hvm_rest,
            allocCallPreserved_trans hacp1 hacp_rest, hor⟩
        · obtain ⟨hs2P, hkf1, hsym1⟩ := step_P_extern_eq_vm h1_P hr2P heP
          rw [hs2P] at hrest_P
          have hstepP := Step.extern hr1 heP hkf1 hsym1
          have hvm1 := vmPreserved_compress256Hook_vm F s1
          have hperm2 : ∀ a, (compress256Hook F s1).mem.perm a = m₀.perm a :=
            fun a => (hvm1.2.2.1 a).trans (hperm1 a)
          obtain ⟨sf, hsteps_rest, hvm_rest, hacp_rest, hor⟩ :=
            ih hrun_f (compress256Hook F s1) sfP
              (stripS_compress256Hook_vm F (ProofLib.progKeep Q) s1) hperm2
              (hL1.of_keepsFrozen hkf1) hrest_P hrun_sfP
          exact ⟨sf, .step hstepP hsteps_rest, hvm1.trans hvm_rest,
            allocCallPreserved_trans (allocCallPreserved_compress256Hook_vm F s1) hacp_rest, hor⟩
      | @exec inst hr1' hfe' =>
        have hr1 : s1.status = .Running := by cases s1; exact hr1'
        have hL1' : Q.CodeLoaded (ProofLib.stripS (ProofLib.progKeep Q) s1).mem :=
          strip_codeLoaded_of_keep_vm hL1
        have hexec' : Q.ExecOnlyIn (ProofLib.stripS (ProofLib.progKeep Q) s1).mem :=
          strip_execOnlyIn_of_keep_vm Q s1.mem
        have hnsvc0 : inst.isSvc0 = false := by
          simpa using Program.fetchMem_of_allInstrs hall_svc hL1' hexec' _ inst hfe'
        have hnmsr : inst.isMsrTpidrEl0 = false := by
          simpa using Program.fetchMem_of_allInstrs hall_msr hL1' hexec' _ inst hfe'
        have hfe_P : P.fetchMem s1.mem s1.pc = some inst := by
          have hpc_eq : (ProofLib.stripS (ProofLib.progKeep Q) s1).pc = s1.pc := by cases s1; rfl
          have hmem_eq : (ProofLib.stripS (ProofLib.progKeep Q) s1).mem =
              ProofLib.stripExecOutside (ProofLib.progKeep Q) s1.mem := by cases s1; rfl
          rw [hpc_eq, hmem_eq] at hfe'
          unfold Program.fetchMem at hfe' ⊢
          have his : (Q.externAt? s1.pc).isSome = (P.externAt? s1.pc).isSome :=
            blockProgram_hmacNoMemsetExcHooks_externAt?_isSome_vm lib pl i h_c256
              m₀ (ProofLib.progKeep P) s1.pc
          rw [his] at hfe'
          cases heP : (P.externAt? s1.pc).isSome
          · simp only [heP, Bool.false_eq_true, ↓reduceIte] at hfe' ⊢
            by_cases hal_pc : s1.pc.toNat % 4 = 0
            · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfe' ⊢
              split at hfe'
              · contradiction
              · rename_i hce'
                have hce : s1.mem.canExec s1.pc 4 = true := by
                  simp only [Bool.not_eq_true', Bool.not_eq_false] at hce'
                  unfold Memory.canExec at hce' ⊢
                  rw [Memory.allPerm_iff] at hce' ⊢
                  intro k hk
                  have hxk := hce' k hk
                  rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
                have hr32 : (ProofLib.stripExecOutside (ProofLib.progKeep Q) s1.mem).read32 s1.pc =
                    s1.mem.read32 s1.pc := by simp [Memory.read32, ProofLib.strip_read8]
                rw [hr32] at hfe'
                simp only [hce, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                exact hfe'
            · simp only [hal_pc, ne_eq, not_false_eq_true, ↓reduceIte] at hfe'; contradiction
          · simp only [heP, ↓reduceIte] at hfe'; contradiction
        have hev_Q : Q.evalInst inst (ProofLib.stripS (ProofLib.progKeep Q) s1) =
            ProofLib.stripS (ProofLib.progKeep Q) (execInst inst s1) := by
          rw [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
        have hs2P := step_P_exec_eq_vm h1_P hfe_P hnsvc0
        rw [hs2P] at hrest_P
        have hstep_P : Step P s1 (execInst inst s1) := by
          have := Step.exec (prog := P) hr1 hfe_P
          rwa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] at this
        have hLQ_next : Q.CodeLoaded (execInst inst s1).mem := hstep_P.codeLoaded hL1
        have hbo1 := ProofLib.execInst_brk_oracle_of_not_isSvc0 hnsvc0 s1
        have hnsp1 := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1
        have htp1 := Arm64.execInst_tpidrEl0_of_not_isMsrTpidrEl0 hnmsr s1
        have hvm1 := hnsp1.toVmPreserved htp1
        have hperm2 : ∀ a, (execInst inst s1).mem.perm a = m₀.perm a :=
          fun a => (hvm1.2.2.1 a).trans (hperm1 a)
        obtain ⟨sf, hsteps_rest, hvm_rest, hacp_rest, hor⟩ :=
          ih hrun_f (execInst inst s1) sfP hev_Q hperm2 hLQ_next hrest_P hrun_sfP
        have hacp1 : AllocCallPreserved s1 (execInst inst s1) :=
          ⟨hbo1.2.2.2.2.2, hnsp1.1, hbo1.1, htp1, hbo1.2.2.1,
            execInst_projOracle_of_not_isSvc0 hnsvc0 s1, hstep_P.symtab_eq⟩
        exact ⟨sf, .step hstep_P hsteps_rest, hvm1.trans hvm_rest,
          allocCallPreserved_trans hacp1 hacp_rest, hor⟩

theorem blk379_noSvc0 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib_379.text = true := by decide +kernel
theorem blk379_noMsr :
    checkBlockNoMsrTpidrEl0 blkLib_379.text = true := by decide +kernel
theorem blk402_noSvc0 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib_402.text = true := by decide +kernel
theorem blk402_noMsr :
    checkBlockNoMsrTpidrEl0 blkLib_402.text = true := by decide +kernel
theorem blk425_noSvc0 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib_425.text = true := by decide +kernel
theorem blk425_noMsr :
    checkBlockNoMsrTpidrEl0 blkLib_425.text = true := by decide +kernel

theorem lift_block_to_379_vm [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactSat C.F H]
    {j : Nat} {blkLib : PlacedLib} {Pj : Program} [hcallee : IsLsBlockProg Pj j H]
    (hlib : blkLib = libsignalSessionLib.blockLib j)
    (hchk_svc : VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib.text = true)
    (hchk_msr : checkBlockNoMsrTpidrEl0 blkLib.text = true)
    (hj_lt : j < 619) (hj_unmut : (j ∈ libsignalMutatedBlocks) = false)
    {s : State} {PostP PostQ : State → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hrunsP : RunsTo (libsignalSessionLib.blockProgram lsmpl j H) s PostP)
    (hrunsQ : RunsTo
      (libsignalSessionLib.blockProgram lsmpl j
        (hmacNoMemsetExcHooks C.F H s.mem
          (ProofLib.progKeep (libsignalSessionLib.blockProgram lsmpl j H))))
      (ProofLib.stripS (ProofLib.progKeep
        (libsignalSessionLib.blockProgram lsmpl j
          (hmacNoMemsetExcHooks C.F H s.mem
            (ProofLib.progKeep (libsignalSessionLib.blockProgram lsmpl j H))))) s) PostQ)
    (hrunP : ∀ s', PostP s' → s'.status = .Running)
    (hrunQ : ∀ s', PostQ s' → s'.status = .Running)
    (hunstrip : ∀ sf, VmPreserved s sf →
      PostQ (ProofLib.stripS (ProofLib.progKeep
        (libsignalSessionLib.blockProgram lsmpl j
          (hmacNoMemsetExcHooks C.F H s.mem
            (ProofLib.progKeep (libsignalSessionLib.blockProgram lsmpl j H))))) sf) → PostP sf) :
    RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s PostP := by
  subst hlib
  intro hL379
  let kp := ProofLib.progKeep (libsignalSessionLib.blockProgram lsmpl j H)
  let Q := libsignalSessionLib.blockProgram lsmpl j (hmacNoMemsetExcHooks C.F H s.mem kp)
  have hLj : (libsignalSessionLib.blockProgram lsmpl j H).CodeLoaded s.mem :=
    hcl j (Nat.lt_trans hj_lt (by decide)) hj_unmut H (fun _ => none) Syscall.standard
  have hall_svc : Q.allInstrs (fun ins => !ins.isSvc0) = true :=
    blockProgram_rebase_allInstrs_not_isSvc0 libsignalSessionLib lsmpl j hchk_svc
  have hall_msr : Q.allInstrs (fun ins => !ins.isMsrTpidrEl0) = true :=
    blockProgram_allInstrs_not_isMsrTpidrEl0 libsignalSessionLib lsmpl j
      (hmacNoMemsetExcHooks C.F H s.mem kp) hchk_msr
  have hLQ : Q.CodeLoaded s.mem := hLj.of_base_code rfl rfl
  have hLQ_strip : Q.CodeLoaded (ProofLib.stripS (ProofLib.progKeep Q) s).mem := by
    have hm : (ProofLib.stripS (ProofLib.progKeep Q) s).mem =
        ProofLib.stripExecOutside (ProofLib.progKeep Q) s.mem := by cases s; rfl
    rw [hm]; exact strip_codeLoaded_of_keep_vm hLQ
  obtain ⟨sfP, hstepsP, ⟨htrP, hvregsP⟩, hPostP, _⟩ := hrunsP hLj
  obtain ⟨sf', hstepsQ, ⟨htr', hvregs'⟩, hPost', _⟩ := hrunsQ hLQ_strip
  obtain ⟨sf, hst_j, hvm, hacp, hsf_eq | rfl⟩ :=
    steps_hmacNoMemsetExc_lift_strip_allocVm libsignalSessionLib lsmpl j hH.memcpy hH.compress256
      s.mem hall_svc hall_msr hstepsQ (hrunQ sf' hPost') s sfP rfl (fun _ => rfl) hLQ hstepsP
      (hrunP sfP hPostP)
  · have htr : sf.trace = s.trace := by
      have h1 : sf'.trace = sf.trace := by rw [hsf_eq]; cases sf; rfl
      have h2 : (ProofLib.stripS (ProofLib.progKeep Q) s).trace = s.trace := by cases s; rfl
      exact h1.symm.trans (htr'.trans h2)
    have hvregs : calleeSavedVRegs sf = calleeSavedVRegs s := by
      have h1 : calleeSavedVRegs sf' = calleeSavedVRegs sf := by rw [hsf_eq]; cases sf; rfl
      have h2 : calleeSavedVRegs (ProofLib.stripS (ProofLib.progKeep Q) s) = calleeSavedVRegs s := by
        cases s; rfl
      exact h1.symm.trans (hvregs'.trans h2)
    have hPost : PostP sf := hunstrip sf hvm (hsf_eq ▸ hPost')
    have hcaller : IsLsBlockProg ((blkPC_379).rebase (blkPl_379).base H) 379 H := inferInstance
    have hext : ∀ pc, (libsignalSessionLib.blockProgram lsmpl j H).externAt? pc =
        ((blkPC_379).rebase (blkPl_379).base H).externAt? pc := fun pc => by
      rw [hcaller.eq_blockProgram,
        ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
          (hcallee.externs_eq.trans hcaller.externs_eq.symm)]
    have hsvc : (libsignalSessionLib.blockProgram lsmpl j H).svc =
        ((blkPC_379).rebase (blkPl_379).base H).svc := by rw [hcaller.eq_blockProgram]; rfl
    have hst_379 := Steps.of_sameHooks hext hsvc hst_j
    exact ⟨sf, hst_379, hvm, fun _ => hacp, htr, hvregs, hPost, hst_379.codeLoaded hL379⟩
  · have hcaller : IsLsBlockProg ((blkPC_379).rebase (blkPl_379).base H) 379 H := inferInstance
    have hext : ∀ pc, (libsignalSessionLib.blockProgram lsmpl j H).externAt? pc =
        ((blkPC_379).rebase (blkPl_379).base H).externAt? pc := fun pc => by
      rw [hcaller.eq_blockProgram,
        ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
          (hcallee.externs_eq.trans hcaller.externs_eq.symm)]
    have hsvc : (libsignalSessionLib.blockProgram lsmpl j H).svc =
        ((blkPC_379).rebase (blkPl_379).base H).svc := by rw [hcaller.eq_blockProgram]; rfl
    have hst_379 := Steps.of_sameHooks hext hsvc hst_j
    exact ⟨sf, hst_379, hvm, fun _ => hacp, htrP, hvregsP, hPostP, hst_379.codeLoaded hL379⟩

theorem placed_memset_budget_optAlloc_steps_sat [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_memset : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    {s : State} {dst lr : BitVec 64} {val : BitVec 8} {len : Nat}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsMemsetSym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : (s.readReg64 .x1).truncate 8 = val)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hsp_al : (s.sp &&& 15#64) = 0#64)
    (hrw : s.mem.RW dst len)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    ∃ s' : State,
      Steps prog s s' ∧
      VmPreserved s s' ∧
      (ProgMemsetAllocVm prog → AllocCallPreserved s s') ∧
      s'.trace = s.trace ∧
      calleeSavedVRegs s' = calleeSavedVRegs s ∧
      s'.pc = lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.readReg64 .x0 = dst ∧
      s.mem.KeepsFrozen s'.mem ∧
      s'.mem.readBytes dst len = List.replicate len val ∧
      S2Frame s.mem s'.mem [(dst, len)] ∧
      AgreesOn (fun a => (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false)
        s'.mem (s.mem.writeBytes dst (List.replicate len val)) := by
  obtain ⟨f, hfH, hfOk⟩ := h_memset
  have hhook : prog.externAt? s.pc = some f := by
    rw [hpc, ls_externAt?_of_mem (by decide) hi hunmut, hfH]
  obtain ⟨hkf, hsym, hret, hcc, hvm, hx0', htr', hread', hs2', hag'⟩ :=
    hookOk_sessionMemsetRegionBudget_elim hfOk hrun hx0 hx1 hx2 hsp_al hrw
  have hacp : ProgMemsetAllocVm prog → AllocCallPreserved s (f s) := by
    rintro ⟨f', hext', hfOk_acp⟩
    have hff' : f' = f := Option.some.inj (hext'.symm.trans (hpc ▸ hhook))
    subst hff'
    have hlen_le : len ≤ 2 ^ 64 := by rw [← hx2]; have := (s.readReg64 .x2).isLt; omega
    let hP : Heap := regionHeap dst len s.mem
    have hpP : (memRegion dst len) hP :=
      ((IsBlock.memRegion dst len).iff hP).mpr ⟨s.mem, trivial, rfl⟩
    have hmP : hP.Matches s.mem := IsBlock.regionHeap_matches dst len s.mem hrw
    let R_comp : SepProp := ⟨fun h => h = fullComplementHeap hP s.mem⟩
    have hsep_pre : s.mem ⊨ memRegion dst len ∗ R_comp :=
      Satisfies.sepConj_intro (disjoint_fullComplementHeap hP s.mem) hpP rfl
        (Heap.Matches.union hmP (matches_fullComplementHeap hP s.mem))
    have hx1_32 : (s.readReg32 .x1).truncate 8 = val := by
      rw [State.readReg32, truncate8_truncate32, hx1]
    have hpre_full : s.mem ⊨
        (withAllocVmPreserved sessionMemsetRegionSpec).pre (dst, val, len) s ∗ R_comp := by
      dsimp only [withAllocVmPreserved, sessionMemsetRegionSpec, memsetRegionSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1_32, hx2, hlen_le⟩, hsep_pre⟩
    have hsp_aligned : s.spAligned = true := by simpa [State.spAligned] using hsp_al
    obtain ⟨-, -, hout⟩ := hfOk_acp (dst, val, len) R_comp s hrun hpre_full hsp_aligned
    rcases hout with ⟨-, -, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
    · dsimp only [withAllocVmPreserved] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
      exact hpost.1.1
    · exact False.elim (not_satisfies_false_sepConj hp)
    · exact False.elim (not_satisfies_false_sepConj he)
    · exact False.elim (not_satisfies_false_sepConj ho)
  exact ⟨f s, .step (Step.extern hrun hhook hkf hsym) (.refl (f s)),
    hvm, hacp, htr', hcc.2.2.2.2.2.2.2.2.2.2.2.2, hret.1.trans hlr, hret.2.2, hcc,
    hx0', hkf, hread', hs2', hag'⟩

theorem mem_setMem (s : State) (m : Memory) : (s.setMem m).mem = m := rfl

@[local simp, local arm64_norm]
theorem extractLsb'_0_64_zero128 : BitVec.extractLsb' 0 64 0#128 = 0#64 := rfl

@[local simp, local arm64_norm]
theorem extractLsb'_64_64_zero128 : BitVec.extractLsb' 64 64 0#128 = 0#64 := rfl

theorem stripS_mem (kp : BitVec 64 → Bool) (s : State) :
    (ProofLib.stripS kp s).mem = ProofLib.stripExecOutside kp s.mem := by cases s; rfl

theorem stripS_read8 (kp : BitVec 64 → Bool) (s : State) (a : BitVec 64) :
    (ProofLib.stripS kp s).mem.read8 a = s.mem.read8 a := by
  cases s; simp [ProofLib.stripS, ProofLib.strip_read8]

theorem stripS_read64 (kp : BitVec 64 → Bool) (s : State) (a : BitVec 64) :
    (ProofLib.stripS kp s).mem.read64 a = s.mem.read64 a := by
  cases s; simp [ProofLib.stripS, Memory.read64, ProofLib.strip_read8]

theorem stripS_readBytes (kp : BitVec 64 → Bool) (s : State) (a : BitVec 64) (n : Nat) :
    (ProofLib.stripS kp s).mem.readBytes a n = s.mem.readBytes a n := by
  rw [stripS_mem, stripExecOutside_readBytes]

theorem stripS_hmacSt (kp : BitVec 64 → Bool)
    {F : ShaState → List (BitVec 8) → ShaState} {s : State} {a : BitVec 64}
    {key msg : List (BitVec 8)} :
    HmacSt (ProofLib.stripS kp s).mem a F key msg ↔ HmacSt s.mem a F key msg := by
  unfold HmacSt
  simp only [stripS_read8, stripS_read64, stripS_readBytes]

theorem stripS_hmacStN (kp : BitVec 64 → Bool)
    {F : ShaState → List (BitVec 8) → ShaState} {s : State} {a : BitVec 64}
    {key pfx tail : List (BitVec 8)} :
    HmacStN (ProofLib.stripS kp s).mem a F key pfx tail ↔ HmacStN s.mem a F key pfx tail := by
  unfold HmacStN
  simp only [stripS_read8, stripS_read64, stripS_readBytes]

theorem stripS_finSaved (kp : BitVec 64 → Bool) (s0 s : State) :
    FinSaved (ProofLib.stripS kp s0) ((ProofLib.stripS kp s0).sp - 144#64)
      (ProofLib.stripS kp s).mem ↔
    FinSaved s0 (s0.sp - 144#64) s.mem := by
  have hsp0 : (ProofLib.stripS kp s0).sp = s0.sp := by cases s0; rfl
  have hr : ∀ r, (ProofLib.stripS kp s0).readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
  unfold FinSaved
  simp only [hsp0, hr, stripS_read64]

theorem stripS_hsaved (kp : BitVec 64 → Bool) (s0 s : State) :
    HSaved (ProofLib.stripS kp s0) (ProofLib.stripS kp s).mem ↔ HSaved s0 s.mem := by
  have hsp0 : hsp (ProofLib.stripS kp s0) = hsp s0 := by cases s0; rfl
  have hr : ∀ r, (ProofLib.stripS kp s0).readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
  have h64 : ∀ off, (ProofLib.stripS kp s).mem.read64 (hsp (ProofLib.stripS kp s0) + off) =
      s.mem.read64 (hsp s0 + off) := fun off => by rw [hsp0, stripS_read64]
  constructor <;> rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  · rw [h64, hr] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  · exact ⟨by rw [h64, hr]; exact h0, by rw [h64, hr]; exact h1,
      by rw [h64, hr]; exact h2, by rw [h64, hr]; exact h3,
      by rw [h64, hr]; exact h4, by rw [h64, hr]; exact h5,
      by rw [h64, hr]; exact h6, by rw [h64, hr]; exact h7,
      by rw [h64, hr]; exact h8, by rw [h64, hr]; exact h9,
      by rw [h64, hr]; exact h10, by rw [h64, hr]; exact h11⟩

theorem unstrip_finCommon {kp : BitVec 64 → Bool} {s0 s : State}
    (hc : FinCommon (ProofLib.stripS kp s0) (ProofLib.stripS kp s))
    (hperm : ∀ a, s.mem.perm a = s0.mem.perm a) :
    FinCommon s0 s := by
  rcases hc with ⟨hst, hsp_c, hx29, hx26, hx27, hx28, hsav, hfr⟩
  have hr0 : ∀ r, (ProofLib.stripS kp s0).readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
  have hsp0 : (ProofLib.stripS kp s0).sp = s0.sp := by cases s0; rfl
  rw [stripS_mem, stripS_mem, hr0, hr0, hsp0] at hfr
  exact ⟨(by cases s; exact hst), (by cases s0; cases s; exact hsp_c),
    (by cases s0; cases s; exact hx29), (by cases s0; cases s; exact hx26),
    (by cases s0; cases s; exact hx27), (by cases s0; cases s; exact hx28),
    (stripS_finSaved kp s0 s).mp hsav, unstrip_frame hfr hperm⟩

theorem unstrip_hcommon {kp : BitVec 64 → Bool} {okmLen : Nat} {s0 s : State}
    (hc : HCommon okmLen (ProofLib.stripS kp s0) (ProofLib.stripS kp s))
    (hperm : ∀ a, s.mem.perm a = s0.mem.perm a) :
    HCommon okmLen s0 s := by
  rcases hc with ⟨hst, hsp_c, hx29, hsav, hfr⟩
  have hr0 : (ProofLib.stripS kp s0).readReg64 .x6 = s0.readReg64 .x6 := by cases s0; rfl
  have hsp0 : hsp (ProofLib.stripS kp s0) = hsp s0 := by cases s0; rfl
  unfold HFrame at hfr
  rw [stripS_mem, stripS_mem, hr0, hsp0] at hfr
  exact ⟨(by cases s; exact hst), (by cases s0; cases s; exact hsp_c),
    (by cases s0; cases s; exact hx29), (stripS_hsaved kp s0 s).mp hsav, unstrip_frame hfr hperm⟩

theorem unstrip_hexpCommon {kp : BitVec 64 → Bool}
    {F : ShaState → List (BitVec 8) → ShaState} {prk info : List (BitVec 8)}
    {infoA : BitVec 64} {okmLen : Nat} {s0 s : State}
    (he : HExpCommon F prk info infoA okmLen (ProofLib.stripS kp s0) (ProofLib.stripS kp s))
    (hperm : ∀ a, s.mem.perm a = s0.mem.perm a) :
    HExpCommon F prk info infoA okmLen s0 s := by
  rcases he with ⟨hc, hm0, hm8, hm16, hm24, hhm⟩
  have hsp0 : hsp (ProofLib.stripS kp s0) = hsp s0 := by cases s0; rfl
  rw [hsp0, stripS_read64] at hm0 hm8 hm16 hm24
  rw [hsp0, stripS_hmacSt] at hhm
  exact ⟨unstrip_hcommon hc hperm, hm0, hm8, hm16, hm24, hhm⟩

theorem stripS_hcommon_refl (kp : BitVec 64 → Bool) {okmLen : Nat} {s0 s : State}
    (hc : HCommon okmLen (s0.setMem s.mem) s) :
    HCommon okmLen (ProofLib.stripS kp (s0.setMem s.mem)) (ProofLib.stripS kp s) := by
  rcases hc with ⟨hst, hsp_c, hx29, hsav, _⟩
  have hmem_eq : (ProofLib.stripS kp (s0.setMem s.mem)).mem = (ProofLib.stripS kp s).mem := by
    cases s0; cases s; rfl
  refine ⟨(by cases s; exact hst), (by cases s0; cases s; exact hsp_c),
    (by cases s0; cases s; exact hx29), (stripS_hsaved kp (s0.setMem s.mem) s).mpr hsav, ?_⟩
  unfold HFrame
  rw [hmem_eq]
  exact Frame.refl _ _

theorem stripS_hexpCommon_refl (kp : BitVec 64 → Bool)
    {F : ShaState → List (BitVec 8) → ShaState} {prk info : List (BitVec 8)}
    {infoA : BitVec 64} {okmLen : Nat} {s0 s : State}
    (he : HExpCommon F prk info infoA okmLen (s0.setMem s.mem) s) :
    HExpCommon F prk info infoA okmLen (ProofLib.stripS kp (s0.setMem s.mem))
      (ProofLib.stripS kp s) := by
  rcases he with ⟨hc, hm0, hm8, hm16, hm24, hhm⟩
  have hsp0 : hsp (ProofLib.stripS kp (s0.setMem s.mem)) = hsp (s0.setMem s.mem) := by
    cases s0; cases s; rfl
  refine ⟨stripS_hcommon_refl kp hc, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsp0, stripS_read64]; exact hm0
  · rw [hsp0, stripS_read64]; exact hm8
  · rw [hsp0, stripS_read64]; exact hm16
  · rw [hsp0, stripS_read64]; exact hm24
  · rw [hsp0, stripS_hmacSt]; exact hhm


end LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetVmSat
