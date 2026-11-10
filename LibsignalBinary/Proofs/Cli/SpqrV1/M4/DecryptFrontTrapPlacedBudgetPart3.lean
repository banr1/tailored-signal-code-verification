/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.VerifyMacTrapPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
meta import Lean -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceSecondHalf
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.UuidFsDecodeHex32Placed
import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudgetSat
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSlice
import LibsignalBinary.Proofs.TripleRatchet.InImage.UuidTryParse.ParserTryParse
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.CallsBudget
import LibsignalBinary.Proofs.TripleRatchet.Mac.VerifyBudget
import ProofLib.SepLogic.Entry
import ProofLib.SepLogic.WP.Apply
/-!
# Budget-Threaded CLI Block `433` Segment `S7` Seam

Proves `s7_433_cli` (`S7SeamPlaced`) on Block `433` under `[LibsignalPlacement]` and
`RustCliAllocBudget M`.
-/
@[expose] public section
set_option autoImplicit false
namespace LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptFrontTrapPlacedBudgetPart3
open Arm64 ProofLib SepProp
open CryptoGames.HMAC (ShaState)
open CryptoVerification (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement LibsignalRoLoaded blkLib_254 blkLib_eq_114 blkLib_eq_254 blkPC_60 blkPC_61 blkPC_114 blkPC_252
  blkPC_254 blkPC_255 blkPl_60 blkPl_61 blkPl_114 blkPl_252 blkPl_254 blkPl_255 libsignalSessionLib lsProg_114 ls_hook_ok_ultra_of_mem ls_subroutine_ok_cl_of_block ls_subroutine_ok_cl_of_plain
  ls_subroutine_ok_of_block lsmpl sepWP_seq_lscl subroutine_ok_withLsCodeLoaded_of_plain withLsCl withLsCodeLoaded)
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook)
open CryptoVerification.LibsignalHmac (compress256Hook)
open CryptoVerification.LibsignalSession.CryptoHmacSha256 (CallingConventionPreserved_of_calleeSaved Frame HmacSt disjointRegions_of_ro_rw hookMemset_eq_memsetHook lsCompress256Sym
  lsMemcpySym lsMemsetSym lsSha256IVAddr new_from_slice_placed_run rodata_placed_sha256IV)
open CryptoVerification.LibsignalTripleRatchet (LibsignalCodeRoLoaded SpqrModel keys_ls_subroutine_ok_of_block_cro newFromSliceSpec newFromSliceStack
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded uuidErrParseOther uuidResultAt uuidTryParseCodeSpec uuidTryParseSpec withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer (isBlock_nfsResult)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (blkPC_434 blkPl_434 instIsLsBlockProg_434)
open CryptoVerification.LibsignalTripleRatchet.InImage.UuidTryParse (ParserRegsPreserved braced_all_eq braced_ne_0 braced_ne_37 decodeHex32ResultAt_sp52_none decodeHex32ResultAt_sp52_some
  decodeHex32ResultAt_sp88_none decodeHex32ResultAt_sp88_some decodeHex32Spec eq_ofNat_of_toNat_eq exists_36_parts exists_38_parts exists_45_parts len_eq_of_reg_eq len_ne_of_reg_ne
  memRegion_out17_split memRegion_out28_split memRegion_out32_split memRegion_sp52_17_none memRegion_sp52_17_some memRegion_sp56_17_split memRegion_sp88_17_none memRegion_sp88_17_some
  memRegion_sp88_32_for_hyphen memRegion_sp88_32_for_simple parseHyphenated_all_eq parseHyphenated_ne_8 parseHyphenated_ne_13 parseHyphenated_ne_18 parseHyphenated_ne_23
  parseHyphenated_of_parts parserTryParseResultAt parserTryParseResultAt_some_eq parserTryParseResultAt_sp56_none parserTryParseResultAt_sp56_some parserTryParseSpec sepWP_parser_branch
  sepWP_parser_hyph36 stackAt_parser_split stackAt_uuid_split subroutine_ok_of_sepWP_simple urn_all_eq uuidResultAt_some_eq uuidTryParse_of_other_len)
open CryptoVerification.LibsignalTripleRatchetRepr (decodeHex32 parseHyphenated parseSimple uuidTryParse)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced cliHookTablePlaced lsRustAllocSymCli lsRustAllocZeroedSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli lsStringCloneSym)
open CryptoVerification.SignalSession.Cli.MainHops.UuidFs (decodeHex32_placed_okFs)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_other cliGhostExterns_shim)
open CryptoVerification.SignalSession.Cli.Slots (cliGhostExterns_sat_of_cliExternsPlaced compress256_row_placed)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.VerifyMacTrapPlacedBudget (s7Env verifyMac_433_placed_ok)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget (S7SeamPlaced)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux (hmacExcHooks hmacExcHooks_compress hmacExcHooks_memcpy runsTo_block_lift_vm stripExecOutside_readBytes stripExecOutside_readable stripExecOutside_rw unstrip_frame)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks cliExternsPlaced_alloc_budget_sat cliExternsPlaced_blackBox_budget_sat cliExternsPlaced_compress256Multi_budget_sat cliExternsPlaced_dealloc_budget_sat cliExternsPlaced_exactMemcpy_sat cliExternsPlaced_noAllocShim_budget_sat cliExternsPlaced_sessionMemcpyRegion_budget_sat cliExternsPlaced_sessionMemsetRegion_budget_sat cliExternsPlaced_shim_budget_sat)
open LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudgetSat (new_from_slice_placed_cro_budget_ok_at_block_sat)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget (checkBlockSafeVm isTotalTrapHooks_vmTrapHooks sepWP_lsBlock_vmPreserved stripS_readReg64 stripS_sp stripS_trace vmTrapHooks)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShim_hookOk)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget (public_key_serialize_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.CallsBudget (parse_sid_placed_ok_at_of_code)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget (uuidTryParseCodeBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Mac.ComputeBudgetAux (newFromSliceBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Mac.VerifyBudget (verifyMacWithAddresses_placed_cro_ok)
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
local elab "erase_hkdf_norm" : command => Lean.Elab.Command.liftCoreM do
  for n in [``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp, ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp,
            ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592, ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592] do
    Lean.Attribute.erase n `arm64_norm
erase_hkdf_norm
private theorem sepWP_ret_vm {α : Type} {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)} {spec : Spec α} {x : α} {R : SepProp} {s0 s : State} {Pre : SepProp}
    (hvm0 : VmPreserved s0 s) (hwp : SepWP (P.rebase b Hk) (s0.readReg64 .x30) s Pre (fun sf P_f => VmPreserved s sf ∧ ((sf.mem ⊨ P_f ∗ R → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf))) :
    SepWP (P.rebase b Hk) (s0.readReg64 .x30) s Pre (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (withVmPreserved spec).post x s0 sf ∗ R) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) :=
  SepWP.mono hwp fun _ _ _ _ ⟨hvm1, hm, hsp, hcs⟩ => ⟨fun hsat => by dsimp only [withVmPreserved]; rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hvm0.trans hvm1, hm hsat⟩, hsp, hcs⟩
private theorem sepWP_strip_vm {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)} {Rest : State → SepProp} {R : SepProp} {s0 s : State} {Pre : SepProp}
    (hvm0 : VmPreserved s0 s) (hwp : SepWP (P.rebase b Hk) (s0.readReg64 .x30) s Pre (fun sf Q => VmPreserved s sf ∧ ((sf.mem ⊨ Q ∗ R → sf.mem ⊨ Rest sf) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf))) :
    SepWP (P.rebase b Hk) (s0.readReg64 .x30) s Pre (fun sf Q => (sf.mem ⊨ Q ∗ R → sf.mem ⊨ ⌜VmPreserved s0 sf⌝ ∗ Rest sf) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) :=
  SepWP.mono hwp fun _ _ _ _ ⟨hvm1, hm, hsp, hcs⟩ => ⟨fun hsat => by rw [satisfies_pure_sepConj]; exact ⟨hvm0.trans hvm1, hm hsat⟩, hsp, hcs⟩
private theorem sepWP_lscl_vm_step [LibsignalPlacement] {P : Program} {b mid target : BitVec 64} {Hk : String → Option (State → State)} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hwp : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (LibsignalCodeLoaded lsmpl sm.mem → VmPreserved s sm → SepWP (P.rebase b Hk) target sm Pm post))) :
    SepWP (P.rebase b Hk) target s Pre post := sepWP_seq_lscl hcl (mid := mid) (SepWP.mono hwp fun _ _ _ _ ⟨hvm, hk⟩ hcl' => hk hcl' hvm)
private theorem vm_chain {s0 s1 s2 : State} (h01 : VmPreserved s0 s1) (h12 : VmPreserved s1 s2) : VmPreserved s0 s2 := h01.trans h12
private theorem mem_setMem (s : State) (m : Memory) : (s.setMem m).mem = m := by cases s; rfl
private theorem vm_of_fields {s0 sm s' : State} (hvm : VmPreserved s0 sm) (h1 : s'.brkStart = sm.brkStart) (h2 : s'.brk = sm.brk) (h3 : s'.tpidrEl0 = sm.tpidrEl0)
    (h4 : s'.physMemAvail = sm.physMemAvail) (hm : s'.mem = sm.mem) (hfs : s'.fs = sm.fs) : VmPreserved s0 s' :=
  hvm.trans ⟨⟨h1, h2, h3⟩, h4, fun _ => hm ▸ rfl, LibsignalBinary.Heap.FdsHiFrame.of_fs_eq hfs⟩
local macro "vm_eq " h:term : tactic => `(tactic| refine vm_of_fields $h ?_ ?_ ?_ ?_ ?_ ?_ <;> ((try simp only [wp_norm, arm64_norm, mem_setMem]); try rfl))
private theorem blk254_safeVm : checkBlockSafeVm blkLib_254.text = true := by decide +kernel
private theorem decodeHex32_placed_vm_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_254).rebase (blkPl_254).base H) (blkPl_254).base (withVmPreserved decodeHex32Spec) := by
  apply subroutine_ok_of_sepWP_simple; intro x R s0 hpc hrun hsp; let Ptrap := (blkPC_254).rebase (blkPl_254).base vmTrapHooks; let keep := ProofLib.progKeep Ptrap
  refine sepWP_lsBlock_vmPreserved (Ptrap := Ptrap) blkLib_eq_254 isTotalTrapHooks_vmTrapHooks blk254_safeVm
    (post' := fun sf' P_f => P_f = decodeHex32Spec.keepsFs.post x (ProofLib.stripS keep s0) sf' ∗ emp ∧ sf'.sp = s0.sp ∧ CalleeSavedPreserved (ProofLib.stripS keep s0) sf') ?_ ?_
  · refine SepWP.call_subroutine_frame (F := emp) (decodeHex32_placed_okFs vmTrapHooks) hpc hrun hsp rfl (fun R' hm => ?_)
      (fun _ _ _ => by dsimp only [Spec.keepsFs, decodeHex32Spec]; exact not_satisfies_false_sepConj)
      (fun _ _ _ _ => by dsimp only [Spec.keepsFs, decodeHex32Spec]; exact not_satisfies_false_sepConj) (fun sf' hpc' hrun' hsp' hcs' => SepWP.done hpc' hrun' ⟨rfl, hsp', hcs'⟩)
    dsimp only [withVmPreserved, Spec.keepsFs, decodeHex32Spec] at hm ⊢; simpa only [stripS_readReg64, stripS_sp, emp_sepConj] using hm
  · rintro sf _ hvm ⟨rfl, hsp_sf, hcs_sf⟩; refine ⟨fun hm => ?_, by simpa using hsp_sf, by simpa [CalleeSavedPreserved.iff_regs] using hcs_sf⟩
    dsimp only [withVmPreserved, Spec.keepsFs, decodeHex32Spec] at hm ⊢; simp only [stripS_sp, stripS_trace, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hm ⊢; exact ⟨hvm, hm.2.1, hm.2.2⟩
private abbrev parserPostVm (p : BitVec 64) (bs : List (BitVec 8)) (out17 : BitVec 64) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (withVmPreserved parserTryParseSpec).post (p, bs, out17) s0 sf ∗ R) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf
private abbrev parserFrameSep (sliceP : SepProp) (out17 out_w0 out_w1 : BitVec 64) (out_b2 : BitVec 8) (s0 : State) : SepProp :=
  ((sliceP ∗ (out17 ↦₆₄ out_w0) ∗ ((out17 + 8#64) ↦₆₄ out_w1) ∗ ((out17 + 16#64) ↦₈ out_b2)) ∗
   (stackAt (s0.sp - 96#64) 0x20 ∗ memRegion (s0.sp - 96#64) 8 ∗ memRegion (s0.sp - 88#64) 32 ∗ memRegion (s0.sp - 56#64) 4 ∗ memRegion (s0.sp - 52#64) 17 ∗
    memRegion (s0.sp - 35#64) 3 ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
private theorem wp_err_vm_placed [LibsignalPlacement] (hooks : LibsignalHooks) (p : BitVec 64) (bs : List (BitVec 8)) (out17 : BitVec 64) (R : SepProp)
    (out_w0 out_w1 : BitVec 64) (out_b2 : BitVec 8) (s0 s : State) (hsp_align : s0.spAligned = true) (huuid : uuidTryParse bs = none) (hpc : s.pc = (blkPl_255).base + bv% (420))
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64) (hx8 : s.readReg64 .x8 = out17) (htr : s.trace = s0.trace) (hvm0 : VmPreserved s0 s) (hcs : ParserRegsPreserved s0 s) :
    SepWP ((blkPC_255).rebase (blkPl_255).base hooks) (s0.readReg64 .x30) s (parserFrameSep (p ↦ₛ bs) out17 out_w0 out_w1 out_b2 s0) (parserPostVm p bs out17 s0 R) := by
  rcases hcs with ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩; dsimp only [parserFrameSep, parserPostVm]; apply sepWP_ret_vm hvm0
  by_vm_steps (wp_steps; dsimp only [parserTryParseSpec]; simp only [huuid, parserTryParseResultAt, stackAt_parser_split s0.sp]; wp_done)
private theorem wp_simple_vm_placed [LibsignalPlacement] (hooks : LibsignalHooks) (p : BitVec 64) (bs : List (BitVec 8)) (out17 : BitVec 64) (R : SepProp)
    (out_w0 out_w1 : BitVec 64) (out_b2 : BitVec 8) (s0 s : State) (hcl0 : LibsignalCodeLoaded lsmpl s.mem) (hsp_align : s0.spAligned = true) (hlen : bs.length = 32)
    (hpc : s.pc = (blkPl_255).base + bv% (328)) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = p) (hx8 : s.readReg64 .x8 = out17)
    (htr : s.trace = s0.trace) (hvm0 : VmPreserved s0 s) (hcs : ParserRegsPreserved s0 s) :
    SepWP ((blkPC_255).rebase (blkPl_255).base hooks) (s0.readReg64 .x30) s (parserFrameSep (p ↦ₛ bs) out17 out_w0 out_w1 out_b2 s0) (parserPostVm p bs out17 s0 R) := by
  rcases hcs with ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  have hcallee_hex := ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_255).rebase (blkPl_255).base hooks) (decodeHex32_placed_vm_ok hooks)
  change subroutine_ok _ (lsmpl.base 254) _ at hcallee_hex; simp only [withLsCl, withVmPreserved, decodeHex32Spec, sepConj_assoc] at hcallee_hex
  have huuid : uuidTryParse bs = decodeHex32 bs := by unfold uuidTryParse parseSimple; simp [hlen]
  dsimp only [parserFrameSep]; rw [memRegion_sp88_32_for_simple s0.sp]; apply sepWP_lscl_vm_step hcl0 (mid := lsmpl.base 254); by_vm_steps
    wp_steps; refine SepWP.done (by rfl) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun _ hvm1 => ?_⟩; have hvm01 := vm_chain hvm0 hvm1; wp_apply; have hvm_hex := vm_chain hvm01 ‹_›
    cases hdec : decodeHex32 bs with
    | none => rw [decodeHex32ResultAt_sp88_none s0.sp, hsp]; apply sepWP_ret_vm hvm_hex; by_vm_steps (wp_steps; dsimp only [parserTryParseSpec]; simp only [huuid, hdec, parserTryParseResultAt, stackAt_parser_split s0.sp, memRegion_sp88_32_for_simple s0.sp, memRegion_sp88_17_none s0.sp]; wp_done)
    | some u => rw [decodeHex32ResultAt_sp88_some s0.sp u, hsp]; apply sepWP_ret_vm hvm_hex; by_vm_steps (wp_steps; dsimp only [parserTryParseSpec]; simp only [huuid, hdec, parserTryParseResultAt_some_eq, stackAt_parser_split s0.sp, memRegion_sp88_32_for_simple s0.sp, memRegion_sp88_17_some s0.sp]; wp_done)
private theorem wp_hyphenated_vm_placed [LibsignalPlacement] (hooks : LibsignalHooks) (p p19 : BitVec 64) (bs s36 : List (BitVec 8)) (FrameS : SepProp) (out17 : BitVec 64)
    (R : SepProp) (out_w0 out_w1 : BitVec 64) (out_b2 : BitVec 8) (s0 s : State) (hcl0 : LibsignalCodeLoaded lsmpl s.mem) (hsp_align : s0.spAligned = true) (hs36 : s36.length = 36)
    (hframe : (p ↦ₛ bs) = ((p19 ↦ₛ s36) ∗ FrameS)) (huuid : uuidTryParse bs = parseHyphenated s36) (hpc : s.pc = (blkPl_255).base + bv% (44)) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = p19) (hx8 : s.readReg64 .x8 = out17) (hx29 : s.readReg64 .x29 = s0.sp - 32#64) (htr : s.trace = s0.trace)
    (hvm0 : VmPreserved s0 s) (hcs : ParserRegsPreserved s0 s) :
    SepWP ((blkPC_255).rebase (blkPl_255).base hooks) (s0.readReg64 .x30) s (parserFrameSep ((p19 ↦ₛ s36) ∗ FrameS) out17 out_w0 out_w1 out_b2 s0) (parserPostVm p bs out17 s0 R) := by
  rcases hcs with ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  have hcallee_hex := ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_255).rebase (blkPl_255).base hooks) (decodeHex32_placed_vm_ok hooks)
  change subroutine_ok _ (lsmpl.base 254) _ at hcallee_hex; simp only [withLsCl, withVmPreserved, decodeHex32Spec, sepConj_assoc] at hcallee_hex
  rcases exists_36_parts s36 hs36 with ⟨hex32, b8, b13, b18, b23, w0, w4, w1, w2, w3, w5, _, hb8, hb13, hb18, hb23, hhex_eq, hp19_split, hsp_hex32⟩
  have hph := parseHyphenated_of_parts s36 hex32 b8 b13 b18 b23 hs36 hb8 hb13 hb18 hb23 hhex_eq
  dsimp only [parserFrameSep]; rw [hp19_split p19, memRegion_sp88_32_for_hyphen s0.sp]; wp_pull_exists; wp_steps; wp_if h8
  · apply sepWP_ret_vm (vm_chain hvm0 (by simp only [arm64_norm])); by_vm_steps (wp_steps; dsimp only [parserTryParseSpec]; simp only [hframe, hp19_split p19, huuid, parseHyphenated_ne_8 hph h8, parserTryParseResultAt, stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp]; wp_done)
  · wp_steps; wp_if h13
    · apply sepWP_ret_vm (vm_chain hvm0 (by simp only [arm64_norm])); by_vm_steps (wp_steps; dsimp only [parserTryParseSpec]; simp only [hframe, hp19_split p19, huuid, parseHyphenated_ne_13 hph h13, parserTryParseResultAt, stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp]; wp_done)
    · wp_steps; wp_if h18
      · apply sepWP_ret_vm (vm_chain hvm0 (by simp only [arm64_norm])); by_vm_steps (wp_steps; dsimp only [parserTryParseSpec]; simp only [hframe, hp19_split p19, huuid, parseHyphenated_ne_18 hph h18, parserTryParseResultAt, stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp]; wp_done)
      · wp_steps; wp_if h23
        · apply sepWP_ret_vm (vm_chain hvm0 (by simp only [arm64_norm])); by_vm_steps (wp_steps; dsimp only [parserTryParseSpec]; simp only [hframe, hp19_split p19, huuid, parseHyphenated_ne_23 hph h23, parserTryParseResultAt, stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp]; wp_done)
        · have hall := parseHyphenated_all_eq hph h8 h13 h18 h23; apply sepWP_lscl_vm_step (by convert hcl0 using 1; wp_norm_lhs) (mid := lsmpl.base 254); by_vm_steps
            wp_steps; refine SepWP.done (by rfl) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun _ hvm1 => ?_⟩
            have hvm01 := vm_chain (vm_chain hvm0 (by simp only [arm64_norm])) hvm1; apply SepWP.focus_rw (hsp_hex32 s0.sp); wp_apply; have hvm_hex := vm_chain hvm01 ‹_›
            cases hdec : decodeHex32 hex32 with
            | none => rw [decodeHex32ResultAt_sp52_none s0.sp, ← hsp_hex32 s0.sp, hsp]; apply sepWP_ret_vm hvm_hex; by_vm_steps (wp_steps; dsimp only [parserTryParseSpec]; simp only [hframe, hp19_split p19, huuid, hall, hdec, parserTryParseResultAt, stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp, memRegion_sp52_17_none s0.sp]; wp_done)
            | some u => rw [decodeHex32ResultAt_sp52_some s0.sp u, ← hsp_hex32 s0.sp, hsp]; apply sepWP_ret_vm hvm_hex; by_vm_steps (wp_steps; dsimp only [parserTryParseSpec]; simp only [hframe, hp19_split p19, huuid, hall, hdec, parserTryParseResultAt_some_eq, stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp, memRegion_sp52_17_some s0.sp]; wp_done)
private theorem wp_braced_vm_placed [LibsignalPlacement] (hooks : LibsignalHooks) (p : BitVec 64) (bs : List (BitVec 8)) (out17 : BitVec 64) (R : SepProp)
    (out_w0 out_w1 : BitVec 64) (out_b2 : BitVec 8) (s0 s : State) (hcl0 : LibsignalCodeLoaded lsmpl s.mem) (hsp_align : s0.spAligned = true) (hlen : bs.length = 38)
    (hpc : s.pc = (blkPl_255).base + bv% (388)) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = p) (hx8 : s.readReg64 .x8 = out17)
    (hx29 : s.readReg64 .x29 = s0.sp - 32#64) (htr : s.trace = s0.trace) (hvm0 : VmPreserved s0 s) (hcs : ParserRegsPreserved s0 s) :
    SepWP ((blkPC_255).rebase (blkPl_255).base hooks) (s0.readReg64 .x30) s (parserFrameSep (p ↦ₛ bs) out17 out_w0 out_w1 out_b2 s0) (parserPostVm p bs out17 s0 R) := by
  rcases hcs with ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩; have h_hyph := wp_hyphenated_vm_placed hooks; have h_err := wp_err_vm_placed hooks
  rcases exists_38_parts bs hlen with ⟨b0, b37, s36, hs36, _, huuid, hp_split⟩; dsimp only [parserFrameSep]; rw [hp_split p]; wp_steps; wp_if hb0
  · rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align (braced_ne_0 huuid hb0) ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
  · wp_steps; wp_if hb37
    · rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align (braced_ne_37 huuid hb37) ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
    · wp_step; wp_step; refine h_hyph p (p + 1#64) bs s36 ((p ↦₈ b0) ∗ ((p + 37#64) ↦₈ b37)) out17 R out_w0 out_w1 out_b2 s0 _ (by convert hcl0 using 1; wp_norm_lhs) hsp_align hs36 (hp_split p) (braced_all_eq huuid hb0 hb37) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
private theorem wp_urn_vm_placed [LibsignalPlacement] (hooks : LibsignalHooks) (p : BitVec 64) (bs : List (BitVec 8)) (out17 : BitVec 64) (R : SepProp)
    (out_w0 out_w1 : BitVec 64) (out_b2 : BitVec 8) (s0 s : State) (hcl0 : LibsignalCodeLoaded lsmpl s.mem) (hsp_align : s0.spAligned = true) (hlen : bs.length = 45)
    (hpc : s.pc = (blkPl_255).base + bv% (212)) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = p) (hx8 : s.readReg64 .x8 = out17)
    (hx29 : s.readReg64 .x29 = s0.sp - 32#64) (htr : s.trace = s0.trace) (hvm0 : VmPreserved s0 s) (hcs : ParserRegsPreserved s0 s) :
    SepWP ((blkPC_255).rebase (blkPl_255).base hooks) (s0.readReg64 .x30) s (parserFrameSep (p ↦ₛ bs) out17 out_w0 out_w1 out_b2 s0) (parserPostVm p bs out17 s0 R) := by
  rcases hcs with ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩; have h_hyph := wp_hyphenated_vm_placed hooks; have h_err := wp_err_vm_placed hooks
  rcases exists_45_parts bs hlen with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, s36, hs36, huuid, hp_split⟩; dsimp only [parserFrameSep]; rw [hp_split p]; wp_steps; wp_if hb0
  · rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align (by simp [huuid, show 0x75#8 ≠ b0 from fun h => hb0 (h ▸ rfl)]) ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
  · wp_steps; wp_if hb1
    · rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align (by simp [huuid, show 0x72#8 ≠ b1 from fun h => hb1 (h ▸ rfl)]) ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
    · wp_steps; wp_if hb2
      · rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align (by simp [huuid, show 0x6e#8 ≠ b2 from fun h => hb2 (h ▸ rfl)]) ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
      · wp_steps; wp_if hb3
        · rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align (by simp [huuid, show 0x3a#8 ≠ b3 from fun h => hb3 (h ▸ rfl)]) ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
        · wp_steps; wp_if hb4
          · rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align (by simp [huuid, show 0x75#8 ≠ b4 from fun h => hb4 (h ▸ rfl)]) ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
          · wp_steps; wp_if hb5
            · rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align (by simp [huuid, show 0x75#8 ≠ b5 from fun h => hb5 (h ▸ rfl)]) ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
            · wp_steps; wp_if hb6
              · rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align (by simp [huuid, show 0x69#8 ≠ b6 from fun h => hb6 (h ▸ rfl)]) ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
              · wp_steps; wp_if hb7
                · rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align (by simp [huuid, show 0x64#8 ≠ b7 from fun h => hb7 (h ▸ rfl)]) ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
                · wp_steps; wp_if hb8
                  · rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align (by simp [huuid, show 0x3a#8 ≠ b8 from fun h => hb8 (h ▸ rfl)]) ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
                  · wp_step; wp_step; refine h_hyph p (p + 9#64) bs s36 ((p ↦₈ b0) ∗ ((p + 1#64) ↦₈ b1) ∗ ((p + 2#64) ↦₈ b2) ∗ ((p + 3#64) ↦₈ b3) ∗ ((p + 4#64) ↦₈ b4) ∗ ((p + 5#64) ↦₈ b5) ∗ ((p + 6#64) ↦₈ b6) ∗ ((p + 7#64) ↦₈ b7) ∗ ((p + 8#64) ↦₈ b8)) out17 R out_w0 out_w1 out_b2 s0 _ (by convert hcl0 using 1; wp_norm_lhs) hsp_align hs36 (hp_split p) (urn_all_eq huuid hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
private theorem parserTryParse_placed_vm_ok [LibsignalPlacement] (hooks : LibsignalHooks) :
    subroutine_ok ((blkPC_255).rebase (blkPl_255).base hooks) (blkPl_255).base (withLsCodeLoaded lsmpl (withVmPreserved parserTryParseSpec)) := by
  apply subroutine_ok_of_sepWP_simple; intro ⟨p, bs, out17⟩ R s0 hpc hrun hsp
  change SepWP ((blkPC_255).rebase (blkPl_255).base hooks) (s0.readReg64 .x30) s0 (((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧ s0.readReg64 .x8 = out17⌝ ∗ (p ↦ₛ bs) ∗ memRegion out17 17) ∗ stackAt s0.sp 0x80) ∗ ⌜LibsignalCodeLoaded lsmpl s0.mem⌝) (parserPostVm p bs out17 s0 R)
  rw [sepConj_comm]; apply SepWP.pure_elim; intro hcl0
  have h_braced := wp_braced_vm_placed hooks; have h_urn := wp_urn_vm_placed hooks; have h_simple := wp_simple_vm_placed hooks; have h_hyph := wp_hyphenated_vm_placed hooks; have h_err := wp_err_vm_placed hooks
  simp only [sepConj_assoc]; apply SepWP.pure_elim; rintro ⟨hx0, hx1, hx8⟩; rw [memRegion_out17_split out17, stackAt_parser_split s0.sp]; wp_pull_exists
  apply sepWP_lscl_vm_step hcl0 (mid := (blkPl_255).base + bv% (24)); by_vm_steps
    wp_steps; refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun hcl1 hvm1 => ?_⟩; wp_steps; wp_if hgt
    · have hne32 : bs.length ≠ 32 := fun hlen => by rw [show s0.readReg64 .x1 = 32#64 by rw [eq_ofNat_of_toNat_eq hx1, hlen]] at hgt; revert hgt; decide
      have hne36 : bs.length ≠ 36 := fun hlen => by rw [show s0.readReg64 .x1 = 36#64 by rw [eq_ofNat_of_toNat_eq hx1, hlen]] at hgt; revert hgt; decide
      wp_steps; wp_if heq38
      · apply sepWP_parser_branch; refine h_braced p bs out17 R _ _ _ s0 _ (by convert hcl1 using 1; wp_norm_lhs) hsp (len_eq_of_reg_eq hx1 heq38) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by vm_eq hvm1) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
      · have hne38 := len_ne_of_reg_ne hx1 heq38; wp_steps; wp_if hne45_reg
        · apply sepWP_parser_branch; refine h_err p bs out17 R _ _ _ s0 _ hsp (uuidTryParse_of_other_len hne32 hne36 hne38 (len_ne_of_reg_ne hx1 hne45_reg)) ?_ ?_ ?_ ?_ ?_ (by vm_eq hvm1) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
        · apply sepWP_parser_branch; refine h_urn p bs out17 R _ _ _ s0 _ (by convert hcl1 using 1; wp_norm_lhs) hsp (len_eq_of_reg_eq hx1 hne45_reg) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by vm_eq hvm1) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
    · have hne38 : bs.length ≠ 38 := fun hlen => by rw [show s0.readReg64 .x1 = 38#64 by rw [eq_ofNat_of_toNat_eq hx1, hlen]] at hgt; revert hgt; decide
      have hne45 : bs.length ≠ 45 := fun hlen => by rw [show s0.readReg64 .x1 = 45#64 by rw [eq_ofNat_of_toNat_eq hx1, hlen]] at hgt; revert hgt; decide
      wp_steps; wp_if heq32
      · apply sepWP_parser_branch; refine h_simple p bs out17 R _ _ _ s0 _ (by convert hcl1 using 1; wp_norm_lhs) hsp (len_eq_of_reg_eq hx1 heq32) ?_ ?_ ?_ ?_ ?_ ?_ (by vm_eq hvm1) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
      · have hne32 := len_ne_of_reg_ne hx1 heq32; wp_steps; wp_if hne36_reg
        · apply sepWP_parser_branch; refine h_err p bs out17 R _ _ _ s0 _ hsp (uuidTryParse_of_other_len hne32 (len_ne_of_reg_ne hx1 hne36_reg) hne38 hne45) ?_ ?_ ?_ ?_ ?_ (by vm_eq hvm1) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
        · have hlen36 := len_eq_of_reg_eq hx1 hne36_reg; have huuid : uuidTryParse bs = parseHyphenated bs := by unfold uuidTryParse; simp [hlen36]
          apply sepWP_parser_hyph36; refine h_hyph p p bs bs emp out17 R _ _ _ s0 _ (by convert hcl1 using 1; wp_norm_lhs) hsp hlen36 (sepConj_emp (p ↦ₛ bs)).symm huuid ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by vm_eq hvm1) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
private theorem uuidTryParse_placed_vm_ok [LibsignalPlacement] (hooks : LibsignalHooks) :
    subroutine_ok ((blkPC_252).rebase (blkPl_252).base hooks) (blkPl_252).base (withLsCodeLoaded lsmpl (uuidTryParseCodeBudgetSpec uuidTryParse)) := by
  have hcallee := ls_subroutine_ok_cl_of_block (callerProg := (blkPC_252).rebase (blkPl_252).base hooks) (parserTryParse_placed_vm_ok hooks)
  change subroutine_ok _ (lsmpl.base 255) _ at hcallee; simp only [withLsCl, withVmPreserved, parserTryParseSpec, sepConj_assoc] at hcallee
  apply subroutine_ok_of_sepWP_simple; intro ⟨p, bs, out⟩ R s0 hpc hrun hsp
  dsimp only [withLsCodeLoaded, uuidTryParseCodeBudgetSpec]; rw [sepConj_comm]; apply SepWP.pure_elim; intro hcl0
  change SepWP _ _ _ ((uuidTryParseCodeSpec uuidTryParse).pre (p, bs, out) s0) _
  dsimp only [uuidTryParseCodeSpec, uuidTryParseSpec, BitVec.ofNat_eq_ofNat]; simp only [sepConj_assoc]; apply SepWP.pure_elim; rintro ⟨hx0, hx1, hx8⟩
  rw [memRegion_out32_split out, stackAt_uuid_split s0.sp]; wp_pull_exists; apply sepWP_lscl_vm_step hcl0 (mid := lsmpl.base 255); by_vm_steps
    wp_steps; refine SepWP.done (by rfl) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun _ hvm1 => ?_⟩; wp_apply; have hvm_p := vm_chain hvm1 ‹_›
    cases huuid : uuidTryParse bs with
    | none => rw [parserTryParseResultAt_sp56_none s0.sp]; wp_pull_exists; wp_focus_pure; intro _htag; apply sepWP_strip_vm hvm_p; by_vm_steps (wp_steps; simp only [uuidResultAt, uuidErrParseOther, memRegion_out28_split out, memRegion_sp56_17_split s0.sp, stackAt_uuid_split s0.sp]; wp_done)
    | some u => rw [parserTryParseResultAt_sp56_some s0.sp u]; simp only [sepConj_assoc]; apply sepWP_strip_vm hvm_p; by_vm_steps (wp_steps; simp only [uuidResultAt_some_eq out u, memRegion_sp56_17_split s0.sp, stackAt_uuid_split s0.sp]; wp_done)
private theorem stripS_read64 (p : BitVec 64 → Bool) (s : State) (a : BitVec 64) : (ProofLib.stripS p s).mem.read64 a = s.mem.read64 a := by cases s; simp [ProofLib.stripS, Memory.read64, ProofLib.strip_read8]
private theorem cliGhost_row (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {sym : String} {f : State → State} (hrow : (sym, f) ∈ cliHookTablePlaced mmpl W)
    (h1 : sym ≠ lsRustAllocSymCli := by decide) (h2 : sym ≠ lsRustDeallocSymCli := by decide)
    (h3 : sym ≠ lsRustReallocSymCli := by decide) (h4 : sym ≠ lsRustAllocZeroedSymCli := by decide)
    (h5 : sym ≠ lsRustNoAllocShimSymCli := by decide) (h6 : sym ≠ lsStringCloneSym := by decide)
    (h7 : sym ≠ CryptoVerification.SignalSession.lsReadFileSym := by decide)
    (h8 : sym ≠ CryptoVerification.SignalSession.lsReadStdinSym := by decide)
    (h9 : sym ≠ CryptoVerification.SignalSession.lsMemsetSym := by decide)
    (h10 : sym ≠ CryptoVerification.SignalSession.lsMemcpySym := by decide) :
    cliGhostExterns g (cliExternsPlaced mmpl W) sym = some f :=
  (cliGhostExterns_other g _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10).trans (cliExternsPlaced_row mmpl W hrow)
private theorem new_from_slice_60_cro_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    subroutine_ok ((blkPC_60).rebase (blkPl_60).base (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 114) (withLsCodeRoLoaded lsmpl (newFromSliceBudgetSpec W.C.F)) :=
  new_from_slice_placed_cro_budget_ok_at_block_sat W.C.F
    (cliExternsPlaced_exactMemcpy_sat mmpl g W hG)
    (cliGhost_row mmpl g W (compress256_row_placed mmpl W))
/-- `S7SeamPlaced` on Block `433` at `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem s7_433_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) (S : SpqrModel) :
    S7SeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C A lim ctl uuidTryParse S (s7Env W.C.F uuidTryParse) := by
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  have _ := instIsLsBlockProg_434 H
  have hpk60 := subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded (ls_subroutine_ok_of_block (callerProg := (blkPC_60).rebase (blkPl_60).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl) (public_key_serialize_placed_ok ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hG.shim_eq), noAllocShim_hookOk⟩ (cliExternsPlaced_alloc_budget_sat mmpl g W hG))))
  have hvmac62 := verifyMacWithAddresses_placed_cro_ok W.C M A lim uuidTryParse H
    (parse_sid_placed_ok_at_of_code (prog := (blkPC_61).rebase (blkPl_61).base H) (uuidTryParse_placed_vm_ok H))
    (new_from_slice_60_cro_ok mmpl g W hG) hpk60
    (ls_hook_ok_ultra_of_mem (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W (cliExternsPlaced_blackBox_budget_sat mmpl W)))
    (cliExternsPlaced_noAllocShim_budget_sat mmpl g W hG.shim_eq)
    (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl g W hG)
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W (cliExternsPlaced_compress256Multi_budget_sat mmpl W))
    (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG)
  exact verifyMac_433_placed_ok W.C A lim ctl S H
    (keys_ls_subroutine_ok_of_block_cro (callerProg := (blkPC_434).rebase (blkPl_434).base H) hvmac62)
    (ls_hook_ok_ultra_of_mem (cliExternsPlaced_shim_budget_sat mmpl g W hG.shim_eq))
    (ls_hook_ok_ultra_of_mem (cliExternsPlaced_alloc_budget_sat mmpl g W hG))
    (ls_hook_ok_ultra_of_mem (cliExternsPlaced_dealloc_budget_sat mmpl g W hG))
end LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptFrontTrapPlacedBudgetPart3
