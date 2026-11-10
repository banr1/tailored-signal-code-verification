/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.DecryptTailTrap507PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SpqrRecvTrapV1_507PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.VerifyMacTrap507PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptTailTrapPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetSat
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.UuidFsPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudgetSat
import LibsignalBinary.Proofs.TripleRatchet.Getters.ClearUnacknowledgedPreKeyMessageBudget
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.CallsBudget
import LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeysBudget
import LibsignalBinary.Proofs.TripleRatchet.Mac.VerifyBudget
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.ApplyBudget

/-!
# Budget-Threaded Block `507` CLI Segment Seams (`S6`, `S7`, `S9`)

CLI hook-table instantiations for `s6_507_cli`, `s7_507_cli`, and `s9_507_cli` on Block `507`.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudgetPart3

open Arm64 ProofLib
open CryptoVerification (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement LibsignalRoLoaded blkLib_eq_114 blkPC_60 blkPC_61 blkPC_69 blkPC_114 blkPC_252 blkPl_60 blkPl_61 blkPl_69 blkPl_114 blkPl_252 extract_withLsCodeLoaded libsignalMutatedBlocks libsignalSessionLib libsignalSessionLib_blocks_length ls_subroutine_ok_of_block lsmpl subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.CliHandshake.TryDecPlaced (blkPC_508 blkPl_508)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel extract_withLsCodeRoLoaded keys_ls_hook_ok_of_mem keys_ls_subroutine_ok_of_block_cro newFromSliceSpec subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded uuidTryParseCodeSpec withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced cliHookTablePlaced lsRustAllocSymCli lsRustAllocZeroedSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli lsStringCloneSym)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_other cliGhostExterns_shim)
open CryptoVerification.SignalSession.Cli.Slots (cliGhostExterns_sat_of_cliExternsPlaced compress256_row_placed)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptTailTrapPlacedBudget (s9Env)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.VerifyMacTrapPlacedBudget (s7Env)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget (S6SeamPlaced S7SeamPlaced S9SeamPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks cliExternsPlaced_alloc_budget_sat cliExternsPlaced_blackBox_budget_sat cliExternsPlaced_compress256Multi_budget_sat cliExternsPlaced_dealloc_budget_sat cliExternsPlaced_exactMemcpy_sat cliExternsPlaced_framelessMemcpy_budget_sat cliExternsPlaced_noAllocShim_budget_sat cliExternsPlaced_sessionMemcpyRegion_budget_sat cliExternsPlaced_sessionMemsetRegion_budget_sat cliExternsPlaced_shim_budget_sat)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget (calleeSavedPreserved_of_stripS_right checkBlockSafeVm checkBytesSafeVm isTotalTrapHooks_vmTrapHooks placedLib_rebase_allInstrs_safeVm stripS_pc stripS_readReg64 stripS_sp stripS_status vmTrapHooks)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (framelessMemcpyBudgetSpec noAllocShim_hookOk)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget (s6FreeOnlyEnv)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HkdfPlacedHooksExactSat)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget (parseSidCodeBudgetSpec uuidTryParseCodeBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Mac.ComputeBudgetAux (newFromSliceBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

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

private theorem new_from_slice_114_cro_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    subroutine_ok ((blkPC_114).rebase (blkPl_114).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 114) (withLsCodeRoLoaded lsmpl (newFromSliceBudgetSpec W.C.F)) :=
  LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudgetSat.new_from_slice_placed_cro_budget_ok_at_block_sat
    W.C.F (cliExternsPlaced_exactMemcpy_sat mmpl g W hG)
    (cliGhost_row mmpl g W (compress256_row_placed mmpl W))

private theorem new_from_slice_60_cro_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    subroutine_ok ((blkPC_60).rebase (blkPl_60).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 114) (withLsCodeRoLoaded lsmpl (newFromSliceBudgetSpec W.C.F)) :=
  keys_ls_subroutine_ok_of_block_cro (callerProg := (blkPC_60).rebase (blkPl_60).base (cliGhostExterns g (cliExternsPlaced mmpl W))) (new_from_slice_114_cro_ok mmpl g W hG)

private def keepLs [LibsignalPlacement] (pc : BitVec 64) : Bool :=
  (List.range libsignalSessionLib.blocks.length).any fun j =>
    !(decide (j ∈ libsignalMutatedBlocks)) &&
      ProofLib.progKeep (libsignalSessionLib.blockProgram lsmpl j vmTrapHooks) pc
private def relocsSorted : Nat → List Obj.RelocEntry → Bool
  | _, [] => true | bound, r :: rs => decide (bound ≤ r.off ∧ r.off % 4 = 0) && relocsSorted (r.off + 4) rs
private theorem find?_none_of_relocsSorted : ∀ {off bound : Nat} {rs : List Obj.RelocEntry}, off < bound → relocsSorted bound rs = true → rs.find? (·.off == off) = none
  | _, _, [], _, _ => rfl | off, bound, r :: rs, hlt, hs => by simp only [relocsSorted, Bool.and_eq_true, decide_eq_true_eq] at hs; dsimp only [List.find?]; rw [beq_false_of_ne (by omega)]; exact find?_none_of_relocsSorted (by omega) hs.2
private def scanWordsRelocs : Nat → List Obj.RelocEntry → List (BitVec 8) → Bool
  | _, _, [] => true
  | off, [], b0 :: b1 :: b2 :: b3 :: rest => let w := Obj.wordOfBytesLE [b0, b1, b2, b3] 0; ((w != 0xd400_0001#32) && !Arm64.isMsrTpidrEl0Word w) && scanWordsRelocs (off + 4) [] rest
  | off, r :: rs, b0 :: b1 :: b2 :: b3 :: rest =>
    let w := Obj.wordOfBytesLE [b0, b1, b2, b3] 0
    if r.off == off then VerifiedLibraries.RustStd.checkRelocWordNoSvc0 w r && scanWordsRelocs (off + 4) rs rest else decide (off < r.off) && ((w != 0xd400_0001#32) && !Arm64.isMsrTpidrEl0Word w) && scanWordsRelocs (off + 4) (r :: rs) rest
  | _, _, _ => false
private theorem scanWordsRelocs_imp (blk : Obj.CodeBlock) : ∀ (bs : List (BitVec 8)) (off : Nat) (rs : List Obj.RelocEntry),
    off % 4 = 0 → relocsSorted off rs = true → (∀ k, off ≤ k → blk.relocAt? k = rs.find? (·.off == k)) → scanWordsRelocs off rs bs = true → checkBytesSafeVm blk off bs = true
  | [], _, _, _, _, _, _ => rfl
  | [_], _, rs, _, _, _, h | [_, _], _, rs, _, _, _, h | [_, _, _], _, rs, _, _, _, h => by cases rs <;> simp [scanWordsRelocs] at h
  | b0 :: b1 :: b2 :: b3 :: rest, off, [], hal, _, hrel, h => by
    simp only [scanWordsRelocs, Bool.and_eq_true] at h; unfold checkBytesSafeVm; rw [hrel off (Nat.le_refl off)]; dsimp only [List.find?]; simp only [Bool.and_eq_true]; exact ⟨h.1, scanWordsRelocs_imp blk rest (off + 4) [] (by omega) rfl (fun k hk => hrel k (by omega)) h.2⟩
  | b0 :: b1 :: b2 :: b3 :: rest, off, r :: rs, hal, hsort, hrel, h => by
    simp only [relocsSorted, Bool.and_eq_true, decide_eq_true_eq] at hsort; dsimp only [scanWordsRelocs] at h; cases heq : r.off == off
    · rw [heq] at h; simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h
      have hsort' : relocsSorted (off + 4) (r :: rs) = true := by simp only [relocsSorted, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨by omega, hsort.1.2⟩, hsort.2⟩
      unfold checkBytesSafeVm; rw [hrel off (Nat.le_refl off), find?_none_of_relocsSorted (by omega) hsort']; simp only [Bool.and_eq_true]; exact ⟨h.1.2, scanWordsRelocs_imp blk rest (off + 4) (r :: rs) (by omega) hsort' (fun k hk => hrel k (by omega)) h.2⟩
    · rw [heq] at h; simp only [↓reduceIte, Bool.and_eq_true] at h; have hroff : r.off = off := beq_iff_eq.mp heq
      unfold checkBytesSafeVm; rw [hrel off (Nat.le_refl off)]; dsimp only [List.find?]; rw [heq]; simp only [Bool.and_eq_true]
      refine ⟨h.1, scanWordsRelocs_imp blk rest (off + 4) rs (by omega) (hroff ▸ hsort.2) (fun k hk => ?_) h.2⟩; rw [hrel k (by omega)]; dsimp only [List.find?]; rw [beq_false_of_ne (by omega)]
private def checkBlockSafeVmFast (blk : Obj.CodeBlock) : Bool :=
  if relocsSorted 0 blk.relocs then scanWordsRelocs 0 blk.relocs blk.code && blk.relocs.all (fun r => VerifiedLibraries.RustStd.relocKindSafeNoSvc0 r.kind) else checkBlockSafeVm blk
private theorem checkBlockSafeVmFast_imp {blk : Obj.CodeBlock} (h : checkBlockSafeVmFast blk = true) : checkBlockSafeVm blk = true := by
  unfold checkBlockSafeVmFast at h; split at h
  · rename_i hs; simp only [Bool.and_eq_true] at h; unfold checkBlockSafeVm; simp only [Bool.and_eq_true]; exact ⟨scanWordsRelocs_imp blk blk.code 0 blk.relocs rfl hs (fun _ _ => rfl) h.1, h.2⟩
  · exact h
private def checkBlocksAt : Nat → List Obj.CodeBlock → Bool
  | _, [] => true | j, b :: bs => (decide (j ∈ libsignalMutatedBlocks) || checkBlockSafeVmFast b) && checkBlocksAt (j + 1) bs
private theorem checkBlocksAt_append : ∀ (k : Nat) (xs ys : List Obj.CodeBlock), checkBlocksAt k xs = true → checkBlocksAt (k + xs.length) ys = true → checkBlocksAt k (xs ++ ys) = true
  | _, [], _, _, hy => by simpa only [List.nil_append, List.length_nil, Nat.add_zero] using hy
  | k, _ :: xs, ys, hx, hy => by simp only [List.cons_append, checkBlocksAt, Bool.and_eq_true] at hx ⊢; exact ⟨hx.1, checkBlocksAt_append (k + 1) xs ys hx.2 (by simpa only [List.length_cons, show k + 1 + xs.length = k + (xs.length + 1) by omega] using hy)⟩
private theorem checkBlocksAt_getD : ∀ (k : Nat) (bs : List Obj.CodeBlock) (i : Nat), i < bs.length → checkBlocksAt k bs = true → (decide ((k + i) ∈ libsignalMutatedBlocks) || checkBlockSafeVmFast (bs.getD i { code := [] })) = true
  | _, [], _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | k, _ :: _, 0, _, h => by simp only [checkBlocksAt, Bool.and_eq_true] at h; simpa only [Nat.add_zero, List.getD, List.getElem?_cons_zero, Option.getD_some] using h.1
  | k, b :: bs, i + 1, hi, h => by simp only [checkBlocksAt, Bool.and_eq_true] at h; rw [show (b :: bs).getD (i + 1) { code := [] } = bs.getD i { code := [] } from rfl, show k + (i + 1) = k + 1 + i by omega]; exact checkBlocksAt_getD (k + 1) bs i (by simp at hi; omega) h.2
private theorem safeVm_lo : checkBlocksAt 0 (libsignalSessionLib.blocks.take 310) = true := by decide +kernel
private theorem safeVm_hi : checkBlocksAt 310 (libsignalSessionLib.blocks.drop 310) = true := by decide +kernel
private theorem allUnmutated_safeVm : checkBlocksAt 0 libsignalSessionLib.blocks = true := by
  rw [← List.take_append_drop 310 libsignalSessionLib.blocks]; exact checkBlocksAt_append 0 _ _ safeVm_lo (by rw [Nat.zero_add, List.length_take, libsignalSessionLib_blocks_length]; exact safeVm_hi)
private theorem align4_add4_le {pc b off clen : Nat} (hp : pc % 4 = 0) (hb : b % 4 = 0) (hc : clen % 4 = 0) (heq : pc = b + off) (hlt : off < clen) : off + 4 ≤ clen := by omega

private theorem libsignalCodeLoaded_strip [LibsignalPlacement] {m : Memory} (hcl : LibsignalCodeLoaded lsmpl m) : LibsignalCodeLoaded lsmpl (ProofLib.stripExecOutside keepLs m) := fun j hj hunmut X O svc => by
  have hLj := hcl j hj hunmut X O svc; have hno := hLj.no_wrap; refine Program.CodeLoaded.intro hLj.aligned hLj.no_wrap fun k hk => ?_
  let P0 := libsignalSessionLib.blockProgram lsmpl j vmTrapHooks
  have hkeep : keepLs ((libsignalSessionLib.blockProgram lsmpl j X O svc).base + BitVec.ofNat 64 k) = true := by
    refine List.any_eq_true.mpr ⟨j, List.mem_range.mpr hj, Eq.mpr (Bool.and_eq_true _ _) ⟨by simp [hunmut], ?_⟩⟩
    unfold ProofLib.progKeep; change decide ((P0.base + BitVec.ofNat 64 k - P0.base).toNat < P0.code.length) = true
    rw [show P0.base + BitVec.ofNat 64 k - P0.base = BitVec.ofNat 64 k by bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact decide_eq_true hk
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]; exact ⟨hLj.byte_eq k hk, hLj.perm_eq k hk, hLj.isLazyFree_eq k hk⟩
private theorem findSome?_syms_none : ∀ (syms : List (String × Nat)) (off : Nat), (syms.findSome? fun x => if x.2 == off then (none : Option (State → State)) else none) = none
  | [], _ => rfl | _ :: tl, off => by rw [List.findSome?_cons, ite_self]; exact findSome?_syms_none tl off
private theorem stubs_vmTrap_fault : ∀ (stubs : List (String × Nat)) (off : Nat) {f : State → State}, (stubs.findSome? fun x => if x.2 == off then vmTrapHooks x.1 else none) = some f → ∀ s, (f s).status ≠ .Running
  | [], _, _, h => by cases h
  | (n, o) :: tl, off, _, h => by dsimp only [List.findSome?] at h; by_cases ho : o == off; · obtain ⟨g, hg, hnr⟩ := isTotalTrapHooks_vmTrapHooks n; simp [ho, hg] at h; subst h; exact hnr
                                  · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h; exact stubs_vmTrap_fault tl off h
private theorem stubs_none_of_vmTrap (Hk : String → Option (State → State)) : ∀ (stubs : List (String × Nat)) (off : Nat), (stubs.findSome? fun x => if x.2 == off then vmTrapHooks x.1 else none) = none → (stubs.findSome? fun x => if x.2 == off then Hk x.1 else none) = none
  | [], _, _ => rfl
  | (n, o) :: tl, off, h => by dsimp only [List.findSome?] at h ⊢; by_cases ho : o == off; · obtain ⟨g, hg, _⟩ := isTotalTrapHooks_vmTrapHooks n; simp [ho, hg] at h
                               · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact stubs_none_of_vmTrap Hk tl off h
private theorem safeVm_of_keepLs [LibsignalPlacement] {m : Memory} {pc : BitVec 64} {inst : Instr} (hcl : LibsignalCodeLoaded lsmpl m) (hkeep : keepLs pc = true) (hal_pc : pc.toNat % 4 = 0) (hdec : Arm64.decode (m.read32 pc) = some inst) : inst.isSvc0 = false ∧ inst.isMsrTpidrEl0 = false := by
  obtain ⟨j, hj_mem, hboth⟩ := List.any_eq_true.mp hkeep
  have hj : j < libsignalSessionLib.blocks.length := List.mem_range.mp hj_mem
  obtain ⟨hunmut_b, hkp⟩ := Eq.mp (Bool.and_eq_true _ _) hboth
  have hunmut : (j ∈ libsignalMutatedBlocks) = false := by simpa using hunmut_b
  have hall_j := checkBlocksAt_getD 0 libsignalSessionLib.blocks j hj allUnmutated_safeVm; simp only [Nat.zero_add, hunmut] at hall_j
  let lib := libsignalSessionLib.blockLib j; let pl := libsignalSessionLib.blockPlacement lsmpl j; let Q := (lib.program pl).rebase pl.base (fun _ => none)
  have hall := placedLib_rebase_allInstrs_safeVm lib pl (fun _ => none) (checkBlockSafeVmFast_imp hall_j); have hLQ : Q.CodeLoaded m := (hcl j hj hunmut (fun _ => none) (fun _ => none) Syscall.standard).of_base_code rfl rfl
  have hlen_mod4 : Q.code.length % 4 = 0 := by have hc : Q.code = lib.text.patched pl := rfl; rw [hc, Obj.CodeBlock.length_patched]; omega
  have hbase_al : Q.base.toNat % 4 = 0 := hLQ.aligned; have hno_wrap : Q.base.toNat + Q.code.length ≤ 2 ^ 64 := hLQ.no_wrap; have hoff_lt : (pc - Q.base).toNat < Q.code.length := of_decide_eq_true hkp
  have hpc_eq : pc = Q.base + BitVec.ofNat 64 (pc - Q.base).toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm Q.base, BitVec.sub_add_cancel]
  have hpc_nat : pc.toNat = Q.base.toNat + (pc - Q.base).toNat := by conv_lhs => rw [hpc_eq]; rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := (pc - Q.base).toNat) (by omega), Nat.mod_eq_of_lt (by omega)]
  have hin : (pc - Q.base).toNat + 4 ≤ Q.code.length := align4_add4_le hal_pc hbase_al hlen_mod4 hpc_nat hoff_lt
  have hfe_Q : Q.fetchMem m pc = some inst := by
    have hext_Q : Q.externAt? pc = none := by unfold Q Program.externAt? Program.hookAtOff? Program.rebase; dsimp only; rw [findSome?_syms_none, findSome?_syms_none]; rfl
    have hce_Q : m.canExec pc 4 = true := by unfold Memory.canExec; rw [Memory.allPerm_iff]; intro k hk; rw [show pc + BitVec.ofNat 64 k = Q.base + BitVec.ofNat 64 ((pc - Q.base).toNat + k) by conv_lhs => rw [hpc_eq]; rw [BitVec.add_assoc, ← BitVec.ofNat_add], hLQ.perm_eq _ (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk _) hin)]; rfl
    unfold Program.fetchMem; rw [hext_Q]; simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hal_pc, ne_eq, not_true_eq_false, hce_Q, Bool.not_true]; exact hdec
  simpa only [Bool.not_eq_true', Bool.or_eq_false_iff] using Program.fetchMem_of_allInstrs_holdsBytes_in_code hall hbase_al hno_wrap (fun k hk => ⟨hLQ.byte_eq k hk, hLQ.perm_eq k hk, hLQ.isLazyFree_eq k hk⟩) hin hfe_Q

private theorem steps_keepLs_lift [LibsignalPlacement] {P : Program} {b : BitVec 64} {Hk : LibsignalHooks} {s1' sf' : State} (hsteps : Steps (P.rebase b vmTrapHooks) s1' sf') (hrun_f : sf'.status = .Running) :
    ∀ (s1 : State), s1' = ProofLib.stripS keepLs s1 → LibsignalCodeLoaded lsmpl s1.mem → ∃ sf : State, sf' = ProofLib.stripS keepLs sf ∧ Steps (P.rebase b Hk) s1 sf ∧ VmPreserved s1 sf := by
  induction hsteps with
  | refl => intro s1 hs1 _; exact ⟨s1, hs1, .refl s1, VmPreserved.refl s1⟩
  | @step sa' sb' _ h1 hrest ih =>
    intro s1 hsa hcl1; subst hsa; have hrb' : sb'.status = .Running := by cases hrest with | refl => exact hrun_f | step hs _ => cases hs <;> assumption
    cases h1 with
    | halt_unmapped _ _ _ | extern_fault _ _ _ => cases s1; cases hrb'
    | extern _ hext _ _ => unfold Program.externAt? Program.hookAtOff? Program.rebase at hext; dsimp only at hext; rw [findSome?_syms_none, Option.or_none] at hext; exact False.elim (stubs_vmTrap_fault P.stubs _ hext _ hrb')
    | @exec inst hr1' hfe' =>
      have hr1 : s1.status = .Running := hr1'; have hmem_eq : (ProofLib.stripS keepLs s1).mem = ProofLib.stripExecOutside keepLs s1.mem := by cases s1; rfl
      rw [stripS_pc, hmem_eq] at hfe'; unfold Program.fetchMem at hfe'; have hext_T : (P.rebase b vmTrapHooks).externAt? s1.pc = none := by cases he : (P.rebase b vmTrapHooks).externAt? s1.pc <;> simp_all
      have hext_H : (P.rebase b Hk).externAt? s1.pc = none := by unfold Program.externAt? Program.hookAtOff? Program.rebase at hext_T ⊢; dsimp only at hext_T ⊢; rw [findSome?_syms_none, Option.or_none] at hext_T ⊢; exact stubs_none_of_vmTrap Hk P.stubs _ hext_T
      rw [hext_T] at hfe'; simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfe'; by_cases hal_pc : s1.pc.toNat % 4 = 0
      · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfe'; split at hfe'; · contradiction
        rename_i hce'; simp only [Bool.not_eq_true', Bool.not_eq_false] at hce'; unfold Memory.canExec at hce'; rw [Memory.allPerm_iff] at hce'
        have hkeep1 : keepLs s1.pc = true := by simpa using (ProofLib.strip_perm_x_imp (hce' 0 (by decide))).2
        have hce : s1.mem.canExec s1.pc 4 = true := by unfold Memory.canExec; rw [Memory.allPerm_iff]; intro k hk; have hxk := hce' k hk; rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
        have hr32 : (ProofLib.stripExecOutside keepLs s1.mem).read32 s1.pc = s1.mem.read32 s1.pc := by simp [Memory.read32, ProofLib.strip_read8]
        rw [hr32] at hfe'; obtain ⟨hnsvc0, hnmsr⟩ := safeVm_of_keepLs hcl1 hkeep1 hal_pc hfe'
        have hfe_H : (P.rebase b Hk).fetchMem s1.mem s1.pc = some inst := by unfold Program.fetchMem; rw [hext_H]; simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hal_pc, ne_eq, not_true_eq_false, hce, Bool.not_true]; exact hfe'
        have hev_T : (P.rebase b vmTrapHooks).evalInst inst (ProofLib.stripS keepLs s1) = ProofLib.stripS keepLs (execInst inst s1) := by rw [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
        have hstep_H : Step (P.rebase b Hk) s1 (execInst inst s1) := by simpa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] using Step.exec (prog := P.rebase b Hk) hr1 hfe_H
        have hvm1 : VmPreserved s1 (execInst inst s1) := VmPreserved.of_vm_tpidr (VerifiedLibraries.RustStd.nonSyscallPreserved_toVmFields (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1)) (Arm64.execInst_tpidrEl0_of_not_isMsrTpidrEl0 hnmsr s1) (LibsignalBinary.Heap.FdsHiFrame.of_fs_eq (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1).2.2.2.2.2.2)
        obtain ⟨sf, hsf_eq, hsteps_H, hvm_rest⟩ := ih hrun_f (execInst inst s1) hev_T (hcl1.of_keepsFrozen (Step.keepsFrozen hstep_H)); exact ⟨sf, hsf_eq, .step hstep_H hsteps_H, hvm1.trans hvm_rest⟩
      · simp [hal_pc] at hfe'

private theorem uuidTryParse_252_ok [LibsignalPlacement] (H : LibsignalHooks) : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H) (blkPl_252).base (withLsCodeLoaded lsmpl (uuidTryParseCodeBudgetSpec uuidTryParse)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre_cl hsp => ?_
  obtain ⟨hcl, hpre_u⟩ := extract_withLsCodeLoaded hpre_cl; dsimp only [uuidTryParseCodeBudgetSpec, withVmPreserved] at hpre_u; obtain ⟨R_view, hpre_strip, hunstrip⟩ := ProofLib.strip_frame keepLs hpre_u
  have hs0'_mem : (ProofLib.stripS keepLs s0).mem = ProofLib.stripExecOutside keepLs s0.mem := by cases s0; rfl
  have hpre_eq : (uuidTryParseCodeSpec uuidTryParse).pre x (ProofLib.stripS keepLs s0) = (uuidTryParseCodeSpec uuidTryParse).pre x s0 := by cases s0; rfl
  have hpre_T : (ProofLib.stripS keepLs s0).mem ⊨ (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse).keepsFs).pre x (ProofLib.stripS keepLs s0) ∗ R_view := by
    dsimp only [withLsCodeLoaded, Spec.keepsFs]; rw [hpre_eq, hs0'_mem, sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]; exact ⟨libsignalCodeLoaded_strip hcl, hpre_strip⟩
  have hLT : ((blkPC_252).rebase (blkPl_252).base vmTrapHooks).CodeLoaded (ProofLib.stripS keepLs s0).mem := by
    rw [hs0'_mem, IsLsBlockProg.eq_blockProgram (prog := (blkPC_252).rebase (blkPl_252).base vmTrapHooks)]; exact libsignalCodeLoaded_strip hcl 252 (by decide) (by decide) vmTrapHooks (fun _ => none) Syscall.standard
  obtain ⟨sf', hsteps', ⟨hret', hcc', hpost'⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩, _⟩ :=
    (CryptoVerification.SignalSession.Cli.MainHops.UuidFs.uuidTryParse_placed_okFs_F vmTrapHooks).no_fault_before_outcome x R_view (ProofLib.stripS keepLs s0) hpc hrun hpre_T (by cases s0; exact hsp) hLT
  · obtain ⟨sf, hsf_eq, hsteps_H, hvm⟩ := steps_keepLs_lift hsteps' hret'.2.2 s0 rfl hcl
    subst hsf_eq; dsimp only [withLsCodeLoaded, Spec.keepsFs] at hpost'; rw [sepConj_assoc, satisfies_pure_sepConj] at hpost'
    have hpost_eq : (uuidTryParseCodeSpec uuidTryParse).post x (ProofLib.stripS keepLs s0) (ProofLib.stripS keepLs sf) = (uuidTryParseCodeSpec uuidTryParse).post x s0 sf := by cases s0; cases sf; rfl
    have hsf_mem : (ProofLib.stripS keepLs sf).mem = ProofLib.stripExecOutside keepLs sf.mem := by cases sf; rfl
    have hpost_u := hpost'.2; rw [hpost_eq, hsf_mem] at hpost_u; have hret : Returned s0 sf := by simpa only [Returned, stripS_pc, stripS_readReg64, stripS_sp, stripS_status] using hret'
    have hcc : CallingConventionPreserved s0 sf := ⟨hcc'.1, calleeSavedPreserved_of_stripS_right (by cases s0; exact hcc'.2)⟩
    refine reaches_outcome_steps hsteps_H (reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, ?_⟩))
    dsimp only [withLsCodeLoaded, uuidTryParseCodeBudgetSpec, withVmPreserved]; rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hvm, hunstrip hvm.perm_eq hpost_u⟩
  all_goals exact False.elim (not_satisfies_false_sepConj ‹_›)
private theorem parseSid_61_ok [LibsignalPlacement] (H : LibsignalHooks) : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsmpl.base 206) (withLsCodeLoaded lsmpl (parseSidCodeBudgetSpec uuidTryParse)) :=
  LibsignalBinary.Proofs.TripleRatchet.InImageCallees.CallsBudget.parse_sid_placed_ok_at_of_code (prog := (blkPC_61).rebase (blkPl_61).base H) (uuidTryParse_252_ok H)

theorem s6_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) :
    S6SeamPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base W.C A lim ctl s6FreeOnlyEnv := by
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  have _ := CryptoVerification.CliHandshake.TryDecPlaced.instIsLsBlockProg_508 H
  have : HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactSat.of_allocHooks hG
  have : HkdfPlacedHooksExactBudgetSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat
      (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG)
  have hext69 :=
    LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat.extract_placed_vm_ok_of_other_block_sat
      W.C (callerProg := (blkPC_69).rebase (blkPl_69).base H) H
  have hexp69 :=
    LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetSat.expand_multi_info_placed_vm_ok_of_other_block_sat
      W.C (callerProg := (blkPC_69).rebase (blkPl_69).base H) H
  have hgen69 := LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeysBudget.generateKeys_placed_ok_of_contracts
    hext69 hexp69 (keys_ls_hook_ok_of_mem (cliExternsPlaced_dealloc_budget_sat mmpl g W hG))
  exact LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SpqrRecvTrapV1_507PlacedBudget.deriveKeys_507_placed_ok W.C A lim ctl H
    (keys_ls_subroutine_ok_of_block_cro (callerProg := (blkPC_508).rebase (blkPl_508).base H) hgen69)

theorem s9_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    S9SeamPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base W.C A lim ctl uuidTryParse S tdEnv s9Env := by
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  have _ := CryptoVerification.CliHandshake.TryDecPlaced.instIsLsBlockProg_508 H
  have hmc_fl : HookSat H "memcpy" framelessMemcpyBudgetSpec := by
    rcases cliExternsPlaced_framelessMemcpy_budget_sat mmpl g W hG with ⟨f, hf, h⟩
    refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
    rcases h x R s0 hrun hpre hsp with ⟨hkeep, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
    · refine ⟨hkeep, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
      rcases x with ⟨dst, src, bs⟩
      dsimp only [withVmPreserved, CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec,
        framelessMemcpyBudgetSpec] at hpost ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, sepConj_assoc,
        satisfies_pure_sepConj] at hpost
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hpost.2.1.1, hpost.2.1.2, hpost.1⟩, hpost.2.2⟩
    · exact ⟨hkeep, hsym, Or.inr hrest⟩
  have hTrApply58 := LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.ApplyBudget.trApply_placed_ok
    ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hG.shim_eq), noAllocShim_hookOk⟩
    (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)
    hmc_fl
  have hClearUpk35 := subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
    (LibsignalBinary.Proofs.TripleRatchet.Getters.ClearUnacknowledgedPreKeyMessageBudget.clear_unacknowledged_pre_key_message_placed_ok
      (cliExternsPlaced_dealloc_budget_sat mmpl g W hG))
  exact LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.DecryptTailTrap507PlacedBudget.applyRatchet_507_placed_ok W.C A lim ctl S tdEnv H
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded (ls_subroutine_ok_of_block (callerProg := (blkPC_508).rebase (blkPl_508).base H) hTrApply58))
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded (ls_subroutine_ok_of_block (callerProg := (blkPC_508).rebase (blkPl_508).base H) hClearUpk35))
    (keys_ls_hook_ok_of_mem (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl g W hG))
    (keys_ls_hook_ok_of_mem (cliExternsPlaced_dealloc_budget_sat mmpl g W hG))

theorem s7_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) (S : SpqrModel) :
    S7SeamPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base W.C A lim ctl uuidTryParse S (s7Env W.C.F uuidTryParse) := by
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  have _ := CryptoVerification.CliHandshake.TryDecPlaced.instIsLsBlockProg_508 H
  have hpk60 := subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded (ls_subroutine_ok_of_block (callerProg := (blkPC_60).rebase (blkPl_60).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
      (LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget.public_key_serialize_placed_ok
        ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hG.shim_eq), noAllocShim_hookOk⟩
        (cliExternsPlaced_alloc_budget_sat mmpl g W hG))))
  have hvmac62 := LibsignalBinary.Proofs.TripleRatchet.Mac.VerifyBudget.verifyMacWithAddresses_placed_cro_ok W.C M A lim uuidTryParse H
    (parseSid_61_ok H) (new_from_slice_60_cro_ok mmpl g W hG) hpk60
    (keys_ls_hook_ok_of_mem (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W (cliExternsPlaced_blackBox_budget_sat mmpl W)))
    (cliExternsPlaced_noAllocShim_budget_sat mmpl g W hG.shim_eq)
    (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl g W hG)
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W (cliExternsPlaced_compress256Multi_budget_sat mmpl W))
    (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG)
  exact LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.VerifyMacTrap507PlacedBudget.verifyMac_507_placed_ok W.C A lim ctl S H
    (keys_ls_subroutine_ok_of_block_cro (callerProg := (blkPC_508).rebase (blkPl_508).base H) hvmac62)
    (keys_ls_hook_ok_of_mem (cliExternsPlaced_shim_budget_sat mmpl g W hG.shim_eq))
    (keys_ls_hook_ok_of_mem (cliExternsPlaced_alloc_budget_sat mmpl g W hG))
    (keys_ls_hook_ok_of_mem (cliExternsPlaced_dealloc_budget_sat mmpl g W hG))

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudgetPart3
