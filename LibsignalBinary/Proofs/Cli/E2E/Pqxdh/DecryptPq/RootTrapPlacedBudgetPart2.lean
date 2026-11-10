/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.ChainLookup507PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.ChainLookupS0_507PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.ChainLookupS1Err507PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.DecryptTailTrap507PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SpqrRecvTrapV1_507PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget
import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.UuidFsPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.VecExtBudget
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.ExtBudget
import LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.MainBudget
import ProofLib.Placed.OpcodeExclusion

/-!
# Budget-Threaded Block `507` CLI Segment Seams (`ErrTail`, `S5`, `S8`, `S0`–`S2`)

CLI hook-table instantiations for `ErrTail`, `S5`, `S8`, and `S0`–`S2` on Block `507`.
-/
@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudgetPart2

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
  blkPC_57 blkPl_57 blkPC_252 blkPl_252 extract_withLsCodeLoaded libsignalMutatedBlocks
  libsignalSessionLib libsignalSessionLib_blocks_length ls_hook_ok_ultra_of_mem lsmpl
  withLsCodeLoaded)
open CryptoVerification.CliHandshake.TryDecPlaced (blkPC_508 blkPl_508 instIsLsBlockProg_508)
open CryptoVerification.E2E (aesDecHookMallocng formatInnerHook0)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (SendCall SpqrModel uuidTryParseCodeSpec)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced cliHookTablePlaced lsAesDecSym lsFormatInnerSym
  lsRustAllocSymCli lsRustAllocZeroedSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli
  lsRustReallocSymCli lsStringCloneSym
)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_other
)
open CryptoVerification.SignalSession.Cli.Slots (aesDec_row_placed blackBox_row_placed formatInner_row_placed)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (FormatInnerEnv aesDecBudgetSpec formatInnerBudgetEnvSpec formatInnerBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptTailTrapPlacedBudget (s8Env)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookupS1ErrPlacedBudget (S1TightSeamFreePlaced S1TightSeamPinnedFreePlaced)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget (ErrTailTightSeamPlaced S0PSeamPlaced S2SeamPlaced S5WTSeamPlaced S8SeamPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks cliExternsPlaced_dealloc_budget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (SpqrRecvBytesEnv SpqrV1PlacedSeams SpqrV1PlacedSeamsOfEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs (PqRecvEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

private def walkLsPatchSafe : Nat → List CodeBlock → Bool
  | _, [] => true
  | j, blk :: rest =>
    (decide (j ∈ libsignalMutatedBlocks) || (blk.patchSafe svc0Pat && blk.patchSafe msrTpidrEl0Pat)) && walkLsPatchSafe (j + 1) rest
private theorem walkLsPatchSafe_append : ∀ (k : Nat) (xs ys : List CodeBlock),
    walkLsPatchSafe k xs = true → walkLsPatchSafe (k + xs.length) ys = true → walkLsPatchSafe k (xs ++ ys) = true
  | _, [], _, _, hy => by simpa only [List.nil_append, List.length_nil, Nat.add_zero] using hy
  | k, _ :: xs, ys, hx, hy => by
    simp only [List.cons_append, walkLsPatchSafe, Bool.and_eq_true] at hx ⊢
    exact ⟨hx.1, walkLsPatchSafe_append (k + 1) xs ys hx.2 (by simpa only [List.length_cons, show k + 1 + xs.length = k + (xs.length + 1) by omega] using hy)⟩
private theorem walkLsPatchSafe_lo : walkLsPatchSafe 0 (libsignalSessionLib.blocks.take 312) = true := by decide +kernel
private theorem walkLsPatchSafe_hi : walkLsPatchSafe 312 (libsignalSessionLib.blocks.drop 312) = true := by decide +kernel
private theorem walkLsPatchSafe_ok : walkLsPatchSafe 0 libsignalSessionLib.blocks = true := by
  rw [← List.take_append_drop 312 libsignalSessionLib.blocks]
  exact walkLsPatchSafe_append 0 _ _ walkLsPatchSafe_lo (by rw [Nat.zero_add, List.length_take, libsignalSessionLib_blocks_length]; exact walkLsPatchSafe_hi)
private theorem walkLsPatchSafe_getD : ∀ (k i : Nat) (bs : List CodeBlock),
    walkLsPatchSafe k bs = true → i < bs.length → ¬(k + i ∈ libsignalMutatedBlocks) →
    (bs.getD i { code := [] }).patchSafe svc0Pat = true ∧ (bs.getD i { code := [] }).patchSafe msrTpidrEl0Pat = true
  | _, _, [], _, hi, _ => nomatch hi
  | _, 0, _ :: _, hw, _, hun => by
    simp only [walkLsPatchSafe, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hw; exact hw.1.resolve_left hun
  | k, i + 1, _ :: rest, hw, hi, hun => by
    simp only [walkLsPatchSafe, Bool.and_eq_true] at hw
    exact walkLsPatchSafe_getD (k + 1) i rest hw.2 (by simp at hi; omega) (by rwa [show (k + 1) + i = k + (i + 1) by omega])
private theorem flatMap_bytesOfWordLE_len {α : Type} (g : α → BitVec 32) :
    ∀ L : List α, (L.flatMap fun a => bytesOfWordLE (g a)).length = 4 * L.length
  | [] => rfl | _ :: L => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons, show (bytesOfWordLE _).length = 4 from rfl, flatMap_bytesOfWordLE_len g L]; omega
private def keepLs (pl : MultiPlacement) (a : BitVec 64) : Bool :=
  (List.range libsignalSessionLib.blocks.length).any fun j => !decide (j ∈ libsignalMutatedBlocks) && ProofLib.progKeep (libsignalSessionLib.blockProgram pl j) a
private theorem strip_lsCodeLoaded {pl : MultiPlacement} {m : Memory} (hcl : LibsignalCodeLoaded pl m) :
    LibsignalCodeLoaded pl (ProofLib.stripExecOutside (keepLs pl) m) := fun j hj hun X O svc => by
  have hL := hcl j hj hun X O svc; refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun k hk => ?_
  have hno := hL.no_wrap; let R := libsignalSessionLib.blockProgram pl j X O svc
  have hnm : ¬(j ∈ libsignalMutatedBlocks) := fun hm => Bool.noConfusion (Eq.mp hun hm)
  have hkj : ProofLib.progKeep (libsignalSessionLib.blockProgram pl j) (R.base + BitVec.ofNat 64 k) = true := by
    change decide ((R.base + BitVec.ofNat 64 k - R.base).toNat < R.code.length) = true
    rw [show R.base + BitVec.ofNat 64 k - R.base = BitVec.ofNat 64 k by bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true hk
  have hkeep : keepLs pl (R.base + BitVec.ofNat 64 k) = true :=
    List.any_eq_true.mpr ⟨j, List.mem_range.mpr hj, Eq.mpr (Bool.and_eq_true _ _) ⟨by simp [hun], hkj⟩⟩
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]
  exact ⟨hL.byte_eq k hk, hL.perm_eq k hk, hL.isLazyFree_eq k hk⟩
private theorem findSome?_const_none {α β : Type} : ∀ (l : List α), l.findSome? (fun _ => (none : Option β)) = none
  | [] => rfl | _ :: tl => findSome?_const_none tl
private theorem findSome?_trapHooks_some : ∀ (l : List (String × Nat)) {off : Nat} {f : State → State},
    (l.findSome? fun (n, o) => if o == off then Placed.BudgetVmSteps.trapHooks n else none) = some f → f = fun s => s.setStatus (.Exception "extern")
  | [], _, _, h => by simp at h
  | (_, o) :: tl, off, _, h => by
    simp only [List.findSome?_cons, Placed.BudgetVmSteps.trapHooks] at h
    by_cases ho : (o == off) = true <;> simp only [ho, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h; exacts [h.symm, findSome?_trapHooks_some tl h]
private theorem findSome?_stubs_eq_none (Hk : String → Option (State → State)) : ∀ (l : List (String × Nat)) {off : Nat},
    (l.findSome? fun (n, o) => if o == off then Placed.BudgetVmSteps.trapHooks n else none) = none → (l.findSome? fun (n, o) => if o == off then Hk n else none) = none
  | [], _, _ => rfl
  | (_, o) :: tl, off, h => by
    simp only [List.findSome?_cons, Placed.BudgetVmSteps.trapHooks] at h ⊢
    by_cases ho : (o == off) = true <;> simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢; · cases h
    · exact findSome?_stubs_eq_none Hk tl h
private theorem externAt?_trap_some {P : Program} {b pc : BitVec 64} {f : State → State} (h : (P.rebase b Placed.BudgetVmSteps.trapHooks).externAt? pc = some f) :
    f = fun s => s.setStatus (.Exception "extern") := by
  dsimp only [Program.externAt?, Program.hookAtOff?, Program.rebase] at h; simp only [ite_self, findSome?_const_none, Option.or_none] at h; exact findSome?_trapHooks_some P.stubs h
private theorem externAt?_trap_none (Hk : String → Option (State → State)) {P : Program} {b pc : BitVec 64} (h : (P.rebase b Placed.BudgetVmSteps.trapHooks).externAt? pc = none) :
    (P.rebase b Hk).externAt? pc = none := by
  dsimp only [Program.externAt?, Program.hookAtOff?, Program.rebase] at h ⊢; simp only [ite_self, findSome?_const_none, Option.or_none] at h ⊢; exact findSome?_stubs_eq_none Hk P.stubs h
private theorem fetch_ls_lift {pl : MultiPlacement} {m : Memory} {Q P : Program} {pc : BitVec 64} {inst : Instr}
    (hcl : LibsignalCodeLoaded pl m) (hextQ : Q.externAt? pc = none) (hextP : P.externAt? pc = none)
    (hfe' : Q.fetchMem (ProofLib.stripExecOutside (keepLs pl) m) pc = some inst) :
    P.fetchMem m pc = some inst ∧ inst.isSvc0 = false ∧ inst.isMsrTpidrEl0 = false := by
  have hal_pc : pc.toNat % 4 = 0 := by by_cases ha : pc.toNat % 4 = 0; · exact ha
                                       · simp [Program.fetchMem, hextQ, ha] at hfe'
  obtain ⟨hce', hdec'⟩ : (ProofLib.stripExecOutside (keepLs pl) m).canExec pc 4 = true ∧
      decode ((ProofLib.stripExecOutside (keepLs pl) m).read32 pc) = some inst := by simpa [Program.fetchMem, hextQ, hal_pc] using hfe'
  have hce : m.canExec pc 4 = true := by
    have hc0 := hce'; unfold Memory.canExec at hc0 ⊢; rw [Memory.allPerm_iff] at hc0 ⊢
    intro k hk; have hxk := hc0 k hk; rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
  have hr32 : (ProofLib.stripExecOutside (keepLs pl) m).read32 pc = m.read32 pc := by simp [Memory.read32, ProofLib.strip_read8]
  have hfe_P : P.fetchMem m pc = some inst := by simp [Program.fetchMem, hextP, hal_pc, hce, ← hr32, hdec']
  have hpx0 := by have hc0 := hce'; unfold Memory.canExec at hc0; rw [Memory.allPerm_iff] at hc0; simpa using hc0 0 (by omega)
  obtain ⟨j, hj_mem, hjb⟩ := List.any_eq_true.mp (ProofLib.strip_perm_x_imp hpx0).2
  have hj : j < libsignalSessionLib.blocks.length := List.mem_range.mp hj_mem; simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hjb
  let Rj := libsignalSessionLib.blockProgram pl j
  have hextR : Rj.externAt? pc = none := by
    dsimp only [Rj, Program.externAt?, Program.hookAtOff?, MultiPlacedLib.blockProgram, MultiPlacedLib.blockPlacement, PlacedLib.program]; simp only [ite_self, findSome?_const_none, Option.or_none]
  have hfe_R : Rj.fetchMem (ProofLib.stripExecOutside (keepLs pl) m) pc = some inst := by simp [Program.fetchMem, hextR, hal_pc, hce', hdec']
  have hun_eq : (j ∈ libsignalMutatedBlocks) = false := propext ⟨fun hm => False.elim (hjb.1 hm), fun hf => Bool.noConfusion hf⟩
  have hLj' := strip_lsCodeLoaded hcl j hj hun_eq (fun _ => none) (fun _ => none) Syscall.standard
  have hlt : (pc - Rj.base).toNat < Rj.code.length := of_decide_eq_true hjb.2
  have hmod_c : Rj.code.length % 4 = 0 := by
    change (((libsignalSessionLib.blockLib j).text).patched (libsignalSessionLib.blockPlacement pl j)).length % 4 = 0; unfold CodeBlock.patched; rw [flatMap_bytesOfWordLE_len]; omega
  have hin : (pc - Rj.base).toNat + 4 ≤ Rj.code.length := by
    have hhal : Rj.base.toNat % 4 = 0 := hLj'.aligned; have hb_lt : Rj.base.toNat < 18446744073709551616 := Rj.base.isLt; have hp_lt : pc.toNat < 18446744073709551616 := pc.isLt
    have hsub : (pc - Rj.base).toNat = (18446744073709551616 - Rj.base.toNat + pc.toNat) % 18446744073709551616 := BitVec.toNat_sub pc Rj.base; omega
  have hp := walkLsPatchSafe_getD 0 j libsignalSessionLib.blocks walkLsPatchSafe_ok hj (by simpa using hjb.1)
  have hH : HoldsBytes (ProofLib.stripExecOutside (keepLs pl) m) Rj.base Rj.code (fun _ => Perm.rx) := fun k hk => ⟨hLj'.byte_eq k hk, hLj'.perm_eq k hk, hLj'.isLazyFree_eq k hk⟩
  have h1 := Program.fetchMem_of_allInstrs_holdsBytes_in_code (PlacedLib.program_noSvc0_of_patchSafe hp.1 (libsignalSessionLib.blockPlacement pl j)) hLj'.aligned hLj'.no_wrap hH hin hfe_R
  have h2 := Program.fetchMem_of_allInstrs_holdsBytes_in_code (PlacedLib.program_noMsrTpidrEl0_of_patchSafe hp.2 (libsignalSessionLib.blockPlacement pl j)) hLj'.aligned hLj'.no_wrap hH hin hfe_R
  simp only [Bool.not_eq_true'] at h1 h2; exact ⟨hfe_P, h1, h2⟩
private noncomputable abbrev prog252 [LibsignalPlacement] (H : LibsignalHooks) : Program := (blkPC_252).rebase (blkPl_252).base H
private theorem steps_blk252_lift_ls [LibsignalPlacement] (H : LibsignalHooks)
    {s1' sf' : State} (hsteps : Steps (prog252 Placed.BudgetVmSteps.trapHooks) s1' sf') (hrun_f : sf'.status = .Running) :
    ∀ (s1 : State), s1' = ProofLib.stripS (keepLs lsmpl) s1 → LibsignalCodeLoaded lsmpl s1.mem →
      ∃ sf : State, sf' = ProofLib.stripS (keepLs lsmpl) sf ∧ Steps (prog252 H) s1 sf ∧ ProofLib.NonSyscallPreserved s1 sf ∧ sf.tpidrEl0 = s1.tpidrEl0 := by
  induction hsteps with
  | refl => exact fun s1 hs1 _ => ⟨s1, hs1, .refl s1, ProofLib.NonSyscallPreserved.refl s1, rfl⟩
  | @step _ sb' _ h1 hrest ih =>
    intro s1 hsa hcl1; subst hsa
    have hrb' : sb'.status = .Running := by cases hrest with | refl => exact hrun_f | step hs _ => cases hs <;> assumption
    cases h1 with
    | halt_unmapped _ _ _ | extern_fault _ _ _ => cases s1; cases hrb'
    | extern _ he _ _ => rw [externAt?_trap_some he] at hrb'; cases s1; cases hrb'
    | @exec inst hr1' hfe' =>
      have hr1 : s1.status = .Running := by cases s1; exact hr1'
      rw [show (ProofLib.stripS (keepLs lsmpl) s1).pc = s1.pc by cases s1; rfl,
        show (ProofLib.stripS (keepLs lsmpl) s1).mem = ProofLib.stripExecOutside (keepLs lsmpl) s1.mem by cases s1; rfl] at hfe'
      have hext_Q : (prog252 Placed.BudgetVmSteps.trapHooks).externAt? s1.pc = none := by
        cases he : (prog252 Placed.BudgetVmSteps.trapHooks).externAt? s1.pc with | none => rfl | some _ => unfold Program.fetchMem at hfe'; rw [he] at hfe'; cases hfe'
      have hext_P := externAt?_trap_none H hext_Q; obtain ⟨hfe_P, hnsvc0, hnmsr⟩ := fetch_ls_lift hcl1 hext_Q hext_P hfe'
      have hev_Q : (prog252 Placed.BudgetVmSteps.trapHooks).evalInst inst (ProofLib.stripS (keepLs lsmpl) s1) = ProofLib.stripS (keepLs lsmpl) (execInst inst s1) := by
        rw [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
      have hstep_P : Step (prog252 H) s1 (execInst inst s1) := by have := Step.exec (prog := prog252 H) hr1 hfe_P; rwa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] at this
      have htp_1 : (execInst inst s1).tpidrEl0 = s1.tpidrEl0 := Step.tpidrEl0_of_noMsrTpidrEl0
        (fun _ hfi => by rw [hfe_P] at hfi; injection hfi with h_eq; subst h_eq; exact hnmsr) (fun _ hfk => by rw [hext_P] at hfk; cases hfk) hstep_P
      obtain ⟨sf, hsf_eq, hsteps_P, hnsp_rest, htp_rest⟩ := ih hrun_f (execInst inst s1) hev_Q (hcl1.of_keepsFrozen hstep_P.keepsFrozen)
      exact ⟨sf, hsf_eq, .step hstep_P hsteps_P, ProofLib.NonSyscallPreserved.trans (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1) hnsp_rest, htp_rest.trans htp_1⟩
private theorem uuidTryParse_vm_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok (prog252 H) (blkPl_252).base (withLsCodeLoaded lsmpl (withVmPreserved (uuidTryParseCodeSpec uuidTryParse))) := by
  apply subroutine_ok_intro; intro x R s0 hpc hrun hpre hal _; obtain ⟨hcl, hpre_core⟩ := extract_withLsCodeLoaded hpre
  let keep := keepLs lsmpl
  have hQ_eq := (inferInstance : IsLsBlockProg (prog252 Placed.BudgetVmSteps.trapHooks) 252 Placed.BudgetVmSteps.trapHooks).eq_blockProgram
  have hL_Q : (prog252 Placed.BudgetVmSteps.trapHooks).CodeLoaded (ProofLib.stripExecOutside keep s0.mem) :=
    hQ_eq ▸ strip_lsCodeLoaded hcl 252 (by decide) (by decide) Placed.BudgetVmSteps.trapHooks (fun _ => none) Syscall.standard
  obtain ⟨R_view, hm_strip, hunstrip⟩ := ProofLib.strip_frame keep hpre_core
  have hm_s : (ProofLib.stripS keep s0).mem ⊨ (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse).keepsFs).pre x (ProofLib.stripS keep s0) ∗ R_view := by
    dsimp only [withLsCodeLoaded, Spec.keepsFs]; rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨by cases s0; exact strip_lsCodeLoaded hcl, by cases s0; exact hm_strip⟩
  obtain ⟨sf', hstepsQ, ⟨hpc_f', hrun_f', hpost', hcc'⟩ | ⟨_, hoom'⟩⟩ :=
    subroutine_ok_apply_full (oom := fun _ => False) (CryptoVerification.SignalSession.Cli.MainHops.UuidFs.uuidTryParse_placed_okFs_F Placed.BudgetVmSteps.trapHooks)
      x R_view (by cases s0; exact hpc) (by cases s0; exact hrun) hm_s (by cases s0; exact hal)
      (fun _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ ho => not_satisfies_false_sepConj ho) hL_Q
  · obtain ⟨sf, hsf_eq, hstepsP, hnsp, htp⟩ := steps_blk252_lift_ls H hstepsQ hrun_f' s0 rfl hcl
    have hpost_fs := hunstrip (fun a => congrFun hnsp.2.1 a)
      (show ProofLib.stripExecOutside keep sf.mem ⊨ (uuidTryParseCodeSpec uuidTryParse).keepsFs.post x s0 sf ∗ R_view by
        rw [hsf_eq] at hpost'; cases s0; cases sf; exact hpost')
    dsimp only [Spec.keepsFs] at hpost_fs; rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_fs
    refine ⟨sf, hstepsP, Or.inl ⟨by rw [hsf_eq] at hpc_f'; cases s0; cases sf; exact hpc_f', by rw [hsf_eq] at hrun_f'; cases sf; exact hrun_f', ?_,
      ⟨by have h1 := hcc'.1; rw [hsf_eq] at h1; cases s0; cases sf; exact h1, by have h2 := hcc'.2; rw [hsf_eq] at h2; cases s0; cases sf; exact h2⟩⟩⟩
    dsimp only [withLsCodeLoaded, withVmPreserved]; rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hnsp.toVmPreserved htp, hpost_fs.2⟩
  · exact False.elim hoom'
private theorem sub_ok_same_blk [LibsignalPlacement] {α : Type} {P Q : Program}
    {i : Nat} {H : LibsignalHooks} [hP : IsLsBlockProg P i H] [hQ : IsLsBlockProg Q i H]
    {entry : BitVec 64} {spec : Spec α} (h : subroutine_ok P entry spec) : subroutine_ok Q entry spec :=
  (hP.eq_blockProgram.trans hQ.eq_blockProgram.symm) ▸ h
private theorem cliGhost_row (mmpl : MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
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

private theorem formatInner_budget_sat {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (mmpl : MultiPlacement) (g : CliGhostHooks) (W : CliHooks) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerBudgetSpec M A lim) :=
  ⟨formatInnerHook0, cliGhost_row mmpl g W (formatInner_row_placed mmpl W),
    Heap.Fine.formatInnerHook0_budget_ok M A lim⟩

private theorem trFrom_57_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    subroutine_ok
      ((blkPC_57).rebase (blkPl_57).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_57).base
      (TripleRatchet.ReceiveRatchet.From.Step244PlacedBudget.trFromPlacedSpec M A lim) :=
  TripleRatchet.ReceiveRatchet.From.MainBudget.trFrom_placed_ok
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)
    (sub_ok_same_blk (TripleRatchet.Getters.IdentityBudget.remote_identity_key_placed_ok A.repAlloc
      (cliGhostExterns g (cliExternsPlaced mmpl W))))
    (sub_ok_same_blk (TripleRatchet.Getters.Drops.SignalProtocolError.ExtBudget.drop_spe_placed_ok
      (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)))
    (sub_ok_same_blk (TripleRatchet.Getters.Drops.Chain.VecExtBudget.drop_vec_chain_placed_ok
      (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)))

theorem errTail_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    ErrTailTightSeamPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base W.C A lim ctl uuidTryParse S tdEnv := by
  exact ChainLookupS1Err507PlacedBudget.errTail_507_placed_okT
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)

theorem pqRecv_507_cli_ofEnv [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {fmtEnv : List AllocEvent → Prop}
    (mmpl : MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl g W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hFmtInner : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerBudgetEnvSpec M A lim fmtEnv))
    (ctl : BitVec 64) :
    S5WTSeamPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base tokenInitPlacedAt W.C A lim ctl uuidTryParse
      (spqrV1 W.C.F W.Q.K) (PqRecvEnv (spqrV1 W.C.F W.Q.K) RecvBytesEnv fmtEnv) := by
  have _ := instIsLsBlockProg_508 (cliGhostExterns g (cliExternsPlaced mmpl W))
  exact SpqrRecvTrapV1_507PlacedBudget.pqRecv_507_placed_ok_WT_cli_of_seams_ofEnv hSpqr ctl
    (ls_hook_ok_ultra_of_mem hFmtInner)
    (ls_hook_ok_ultra_of_mem (cliExternsPlaced_dealloc_budget_sat mmpl g W hG))

theorem pqRecv_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl g W) (ctl : BitVec 64) :
    S5WTSeamPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base tokenInitPlacedAt W.C A lim ctl uuidTryParse
      (spqrV1 W.C.F W.Q.K) (PqRecvEnv (spqrV1 W.C.F W.Q.K) SpqrRecvBytesEnv FormatInnerEnv) := by
  exact pqRecv_507_cli_ofEnv mmpl g W hG hSpqr (formatInner_budget_sat mmpl g W) ctl

theorem aesDecrypt_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (ctl : BitVec 64) (S : SpqrModel) :
    S8SeamPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base W.C A lim ctl uuidTryParse S s8Env := by
  have _ := instIsLsBlockProg_508 (cliGhostExterns g (cliExternsPlaced mmpl W))
  exact DecryptTailTrap507PlacedBudget.aesDecrypt_507_placed_ok W.C A lim ctl S
    (cliGhostExterns g (cliExternsPlaced mmpl W))
    (ls_hook_ok_ultra_of_mem
      ⟨aesDecHookMallocng mmpl W.C.D, cliGhost_row mmpl g W (aesDec_row_placed mmpl W), hAesDec⟩)
    (ls_hook_ok_ultra_of_mem (formatInner_budget_sat mmpl g W))
    (ls_hook_ok_ultra_of_mem (cliExternsPlaced_dealloc_budget_sat mmpl g W hG))

theorem s0_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (ctl : BitVec 64) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    S0PSeamPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base W.C A lim ctl uuidTryParse S tdEnv := by
  exact ChainLookupS0_507PlacedBudget.s0_507_placed_ok_P_of_callees
    (cliGhost_row mmpl g W (blackBox_row_placed mmpl W))
    (uuidTryParse_vm_placed_ok (cliGhostExterns g (cliExternsPlaced mmpl W)))

theorem s1_pinned_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    S1TightSeamPinnedFreePlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base W.C A lim ctl uuidTryParse S tdEnv (fun _ => FreeOnlyEvs) := by
  exact ChainLookupS1Err507PlacedBudget.loadRatchet_pinned_507_placed_okT
    (trFrom_57_cli mmpl g W hG) (fun _ _ h => h)

theorem s1_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    S1TightSeamFreePlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base W.C A lim ctl uuidTryParse S tdEnv (fun _ => FreeOnlyEvs) := by
  exact ChainLookupS1Err507PlacedBudget.loadRatchet_507_placed_okT
    (trFrom_57_cli mmpl g W hG) (fun _ _ h => h)

theorem s2_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64) :
    S2SeamPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base A lim ctl := by
  exact ChainLookup507PlacedBudget.findChain_507_placed_ok_of_bb
    (cliGhost_row mmpl g W (blackBox_row_placed mmpl W))

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudgetPart2
