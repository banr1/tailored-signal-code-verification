/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import ProofLib -- shake: keep
public meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget -- shake: keep
public import ProofLib.SepLogic.Bytes
public import ProofLib.SepLogic.WP.Apply
public import LibsignalBinary.Proofs.SignalSession.Cli.Fs
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import Init.Data.String.Defs
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Segment and Framing Helpers for Budget-Threaded Arm `R0`

Internal layout, framing, and weakest-precondition segment lemmas on Block `579` supporting
`R0ProofPlacedBudget`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudgetAux

open Arm64 Arm64.Process ProofLib SepProp
open AsmConstants
  (boxSliceLenOff decResultVecOff speInvalidStateFnOff spePayloadOff speSize vecSize)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsroCheck lsro_intro_chk lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (TraceFsSound subroutine_ok_rocl_of_withLsCodeRoLoaded withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost noneCap okTagVec protocolAddressAt speAt speWord strRefAt uuidTryParse
   vecResultAt)
open CryptoVerification.RustHeap (LayoutOk RustAlloc vecHeader vecU8 vecU8At)
open CryptoVerification.SignalSession (Cmd lsFromUtf8Sym lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli
  (StoresGhost dirAt files_eq_at_callback getResultAt pathOf utf8 withFsInv_entry)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV CallV CallW LsCodeInv RunCall addrParse addrWords callAt callHeap cliIo cliWrOk
   cliWrOk_own coinsInstalledPlaced inputOf mainSaved main_call_rocl_steps ownedBytes parseArgs
   runResSize storesAt)
open CryptoVerification.SignalSession.Cli.Path.Helpers (memRegion_1_eq_pointsTo8)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_553)
open CryptoVerification.SignalSession.Cli.Run.Placed (blkPl_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtRunEntryPlaced Bytes MeAtDispatch RunSem addrNameHeap addrUpperAt dispatchCells
   dispatchMeHeap protocolAddressAt_eq_parts runFiles runFsp runLocalBytes runLocals runLocalsFrom
   runLocals_empty_eq runOom runPcPlaced runPcPlaced_eq runProgPlaced runProgPlaced_eq runSaved)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget
  (sepWP_with_vm_oom)

/-! ## Framing and Layout Helpers -/

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

scoped syntax "by_vm_open " tacticSeq : tactic
scoped elab_rules : tactic
  | `(tactic| by_vm_open $tac:tacticSeq) => do
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply sepWP_with_vm_oom))
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      let e2 := ty.getArg! 0
      let e1 := e2.getArg! 0
      let ty1 := Lean.mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
      let g1 ← Lean.Meta.mkFreshExprMVar ty1
      let savedGoals ← Lean.Elab.Tactic.getGoals
      Lean.Elab.Tactic.setGoals [g1.mvarId!]
      Lean.Elab.Tactic.evalTactic (← `(tactic| ($tac)))
      let rem ← Lean.Elab.Tactic.getGoals
      unless rem.isEmpty do
        throwError "by_vm_open: inner tactic left {rem.length} unsolved goal(s)"
      Lean.Elab.Tactic.setGoals savedGoals.tail!
      let prf1 ← Lean.instantiateMVars g1
      let prf2 := prf1.replace fun sub =>
        if sub.eqv e2 then some e2 else if sub.eqv e1 then some e2 else none
      g.assign prf2

@[local simp, local arm64_norm, local wp_norm]
theorem r0_pool_setMem_write64_2_rp {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (a1 v1 a2 v2 : BitVec 64) :
    A.pool lim st (s.setMem ((s.mem.write64 a1 v1).write64 a2 v2)) = A.pool lim st s :=
  A.pool_setMem_of_perm lim st s _ (by simp [Memory.perm_write64])

local macro "r0_close_post_rp" : tactic =>
  `(tactic| (repeat' apply And.intro; all_goals (try simp only [wp_norm, arm64_norm, runPcPlaced_eq, eq_self, *]; try rfl)))

private theorem r0_byteArray_toList_loop_rp (l : List UInt8) :
    ∀ k i r, l.length - i = k →
      ByteArray.toList.loop ⟨⟨l⟩⟩ i r = r.reverse ++ l.drop i := by
  intro k; induction k with
  | zero =>
    intro i r hk; rw [ByteArray.toList.loop.eq_1]
    have hni : ¬ i < (⟨⟨l⟩⟩ : ByteArray).size := by change ¬ i < l.length; omega
    simp only [hni, ↓reduceIte]; rw [List.drop_eq_nil_of_le (by omega), List.append_nil]
  | succ k ih =>
    intro i r hk; rw [ByteArray.toList.loop.eq_1]
    have hi : i < (⟨⟨l⟩⟩ : ByteArray).size := by change i < l.length; omega
    have hget : (⟨⟨l⟩⟩ : ByteArray).get! i = l[i]'hi := getElem!_pos (⟨l⟩ : Array UInt8) i hi
    simp only [hi, ↓reduceIte]
    rw [ih (i + 1) ((⟨⟨l⟩⟩ : ByteArray).get! i :: r) (by omega),
      List.reverse_cons, List.append_assoc, List.singleton_append, hget, ← List.drop_eq_getElem_cons]

private theorem r0_toList_toByteArray_eq_rp (l : List UInt8) : l.toByteArray.toList = l := by
  have h1 : l.toByteArray = ⟨⟨l⟩⟩ := by ext1; exact List.data_toByteArray
  rw [h1, ByteArray.toList.eq_1, r0_byteArray_toList_loop_rp l l.length 0 [] (Nat.sub_zero _),
    List.reverse_nil, List.nil_append, List.drop_zero]

theorem r0_utf8_eq_flatMap_rp (s : String) :
    utf8 s = (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat := by
  conv_lhs => rw [← String.ofList_toList (s := s)]
  unfold utf8
  simp only [String.toUTF8_eq_toByteArray, String.toByteArray_ofList, List.utf8Encode.eq_1,
    r0_toList_toByteArray_eq_rp]

theorem r0_tri_utf8_eq_flatMap_rp (s : String) :
    CryptoVerification.LibsignalTripleRatchetRepr.utf8 s =
      (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat := by
  conv_lhs => rw [← String.ofList_toList (s := s)]
  unfold CryptoVerification.LibsignalTripleRatchetRepr.utf8
  simp only [String.toUTF8_eq_toByteArray, String.toByteArray_ofList, List.utf8Encode.eq_1,
    r0_toList_toByteArray_eq_rp]

abbrev r0_addrSym_rp : String := "libsignal_cli:.rodata..Lanon.54"

theorem r0_utf8_address_rp :
    utf8 "address" = [0x61#8, 0x64#8, 0x64#8, 0x72#8, 0x65#8, 0x73#8, 0x73#8] := by
  rw [r0_utf8_eq_flatMap_rp]; rfl

theorem r0_lsroCheck_address_rp : lsroCheck r0_addrSym_rp (utf8 "address") = true := by
  rw [r0_utf8_address_rp]; decide +kernel

theorem r0_sepWPp_intro_address_rp [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : CodeOk s.mem)
    (h : SepWPp prog ret s (((lsρ r0_addrSym_rp) ↦ᵣ utf8 "address") ∗ P) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  have hm' := lsro_intro_chk (LsCodeInv.toRoCl hinv).2 r0_lsroCheck_address_rp hm
  exact h R (by simpa only [lsρ, sepConj_assoc] using hm') hL

theorem r0_extractLsb_append_lo_rp (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by bv_bits
theorem r0_extractLsb_append_hi_rp (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by bv_bits
theorem r0_calleeSavedVRegs_q0_rp (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 0#5 v) = calleeSavedVRegs s := by
  simp [calleeSavedVRegs, State.writeVReg128, VRegFile.calleeSaved, VRegFile.write, VRegFile.read]
theorem r0_calleeSavedVRegs_writeReg64_rp (s : State) (r : Reg) (v : BitVec 64) :
    calleeSavedVRegs (s.writeReg64 r v) = calleeSavedVRegs s := by cases s; cases r <;> rfl
theorem r0_calleeSavedVRegs_setPC_rp (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by cases s; rfl
theorem r0_calleeSavedVRegs_setMem_rp (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl
theorem r0_calleeSavedVRegs_setPState_rp (s : State) (ps : PState) :
    calleeSavedVRegs (s.setPState ps) = calleeSavedVRegs s := by cases s; rfl
theorem r0_readReg64_setPState_rp (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
theorem r0_sp_setPState_rp (s : State) (ps : PState) : (s.setPState ps).sp = s.sp := by cases s; rfl
theorem r0_mem_setPState_rp (s : State) (ps : PState) : (s.setPState ps).mem = s.mem := by cases s; rfl
theorem r0_status_setPState_rp (s : State) (ps : PState) :
    (s.setPState ps).status = s.status := by cases s; rfl
theorem r0_trace_setPState_rp (s : State) (ps : PState) :
    (s.setPState ps).trace = s.trace := by cases s; rfl
theorem r0_symtab_setPState_rp (s : State) (ps : PState) :
    (s.setPState ps).symtab = s.symtab := by cases s; rfl
theorem r0_fs_setPState_rp (s : State) (ps : PState) : (s.setPState ps).fs = s.fs := by cases s; rfl
theorem r0_fs_writeReg64_rp (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).fs = s.fs := by cases s; cases r <;> rfl
theorem r0_fs_writeVReg128_rp (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).fs = s.fs := by cases s; rfl
theorem r0_fs_setPC_rp (s : State) (pc : BitVec 64) : (s.setPC pc).fs = s.fs := by cases s; rfl
theorem r0_fs_setMem_rp (s : State) (m : Memory) : (s.setMem m).fs = s.fs := by cases s; rfl
theorem r0_tpidrEl0_setPState_rp (s : State) (ps : PState) :
    (s.setPState ps).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
theorem r0_tpidrEl0_writeVReg128_rp (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
theorem r0_tpidrEl0_writeReg64_rp (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).tpidrEl0 = s.tpidrEl0 := by cases s; cases r <;> rfl
theorem r0_tpidrEl0_setPC_rp (s : State) (pc : BitVec 64) :
    (s.setPC pc).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
theorem r0_tpidrEl0_setMem_rp (s : State) (m : Memory) :
    (s.setMem m).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
theorem r0_sp_step1_rp (sp0 : BitVec 64) :
    (sp0 - 96#64) - 4096#64 = sp0 - 4192#64 := by rw [BitVec.sub_sub]; rfl
theorem r0_sp_step2_rp (sp0 : BitVec 64) :
    (sp0 - 4192#64) - 4096#64 = sp0 - 8288#64 := by rw [BitVec.sub_sub]; rfl
theorem r0_sp_step3_rp (sp0 : BitVec 64) :
    (sp0 - 8288#64) - 2544#64 = sp0 - 0x2a50#64 := by rw [BitVec.sub_sub]; rfl

attribute [local simp, local arm64_norm, local wp_norm]
  r0_extractLsb_append_lo_rp r0_extractLsb_append_hi_rp r0_calleeSavedVRegs_q0_rp
  r0_calleeSavedVRegs_writeReg64_rp r0_calleeSavedVRegs_setPC_rp r0_calleeSavedVRegs_setMem_rp
  r0_calleeSavedVRegs_setPState_rp r0_readReg64_setPState_rp r0_sp_setPState_rp
  r0_mem_setPState_rp r0_status_setPState_rp r0_trace_setPState_rp r0_symtab_setPState_rp
  r0_fs_setPState_rp r0_fs_writeReg64_rp r0_fs_writeVReg128_rp r0_fs_setPC_rp r0_fs_setMem_rp
  r0_tpidrEl0_setPState_rp r0_tpidrEl0_writeVReg128_rp r0_tpidrEl0_writeReg64_rp
  r0_tpidrEl0_setPC_rp r0_tpidrEl0_setMem_rp
  r0_sp_step1_rp r0_sp_step2_rp r0_sp_step3_rp

theorem r0_spAligned_rp {s0 s : State} (h0 : s0.spAligned = true) (hsp : s.sp = runFsp s0) :
    s.spAligned = true := by
  have h1 : ((s0.sp - 0x2a50#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x2a50#64 h0
  show (s.sp &&& 15#64 == 0#64) = true; rwa [hsp]

theorem r0_sepWPp_drop_left_rp {prog : Program} {ret : BitVec 64} {s : State}
    {Drop Keep : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWPp prog ret s Keep Q Qp oom) : SepWPp prog ret s (Drop ∗ Keep) Q Qp oom := by
  intro R hm hL; rw [sepConj_assoc] at hm; exact h R (Satisfies.of_sep_right hm) hL

theorem r0_sepWPp_exists_all_rp {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {Φ : α → SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x : α, SepWPp prog ret s (Φ x) Q Qp oom) :
    SepWPp prog ret s (∃∗ x : α, Φ x) Q Qp oom := by
  intro R hm hL; rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨x, hmx⟩; exact h x R hmx hL

theorem r0_sepWPp_exists_left_rp {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {Φ : α → SepProp} {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x : α, SepWPp prog ret s (Φ x ∗ F) Q Qp oom) :
    SepWPp prog ret s ((∃∗ x : α, Φ x) ∗ F) Q Qp oom := by
  intro R hm hL; rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨x, hmx⟩; exact h x R (by simpa only [sepConj_assoc] using hmx) hL

theorem r0_sepWPp_pure_left_rp {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : φ → SepWPp prog ret s F Q Qp oom) : SepWPp prog ret s (⌜φ⌝ ∗ F) Q Qp oom := by
  intro R hm hL; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact h hm.1 R hm.2 hL

theorem r0_frame_seq_rp [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {prog : Program} {mid ret : BitVec 64} {s : State} {P_in P P' F : SepProp}
    {post : State → Prop} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : CodeOk s.mem) (hP : P_in ⊢ P ∗ F)
    (h : SepWP prog mid s P (fun s1 P1 => post s1 ∧ P1 = P') (fun _ => ⌜False⌝))
    (hk : ∀ s1 : State, CodeOk s1.mem → s1.pc = mid → s1.status = .Running → post s1 →
      SepWPp prog ret s1 (P' ∗ F) Q Qp oom) :
    SepWPp prog ret s P_in Q Qp oom := by
  intro R hm hL
  have hm0 : s.mem ⊨ P ∗ (F ∗ R) := by
    simpa only [sepConj_assoc] using Satisfies.mono (sepConj_mono_left hP) hm
  rcases h.elim hm0 hL with ⟨s1, hsteps, ⟨hpc1, hrun1, P1, hm1, hpost1, rfl⟩ | ⟨_, hfalse⟩⟩
  · obtain ⟨sf, hsteps2, hout⟩ :=
      hk s1 (LsCodeInv.of_keepsFrozen hinv hsteps.keepsFrozen) hpc1 hrun1 hpost1 R
        (by simpa only [sepConj_assoc] using hm1) (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps2, hout⟩
  · exact (not_satisfies_false_sepConj hfalse).elim

theorem r0_call_rocl_steps_rp [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {α : Type} {H : LibsignalHooks} {entry ret_pc ret : BitVec 64} {spec : Spec α}
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop} (x : α)
    (hcall : subroutine_ok (runProgPlaced H) entry (withLsRoCl lsmpl spec))
    (hinv : CodeOk s.mem) (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hP : P ⊢ spec.pre x s ∗ F)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F) := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ runOom s0 sf ∗ R') := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sf : State, Steps (runProgPlaced H) s sf → CodeOk sf.mem →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp (runProgPlaced H) ret sf (spec.post x s sf ∗ F) Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) ret s P Q Qp (runOom s0) :=
  main_call_rocl_steps (oom := runOom s0) x hcall hinv hpc hrun hsp hlr hP hpanic hexit hoom hnext s0

theorem r0_call_lscro_steps_rp [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {α : Type} {H : LibsignalHooks} {entry ret_pc ret : BitVec 64} {spec : Spec α}
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop} (x : α)
    (hcall : subroutine_ok (runProgPlaced H) entry (withLsCodeRoLoaded lsmpl spec))
    (hinv : CodeOk s.mem) (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hP : P ⊢ spec.pre x s ∗ F)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F) := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ runOom s0 sf ∗ R') := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sf : State, Steps (runProgPlaced H) s sf → CodeOk sf.mem →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp (runProgPlaced H) ret sf (spec.post x s sf ∗ F) Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) ret s P Q Qp (runOom s0) :=
  r0_call_rocl_steps_rp x (subroutine_ok_rocl_of_withLsCodeRoLoaded hcall)
    hinv hpc hrun hsp hlr hP hpanic hexit hoom hnext

theorem r0_files_eq_of_trace_eq_rp {prog : Program} {s sf : State}
    (hfs : TraceFsSound prog) (hsteps : Steps prog s sf) (htr : sf.trace = s.trace) :
    sf.fs.files = s.fs.files :=
  files_eq_at_callback ((withFsInv_entry s).of_steps hfs hsteps)
    (by rw [htr, List.append_nil]) (fun _ h => by cases h)

theorem r0_own_wrOk_rp :
    cliWrOk (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) := by
  apply cliWrOk_own
  · rw [r0_utf8_address_rp]; refine ⟨?_, ⟨0x61#8, List.Mem.head _, by decide⟩⟩
    rintro b hb; rcases hb with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, hb⟩⟩⟩⟩⟩⟩⟩
    all_goals first | decide | cases hb
  · rw [r0_utf8_address_rp]; decide

theorem r0_call_not_keygen_rp [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {s0 : State} (he : AtRunEntryPlaced CodeOk S g s0) :
    ∀ me n, g.c ≠ .keygen me n := by
  intro me n hkg; rcases he.rel.1 with ⟨_, cmd, _, hargv⟩; have hp := he.parse; rw [hargv, hkg] at hp
  have hb_i : bytesOfString "init" = [0x69#8, 0x6e#8, 0x69#8, 0x74#8] := by simp [bytesOfString]
  have hb_s : bytesOfString "send" = [0x73#8, 0x65#8, 0x6e#8, 0x64#8] := by simp [bytesOfString]
  have hb_r : bytesOfString "recv" = [0x72#8, 0x65#8, 0x63#8, 0x76#8] := by simp [bytesOfString]
  have hu_i : utf8 "init" = [0x69#8, 0x6e#8, 0x69#8, 0x74#8] := by rw [r0_utf8_eq_flatMap_rp]; rfl
  have hu_s : utf8 "send" = [0x73#8, 0x65#8, 0x6e#8, 0x64#8] := by rw [r0_utf8_eq_flatMap_rp]; rfl
  have hu_r : utf8 "recv" = [0x72#8, 0x65#8, 0x63#8, 0x76#8] := by rw [r0_utf8_eq_flatMap_rp]; rfl
  have hu_k : utf8 "keygen" = [0x6b#8, 0x65#8, 0x79#8, 0x67#8, 0x65#8, 0x6e#8] := by rw [r0_utf8_eq_flatMap_rp]; rfl
  cases cmd <;> simp [Cmd.argv, parseArgs, hb_i, hb_s, hb_r, hu_i, hu_s, hu_r, hu_k] at hp

theorem r0_sepProp_ext_rp {P Q : SepProp} (h1 : P ⊢ Q) (h2 : Q ⊢ P) : P = Q :=
  Entails.antisymm h1 h2

theorem r0_apply_head_rp {A B F P : SepProp} (h : A ⊢ B) (heq : P = A ∗ F) : P ⊢ B ∗ F := by
  rw [heq]; exact sepConj_mono_left h

def r0_gaps_rp (fsp : BitVec 64) : SepProp :=
  memRegion fsp 0x1d0 ∗ memRegion (fsp + 0x1e0#64) (0x4d0 - 0x1e0) ∗
    memRegion (fsp + 0x500#64) (0x1750 - 0x500) ∗ memRegion (fsp + 0x1770#64) (runLocalBytes - 0x1770)
attribute [local irreducible] r0_gaps_rp

def r0_storesRest_rp (A : RustAlloc) (a : BitVec 64) (g : StoresGhost) : SepProp :=
  dirAt A (a + 0x28#64) g.identity.peers ∗ dirAt A (a + 0x50#64) g.signed ∗
    dirAt A (a + 0x78#64) g.kyber.oneTime ∗ dirAt A (a + 0xa0#64) g.kyber.lastResort ∗
    dirAt A (a + 0xc8#64) g.oneTime ∗ dirAt A (a + 0xf0#64) g.sessions ∗
    dirAt A (a + 0x118#64) g.pub

theorem r0_storesAt_eq_rp (A : RustAlloc) (a : BitVec 64) (g : StoresGhost) :
    storesAt A a g = dirAt A a g.identity.own ∗ r0_storesRest_rp A a g := rfl

theorem r0_memRegion_8_24_rp (a : BitVec 64) :
    memRegion a 32 = memRegion a 8 ∗ memRegion (a + 8#64) 24 :=
  ProofLib.memRegion_split a 8 24 (by decide)

theorem r0_memRegion_two_words_rp (a : BitVec 64) :
    memRegion a 16 = (∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64, (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1)) := by
  rw [ProofLib.memRegion_split a 8 8 (by decide), ProofLib.memRegion_eight a,
      ProofLib.memRegion_eight (a + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem r0_two_words_entails_memRegion_rp (a u0 u1 : BitVec 64) :
    (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ⊢ memRegion a 16 := by
  rw [r0_memRegion_two_words_rp a]
  exact Entails.sepExists_right u1 (Entails.sepExists_right u0 (Entails.refl _))

theorem r0_three_words_entails_24_rp (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
  have h1 := ProofLib.memRegion_split a 8 16 (by decide)
  have ha : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  rw [h1, ← ha]
  exact sepConj_mono (pointsTo64_entails_memRegion a w0) (r0_two_words_entails_memRegion_rp _ w1 w2)

theorem r0_four_words_entails_32_rp (a w0 w1 w2 w3 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ⊢
      memRegion a 32 := by
  have h1 := ProofLib.memRegion_split a 8 24 (by decide)
  have ha16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  have ha24 : (a + 8#64) + 16#64 = a + 24#64 := by bv_omega
  rw [h1, ← ha16, ← ha24]
  exact sepConj_mono (pointsTo64_entails_memRegion a w0) (r0_three_words_entails_24_rp _ w1 w2 w3)

theorem r0_memRegion_12_cells_rp (b : BitVec 64) :
    memRegion b 0x60 = (∃∗ v11 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v9 : BitVec 64,
      ∃∗ v8 : BitVec 64, ∃∗ v7 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v5 : BitVec 64,
      ∃∗ v4 : BitVec 64, ∃∗ v3 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v1 : BitVec 64,
      ∃∗ v0 : BitVec 64,
        (b ↦₆₄ v0) ∗ ((b + 0x08#64) ↦₆₄ v1) ∗ ((b + 0x10#64) ↦₆₄ v2) ∗ ((b + 0x18#64) ↦₆₄ v3) ∗
        ((b + 0x20#64) ↦₆₄ v4) ∗ ((b + 0x28#64) ↦₆₄ v5) ∗ ((b + 0x30#64) ↦₆₄ v6) ∗
        ((b + 0x38#64) ↦₆₄ v7) ∗ ((b + 0x40#64) ↦₆₄ v8) ∗ ((b + 0x48#64) ↦₆₄ v9) ∗
        ((b + 0x50#64) ↦₆₄ v10) ∗ ((b + 0x58#64) ↦₆₄ v11)) := by
  have step (a : BitVec 64) (k : Nat) (hk : 8 + k ≤ 2 ^ 64) :
      memRegion a (8 + k) = (∃∗ v : BitVec 64, a ↦₆₄ v) ∗ memRegion (a + 8#64) k := by
    rw [ProofLib.memRegion_split a 8 k hk, ProofLib.memRegion_eight]
  rw [step b 88 (by decide), step _ 80 (by decide), step _ 72 (by decide), step _ 64 (by decide),
    step _ 56 (by decide), step _ 48 (by decide), step _ 40 (by decide), step _ 32 (by decide),
    step _ 24 (by decide), step _ 16 (by decide), step _ 8 (by decide), ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem r0_memRegion_saved_open_rp (s0 : State) :
    memRegion (s0.sp - 0x60#64) 0x60 = (∃∗ v11 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v9 : BitVec 64,
      ∃∗ v8 : BitVec 64, ∃∗ v7 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v5 : BitVec 64,
      ∃∗ v4 : BitVec 64, ∃∗ v3 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v1 : BitVec 64,
      ∃∗ v0 : BitVec 64,
        ((s0.sp - 0x60#64) ↦₆₄ v0) ∗ ((s0.sp - 0x58#64) ↦₆₄ v1) ∗ ((s0.sp - 0x50#64) ↦₆₄ v2) ∗
        ((s0.sp - 0x48#64) ↦₆₄ v3) ∗ ((s0.sp - 0x40#64) ↦₆₄ v4) ∗ ((s0.sp - 0x38#64) ↦₆₄ v5) ∗
        ((s0.sp - 0x30#64) ↦₆₄ v6) ∗ ((s0.sp - 0x28#64) ↦₆₄ v7) ∗ ((s0.sp - 0x20#64) ↦₆₄ v8) ∗
        ((s0.sp - 0x18#64) ↦₆₄ v9) ∗ ((s0.sp - 0x10#64) ↦₆₄ v10) ∗ ((s0.sp - 0x08#64) ↦₆₄ v11)) := by
  rw [r0_memRegion_12_cells_rp (s0.sp - 0x60#64), ProofLib.bv_sub_add_lit s0.sp 0x60 0x08,
    ProofLib.bv_sub_add_lit s0.sp 0x60 0x10, ProofLib.bv_sub_add_lit s0.sp 0x60 0x18,
    ProofLib.bv_sub_add_lit s0.sp 0x60 0x20, ProofLib.bv_sub_add_lit s0.sp 0x60 0x28,
    ProofLib.bv_sub_add_lit s0.sp 0x60 0x30, ProofLib.bv_sub_add_lit s0.sp 0x60 0x38,
    ProofLib.bv_sub_add_lit s0.sp 0x60 0x40, ProofLib.bv_sub_add_lit s0.sp 0x60 0x48,
    ProofLib.bv_sub_add_lit s0.sp 0x60 0x50, ProofLib.bv_sub_add_lit s0.sp 0x60 0x58]

theorem r0_subStack_split_rp (fsp : BitVec 64) {sub k : Nat} (hle : k ≤ sub) (h64 : sub ≤ 2 ^ 64) :
    stackAt fsp sub = memRegion (fsp - BitVec.ofNat 64 sub) (sub - k) ∗ stackAt fsp k := by
  have h := ProofLib.stackAt_split_bottom fsp k (sub - k) (by omega)
  rwa [show k + (sub - k) = sub by omega] at h

theorem r0_frame3_split_rp (fsp : BitVec 64) :
    memRegion fsp runLocalBytes =
      r0_gaps_rp fsp ∗ memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x4d0#64) 48 ∗
        memRegion (fsp + 0x1750#64) 32 := by
  delta r0_gaps_rp
  have s1 := ProofLib.memRegion_split fsp 0x1d0 (runLocalBytes - 0x1d0) (by decide)
  have s2 := ProofLib.memRegion_split (fsp + 0x1d0#64) 16 (runLocalBytes - 0x1e0) (by decide)
  have s3 := ProofLib.memRegion_split (fsp + 0x1e0#64) (0x4d0 - 0x1e0) (runLocalBytes - 0x4d0) (by decide)
  have s4 := ProofLib.memRegion_split (fsp + 0x4d0#64) 48 (runLocalBytes - 0x500) (by decide)
  have s5 := ProofLib.memRegion_split (fsp + 0x500#64) (0x1750 - 0x500) (runLocalBytes - 0x1750) (by decide)
  have s6 := ProofLib.memRegion_split (fsp + 0x1750#64) 32 (runLocalBytes - 0x1770) (by decide)
  simp only [Nat.reduceSub, BitVec.add_assoc, BitVec.reduceAdd] at s1 s2 s3 s4 s5 s6
  rw [show runLocalBytes = 0x1d0 + (runLocalBytes - 0x1d0) from rfl, s1,
    show runLocalBytes - 0x1d0 = 16 + (runLocalBytes - 0x1e0) from rfl, s2,
    show runLocalBytes - 0x1e0 = (0x4d0 - 0x1e0) + (runLocalBytes - 0x4d0) from rfl, s3,
    show runLocalBytes - 0x4d0 = 48 + (runLocalBytes - 0x500) from rfl, s4,
    show runLocalBytes - 0x500 = (0x1750 - 0x500) + (runLocalBytes - 0x1750) from rfl, s5,
    show runLocalBytes - 0x1750 = 32 + (runLocalBytes - 0x1770) from rfl, s6]
  sep_ac_rfl

theorem r0_frame3_rejoin_rp (fsp : BitVec 64) :
    r0_gaps_rp fsp ∗ memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x4d0#64) 48 ∗
      memRegion (fsp + 0x1750#64) 32 = runLocals fsp [] := by
  rw [runLocals_empty_eq, ← r0_frame3_split_rp fsp]

theorem r0_probes_split_rp (s0 : State) :
    memRegion (runFsp s0) runLocalBytes = (∃∗ p2 : BitVec 64, ∃∗ p1 : BitVec 64, ∃∗ p0 : BitVec 64,
      ((s0.sp - 0x2a50#64) ↦₆₄ p0) ∗ ((s0.sp - 8288#64) ↦₆₄ p1) ∗ ((s0.sp - 4192#64) ↦₆₄ p2) ∗
      memRegion (runFsp s0 + 0x08#64) (0x9f0 - 8) ∗ memRegion (runFsp s0 + 0x9f8#64) (0x19f0 - 0x9f8) ∗
      memRegion (runFsp s0 + 0x19f8#64) (runLocalBytes - 0x19f8)) := by
  have c1 := ProofLib.memRegion_split (runFsp s0) 8 (runLocalBytes - 8) (by decide)
  have c2 := ProofLib.memRegion_split (runFsp s0 + 0x08#64) (0x9f0 - 8) (runLocalBytes - 0x9f0) (by decide)
  have c3 := ProofLib.memRegion_split (runFsp s0 + 0x9f0#64) 8 (runLocalBytes - 0x9f8) (by decide)
  have c4 := ProofLib.memRegion_split (runFsp s0 + 0x9f8#64) (0x19f0 - 0x9f8) (runLocalBytes - 0x19f0) (by decide)
  have c5 := ProofLib.memRegion_split (runFsp s0 + 0x19f0#64) 8 (runLocalBytes - 0x19f8) (by decide)
  simp only [Nat.reduceSub, BitVec.add_assoc, BitVec.reduceAdd] at c1 c2 c3 c4 c5
  rw [show runLocalBytes = 8 + (runLocalBytes - 8) from rfl, c1,
    show runLocalBytes - 8 = (0x9f0 - 8) + (runLocalBytes - 0x9f0) from rfl, c2,
    show runLocalBytes - 0x9f0 = 8 + (runLocalBytes - 0x9f8) from rfl, c3,
    show runLocalBytes - 0x9f8 = (0x19f0 - 0x9f8) + (runLocalBytes - 0x19f0) from rfl, c4,
    show runLocalBytes - 0x19f0 = 8 + (runLocalBytes - 0x19f8) from rfl, c5]
  have ha1 : runFsp s0 + 0x9f0#64 = s0.sp - 8288#64 := ProofLib.bv_sub_add_lit s0.sp 0x2a50 0x9f0
  have ha2 : runFsp s0 + 0x19f0#64 = s0.sp - 4192#64 := ProofLib.bv_sub_add_lit s0.sp 0x2a50 0x19f0
  rw [ha1, ha2, show runFsp s0 = s0.sp - 0x2a50#64 from rfl,
    ProofLib.memRegion_eight (s0.sp - 0x2a50#64), ProofLib.memRegion_eight (s0.sp - 8288#64),
    ProofLib.memRegion_eight (s0.sp - 4192#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  repeat (apply sepExists_congr; intro _)
  sep_ac_rfl

theorem r0_probes_rejoin_rp (s0 : State) :
    ((s0.sp - 0x2a50#64) ↦₆₄ 0#64) ∗ ((s0.sp - 8288#64) ↦₆₄ 0#64) ∗
      ((s0.sp - 4192#64) ↦₆₄ 0#64) ∗ memRegion (runFsp s0 + 0x08#64) (0x9f0 - 8) ∗
      memRegion (runFsp s0 + 0x9f8#64) (0x19f0 - 0x9f8) ∗
      memRegion (runFsp s0 + 0x19f8#64) (runLocalBytes - 0x19f8) ⊢
    memRegion (runFsp s0) runLocalBytes := by
  rw [r0_probes_split_rp s0]
  exact Entails.sepExists_right 0#64
    (Entails.sepExists_right 0#64 (Entails.sepExists_right 0#64 (Entails.refl _)))

def r0_ownedRest_rp (A : RustAlloc) (cap ptr : BitVec 64) (bs : Bytes) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ if cap = 0 then emp
    else A.live ptr cap.toNat 1 ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)

theorem r0_ownedBytes_split_rp (A : RustAlloc) (cap ptr len : BitVec 64) (bs : Bytes) :
    ownedBytes A cap ptr len bs ⊢
      ⌜len = BitVec.ofNat 64 bs.length⌝ ∗ (ptr ↦ₛ bs) ∗ r0_ownedRest_rp A cap ptr bs := by
  unfold ownedBytes r0_ownedRest_rp; apply Entails.pure_left; rintro ⟨hlen, hle, hlt, hne⟩
  by_cases hcap : cap = 0
  · subst hcap; have hnil : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    subst hnil; simp only [↓reduceIte, pointsToBytes_nil, emp_sepConj]
    exact Entails.pure_right hlen (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))
  · simp only [hcap, ↓reduceIte]
    exact Entails.pure_right hlen
      (Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (sepConj_mono_right (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))))

theorem r0_ownedBytes_free_rp (A : RustAlloc) (cap ptr : BitVec 64) (bs : Bytes) :
    (ptr ↦ₛ bs) ∗ r0_ownedRest_rp A cap ptr bs ⊢
      if cap = 0 then emp
      else ⌜LayoutOk cap.toNat 1⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  unfold r0_ownedRest_rp; rw [sepConj_left_comm (ptr ↦ₛ bs)]; apply Entails.pure_left
  rintro ⟨hle, hlt, _⟩
  by_cases hcap : cap = 0
  · subst hcap; have hnil : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    subst hnil; simp only [↓reduceIte, pointsToBytes_nil, emp_sepConj]; exact Entails.refl _
  · simp only [hcap, ↓reduceIte]
    have hpos : 0 < cap.toNat := by
      by_contra h0; exact hcap (BitVec.eq_of_toNat_eq (by simpa using h0))
    have hlay : LayoutOk cap.toNat 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
    have hm : (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ⊢
        memRegion ptr cap.toNat := by
      have hsplit := ProofLib.memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)
      rw [show bs.length + (cap.toNat - bs.length) = cap.toNat by omega] at hsplit
      rw [hsplit]; exact sepConj_mono_left (ProofLib.pointsToBytes_entails_memRegion ptr bs)
    exact Entails.pure_right hlay (Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono_right hm))

theorem r0_addrUpperAt_open_rp (a : BitVec 64) (meG : AddrGhost) :
    addrUpperAt a meG ⊢ ∃∗ w1 : BitVec 64, ⌜w1.setWidth 8 = meG.device⌝ ∗
      (a ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((a + 8#64) ↦₆₄ w1) := by
  unfold addrUpperAt
  have step1 (p : BitVec 64) (k : Nat) (hk : 1 + k ≤ 2 ^ 64) :
      memRegion p (1 + k) = (∃∗ b : BitVec 8, p ↦₈ b) ∗ memRegion (p + 1#64) k := by
    rw [ProofLib.memRegion_split p 1 k hk, memRegion_1_eq_pointsTo8 p]
  rw [step1 (a + 9#64) 6 (by decide), step1 _ 5 (by decide), step1 _ 4 (by decide),
    step1 _ 3 (by decide), step1 _ 2 (by decide), step1 _ 1 (by decide), memRegion_1_eq_pointsTo8 _]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  apply Entails.sepExists_elim; intro b7; apply Entails.sepExists_elim; intro b6
  apply Entails.sepExists_elim; intro b5; apply Entails.sepExists_elim; intro b4
  apply Entails.sepExists_elim; intro b3; apply Entails.sepExists_elim; intro b2
  apply Entails.sepExists_elim; intro b1
  let w1 : BitVec 64 := b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ meG.device
  refine Entails.sepExists_right w1 ?_
  have hw_lo : w1.setWidth 8 = meG.device := by dsimp [w1]; bv_bits
  have hunpack : unpack64 w1 = [meG.device, b1, b2, b3, b4, b5, b6, b7] :=
    ProofLib.unpack64_pack64 meG.device b1 b2 b3 b4 b5 b6 b7
  have hword : ((a + 8#64) ↦₆₄ w1) = ((a + 8#64) ↦₈ meG.device) ∗ ((a + 9#64) ↦₈ b1) ∗
      ((a + 10#64) ↦₈ b2) ∗ ((a + 11#64) ↦₈ b3) ∗ ((a + 12#64) ↦₈ b4) ∗ ((a + 13#64) ↦₈ b5) ∗
      ((a + 14#64) ↦₈ b6) ∗ ((a + 15#64) ↦₈ b7) := by
    rw [pointsTo64_eq_pointsToBytes, hunpack]
    simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  rw [hword]; exact Entails.pure_right hw_lo (Entails.of_eq (by sep_ac_rfl))

theorem r0_addrUpperAt_close_rp (b w1 : BitVec 64) (meG : AddrGhost) (hw1 : w1.setWidth 8 = meG.device) :
    (b ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((b + 8#64) ↦₆₄ w1) ⊢ addrUpperAt b meG := by
  unfold addrUpperAt
  have hcons : unpack64 w1 = meG.device :: (unpack64 w1).tail := by
    have h0 : w1.extractLsb' 0 8 = meG.device := by rw [← hw1]; bv_bits
    dsimp [unpack64]; rw [h0]
  have hword : ((b + 8#64) ↦₆₄ w1) ⊢ ((b + 8#64) ↦₈ meG.device) ∗ memRegion (b + 9#64) 7 := by
    rw [pointsTo64_eq_pointsToBytes, hcons, pointsToBytes_cons,
      show (b + 8#64) + 1#64 = b + 9#64 by bv_omega,
      show (7 : Nat) = (unpack64 w1).tail.length from rfl]
    exact sepConj_mono_right (ProofLib.pointsToBytes_entails_memRegion _ _)
  exact sepConj_mono_right hword

set_option maxHeartbeats 800000 in
theorem r0_frame3_rejoin_some_rp (fsp : BitVec 64) (meG : AddrGhost) :
    (memRegion (fsp + 0x1750#64) 32 ∗ addrUpperAt (fsp + 0x1d0#64) meG) ∗ r0_gaps_rp fsp ∗
      memRegion (fsp + 0x4d0#64) 48 ⊢
    runLocals fsp [(0x1d0, 16, addrUpperAt (fsp + 0x1d0#64) meG)] := by
  delta r0_gaps_rp
  have htail : memRegion (fsp + 0x1e0#64) (runLocalBytes - 0x1e0) =
      memRegion (fsp + 0x1e0#64) (0x4d0 - 0x1e0) ∗ memRegion (fsp + 0x4d0#64) 48 ∗
      memRegion (fsp + 0x500#64) (0x1750 - 0x500) ∗ memRegion (fsp + 0x1750#64) 32 ∗
      memRegion (fsp + 0x1770#64) (runLocalBytes - 0x1770) := by
    have s3 := ProofLib.memRegion_split (fsp + 0x1e0#64) (0x4d0 - 0x1e0) (runLocalBytes - 0x4d0) (by decide)
    have s4 := ProofLib.memRegion_split (fsp + 0x4d0#64) 48 (runLocalBytes - 0x500) (by decide)
    have s5 := ProofLib.memRegion_split (fsp + 0x500#64) (0x1750 - 0x500) (runLocalBytes - 0x1750) (by decide)
    have s6 := ProofLib.memRegion_split (fsp + 0x1750#64) 32 (runLocalBytes - 0x1770) (by decide)
    simp only [Nat.reduceSub, BitVec.add_assoc, BitVec.reduceAdd] at s3 s4 s5 s6
    rw [show runLocalBytes - 0x1e0 = (0x4d0 - 0x1e0) + (runLocalBytes - 0x4d0) from rfl, s3,
      show runLocalBytes - 0x4d0 = 48 + (runLocalBytes - 0x500) from rfl, s4,
      show runLocalBytes - 0x500 = (0x1750 - 0x500) + (runLocalBytes - 0x1750) from rfl, s5,
      show runLocalBytes - 0x1750 = 32 + (runLocalBytes - 0x1770) from rfl]
    exact s6 ▸ rfl
  dsimp only [runLocals, runLocalsFrom]
  rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero fsp,
    show BitVec.ofNat 64 (0x1d0 + 16) = 0x1e0#64 from rfl,
    show 0x1d0 - 0 = 0x1d0 from rfl, show runLocalBytes - (0x1d0 + 16) = runLocalBytes - 0x1e0 from rfl, htail]
  exact Entails.of_eq (by sep_ac_rfl)

theorem r0_vecU8_eq_rp (A : RustAlloc) (p : BitVec 64) (bs : Bytes) :
    vecU8 A p bs = ∃∗ ptr : BitVec 64, ∃∗ cap : BitVec 64,
      (p ↦₆₄ cap) ∗ ((p + 8#64) ↦₆₄ ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ownedBytes A cap ptr (BitVec.ofNat 64 bs.length) bs := by
  unfold vecU8 vecU8At vecHeader ownedBytes; apply r0_sepProp_ext_rp
  · apply Entails.sepExists_elim; intro cap; apply Entails.sepExists_elim; intro ptr
    exact Entails.sepExists_right ptr (Entails.sepExists_right cap (Entails.of_eq (by simp only [true_and, sepConj_assoc])))
  · apply Entails.sepExists_elim; intro ptr; apply Entails.sepExists_elim; intro cap
    exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.of_eq (by simp only [true_and, sepConj_assoc])))

theorem r0_speInvalidState_eq_words_rp (A : RustAlloc) (fnName : Bytes) (a : BitVec 64) :
    speAt A fnName a .invalidState = ∃∗ fnPtr : BitVec 64, ∃∗ bs : Bytes,
      ∃∗ ptr : BitVec 64, ∃∗ cap : BitVec 64,
        (a ↦₆₄ speWord 1) ∗ ((a + 0x08#64) ↦₆₄ cap) ∗ ((a + 0x10#64) ↦₆₄ ptr) ∗
        ((a + 0x18#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((a + 0x20#64) ↦₆₄ fnPtr) ∗
        ((a + 0x28#64) ↦₆₄ BitVec.ofNat 64 fnName.length) ∗ (fnPtr ↦ᵣ fnName) ∗
        ownedBytes A cap ptr (BitVec.ofNat 64 bs.length) bs := by
  unfold speAt strRefAt
  have ha16 : (a + 0x08#64) + 8#64 = a + 0x10#64 := by bv_omega
  have ha24 : (a + 0x08#64) + 16#64 = a + 0x18#64 := by bv_omega
  have ha40 : (a + 0x20#64) + asm64% boxSliceLenOff = a + 0x28#64 := by bv_omega
  rw [show a + asm64% spePayloadOff = a + 0x08#64 from rfl,
    show a + asm64% speInvalidStateFnOff = a + 0x20#64 from rfl]
  simp only [r0_vecU8_eq_rp, ha16, ha24, ha40, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat (apply sepExists_congr; intro _)
  sep_ac_rfl

theorem r0_decResultOk_eq_words_rp (A : RustAlloc) (a : BitVec 64) (bs : Bytes) :
    vecResultAt A a (.ok bs) = ∃∗ ptr : BitVec 64, ∃∗ cap : BitVec 64,
      ((a ↦₆₄ okTagVec) ∗ ((a + 0x08#64) ↦₆₄ cap) ∗ ((a + 0x10#64) ↦₆₄ ptr) ∗
        ((a + 0x18#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
      memRegion (a + 0x20#64) 16 ∗ ownedBytes A cap ptr (BitVec.ofNat 64 bs.length) bs := by
  unfold vecResultAt
  have ha16 : (a + 0x08#64) + 8#64 = a + 0x10#64 := by bv_omega
  have ha24 : (a + 0x08#64) + 16#64 = a + 0x18#64 := by bv_omega
  rw [show a + asm64% decResultVecOff = a + 0x08#64 from rfl,
    show a + asm64% (decResultVecOff + vecSize) = a + 0x20#64 from rfl,
    show asm% (speSize - (decResultVecOff + vecSize)) = 16 from rfl]
  simp only [r0_vecU8_eq_rp, ha16, ha24, sepExists_sepConj_left, sepExists_sepConj_right]
  repeat (apply sepExists_congr; intro _)
  sep_ac_rfl

abbrev r0_constFrame_rp [LibsignalPlacement] (A : RustAlloc) (g : RunCall) (s0 : State) : SepProp :=
  memRegion g.res runResSize ∗ callAt A g.call g.c ∗ storesAt A g.stores StoresGhost.opened ∗
    (g.inp ↦ₛ inputOf g.i g.c) ∗
    coinsInstalledPlaced g.coins (CryptoVerification.SignalSession.Cli.MainHops.coinsOf g.i) ∗
    CryptoVerification.SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
    lsLogOff ∗ runSaved s0

def r0_meRegs_rp (me : MeAtDispatch) (s : State) : Prop :=
  match me with
  | .none => s.readReg64 (.gpr 21#5) = noneCap
  | .some meV meG => s.readReg64 (.gpr 21#5) = meG.name.cap ∧ s.readReg64 (.gpr 28#5) = meG.name.ptr ∧
      meG.name.bytes = meV.name ∧ meG.name.cap = BitVec.ofNat 64 meV.name.length ∧ meG.device = meV.device

def r0_ownSem_rp (g : RunCall) (me : MeAtDispatch) : Prop :=
  ∃ ownB : Bytes, StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") = .ok ownB ∧
    match me with
    | .none => addrParse uuidTryParse ownB = Option.none
    | .some meV _ => addrParse uuidTryParse ownB = Option.some meV

def r0_tagRel_rp (w0 : BitVec 64) (tag : Nat) : Prop :=
  (w0.toNat < 2 ^ 63 ∧ tag = 1) ∨ (w0 = 0x8000000000000002#64 ∧ tag = 2) ∨
    (w0 = 0x8000000000000003#64 ∧ tag = 3)

theorem r0_cmn_some_eq_false_rp {cap : BitVec 64} (hcap : cap.toNat < 2 ^ 63) :
    ConditionHolds .EQ (AddWithCarry64 cap 1#64 false).2 = false ∧ (cap + 1#64 == 0#64) = false := by
  have hne : cap + 1#64 ≠ 0#64 := by
    intro h; have hmax : cap = 0xffffffffffffffff#64 := by bv_omega
    subst hmax; have htop : (0xffffffffffffffff#64).toNat = 2 ^ 64 - 1 := rfl; rw [htop] at hcap; omega
  have hbeq : (cap + 1#64 == 0#64) = false := beq_false_of_ne hne
  refine ⟨?_, hbeq⟩; dsimp [ConditionHolds, AddWithCarry64]
  have hbw : BitVec.setWidth 64 (0#65 + (1#65 + BitVec.setWidth 65 cap)) = cap + 1#64 := by bv_bits
  rw [hbw]; exact hbeq

theorem r0_lift_pure_7_rp {φ : Prop} {H0 : SepProp} (a0 a1 a2 a3 a4 a5 a6 : SepProp)
    (h : H0 ⊢ ⌜φ⌝ ∗ H0) :
    a0 ∗ a1 ∗ a2 ∗ a3 ∗ a4 ∗ a5 ∗ a6 ∗ H0 ⊢ ⌜φ⌝ ∗ (a0 ∗ (a1 ∗ a2 ∗ a3 ∗ a4 ∗ a5 ∗ a6 ∗ H0)) := by
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h))))))) ?_
  exact Entails.of_eq (by simp only [sepConj_left_comm _ ⌜φ⌝])

theorem r0_callAt_peek_w0_rp [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {s0 : State} (he : AtRunEntryPlaced CodeOk S g s0) (A : RustAlloc) :
    callAt A g.call g.c ⊢ ∃∗ w : CallW, ⌜r0_tagRel_rp w.w0 g.c.tag⌝ ∗ (g.call ↦₆₄ w.w0) ∗
      (((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗ ((g.call + 24#64) ↦₆₄ w.w3) ∗
        ((g.call + 32#64) ↦₆₄ w.w4) ∗ ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6) ∗
        callHeap A w g.c) := by
  cases hgc : g.c with
  | keygen me0 n0 => exact (r0_call_not_keygen_rp he me0 n0 hgc).elim
  | init peer dir =>
    unfold callAt; apply Entails.sepExists_elim; intro w; refine Entails.sepExists_right w ?_
    refine r0_lift_pure_7_rp _ _ _ _ _ _ _ ?_; dsimp only [callHeap, addrWords]
    have hob : ownedBytes A w.w0 w.w1 w.w2 peer.name ⊢
        ⌜r0_tagRel_rp w.w0 (CallV.init peer dir).tag⌝ ∗ ownedBytes A w.w0 w.w1 w.w2 peer.name := by
      unfold ownedBytes; apply Entails.pure_left; rintro ⟨hw2, hle, hlt, hne⟩
      exact Entails.pure_right (Or.inl ⟨hlt, rfl⟩) (Entails.pure_right ⟨hw2, hle, hlt, hne⟩ (Entails.refl _))
    exact Entails.trans (sepConj_mono_left (sepConj_mono_left hob)) (Entails.of_eq (by simp only [sepConj_assoc]))
  | send peer =>
    unfold callAt; apply Entails.sepExists_elim; intro w; refine Entails.sepExists_right w ?_
    refine r0_lift_pure_7_rp _ _ _ _ _ _ _ ?_; dsimp only [callHeap]; apply Entails.pure_left; intro hw0
    exact Entails.pure_right (Or.inr (Or.inl ⟨hw0, rfl⟩)) (Entails.pure_right hw0 (Entails.refl _))
  | recv peer =>
    unfold callAt; apply Entails.sepExists_elim; intro w; refine Entails.sepExists_right w ?_
    refine r0_lift_pure_7_rp _ _ _ _ _ _ _ ?_; dsimp only [callHeap]; apply Entails.pure_left; intro hw0
    exact Entails.pure_right (Or.inr (Or.inr ⟨hw0, rfl⟩)) (Entails.pure_right hw0 (Entails.refl _))

/-! ## Straight-Line and Branching Segment Lemmas -/

theorem r0_step_dispatch_tail_rp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks} {s0 s : State}
    {fsp fpVal callPtr w0 : BitVec 64} {tag : Nat}
    (hpc : s.pc = runPcPlaced 504) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (_hal : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (hx25 : s.readReg64 (.gpr 25#5) = callPtr)
    (htag : r0_tagRel_rp w0 tag) :
    SepWP (runProgPlaced H) (runPcPlaced 532) s (callPtr ↦₆₄ w0) (fun s1 P1 =>
      (s1.sp = fsp ∧ s1.readReg64 .fp = fpVal ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧
        s1.trace = s.trace ∧ s1.fs = s.fs ∧ A.pool lim st s1 = A.pool lim st s ∧
        s1.readReg64 (.gpr 8#5) = BitVec.ofNat 64 tag ∧
        s1.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        s1.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        s1.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
        s1.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        s1.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
        s1.readReg64 (.gpr 25#5) = callPtr ∧ s1.readReg64 (.gpr 26#5) = fsp + 0x4d0#64 ∧
        s1.readReg64 (.gpr 27#5) = fsp + 0x1750#64 ∧
        s1.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5)) ∧ P1 = (callPtr ↦₆₄ w0))
      (fun _ => ⌜False⌝) := by
  subst hsp; rw [runProgPlaced_eq, runPcPlaced_eq]; change s.pc = (blkPl_579).base + 504#64 at hpc; wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine ⟨⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *], ?_, ?_⟩, rfl⟩
  · rcases htag with ⟨hlt, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [wp_norm, arm64_norm, subsPState64, addsPState64, ConditionHolds, AddWithCarry64]
      have hbw1 : BitVec.setWidth 64 (1#65 + (0xffffffffffffffff#65 + BitVec.setWidth 65 w0)) = w0 := by bv_bits
      have hbw2 : BitVec.setWidth 64 (BitVec.setWidth 65 w0 + 0xffffffffffffffff#65 + 1#65) = w0 := by bv_bits
      have hbw3 : BitVec.setWidth 64 (BitVec.setWidth 65 w0 + 0xffffffffffffffff#65 + 0x1#65) = w0 := hbw2
      simp only [hbw1, hbw2, hbw3, BitVec.msb_eq_false_iff_two_mul_lt.mpr (by omega : 2 * w0.toNat < 2 ^ 64),
        Bool.false_eq_true, ↓reduceIte]
    · simp only [wp_norm, arm64_norm, subsPState64, addsPState64, ConditionHolds, AddWithCarry64]
    · simp only [wp_norm, arm64_norm, subsPState64, addsPState64, ConditionHolds, AddWithCarry64]
  · r0_close_post_rp

theorem r0_step_dealloc_pre_rp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks} {s0 s : State}
    {fsp fpVal ptr cap : BitVec 64}
    (hpc : s.pc = runPcPlaced 488) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (_hal : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx26 : s.readReg64 (.gpr 26#5) = ptr) (hx27 : s.readReg64 (.gpr 27#5) = cap) :
    SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s emp (fun s1 P1 =>
      (s1.sp = fsp ∧ s1.readReg64 .fp = fpVal ∧ s1.readReg64 .lr = runPcPlaced 504 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
        A.pool lim st s1 = A.pool lim st s ∧
        s1.readReg64 .x0 = ptr ∧ s1.readReg64 .x1 = cap ∧ s1.readReg64 .x2 = 1#64 ∧
        s1.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        s1.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        s1.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
        s1.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        s1.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
        s1.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
        s1.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5)) ∧ P1 = emp)
      (fun _ => ⌜False⌝) := by
  subst hsp; rw [runProgPlaced_eq]; change s.pc = (blkPl_579).base + 488#64 at hpc; wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine ⟨?_, rfl⟩; r0_close_post_rp

theorem r0_step_post_none_zero_rp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks} {s0 s : State}
    {fsp fpVal : BitVec 64}
    (hpc : s.pc = runPcPlaced 460) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (_hal : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (hx27 : s.readReg64 (.gpr 27#5) = 0#64) :
    SepWP (runProgPlaced H) (runPcPlaced 504) s ((fsp + 0x1750#64) ↦₆₄ noneCap) (fun s1 P1 =>
      (s1.sp = fsp ∧ s1.readReg64 .fp = fpVal ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧
        s1.trace = s.trace ∧ s1.fs = s.fs ∧ A.pool lim st s1 = A.pool lim st s ∧
        s1.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        s1.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        s1.readReg64 (.gpr 21#5) = noneCap ∧
        s1.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        s1.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
        s1.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5)) ∧
        P1 = ((fsp + 0x1750#64) ↦₆₄ noneCap)) (fun _ => ⌜False⌝) := by
  subst hsp; dsimp only [noneCap]; rw [runProgPlaced_eq, runPcPlaced_eq]
  change s.pc = (blkPl_579).base + 460#64 at hpc; wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine ⟨?_, rfl⟩; r0_close_post_rp

theorem r0_step_post_none_nz_rp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks} {s0 s : State}
    {fsp fpVal ptr cap : BitVec 64}
    (hpc : s.pc = runPcPlaced 460) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (_hal : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx26 : s.readReg64 (.gpr 26#5) = ptr) (hx27 : s.readReg64 (.gpr 27#5) = cap)
    (hcap0 : cap ≠ 0#64) :
    SepWP (runProgPlaced H) (runPcPlaced 488) s ((fsp + 0x1750#64) ↦₆₄ noneCap) (fun s1 P1 =>
      (s1.sp = fsp ∧ s1.readReg64 .fp = fpVal ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧
        s1.trace = s.trace ∧ s1.fs = s.fs ∧ A.pool lim st s1 = A.pool lim st s ∧
        s1.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        s1.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        s1.readReg64 (.gpr 21#5) = noneCap ∧
        s1.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        s1.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
        s1.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
        s1.readReg64 (.gpr 26#5) = ptr ∧ s1.readReg64 (.gpr 27#5) = cap) ∧
        P1 = ((fsp + 0x1750#64) ↦₆₄ noneCap)) (fun _ => ⌜False⌝) := by
  subst hsp; have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap0
  dsimp only [noneCap]; rw [runProgPlaced_eq, runPcPlaced_eq]
  change s.pc = (blkPl_579).base + 460#64 at hpc; wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine ⟨?_, rfl⟩; r0_close_post_rp

theorem r0_step_post_some_zero_rp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks} {s0 s : State}
    {fsp fpVal mCap mPtr mLen w1 u0 u1 : BitVec 64}
    (hpc : s.pc = runPcPlaced 460) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (_hal : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx27 : s.readReg64 (.gpr 27#5) = 0#64) (hlt : mCap.toNat < 2 ^ 63) :
    SepWP (runProgPlaced H) (runPcPlaced 504) s
      (((fsp + 0x1750#64) ↦₆₄ mCap) ∗ ((fsp + 0x1758#64) ↦₆₄ mPtr) ∗
        ((fsp + 0x1760#64) ↦₆₄ mLen) ∗ ((fsp + 0x1768#64) ↦₆₄ w1) ∗
        ((fsp + 0x1d0#64) ↦₆₄ u0) ∗ ((fsp + 0x1d8#64) ↦₆₄ u1))
      (fun s1 P1 =>
        (s1.sp = fsp ∧ s1.readReg64 .fp = fpVal ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧
          s1.trace = s.trace ∧ s1.fs = s.fs ∧ A.pool lim st s1 = A.pool lim st s ∧
          s1.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
          s1.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
          s1.readReg64 (.gpr 21#5) = mCap ∧
          s1.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
          s1.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
          s1.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
          s1.readReg64 (.gpr 28#5) = mPtr) ∧
          P1 = (((fsp + 0x1750#64) ↦₆₄ mCap) ∗ ((fsp + 0x1758#64) ↦₆₄ mPtr) ∗
            ((fsp + 0x1760#64) ↦₆₄ mLen) ∗ ((fsp + 0x1768#64) ↦₆₄ w1) ∗
            ((fsp + 0x1d0#64) ↦₆₄ mLen) ∗ ((fsp + 0x1d8#64) ↦₆₄ w1)))
      (fun _ => ⌜False⌝) := by
  subst hsp; have hcmn_eq := (r0_cmn_some_eq_false_rp hlt).1
  have hcmn_f := (r0_cmn_some_eq_false_rp hlt).2
  rw [runProgPlaced_eq, runPcPlaced_eq]; change s.pc = (blkPl_579).base + 460#64 at hpc
  by_vm_open (
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    have hpool := (A.pool_transport lim st s _ hvm).symm
    refine ⟨?_, by sep_ac_rfl⟩; r0_close_post_rp
  )

theorem r0_step_post_some_nz_rp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks} {s0 s : State}
    {fsp fpVal mCap mPtr mLen w1 u0 u1 ptr cap : BitVec 64}
    (hpc : s.pc = runPcPlaced 460) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (_hal : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx26 : s.readReg64 (.gpr 26#5) = ptr) (hx27 : s.readReg64 (.gpr 27#5) = cap)
    (hcap0 : cap ≠ 0#64) (hlt : mCap.toNat < 2 ^ 63) :
    SepWP (runProgPlaced H) (runPcPlaced 488) s
      (((fsp + 0x1750#64) ↦₆₄ mCap) ∗ ((fsp + 0x1758#64) ↦₆₄ mPtr) ∗
        ((fsp + 0x1760#64) ↦₆₄ mLen) ∗ ((fsp + 0x1768#64) ↦₆₄ w1) ∗
        ((fsp + 0x1d0#64) ↦₆₄ u0) ∗ ((fsp + 0x1d8#64) ↦₆₄ u1))
      (fun s1 P1 =>
        (s1.sp = fsp ∧ s1.readReg64 .fp = fpVal ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧
          s1.trace = s.trace ∧ s1.fs = s.fs ∧ A.pool lim st s1 = A.pool lim st s ∧
          s1.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
          s1.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
          s1.readReg64 (.gpr 21#5) = mCap ∧
          s1.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
          s1.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
          s1.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
          s1.readReg64 (.gpr 26#5) = ptr ∧ s1.readReg64 (.gpr 27#5) = cap ∧
          s1.readReg64 (.gpr 28#5) = mPtr) ∧
          P1 = (((fsp + 0x1750#64) ↦₆₄ mCap) ∗ ((fsp + 0x1758#64) ↦₆₄ mPtr) ∗
            ((fsp + 0x1760#64) ↦₆₄ mLen) ∗ ((fsp + 0x1768#64) ↦₆₄ w1) ∗
            ((fsp + 0x1d0#64) ↦₆₄ mLen) ∗ ((fsp + 0x1d8#64) ↦₆₄ w1)))
      (fun _ => ⌜False⌝) := by
  subst hsp; have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap0
  have hcmn_eq := (r0_cmn_some_eq_false_rp hlt).1; have hcmn_f := (r0_cmn_some_eq_false_rp hlt).2
  rw [runProgPlaced_eq, runPcPlaced_eq]; change s.pc = (blkPl_579).base + 460#64 at hpc
  by_vm_open (
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    have hpool := (A.pool_transport lim st s _ hvm).symm
    refine ⟨?_, by sep_ac_rfl⟩; r0_close_post_rp
  )

theorem r0_step_ok_pre_utf8_rp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks} {s0 s : State}
    {fsp fpVal cap ptr lenW : BitVec 64}
    (hpc : s.pc = runPcPlaced 96) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (_hal : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (runProgPlaced H) (lsρ lsFromUtf8Sym) s
      (((fsp + 0x4d0#64) ↦₆₄ okTagVec) ∗ ((fsp + 0x4d8#64) ↦₆₄ cap) ∗
        ((fsp + 0x4e0#64) ↦₆₄ ptr) ∗ ((fsp + 0x4e8#64) ↦₆₄ lenW))
      (fun s1 P1 =>
        (s1.sp = fsp ∧ s1.readReg64 .fp = fpVal ∧ s1.readReg64 .lr = runPcPlaced 136 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          A.pool lim st s1 = A.pool lim st s ∧
          s1.readReg64 .x0 = ptr ∧ s1.readReg64 .x1 = lenW ∧
          s1.readReg64 (.gpr 8#5) = fsp + 0x4d0#64 ∧
          s1.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
          s1.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
          s1.readReg64 (.gpr 21#5) = lenW ∧
          s1.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
          s1.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
          s1.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
          s1.readReg64 (.gpr 26#5) = ptr ∧ s1.readReg64 (.gpr 27#5) = cap) ∧
          P1 = (((fsp + 0x4d0#64) ↦₆₄ okTagVec) ∗ ((fsp + 0x4d8#64) ↦₆₄ cap) ∗
            ((fsp + 0x4e0#64) ↦₆₄ ptr) ∗ ((fsp + 0x4e8#64) ↦₆₄ lenW)))
      (fun _ => ⌜False⌝) := by
  subst hsp; dsimp only [okTagVec]; rw [runProgPlaced_eq]
  change s.pc = (blkPl_579).base + 96#64 at hpc; wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine ⟨?_, rfl⟩; r0_close_post_rp

theorem r0_step_ok_pre_addr_rp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks} {s0 s : State}
    {fsp fpVal ptr lenW cap : BitVec 64}
    (hpc : s.pc = runPcPlaced 136) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (_hal : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx21 : s.readReg64 (.gpr 21#5) = lenW) (hx26 : s.readReg64 (.gpr 26#5) = ptr)
    (hx27 : s.readReg64 (.gpr 27#5) = cap) :
    SepWP (runProgPlaced H) (lsmpl.base 580) s ((fsp + 0x4d0#64) ↦₆₄ 0#64) (fun s1 P1 =>
      (s1.sp = fsp ∧ s1.readReg64 .fp = fpVal ∧ s1.readReg64 .lr = runPcPlaced 460 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
        A.pool lim st s1 = A.pool lim st s ∧
        s1.readReg64 .x0 = fsp + 0x1750#64 ∧ s1.readReg64 .x1 = ptr ∧ s1.readReg64 .x2 = lenW ∧
        s1.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        s1.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        s1.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        s1.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
        s1.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
        s1.readReg64 (.gpr 26#5) = ptr ∧ s1.readReg64 (.gpr 27#5) = cap) ∧
        P1 = ((fsp + 0x4d0#64) ↦₆₄ 0#64)) (fun _ => ⌜False⌝) := by
  subst hsp; rw [runProgPlaced_eq]; change s.pc = (blkPl_579).base + 136#64 at hpc
  rw [ProofLib.pointsTo64_split32 (s.sp + 0x4d0#64) 0#64]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine ⟨?_, rfl⟩; r0_close_post_rp

theorem r0_step_err_pre_drop_rp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks} {s0 s : State}
    {fsp fpVal cap ptr lenW fnPtr fnLenW : BitVec 64}
    (hpc : s.pc = runPcPlaced 96) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (_hal : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (runProgPlaced H) (blkPl_553).base s
      (((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗ ((fsp + 0x4d8#64) ↦₆₄ cap) ∗
        ((fsp + 0x4e0#64) ↦₆₄ ptr) ∗ ((fsp + 0x4e8#64) ↦₆₄ lenW) ∗
        ((fsp + 0x4f0#64) ↦₆₄ fnPtr) ∗ ((fsp + 0x4f8#64) ↦₆₄ fnLenW))
      (fun s1 P1 =>
        (s1.sp = fsp ∧ s1.readReg64 .fp = fpVal ∧ s1.readReg64 .lr = runPcPlaced 292 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          A.pool lim st s1 = A.pool lim st s ∧ s1.readReg64 .x0 = fsp + 0x4d0#64 ∧
          s1.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
          s1.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
          s1.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5)) ∧
          P1 = (((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗ ((fsp + 0x4d8#64) ↦₆₄ cap) ∗
            ((fsp + 0x4e0#64) ↦₆₄ ptr) ∗ ((fsp + 0x4e8#64) ↦₆₄ lenW) ∗
            ((fsp + 0x4f0#64) ↦₆₄ fnPtr) ∗ ((fsp + 0x4f8#64) ↦₆₄ fnLenW)))
      (fun _ => ⌜False⌝) := by
  subst hsp; dsimp only [speWord]; rw [runProgPlaced_eq]
  change s.pc = (blkPl_579).base + 96#64 at hpc
  by_vm_open (
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; rfl) (by simp only [wp_norm, arm64_norm, *])
    refine ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    have hpool := (A.pool_transport lim st s _ hvm).symm
    refine ⟨?_, by sep_ac_rfl⟩; r0_close_post_rp
  )

theorem r0_mainSaved_eq_sub_rp (s0 : State) : runSaved s0 =
    ((s0.sp - 0x60#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 0x58#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 0x50#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
      ((s0.sp - 0x48#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
      ((s0.sp - 0x40#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
      ((s0.sp - 0x38#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
      ((s0.sp - 0x30#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
      ((s0.sp - 0x28#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
      ((s0.sp - 0x20#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
      ((s0.sp - 0x18#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
      ((s0.sp - 0x10#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
      ((s0.sp - 0x08#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) := by
  dsimp only [runSaved, mainSaved]
  rw [BitVec.add_zero (s0.sp - 0x60#64), ProofLib.bv_sub_add_lit s0.sp 0x60 0x08,
    ProofLib.bv_sub_add_lit s0.sp 0x60 0x10, ProofLib.bv_sub_add_lit s0.sp 0x60 0x18,
    ProofLib.bv_sub_add_lit s0.sp 0x60 0x20, ProofLib.bv_sub_add_lit s0.sp 0x60 0x28,
    ProofLib.bv_sub_add_lit s0.sp 0x60 0x30, ProofLib.bv_sub_add_lit s0.sp 0x60 0x38,
    ProofLib.bv_sub_add_lit s0.sp 0x60 0x40, ProofLib.bv_sub_add_lit s0.sp 0x60 0x48,
    ProofLib.bv_sub_add_lit s0.sp 0x60 0x50, ProofLib.bv_sub_add_lit s0.sp 0x60 0x58]

set_option maxHeartbeats 800000 in
theorem r0_step_prologue_rp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks} {s0 : State}
    {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 p0 p1 p2 : BitVec 64}
    (hpc : s0.pc = (blkPl_579).base) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true) :
    SepWP (runProgPlaced H) (lsmpl.base 589) s0
      (((s0.sp - 0x60#64) ↦₆₄ v0) ∗ ((s0.sp - 0x58#64) ↦₆₄ v1) ∗ ((s0.sp - 0x50#64) ↦₆₄ v2) ∗
        ((s0.sp - 0x48#64) ↦₆₄ v3) ∗ ((s0.sp - 0x40#64) ↦₆₄ v4) ∗ ((s0.sp - 0x38#64) ↦₆₄ v5) ∗
        ((s0.sp - 0x30#64) ↦₆₄ v6) ∗ ((s0.sp - 0x28#64) ↦₆₄ v7) ∗ ((s0.sp - 0x20#64) ↦₆₄ v8) ∗
        ((s0.sp - 0x18#64) ↦₆₄ v9) ∗ ((s0.sp - 0x10#64) ↦₆₄ v10) ∗ ((s0.sp - 0x08#64) ↦₆₄ v11) ∗
        ((s0.sp - 0x2a50#64) ↦₆₄ p0) ∗ ((s0.sp - 8288#64) ↦₆₄ p1) ∗ ((s0.sp - 4192#64) ↦₆₄ p2))
      (fun s1 P1 =>
        (s1.sp = runFsp s0 ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          s1.readReg64 .lr = runPcPlaced 96 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧
          s1.trace = s0.trace ∧ s1.fs = s0.fs ∧ A.pool lim st s1 = A.pool lim st s0 ∧
          s1.readReg64 .x0 = runFsp s0 + 0x4d0#64 ∧ s1.readReg64 .x1 = s0.readReg64 .x2 ∧
          s1.readReg64 .x2 = lsρ r0_addrSym_rp ∧ s1.readReg64 .x3 = 7#64 ∧
          s1.readReg64 (.gpr 19#5) = s0.readReg64 .x2 ∧
          s1.readReg64 (.gpr 20#5) = s0.readReg64 .x0 ∧
          s1.readReg64 (.gpr 23#5) = s0.readReg64 .x3 ∧
          s1.readReg64 (.gpr 24#5) = s0.readReg64 .x4 ∧
          s1.readReg64 (.gpr 25#5) = s0.readReg64 .x1) ∧
          P1 = (runSaved s0 ∗ ((s0.sp - 0x2a50#64) ↦₆₄ 0#64) ∗
            ((s0.sp - 8288#64) ↦₆₄ 0#64) ∗ ((s0.sp - 4192#64) ↦₆₄ 0#64)))
      (fun _ => ⌜False⌝) := by
  have hal_0 : (s0.sp &&& 15#64 == 0#64) = true := hsp0
  have hal_96 : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true := ProofLib.spAligned_sub s0.sp 96#64 hsp0
  have hal_1060 : ((s0.sp - 4192#64) &&& 15#64 == 0#64) = true := ProofLib.spAligned_sub s0.sp 4192#64 hsp0
  have hal_2060 : ((s0.sp - 8288#64) &&& 15#64 == 0#64) = true := ProofLib.spAligned_sub s0.sp 8288#64 hsp0
  have hal_2a50 : ((s0.sp - 0x2a50#64) &&& 15#64 == 0#64) = true := ProofLib.spAligned_sub s0.sp 0x2a50#64 hsp0
  rw [runProgPlaced_eq]
  refine SepWP.seq (mid := (blkPl_579).base + 64#64)
    (Mid := fun sm Pm =>
      (sm.sp = s0.sp - 0x2a50#64 ∧ sm.readReg64 .fp = s0.sp - 0x60#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        sm.trace = s0.trace ∧ sm.fs = s0.fs ∧ A.pool lim st sm = A.pool lim st s0 ∧
        sm.readReg64 .x2 = s0.readReg64 .x2 ∧
        sm.readReg64 .x4 = s0.readReg64 .x4 ∧
        sm.readReg64 (.gpr 19#5) = s0.readReg64 .x2 ∧
        sm.readReg64 (.gpr 20#5) = s0.readReg64 .x0 ∧
        sm.readReg64 (.gpr 23#5) = s0.readReg64 .x3 ∧
        sm.readReg64 (.gpr 25#5) = s0.readReg64 .x1) ∧
        Pm = (runSaved s0 ∗ ((s0.sp - 0x2a50#64) ↦₆₄ p0) ∗
          ((s0.sp - 8288#64) ↦₆₄ 0#64) ∗ ((s0.sp - 4192#64) ↦₆₄ 0#64))) ?_ ?_
  · by_vm_open (
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
      refine ⟨⟨by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        A.pool_transport lim st s0 _ hvm, ?_⟩, ?_⟩
      · r0_close_post_rp
      · rw [r0_mainSaved_eq_sub_rp s0]; sep_ac_rfl
    )
  · rintro sm Pm hpcm hrunm ⟨⟨hspm, hfpm, hvm, htrm, hfsm, hpoolm, hx2m, hx4m, hx19m, hx20m, hx23m, hx25m⟩, rfl⟩
    wp_step
    by_vm_open (
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
      refine ⟨⟨by dsimp [runFsp]; simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, runPcPlaced_eq, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        (A.pool_transport lim st _ _ hvm2).trans
          (by simp only [wp_norm, arm64_norm, RustCliAllocBudget.pool_setPC,
            RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg,
            RustCliAllocBudget.pool_advancePC, hpoolm]),
        by dsimp [runFsp]; simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], ?_⟩, rfl⟩
      r0_close_post_rp
    )

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudgetAux
