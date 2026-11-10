/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SpeOwnedBridges
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ModelBridge
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `signal_session::run` Arm `R3b`: Shared Placed Helpers

Relocatable (`[LibsignalPlacement]`) helper lemmas, word-slot packing, and call combinators for
Arm `R3b` (`run_hop_recvBad_placed_ok` and `run_hop_recvP_placed_ok`) on Block `579`
(`runProgPlaced H`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.RecordCodecs
open CryptoVerification.LibsignalProtoCodec

/-! ## 1. Placed Code Invariant & `SepWPp` / `Entails` Combinators -/

/-- Canonical `CodeOk` predicate on Block `579` under `[LibsignalPlacement]`. -/
abbrev R3bCodeOk [LibsignalPlacement] : Memory → Prop :=
  LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl

theorem r3b_seq [LibsignalPlacement] {CodeOk : Memory → Prop} [hCI : LsCodeInv CodeOk]
    {prog : Program} {ret mid : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : CodeOk s.mem)
    (h : SepWP prog mid s P (fun sm Pm => CodeOk sm.mem → SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom :=
  SepWPp.seq_frozen (fun _ _ h0 hkf => hCI.of_keepsFrozen h0 hkf) hinv h

theorem r3b_perm {P P' Q : SepProp} (h : P' ⊢ Q) (hp : P = P') : P ⊢ Q :=
  hp ▸ h

theorem r3b_perm_post {P Q Q' : SepProp} (h : P ⊢ Q') (hq : Q' = Q) : P ⊢ Q :=
  hq ▸ h

theorem r3b_stackAt_split_ge (sp : BitVec 64) {k n : Nat}
    (hle : k ≤ n) (hn : n ≤ 2 ^ 64) :
    stackAt sp n = memRegion (sp - BitVec.ofNat 64 n) (n - k) ∗ stackAt sp k := by
  have h := ProofLib.stackAt_split_bottom sp k (n - k) (by omega)
  rwa [Nat.add_sub_of_le hle] at h

theorem r3b_sepWPp_weaken_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hP : P ⊢ P') (h : SepWPp prog ret s P' Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  exact h R (Satisfies.mono (sepConj_mono_left hP) hm) hL

theorem r3b_sepWPp_exists_left {α : Sort _} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x : α, SepWPp prog ret s (P x) Q Qp oom) :
    SepWPp prog ret s (∃∗ x, P x) Q Qp oom := by
  intro R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨x, hx⟩ := hm
  exact h x R hx hL

theorem r3b_sepWPp_pure_left {P0 : Prop} {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : P0 → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s (⌜P0⌝ ∗ P) Q Qp oom := by
  intro R hm hL
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL

theorem r3b_pure1 {P0 : Prop} {X Y Q : SepProp}
    (h : P0 → X ∗ Y ⊢ Q) : X ∗ (⌜P0⌝ ∗ Y) ⊢ Q := by
  rw [show X ∗ (⌜P0⌝ ∗ Y) = ⌜P0⌝ ∗ (X ∗ Y) by ac_rfl]
  exact Entails.pure_left h

theorem r3b_pure2 {P0 : Prop} {X1 X2 Y Q : SepProp}
    (h : P0 → X1 ∗ X2 ∗ Y ⊢ Q) : X1 ∗ X2 ∗ (⌜P0⌝ ∗ Y) ⊢ Q := by
  rw [show X1 ∗ X2 ∗ (⌜P0⌝ ∗ Y) = ⌜P0⌝ ∗ (X1 ∗ X2 ∗ Y) by ac_rfl]
  exact Entails.pure_left h

theorem r3b_pure5 {P0 : Prop} {X1 X2 X3 X4 X5 Y Q : SepProp}
    (h : P0 → X1 ∗ X2 ∗ X3 ∗ X4 ∗ X5 ∗ Y ⊢ Q) :
    X1 ∗ X2 ∗ X3 ∗ X4 ∗ X5 ∗ (⌜P0⌝ ∗ Y) ⊢ Q := by
  rw [show X1 ∗ X2 ∗ X3 ∗ X4 ∗ X5 ∗ (⌜P0⌝ ∗ Y) = ⌜P0⌝ ∗ (X1 ∗ X2 ∗ X3 ∗ X4 ∗ X5 ∗ Y) by ac_rfl]
  exact Entails.pure_left h

theorem r3b_call_lscro [LibsignalPlacement] {CodeOk : Memory → Prop} [hCI : LsCodeInv CodeOk]
    {α : Type} {prog : Program}
    {callee retAddr ret : BitVec 64} {spec : Spec α} {s0 s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (x : α)
    (hcall : subroutine_ok prog callee
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec))
    (hinv : CodeOk s.mem)
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = retAddr)
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
    (hnext : ∀ sm : State,
      Steps prog s sm →
      CodeOk sm.mem →
      sm.pc = retAddr →
      sm.status = .Running →
      sm.sp = s.sp →
      CalleeSavedPreserved s sm →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp (runOom s0)) :
    SepWPp prog ret s P Q Qp (runOom s0) := by
  intro R hm hL
  have hm_pre : s.mem ⊨ spec.pre x s ∗ (F ∗ R) :=
    by simpa only [sepConj_assoc] using Satisfies.mono (sepConj_mono_left hP) hm
  have hpre :
      s.mem ⊨ (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hCI.toRoCl hinv, hm_pre⟩
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hpre hsp hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ |
      ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps (hCI.of_keepsFrozen hinv hsteps.keepsFrozen) hpcm hrunm hspm hcsm R hpost
        (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, spec.onPanic x s sm ∗ F,
      by simpa only [sepConj_assoc] using hpost,
      hpanic sm (F ∗ R) hpan hpost⟩)⟩
  · exact (hexit sm code (F ∗ R) hex hpost).elim
  · dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_s, hoom sm R hoom_s hpost⟩)⟩

theorem r3b_call_raw [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {α : Type} {prog : Program}
    {callee retAddr ret : BitVec 64} {spec : Spec α} {s0 s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (x : α)
    (hcall : subroutine_ok prog callee spec)
    (hinv : CodeOk s.mem)
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = retAddr)
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
    (hnext : ∀ sm : State,
      Steps prog s sm →
      CodeOk sm.mem →
      sm.pc = retAddr →
      sm.status = .Running →
      sm.sp = s.sp →
      CalleeSavedPreserved s sm →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp (runOom s0)) :
    SepWPp prog ret s P Q Qp (runOom s0) :=
  r3b_call_lscro x
    (LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain hcall)
    hinv hpc hrun hsp hlr hP hpanic hexit hoom hnext

theorem r3b_dealloc_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hh : RunHooksPlaced A H) :
    subroutine_ok (runProgPlaced H) (lsρ lsRustDeallocSymCli)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (rustDeallocExternSpecWithStack A extHookStack).keepsFs) := by
  have hrocl := AllocContractsFsPlaced.dealloc_rocl (prog := runProgPlaced H) (i := 579) hh.allocFs
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_ (fun _ _ _ _ hp => hp)
  intro x R s0 sf hpost
  dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

theorem r3b_inRun_step [LibsignalPlacement] {CodeOk : Memory → Prop} {s0 s s' : State} {k k' : Nat}
    (h : InRunPlaced CodeOk s0 s k)
    (hpc : s'.pc = runPcPlaced k') (hrun : s'.status = .Running)
    (hsp : s'.sp = s.sp) (hfp : s'.readReg64 .fp = s.readReg64 .fp)
    (hinv : CodeOk s'.mem) (hv : calleeSavedVRegs s' = calleeSavedVRegs s) :
    InRunPlaced CodeOk s0 s' k' :=
  ⟨hpc, hrun, hsp.trans h.sp, hfp.trans h.fp, hinv, hv.trans h.vregs, h.spAligned⟩

theorem r3b_hist_of_eq {i : Inputs} {s0 s s' : State}
    (htr : s'.trace = s.trace) (hfs : s'.fs.files = s.fs.files)
    (h : RunHistOk i s0 s) : RunHistOk i s0 s' :=
  ⟨hfs.trans h.1, by rw [htr]; exact h.2⟩

theorem r3b_files_of_trace_eq {P : Program} (hP : TraceFsSound P) {s sm : State}
    (hsteps : Steps P s sm) (htr : sm.trace = s.trace) : sm.fs.files = s.fs.files :=
  hP.files_eq hsteps (by rw [htr]; simp) NoFsEv.nil

abbrev r3b_stOf {P : Memory → Prop} {s : State} (_ : P s.mem) : State := s

theorem r3b_cs_regs {s sf : State} (hcs : CalleeSavedPreserved s sf) :
    sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
    sf.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
    sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
    sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
    sf.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
    sf.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
    sf.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
    sf.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
    sf.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧
    sf.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
    sf.readReg64 .fp = s.readReg64 .fp ∧
    calleeSavedVRegs sf = calleeSavedVRegs s :=
  hcs

theorem r3b_extractLsb_append_lo (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by bv_bits
theorem r3b_extractLsb_append_hi (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by bv_bits
theorem r3b_calleeSavedVRegs_q0 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 0#5 v) = calleeSavedVRegs s := by
  simp [calleeSavedVRegs, State.writeVReg128, VRegFile.calleeSaved, VRegFile.write, VRegFile.read]
theorem r3b_calleeSavedVRegs_q1 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 1#5 v) = calleeSavedVRegs s := by
  simp [calleeSavedVRegs, State.writeVReg128, VRegFile.calleeSaved, VRegFile.write, VRegFile.read]
theorem r3b_calleeSavedVRegs_q2 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 2#5 v) = calleeSavedVRegs s := by
  simp [calleeSavedVRegs, State.writeVReg128, VRegFile.calleeSaved, VRegFile.write, VRegFile.read]
theorem r3b_calleeSavedVRegs_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    calleeSavedVRegs (s.writeReg64 r v) = calleeSavedVRegs s := by cases s; cases r <;> rfl
theorem r3b_calleeSavedVRegs_setPC (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by cases s; rfl
theorem r3b_calleeSavedVRegs_setMem (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl
theorem r3b_calleeSavedVRegs_setPState (s : State) (ps : PState) :
    calleeSavedVRegs (s.setPState ps) = calleeSavedVRegs s := by cases s; rfl
theorem r3b_readReg64_setPState (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
theorem r3b_sp_setPState (s : State) (ps : PState) :
    (s.setPState ps).sp = s.sp := by cases s; rfl
theorem r3b_mem_setPState (s : State) (ps : PState) :
    (s.setPState ps).mem = s.mem := by cases s; rfl
theorem r3b_status_setPState (s : State) (ps : PState) :
    (s.setPState ps).status = s.status := by cases s; rfl
theorem r3b_trace_setPState (s : State) (ps : PState) :
    (s.setPState ps).trace = s.trace := by cases s; rfl
theorem r3b_symtab_setPState (s : State) (ps : PState) :
    (s.setPState ps).symtab = s.symtab := by cases s; rfl
theorem r3b_fs_setPState (s : State) (ps : PState) :
    (s.setPState ps).fs = s.fs := by cases s; rfl
theorem r3b_fs_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).fs = s.fs := by cases s; cases r <;> rfl
theorem r3b_fs_writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).fs = s.fs := by cases s; rfl
theorem r3b_fs_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).fs = s.fs := by cases s; rfl
theorem r3b_fs_setMem (s : State) (m : Memory) :
    (s.setMem m).fs = s.fs := by cases s; rfl

/-! ## 2. Pure-`SepProp` Magic-Wand Shift & Word Packing Infrastructure -/

def r3b_pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 64 :=
  b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0

theorem r3b_wand_refl (P : SepProp) : emp ⊢ (P -∗ P) :=
  Entails.wand_intro (Entails.of_eq (emp_sepConj P))

theorem r3b_wand_post {P Q Q' : SepProp} (h : Q ⊢ Q') :
    (P -∗ Q) ⊢ (P -∗ Q') :=
  Entails.wand_intro (Entails.trans (Entails.of_eq (sepConj_comm _ _))
    (Entails.trans (Entails.wand_elim P Q) h))

theorem r3b_pointsTo64_pack (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (a ↦₆₄ r3b_pack64 b0 b1 b2 b3 b4 b5 b6 b7) =
      (a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3) ∗
        ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗
        ((a + 7#64) ↦₈ b7) := by
  have a2 : a + 1#64 + 1#64 = a + 2#64 := by bv_omega
  have a3 : a + 2#64 + 1#64 = a + 3#64 := by bv_omega
  have a4 : a + 3#64 + 1#64 = a + 4#64 := by bv_omega
  have a5 : a + 4#64 + 1#64 = a + 5#64 := by bv_omega
  have a6 : a + 5#64 + 1#64 = a + 6#64 := by bv_omega
  have a7 : a + 6#64 + 1#64 = a + 7#64 := by bv_omega
  dsimp only [r3b_pack64]
  rw [← pointsToBytes8_eq_pointsTo64 a b0 b1 b2 b3 b4 b5 b6 b7]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, a2, a3, a4, a5, a6, a7]

theorem r3b_pointsTo64_pack32x2 (a : BitVec 64) (c1 c2 : BitVec 32) :
    (a ↦₆₄ (c2 ++ c1)) = (a ↦₃₂ c1) ∗ ((a + 4#64) ↦₃₂ c2) := by
  have hlo : (c2 ++ c1).extractLsb' 0 32 = c1 := BitVec.extractLsb'_append_eq_right
  have hhi : (c2 ++ c1).extractLsb' 32 32 = c2 := BitVec.extractLsb'_append_eq_left
  rw [pointsTo64_split32 a (c2 ++ c1), hlo, hhi]

theorem r3b_u64_to_u8pad7 (a : BitVec 64) (b0 : BitVec 8) (hi : BitVec 64)
    (hhi : hi.setWidth 8 = b0) :
    (a ↦₆₄ hi) ⊢ (a ↦₈ b0) ∗ memRegion (a + 1#64) 7 := by
  rw [pointsTo64_eq_pointsToBytes a hi]
  dsimp only [unpack64]
  rw [pointsToBytes_cons]
  have hlow : hi.extractLsb' 0 8 = b0 := by
    rw [← BitVec.setWidth_eq_extractLsb' (by decide), hhi]
  rw [hlow]
  exact sepConj_mono_right (ProofLib.pointsToBytes_entails_memRegion (a + 1#64) _)

theorem r3b_u8pad7_to_u64 (a : BitVec 64) (b0 : BitVec 8) :
    ((a ↦₈ b0) ∗ memRegion (a + 1#64) 7) ⊢
      ∃∗ hi : BitVec 64, ⌜hi.setWidth 8 = b0⌝ ∗ (a ↦₆₄ hi) := by
  rw [ProofLib.memRegion_split' (b := a + 1#64) (n := 1) (k := 6) (b' := a + 2#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 2#64) (n := 1) (k := 5) (b' := a + 3#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 3#64) (n := 1) (k := 4) (b' := a + 4#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 4#64) (n := 1) (k := 3) (b' := a + 5#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 5#64) (n := 1) (k := 2) (b' := a + 6#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 6#64) (n := 1) (k := 1) (b' := a + 7#64) rfl (by bv_omega) (by decide)]
  simp only [Path.Helpers.memRegion_1_eq_pointsTo8, sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro b7
  apply Entails.sepExists_elim; intro b6
  apply Entails.sepExists_elim; intro b5
  apply Entails.sepExists_elim; intro b4
  apply Entails.sepExists_elim; intro b3
  apply Entails.sepExists_elim; intro b2
  apply Entails.sepExists_elim; intro b1
  let hi := r3b_pack64 b0 b1 b2 b3 b4 b5 b6 b7
  have hlow : hi.setWidth 8 = b0 := BitVec.setWidth_append_eq_right
  refine Entails.sepExists_right hi (Entails.pure_right hlow ?_)
  rw [r3b_pointsTo64_pack a b0 b1 b2 b3 b4 b5 b6 b7]
  exact Entails.of_eq (by ac_rfl)

theorem r3b_ws_u64 (s d w : BitVec 64) :
    (s ↦₆₄ w) ⊢ (s ↦₆₄ w) ∗ ((d ↦₆₄ w) -∗ (d ↦₆₄ w)) :=
  Entails.trans (Entails.of_eq (sepConj_emp (s ↦₆₄ w)).symm)
    (sepConj_mono_right (r3b_wand_refl (d ↦₆₄ w)))

theorem r3b_ws_mem8 (s d : BitVec 64) :
    memRegion s 8 ⊢ ∃∗ w : BitVec 64, (s ↦₆₄ w) ∗ ((d ↦₆₄ w) -∗ memRegion d 8) := by
  rw [ProofLib.memRegion_eight s]
  apply Entails.sepExists_elim; intro w
  exact Entails.sepExists_right w
    (Entails.trans (r3b_ws_u64 s d w)
      (sepConj_mono_right (r3b_wand_post (pointsTo64_entails_memRegion d w))))

theorem r3b_ws_u8pad7 (s d : BitVec 64) (b0 : BitVec 8) :
    ((s ↦₈ b0) ∗ memRegion (s + 1#64) 7) ⊢
      ∃∗ w : BitVec 64,
        (s ↦₆₄ w) ∗ ((d ↦₆₄ w) -∗ ((d ↦₈ b0) ∗ memRegion (d + 1#64) 7)) := by
  refine Entails.trans (r3b_u8pad7_to_u64 s b0) ?_
  apply Entails.sepExists_elim; intro w
  apply Entails.pure_left; intro hlow
  exact Entails.sepExists_right w
    (Entails.trans (r3b_ws_u64 s d w)
      (sepConj_mono_right (r3b_wand_post (r3b_u64_to_u8pad7 d b0 w hlow))))

theorem r3b_ws_u32x2 (s d : BitVec 64) (c1 c2 : BitVec 32) :
    ((s ↦₃₂ c1) ∗ ((s + 4#64) ↦₃₂ c2)) ⊢
      (s ↦₆₄ (c2 ++ c1)) ∗ ((d ↦₆₄ (c2 ++ c1)) -∗ ((d ↦₃₂ c1) ∗ ((d + 4#64) ↦₃₂ c2))) := by
  rw [← r3b_pointsTo64_pack32x2 s c1 c2, ← r3b_pointsTo64_pack32x2 d c1 c2]
  exact r3b_ws_u64 s d (c2 ++ c1)

theorem r3b_ex_left {α : Sort _} {P : α → SepProp} {Q R : SepProp}
    (h : ∀ x : α, P x ∗ Q ⊢ R) : (∃∗ x, P x) ∗ Q ⊢ R := by
  rw [sepExists_sepConj_left]; exact Entails.sepExists_elim h

theorem r3b_keep {A X Rest G : SepProp} (h : (A ∗ X) ∗ Rest ⊢ G) :
    A ∗ (X ∗ Rest) ⊢ G := by
  rw [← sepConj_assoc]; exact h

theorem r3b_peel {α : Sort _} {A : SepProp} {P : α → SepProp} {Rest G : SepProp}
    (h : ∀ x : α, A ∗ (P x ∗ Rest) ⊢ G) : A ∗ ((∃∗ x, P x) ∗ Rest) ⊢ G := by
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; exact Entails.sepExists_elim h

theorem r3b_peel_end {α : Sort _} {A : SepProp} {P : α → SepProp} {G : SepProp}
    (h : ∀ x : α, A ∗ P x ⊢ G) : A ∗ (∃∗ x, P x) ⊢ G := by
  rw [sepExists_sepConj_right]; exact Entails.sepExists_elim h

def r3b_vecHeap (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    if cap = 0 then emp
    else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)

theorem r3b_vecU8At_eq (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs =
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        r3b_vecHeap A cap ptr bs := by
  dsimp only [vecU8At, vecHeader, r3b_vecHeap]
  ac_rfl

theorem r3b_vecHeap_cap_lt (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    r3b_vecHeap A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ r3b_vecHeap A cap ptr bs := by
  unfold r3b_vecHeap
  apply Entails.pure_left; rintro ⟨hle, hlt, hne⟩
  exact Entails.pure_right hlt (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))

structure r3b_W6 where
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  w4 : BitVec 64
  w5 : BitVec 64

def r3b_slot6 (a : BitVec 64) (e : r3b_W6) : SepProp :=
  (a ↦₆₄ e.w0) ∗ ((a + 8#64) ↦₆₄ e.w1) ∗ ((a + 16#64) ↦₆₄ e.w2) ∗
    ((a + 24#64) ↦₆₄ e.w3) ∗ ((a + 32#64) ↦₆₄ e.w4) ∗ ((a + 40#64) ↦₆₄ e.w5)

theorem r3b_mem48_to_slot6 (a : BitVec 64) :
    memRegion a 48 ⊢ ∃∗ e : r3b_W6, r3b_slot6 a e := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 40) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 32) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 24) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 16) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 8) (b' := a + 40#64) rfl (by bv_omega) (by decide)]
  simp only [ProofLib.memRegion_eight, sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w5
  apply Entails.sepExists_elim; intro w4
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w0
  exact Entails.sepExists_right ⟨w0, w1, w2, w3, w4, w5⟩
    (by dsimp only [r3b_slot6]; exact Entails.of_eq (by ac_rfl))

theorem r3b_slot6_to_mem48 (a : BitVec 64) (e : r3b_W6) :
    r3b_slot6 a e ⊢ memRegion a 48 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 40) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 32) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 24) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 16) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 8) (b' := a + 40#64) rfl (by bv_omega) (by decide)]
  dsimp only [r3b_slot6]
  exact Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (pointsTo64_entails_memRegion _ _))))))

theorem r3b_with_speOwned_words6 {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {src dst : BitVec 64} {k : RunDrop.SpeOwned} {Rest : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hk : ∀ (sw : r3b_W6),
      sw.w0 + 3#64 ≠ 0#64 → sw.w0 + 2#64 ≠ 0#64 →
      SepWPp prog ret s
        (r3b_slot6 src sw ∗ (r3b_slot6 dst sw -∗ RunDrop.speOwnedAt A dst k) ∗ Rest)
        Q Qp oom) :
    SepWPp prog ret s (RunDrop.speOwnedAt A src k ∗ Rest) Q Qp oom := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨w0, w1, w2, w3, w4, w5, Hspe, hw3, hw2, hm', hrest⟩ :=
    RunProofs.Initiate.Stage5Lemmas.speOwnedAt_words6 A src dst k (Rest ∗ R) s.mem hm
  let sw : r3b_W6 := ⟨w0, w1, w2, w3, w4, w5⟩
  have hm1 : s.mem ⊨ (r3b_slot6 src sw ∗ Hspe ∗ Rest) ∗ R := by
    dsimp only [r3b_slot6, sw]
    exact RunProofs.Initiate.Stage5Lemmas.sat_eq (by ac_rfl) hm'
  have hwand : Hspe ⊢ (r3b_slot6 dst sw -∗ RunDrop.speOwnedAt A dst k) := by
    apply Entails.wand_intro
    dsimp only [r3b_slot6, sw]
    exact Entails.trans (Entails.of_eq (by ac_rfl)) hrest
  have hm2 : s.mem ⊨
      (r3b_slot6 src sw ∗ (r3b_slot6 dst sw -∗ RunDrop.speOwnedAt A dst k) ∗ Rest) ∗ R :=
    Satisfies.mono
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hwand))) hm1
  exact hk sw hw3 hw2 R hm2 hL

/-! ## 3. Local Stack Splitting & Address Unpacking -/

theorem r3b_memRegion_to_runLocalsFrom (fsp : BitVec 64) :
    ∀ (off : Nat) (cs : List (Nat × Nat × SepProp)),
      RunLocalsFromWf off cs →
      (∀ c ∈ cs, c.2.2 = memRegion (fsp + BitVec.ofNat 64 c.1) c.2.1) →
      memRegion (fsp + BitVec.ofNat 64 off) (runLocalBytes - off) =
        runLocalsFrom fsp off cs := by
  intro off cs
  induction cs generalizing off with
  | nil => intro _ _; rfl
  | cons hd cs ih =>
    rcases hd with ⟨o, n, P⟩
    rintro ⟨hle, hwf'⟩ hcells
    have hlb : runLocalBytes = 0x29f0 := rfl
    have hon : o + n ≤ runLocalBytes := runLocalsFrom_le hwf'
    have hP : P = memRegion (fsp + BitVec.ofNat 64 o) n := hcells (o, n, P) (.head _)
    have htail := ih (o + n) hwf' (fun c hc => hcells c (.tail _ hc))
    have h1 : memRegion (fsp + BitVec.ofNat 64 off) (runLocalBytes - off) =
        memRegion (fsp + BitVec.ofNat 64 off) (o - off) ∗
          memRegion (fsp + BitVec.ofNat 64 o) (runLocalBytes - o) := by
      have hs := ProofLib.memRegion_split (fsp + BitVec.ofNat 64 off) (o - off)
        (runLocalBytes - o) (by omega)
      have hl : (o - off) + (runLocalBytes - o) = runLocalBytes - off := by omega
      have ha : fsp + BitVec.ofNat 64 off + BitVec.ofNat 64 (o - off) =
          fsp + BitVec.ofNat 64 o := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, show off + (o - off) = o by omega]
      simpa only [hl, ha] using hs
    have h2 : memRegion (fsp + BitVec.ofNat 64 o) (runLocalBytes - o) =
        memRegion (fsp + BitVec.ofNat 64 o) n ∗
          memRegion (fsp + BitVec.ofNat 64 (o + n)) (runLocalBytes - (o + n)) := by
      have hs := ProofLib.memRegion_split (fsp + BitVec.ofNat 64 o) n
        (runLocalBytes - (o + n)) (by omega)
      have hl : n + (runLocalBytes - (o + n)) = runLocalBytes - o := by omega
      have ha : fsp + BitVec.ofNat 64 o + BitVec.ofNat 64 n =
          fsp + BitVec.ofNat 64 (o + n) := by
        rw [BitVec.add_assoc, BitVec.ofNat_add]
      simpa only [hl, ha] using hs
    rw [h1, h2, htail, ← hP]
    rfl

theorem r3b_ownedBytes_entails_nameHeap (A : RustAlloc) (cap ptr len : BitVec 64)
    (bs : List (BitVec 8)) :
    ownedBytes A cap ptr len bs ⊢
      ⌜len = BitVec.ofNat 64 bs.length⌝ ∗
        addrNameHeap A ⟨⟨cap, ptr, bs⟩, 0#8⟩ := by
  unfold ownedBytes addrNameHeap
  apply Entails.pure_left; rintro ⟨hlen, hle, hlt, hne⟩
  exact Entails.pure_right hlen (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))

theorem r3b_addrNameHeap_dev_congr (A : RustAlloc) (v : VecGhost) (d₁ d₂ : BitVec 8) :
    addrNameHeap A ⟨v, d₁⟩ = addrNameHeap A ⟨v, d₂⟩ := rfl

theorem r3b_addrUpperAt_words (a : BitVec 64) (g : AddrGhost) :
    addrUpperAt a g ⊢
      ∃∗ hi : BitVec 64,
        ⌜hi.setWidth 8 = g.device⌝ ∗ (a ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
          ((a + 8#64) ↦₆₄ hi) := by
  unfold addrUpperAt
  have hu := r3b_u8pad7_to_u64 (a + 8#64) g.device
  have ha9 : a + 8#64 + 1#64 = a + 9#64 := by bv_omega
  rw [ha9] at hu
  refine Entails.trans (sepConj_mono_right hu) ?_
  simp only [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro hi
  exact Entails.sepExists_right hi (Entails.of_eq (by ac_rfl))

theorem r3b_words_to_addrUpperAt (a : BitVec 64) (g : AddrGhost) (hi : BitVec 64)
    (hhi : hi.setWidth 8 = g.device) :
    ((a ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗ ((a + 8#64) ↦₆₄ hi)) ⊢ addrUpperAt a g := by
  unfold addrUpperAt
  have hu := r3b_u64_to_u8pad7 (a + 8#64) g.device hi hhi
  have ha9 : a + 8#64 + 1#64 = a + 9#64 := by bv_omega
  rw [ha9] at hu
  exact sepConj_mono_right hu

theorem r3b_nameHeap_dealloc (A : RustAlloc) (g : AddrGhost) (hcap : g.name.cap ≠ 0) :
    addrNameHeap A g ⊢
      ⌜LayoutOk g.name.cap.toNat 1⌝ ∗ A.live g.name.ptr g.name.cap.toNat 1 ∗
        memRegion g.name.ptr g.name.cap.toNat := by
  unfold addrNameHeap
  simp only [hcap, ↓reduceIte]
  apply Entails.pure_left; rintro ⟨hle, hlt, _⟩
  have hpos : 0 < g.name.cap.toNat :=
    Nat.pos_of_ne_zero fun h0 => hcap (BitVec.eq_of_toNat_eq h0)
  refine Entails.pure_right ⟨hpos, ⟨0, rfl⟩, by omega⟩ (sepConj_mono_right ?_)
  have hmerge :
      memRegion g.name.ptr g.name.bytes.length ∗
        memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
          (g.name.cap.toNat - g.name.bytes.length) =
      memRegion g.name.ptr g.name.cap.toNat := by
    have hsum : g.name.bytes.length + (g.name.cap.toNat - g.name.bytes.length) =
        g.name.cap.toNat := Nat.add_sub_of_le hle
    simpa only [hsum] using
      (ProofLib.memRegion_split g.name.ptr g.name.bytes.length
        (g.name.cap.toNat - g.name.bytes.length) (by omega)).symm
  rw [← hmerge]
  exact sepConj_mono_left (ProofLib.pointsToBytes_entails_memRegion g.name.ptr g.name.bytes)

theorem r3b_nameHeap_zero (A : RustAlloc) (g : AddrGhost) (hcap : g.name.cap = 0) :
    addrNameHeap A g ⊢ emp := by
  unfold addrNameHeap
  simp only [hcap, ↓reduceIte]
  exact Entails.pure_left fun _ => Entails.refl emp

theorem r3b_call7_to_memRegion56 (a : BitVec 64) (cw : CallW) :
    (a ↦₆₄ cw.w0) ∗ ((a + 8#64) ↦₆₄ cw.w1) ∗ ((a + 16#64) ↦₆₄ cw.w2) ∗
      ((a + 24#64) ↦₆₄ cw.w3) ∗ ((a + 32#64) ↦₆₄ cw.w4) ∗ ((a + 40#64) ↦₆₄ cw.w5) ∗
      ((a + 48#64) ↦₆₄ cw.w6) ⊢ memRegion a 56 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 48) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 40) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 32) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 24) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 16) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 40#64) (n := 8) (k := 8) (b' := a + 48#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo64_entails_memRegion _ _))))))

theorem r3b_words4_entails_mem32 (a w0 w1 w2 w3 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ⊢
      memRegion a 32 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 24) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 8) (b' := a + 24#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)))

theorem r3b_mem32_to_words4 (a : BitVec 64) :
    memRegion a 32 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 24) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 8) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64), ProofLib.memRegion_eight (a + 24#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w0
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.of_eq (by ac_rfl)))))

theorem r3b_nameHeap_cap_ne_neg1 (A : RustAlloc) (g : AddrGhost) :
    addrNameHeap A g ⊢ ⌜g.name.cap ≠ 0xffffffffffffffff#64⌝ ∗ addrNameHeap A g := by
  unfold addrNameHeap
  apply Entails.pure_left; rintro ⟨hle, hlt, hne⟩
  have hne1 : g.name.cap ≠ 0xffffffffffffffff#64 := by
    intro heq
    have hbig : (0xffffffffffffffff#64).toNat = 2 ^ 64 - 1 := by decide
    rw [heq, hbig] at hlt
    omega
  exact Entails.pure_right hne1 (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))

/-! ## 4. 5-Word & 30-Word Slot Bundles for `PreKeySignalMessage` -/

theorem r3b_split_at (fsp : BitVec 64) (a m c : Nat)
    (hsum : m + (c - (a + m)) = c - a) (h64 : c ≤ 2 ^ 64) :
    memRegion (fsp + BitVec.ofNat 64 a) (c - a) =
      memRegion (fsp + BitVec.ofNat 64 a) m ∗
        memRegion (fsp + BitVec.ofNat 64 (a + m)) (c - (a + m)) := by
  have hs := ProofLib.memRegion_split (fsp + BitVec.ofNat 64 a) m (c - (a + m)) (by omega)
  have ha : fsp + BitVec.ofNat 64 a + BitVec.ofNat 64 m = fsp + BitVec.ofNat 64 (a + m) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  simpa only [hsum, ha] using hs

structure r3b_W5 where
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  w4 : BitVec 64

def r3b_slot5 (a : BitVec 64) (e : r3b_W5) : SepProp :=
  (a ↦₆₄ e.w0) ∗ ((a + 8#64) ↦₆₄ e.w1) ∗ ((a + 16#64) ↦₆₄ e.w2) ∗
    ((a + 24#64) ↦₆₄ e.w3) ∗ ((a + 32#64) ↦₆₄ e.w4)

theorem r3b_mem40_to_slot5 (a : BitVec 64) :
    memRegion a 40 ⊢ ∃∗ e : r3b_W5, r3b_slot5 a e := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 32) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 24) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 16) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 8) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64), ProofLib.memRegion_eight (a + 24#64),
      ProofLib.memRegion_eight (a + 32#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w4
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w0
  exact Entails.sepExists_right ⟨w0, w1, w2, w3, w4⟩ (Entails.of_eq (by dsimp only [r3b_slot5]))

theorem r3b_slot5_to_mem40 (a : BitVec 64) (e : r3b_W5) :
    r3b_slot5 a e ⊢ memRegion a 40 := by
  dsimp only [r3b_slot5]
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 32) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 24) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 16) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 8) (b' := a + 32#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))))

structure r3b_W30 where
  b0 : r3b_W5
  b1 : r3b_W5
  b2 : r3b_W5
  b3 : r3b_W5
  b4 : r3b_W5
  b5 : r3b_W5

def r3b_slot30 (a : BitVec 64) (w : r3b_W30) : SepProp :=
  r3b_slot5 a w.b0 ∗ r3b_slot5 (a + 40#64) w.b1 ∗ r3b_slot5 (a + 80#64) w.b2 ∗
    r3b_slot5 (a + 120#64) w.b3 ∗ r3b_slot5 (a + 160#64) w.b4 ∗ r3b_slot5 (a + 200#64) w.b5

theorem r3b_mem240_to_slot30 (a : BitVec 64) :
    memRegion a 240 ⊢ ∃∗ w : r3b_W30, r3b_slot30 a w := by
  rw [ProofLib.memRegion_split' (b := a) (n := 40) (k := 200) (b' := a + 40#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 40#64) (n := 40) (k := 160) (b' := a + 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 80#64) (n := 40) (k := 120) (b' := a + 120#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 120#64) (n := 40) (k := 80) (b' := a + 160#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 160#64) (n := 40) (k := 40) (b' := a + 200#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans
    (sepConj_mono (r3b_mem40_to_slot5 a)
      (sepConj_mono (r3b_mem40_to_slot5 (a + 40#64))
        (sepConj_mono (r3b_mem40_to_slot5 (a + 80#64))
          (sepConj_mono (r3b_mem40_to_slot5 (a + 120#64))
            (sepConj_mono (r3b_mem40_to_slot5 (a + 160#64))
              (r3b_mem40_to_slot5 (a + 200#64))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro b5
  apply Entails.sepExists_elim; intro b4
  apply Entails.sepExists_elim; intro b3
  apply Entails.sepExists_elim; intro b2
  apply Entails.sepExists_elim; intro b1
  apply Entails.sepExists_elim; intro b0
  exact Entails.sepExists_right ⟨b0, b1, b2, b3, b4, b5⟩ (Entails.of_eq (by dsimp only [r3b_slot30]))

theorem r3b_slot30_to_mem240 (a : BitVec 64) (w : r3b_W30) :
    r3b_slot30 a w ⊢ memRegion a 240 := by
  dsimp only [r3b_slot30]
  rw [ProofLib.memRegion_split' (b := a) (n := 40) (k := 200) (b' := a + 40#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 40#64) (n := 40) (k := 160) (b' := a + 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 80#64) (n := 40) (k := 120) (b' := a + 120#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 120#64) (n := 40) (k := 80) (b' := a + 160#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 160#64) (n := 40) (k := 40) (b' := a + 200#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (r3b_slot5_to_mem40 a w.b0)
    (sepConj_mono (r3b_slot5_to_mem40 (a + 40#64) w.b1)
      (sepConj_mono (r3b_slot5_to_mem40 (a + 80#64) w.b2)
        (sepConj_mono (r3b_slot5_to_mem40 (a + 120#64) w.b3)
          (sepConj_mono (r3b_slot5_to_mem40 (a + 160#64) w.b4)
            (r3b_slot5_to_mem40 (a + 200#64) w.b5)))))

def r3b_Own1 (a : BitVec 64) (P : SepProp) : SepProp :=
  ∃∗ w : BitVec 64, (a ↦₆₄ w) ∗ ((a ↦₆₄ w) -∗ P)

def r3b_Own5 (a : BitVec 64) (P : SepProp) : SepProp :=
  ∃∗ e : r3b_W5, r3b_slot5 a e ∗ (r3b_slot5 a e -∗ P)

def r3b_Own30 (a : BitVec 64) (P : SepProp) : SepProp :=
  ∃∗ w : r3b_W30, r3b_slot30 a w ∗ (r3b_slot30 a w -∗ P)

theorem r3b_own1_u64 (a v : BitVec 64) :
    (a ↦₆₄ v) ⊢ r3b_Own1 a (a ↦₆₄ v) :=
  Entails.sepExists_right v (r3b_ws_u64 a a v)

theorem r3b_own1_mem8 (a : BitVec 64) :
    memRegion a 8 ⊢ r3b_Own1 a (memRegion a 8) :=
  r3b_ws_mem8 a a

theorem r3b_own1_u8pad7 (a b1 : BitVec 64) (b0 : BitVec 8) (hb1 : a + 1#64 = b1) :
    ((a ↦₈ b0) ∗ memRegion b1 7) ⊢ r3b_Own1 a ((a ↦₈ b0) ∗ memRegion b1 7) := by
  subst hb1; exact r3b_ws_u8pad7 a a b0

theorem r3b_own1_u32x2 (a b4 : BitVec 64) (c1 c2 : BitVec 32) (hb4 : a + 4#64 = b4) :
    ((a ↦₃₂ c1) ∗ (b4 ↦₃₂ c2)) ⊢ r3b_Own1 a ((a ↦₃₂ c1) ∗ (b4 ↦₃₂ c2)) := by
  subst hb4; exact Entails.sepExists_right (c2 ++ c1) (r3b_ws_u32x2 a a c1 c2)

theorem r3b_own1_u32pad4 (a b4 : BitVec 64) (c1 : BitVec 32) (hb4 : a + 4#64 = b4) :
    ((a ↦₃₂ c1) ∗ memRegion b4 4) ⊢ r3b_Own1 a ((a ↦₃₂ c1) ∗ memRegion b4 4) := by
  subst hb4
  have hm4 : memRegion (a + 4#64) 4 ⊢ ∃∗ c2 : BitVec 32, (a + 4#64) ↦₃₂ c2 := by
    rw [ProofLib.memRegion_split' (b := a + 4#64) (n := 1) (k := 3) (b' := a + 5#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 5#64) (n := 1) (k := 2) (b' := a + 6#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 6#64) (n := 1) (k := 1) (b' := a + 7#64) rfl (by bv_omega) (by decide)]
    simp only [Path.Helpers.memRegion_1_eq_pointsTo8, sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro d3
    apply Entails.sepExists_elim; intro d2
    apply Entails.sepExists_elim; intro d1
    apply Entails.sepExists_elim; intro d0
    refine Entails.sepExists_right (d3 ++ d2 ++ d1 ++ d0) ?_
    rw [← pointsToBytes4_eq_pointsTo32 (a + 4#64) d0 d1 d2 d3]
    simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
    have h1 : a + 4#64 + 1#64 = a + 5#64 := by bv_omega
    have h2 : a + 5#64 + 1#64 = a + 6#64 := by bv_omega
    have h3 : a + 6#64 + 1#64 = a + 7#64 := by bv_omega
    rw [h1, h2, h3]
    exact Entails.of_eq (by ac_rfl)
  refine Entails.trans (sepConj_mono_right hm4) ?_
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro c2
  refine Entails.sepExists_right (c2 ++ c1) ?_
  exact Entails.trans (r3b_ws_u32x2 a a c1 c2)
    (sepConj_mono_right (r3b_wand_post (sepConj_mono_right (pointsTo32_entails_memRegion _ _))))

theorem r3b_own1_bytes8 (a : BitVec 64) (bs : List (BitVec 8)) (hlen : bs.length = 8) :
    (a ↦ₛ bs) ⊢ r3b_Own1 a (a ↦ₛ bs) := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals simp only [List.length_cons, List.length_nil] at hlen; try omega
  rw [pointsToBytes8_eq_pointsTo64 a b0 b1 b2 b3 b4 b5 b6 b7]
  exact r3b_own1_u64 a _

theorem r3b_bytes32_split4 (a a1 a2 a3 : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length = 32) (h1 : a + 8#64 = a1) (h2 : a + 16#64 = a2) (h3 : a + 24#64 = a3) :
    (a ↦ₛ bs) =
      (a ↦ₛ bs.take 8) ∗ (a1 ↦ₛ (bs.drop 8).take 8) ∗
        (a2 ↦ₛ ((bs.drop 8).drop 8).take 8) ∗ (a3 ↦ₛ ((bs.drop 8).drop 8).drop 8) := by
  subst h1; subst h2; subst h3
  have hsplit : bs = bs.take 8 ++ (bs.drop 8).take 8 ++ ((bs.drop 8).drop 8).take 8 ++
      (((bs.drop 8).drop 8).drop 8) := by
    simp only [List.append_assoc, List.take_append_drop]
  have l0 : (bs.take 8).length = 8 := by simp [hlen]
  have l1 : ((bs.drop 8).take 8).length = 8 := by simp [hlen]
  have l2 : (((bs.drop 8).drop 8).take 8).length = 8 := by simp [hlen]
  conv_lhs => rw [hsplit]
  simp only [pointsToBytes_append, List.length_append, l0, l1, l2]
  have ha16 : a + BitVec.ofNat 64 (8 + 8) = a + 16#64 := rfl
  have ha24 : a + BitVec.ofNat 64 (8 + 8 + 8) = a + 24#64 := rfl
  rw [ha16, ha24]
  ac_rfl

theorem r3b_own5_mk {a a1 a2 a3 a4 : BitVec 64} {P0 P1 P2 P3 P4 : SepProp}
    (e1 : a + 8#64 = a1) (e2 : a + 16#64 = a2) (e3 : a + 24#64 = a3) (e4 : a + 32#64 = a4)
    (h0 : P0 ⊢ r3b_Own1 a P0) (h1 : P1 ⊢ r3b_Own1 a1 P1) (h2 : P2 ⊢ r3b_Own1 a2 P2)
    (h3 : P3 ⊢ r3b_Own1 a3 P3) (h4 : P4 ⊢ r3b_Own1 a4 P4) :
    (P0 ∗ P1 ∗ P2 ∗ P3 ∗ P4) ⊢ r3b_Own5 a (P0 ∗ P1 ∗ P2 ∗ P3 ∗ P4) := by
  subst e1; subst e2; subst e3; subst e4
  refine Entails.trans
    (sepConj_mono h0 (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 h4)))) ?_
  dsimp only [r3b_Own1, r3b_Own5]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w4
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w0
  refine Entails.sepExists_right ⟨w0, w1, w2, w3, w4⟩ ?_
  dsimp only [r3b_slot5]
  let W : SepProp :=
    ((a ↦₆₄ w0) -∗ P0) ∗ (((a + 8#64) ↦₆₄ w1) -∗ P1) ∗ (((a + 16#64) ↦₆₄ w2) -∗ P2) ∗
      (((a + 24#64) ↦₆₄ w3) -∗ P3) ∗ (((a + 32#64) ↦₆₄ w4) -∗ P4)
  refine Entails.trans
    (Entails.of_eq (show
      (((a ↦₆₄ w0) ∗ ((a ↦₆₄ w0) -∗ P0)) ∗
        (((a + 8#64) ↦₆₄ w1) ∗ (((a + 8#64) ↦₆₄ w1) -∗ P1)) ∗
        (((a + 16#64) ↦₆₄ w2) ∗ (((a + 16#64) ↦₆₄ w2) -∗ P2)) ∗
        (((a + 24#64) ↦₆₄ w3) ∗ (((a + 24#64) ↦₆₄ w3) -∗ P3)) ∗
        (((a + 32#64) ↦₆₄ w4) ∗ (((a + 32#64) ↦₆₄ w4) -∗ P4))) =
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
        ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4)) ∗ W by dsimp only [W]; ac_rfl))
    (sepConj_mono_right (Entails.wand_intro ?_))
  refine Entails.trans
    (Entails.of_eq (show
      W ∗ ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
        ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4)) =
      ((a ↦₆₄ w0) ∗ ((a ↦₆₄ w0) -∗ P0)) ∗
        (((a + 8#64) ↦₆₄ w1) ∗ (((a + 8#64) ↦₆₄ w1) -∗ P1)) ∗
        (((a + 16#64) ↦₆₄ w2) ∗ (((a + 16#64) ↦₆₄ w2) -∗ P2)) ∗
        (((a + 24#64) ↦₆₄ w3) ∗ (((a + 24#64) ↦₆₄ w3) -∗ P3)) ∗
        (((a + 32#64) ↦₆₄ w4) ∗ (((a + 32#64) ↦₆₄ w4) -∗ P4)) by dsimp only [W]; ac_rfl))
    (sepConj_mono (Entails.wand_elim _ _)
      (sepConj_mono (Entails.wand_elim _ _)
        (sepConj_mono (Entails.wand_elim _ _)
          (sepConj_mono (Entails.wand_elim _ _) (Entails.wand_elim _ _)))))

theorem r3b_own30_mk {a a1 a2 a3 a4 a5 : BitVec 64} {B0 B1 B2 B3 B4 B5 H : SepProp}
    (e1 : a + 40#64 = a1) (e2 : a + 80#64 = a2) (e3 : a + 120#64 = a3)
    (e4 : a + 160#64 = a4) (e5 : a + 200#64 = a5)
    (h0 : B0 ⊢ r3b_Own5 a B0) (h1 : B1 ⊢ r3b_Own5 a1 B1) (h2 : B2 ⊢ r3b_Own5 a2 B2)
    (h3 : B3 ⊢ r3b_Own5 a3 B3) (h4 : B4 ⊢ r3b_Own5 a4 B4) (h5 : B5 ⊢ r3b_Own5 a5 B5) :
    (B0 ∗ B1 ∗ B2 ∗ B3 ∗ B4 ∗ B5 ∗ H) ⊢ r3b_Own30 a (B0 ∗ B1 ∗ B2 ∗ B3 ∗ B4 ∗ B5 ∗ H) := by
  subst e1; subst e2; subst e3; subst e4; subst e5
  refine Entails.trans
    (sepConj_mono h0 (sepConj_mono h1 (sepConj_mono h2
      (sepConj_mono h3 (sepConj_mono h4 (sepConj_mono h5 (Entails.refl H))))))) ?_
  dsimp only [r3b_Own5, r3b_Own30]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro b5
  apply Entails.sepExists_elim; intro b4
  apply Entails.sepExists_elim; intro b3
  apply Entails.sepExists_elim; intro b2
  apply Entails.sepExists_elim; intro b1
  apply Entails.sepExists_elim; intro b0
  refine Entails.sepExists_right ⟨b0, b1, b2, b3, b4, b5⟩ ?_
  dsimp only [r3b_slot30]
  let W : SepProp :=
    (r3b_slot5 a b0 -∗ B0) ∗ (r3b_slot5 (a + 40#64) b1 -∗ B1) ∗
      (r3b_slot5 (a + 80#64) b2 -∗ B2) ∗ (r3b_slot5 (a + 120#64) b3 -∗ B3) ∗
      (r3b_slot5 (a + 160#64) b4 -∗ B4) ∗ (r3b_slot5 (a + 200#64) b5 -∗ B5) ∗ H
  refine Entails.trans
    (Entails.of_eq (show
      ((r3b_slot5 a b0 ∗ (r3b_slot5 a b0 -∗ B0)) ∗
        (r3b_slot5 (a + 40#64) b1 ∗ (r3b_slot5 (a + 40#64) b1 -∗ B1)) ∗
        (r3b_slot5 (a + 80#64) b2 ∗ (r3b_slot5 (a + 80#64) b2 -∗ B2)) ∗
        (r3b_slot5 (a + 120#64) b3 ∗ (r3b_slot5 (a + 120#64) b3 -∗ B3)) ∗
        (r3b_slot5 (a + 160#64) b4 ∗ (r3b_slot5 (a + 160#64) b4 -∗ B4)) ∗
        (r3b_slot5 (a + 200#64) b5 ∗ (r3b_slot5 (a + 200#64) b5 -∗ B5)) ∗ H) =
      (r3b_slot5 a b0 ∗ r3b_slot5 (a + 40#64) b1 ∗ r3b_slot5 (a + 80#64) b2 ∗
        r3b_slot5 (a + 120#64) b3 ∗ r3b_slot5 (a + 160#64) b4 ∗ r3b_slot5 (a + 200#64) b5) ∗ W
      by dsimp only [W]; ac_rfl))
    (sepConj_mono_right (Entails.wand_intro ?_))
  refine Entails.trans
    (Entails.of_eq (show
      W ∗ (r3b_slot5 a b0 ∗ r3b_slot5 (a + 40#64) b1 ∗ r3b_slot5 (a + 80#64) b2 ∗
        r3b_slot5 (a + 120#64) b3 ∗ r3b_slot5 (a + 160#64) b4 ∗ r3b_slot5 (a + 200#64) b5) =
      (r3b_slot5 a b0 ∗ (r3b_slot5 a b0 -∗ B0)) ∗
        (r3b_slot5 (a + 40#64) b1 ∗ (r3b_slot5 (a + 40#64) b1 -∗ B1)) ∗
        (r3b_slot5 (a + 80#64) b2 ∗ (r3b_slot5 (a + 80#64) b2 -∗ B2)) ∗
        (r3b_slot5 (a + 120#64) b3 ∗ (r3b_slot5 (a + 120#64) b3 -∗ B3)) ∗
        (r3b_slot5 (a + 160#64) b4 ∗ (r3b_slot5 (a + 160#64) b4 -∗ B4)) ∗
        (r3b_slot5 (a + 200#64) b5 ∗ (r3b_slot5 (a + 200#64) b5 -∗ B5)) ∗ H
      by dsimp only [W]; ac_rfl))
    (sepConj_mono (Entails.wand_elim _ _)
      (sepConj_mono (Entails.wand_elim _ _)
        (sepConj_mono (Entails.wand_elim _ _)
          (sepConj_mono (Entails.wand_elim _ _)
            (sepConj_mono (Entails.wand_elim _ _)
              (sepConj_mono (Entails.wand_elim _ _) (Entails.refl H)))))))

theorem r3b_own1_optU32 (a : BitVec 64) (o : Option (BitVec 32)) :
    optU32At a o ⊢ r3b_Own1 a (optU32At a o) := by
  cases o with
  | none => exact r3b_own1_u32pad4 a (a + 4#64) 0#32 rfl
  | some v => exact r3b_own1_u32x2 a (a + 4#64) 1#32 v rfl

/-- Decompose `preKeyMsgAt A pmG a pm` (`248` bytes) into word 0 `pmG.msg.pqCap` (`< 2 ^ 63`) +
30 words at `a + 8#64` + a magic wand restoring `preKeyMsgAt A pmG a pm` once the shuffle restores
all 31 words at `[a .. a + 248)`. -/
theorem r3b_pkm_to_words (A : RustAlloc) (pmG : PreKeyMsgGhost) (a : BitVec 64)
    (pm : PreKeySignalMessage) :
    preKeyMsgAt A pmG a pm ⊢
      ∃∗ w : r3b_W30,
        ⌜pmG.msg.pqCap.toNat < 2 ^ 63⌝ ∗
        (a ↦₆₄ pmG.msg.pqCap) ∗
        r3b_slot30 (a + 8#64) w ∗
        (((a ↦₆₄ pmG.msg.pqCap) ∗ r3b_slot30 (a + 8#64) w) -∗ preKeyMsgAt A pmG a pm) := by
  have hsrk_len : pm.message.senderRatchetKey.bytes.toList.length = 32 :=
    pm.message.senderRatchetKey.bytes.toList_length
  have hbk_len : pm.baseKey.bytes.toList.length = 32 := pm.baseKey.bytes.toList_length
  have hik_len : pm.identityKey.publicKey.bytes.toList.length = 32 :=
    pm.identityKey.publicKey.bytes.toList_length
  have hsrk := r3b_bytes32_split4 (a + 56#64) (a + 64#64) (a + 72#64) (a + 80#64)
    pm.message.senderRatchetKey.bytes.toList hsrk_len (by bv_omega) (by bv_omega) (by bv_omega)
  have hbk := r3b_bytes32_split4 (a + 168#64) (a + 176#64) (a + 184#64) (a + 192#64)
    pm.baseKey.bytes.toList hbk_len (by bv_omega) (by bv_omega) (by bv_omega)
  have hik := r3b_bytes32_split4 (a + 200#64) (a + 208#64) (a + 216#64) (a + 224#64)
    pm.identityKey.publicKey.bytes.toList hik_len (by bv_omega) (by bv_omega) (by bv_omega)
  have haddr : ∃ (A0 A1 AH : SepProp),
      optBoxU8At A (a + 88#64) pmG.msg.addrPtr pm.message.addresses = A0 ∗ A1 ∗ AH ∧
        (A0 ⊢ r3b_Own1 (a + 88#64) A0) ∧ (A1 ⊢ r3b_Own1 (a + 96#64) A1) := by
    cases pm.message.addresses with
    | none =>
      refine ⟨(a + 88#64) ↦₆₄ 0#64, memRegion (a + 96#64) 8, emp, ?_,
        r3b_own1_u64 _ _, r3b_own1_mem8 _⟩
      dsimp only [optBoxU8At]
      have ha96 : a + 88#64 + 8#64 = a + 96#64 := by bv_omega
      rw [ha96]; ac_rfl
    | some ad =>
      refine ⟨(a + 88#64) ↦₆₄ pmG.msg.addrPtr,
        (a + 96#64) ↦₆₄ BitVec.ofNat 64 ad.length,
        ⌜pmG.msg.addrPtr ≠ 0 ∧ ad.length < 2 ^ 63⌝ ∗
          (if ad = [] then emp else A.live pmG.msg.addrPtr ad.length 1 ∗ (pmG.msg.addrPtr ↦ₛ ad)),
        ?_, r3b_own1_u64 _ _, r3b_own1_u64 _ _⟩
      dsimp only [optBoxU8At, boxU8At]
      have ha96 : a + 88#64 + 8#64 = a + 96#64 := by bv_omega
      rw [ha96]
  have hkyb : ∃ (K0 K1 K2 KH : SepProp),
      optKyberAt A (a + 144#64) pmG.kyberPtr pm.kyberPayload = K0 ∗ K1 ∗ K2 ∗ KH ∧
        (K0 ⊢ r3b_Own1 (a + 144#64) K0) ∧ (K1 ⊢ r3b_Own1 (a + 152#64) K1) ∧
        (K2 ⊢ r3b_Own1 (a + 160#64) K2) := by
    cases pm.kyberPayload with
    | none =>
      refine ⟨(a + 144#64) ↦₆₄ 0#64, memRegion (a + 152#64) 8, memRegion (a + 160#64) 8, emp,
        ?_, r3b_own1_u64 _ _, r3b_own1_mem8 _, r3b_own1_mem8 _⟩
      dsimp only [optKyberAt]
      have ha152 : a + 144#64 + 8#64 = a + 152#64 := by bv_omega
      rw [ha152, ProofLib.memRegion_split' (b := a + 152#64) (n := 8) (k := 8)
        (b' := a + 160#64) rfl (by bv_omega) (by decide)]
      ac_rfl
    | some k =>
      refine ⟨(a + 144#64) ↦₆₄ pmG.kyberPtr,
        (a + 152#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length,
        ((a + 160#64) ↦₃₂ k.preKeyId) ∗ memRegion (a + 164#64) 4,
        ⌜pmG.kyberPtr ≠ 0 ∧ k.ciphertext.length < 2 ^ 63⌝ ∗
          (if k.ciphertext = [] then emp
           else A.live pmG.kyberPtr k.ciphertext.length 1 ∗ (pmG.kyberPtr ↦ₛ k.ciphertext)),
        ?_, r3b_own1_u64 _ _, r3b_own1_u64 _ _, r3b_own1_u32pad4 _ _ _ (by bv_omega)⟩
      dsimp only [optKyberAt, boxU8At]
      have ha152 : a + 144#64 + 8#64 = a + 152#64 := by bv_omega
      have ha160 : a + 144#64 + 0x10#64 = a + 160#64 := by bv_omega
      have ha164 : a + 144#64 + 0x14#64 = a + 164#64 := by bv_omega
      rw [ha152, ha160, ha164]; ac_rfl
  obtain ⟨A0, A1, AH, haddr_eq, hA0, hA1⟩ := haddr
  obtain ⟨K0, K1, K2, KH, hkyb_eq, hK0, hK1, hK2⟩ := hkyb
  let B0 : SepProp :=
    ((a + 8#64) ↦₆₄ pmG.msg.pqPtr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pm.message.pqRatchet.length) ∗
      ((a + 24#64) ↦₆₄ pmG.msg.ctPtr) ∗
      ((a + 32#64) ↦₆₄ BitVec.ofNat 64 pm.message.ciphertext.length) ∗
      ((a + 40#64) ↦₆₄ pmG.msg.serPtr)
  let B1 : SepProp :=
    ((a + 48#64) ↦₆₄ BitVec.ofNat 64 pm.message.serialized.length) ∗
      ((a + 56#64) ↦ₛ pm.message.senderRatchetKey.bytes.toList.take 8) ∗
      ((a + 64#64) ↦ₛ (pm.message.senderRatchetKey.bytes.toList.drop 8).take 8) ∗
      ((a + 72#64) ↦ₛ ((pm.message.senderRatchetKey.bytes.toList.drop 8).drop 8).take 8) ∗
      ((a + 80#64) ↦ₛ ((pm.message.senderRatchetKey.bytes.toList.drop 8).drop 8).drop 8)
  let B2 : SepProp :=
    A0 ∗ A1 ∗
      (((a + 104#64) ↦₃₂ pm.message.counter) ∗ ((a + 108#64) ↦₃₂ pm.message.previousCounter)) ∗
      (((a + 112#64) ↦₈ pm.message.messageVersion) ∗ memRegion (a + 113#64) 7) ∗
      optU32At (a + 120#64) pm.preKeyId
  let B3 : SepProp :=
    ((a + 128#64) ↦₆₄ pmG.serPtr) ∗
      ((a + 136#64) ↦₆₄ BitVec.ofNat 64 pm.serialized.length) ∗
      K0 ∗ K1 ∗ K2
  let B4 : SepProp :=
    ((a + 168#64) ↦ₛ pm.baseKey.bytes.toList.take 8) ∗
      ((a + 176#64) ↦ₛ (pm.baseKey.bytes.toList.drop 8).take 8) ∗
      ((a + 184#64) ↦ₛ ((pm.baseKey.bytes.toList.drop 8).drop 8).take 8) ∗
      ((a + 192#64) ↦ₛ ((pm.baseKey.bytes.toList.drop 8).drop 8).drop 8) ∗
      ((a + 200#64) ↦ₛ pm.identityKey.publicKey.bytes.toList.take 8)
  let B5 : SepProp :=
    ((a + 208#64) ↦ₛ (pm.identityKey.publicKey.bytes.toList.drop 8).take 8) ∗
      ((a + 216#64) ↦ₛ ((pm.identityKey.publicKey.bytes.toList.drop 8).drop 8).take 8) ∗
      ((a + 224#64) ↦ₛ ((pm.identityKey.publicKey.bytes.toList.drop 8).drop 8).drop 8) ∗
      (((a + 232#64) ↦₃₂ pm.registrationId) ∗ ((a + 236#64) ↦₃₂ pm.signedPreKeyId)) ∗
      (((a + 240#64) ↦₈ pm.messageVersion) ∗ memRegion (a + 241#64) 7)
  let H : SepProp :=
    ⌜macLength + 1 ≤ pm.message.serialized.length ∧ pm.message.serialized.length < 2 ^ 40 ∧
      pm.message.ciphertext.length < 2 ^ 40 ∧ pm.message.pqRatchet.length < 2 ^ 40 ∧
      (∀ ad, pm.message.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
    r3b_vecHeap A pmG.msg.pqCap pmG.msg.pqPtr pm.message.pqRatchet ∗
    ⌜pmG.msg.ctPtr ≠ 0 ∧ pm.message.ciphertext.length < 2 ^ 63⌝ ∗
    (if pm.message.ciphertext = [] then emp
     else A.live pmG.msg.ctPtr pm.message.ciphertext.length 1 ∗ (pmG.msg.ctPtr ↦ₛ pm.message.ciphertext)) ∗
    ⌜pmG.msg.serPtr ≠ 0 ∧ pm.message.serialized.length < 2 ^ 63⌝ ∗
    (if pm.message.serialized = [] then emp
     else A.live pmG.msg.serPtr pm.message.serialized.length 1 ∗ (pmG.msg.serPtr ↦ₛ pm.message.serialized)) ∗
    ⌜pmG.serPtr ≠ 0 ∧ pm.serialized.length < 2 ^ 63⌝ ∗
    (if pm.serialized = [] then emp
     else A.live pmG.serPtr pm.serialized.length 1 ∗ (pmG.serPtr ↦ₛ pm.serialized)) ∗
    AH ∗ KH
  have hpkm_eq : preKeyMsgAt A pmG a pm =
      (a ↦₆₄ pmG.msg.pqCap) ∗ (B0 ∗ B1 ∗ B2 ∗ B3 ∗ B4 ∗ B5 ∗ H) := by
    unfold preKeyMsgAt signalMessageAt
    rw [r3b_vecU8At_eq A a pmG.msg.pqCap pmG.msg.pqPtr pm.message.pqRatchet,
        haddr_eq, hkyb_eq, hsrk, hbk, hik]
    dsimp only [boxU8At, B0, B1, B2, B3, B4, B5, H]
    have c1 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
    have c2 : a + 40#64 + 8#64 = a + 48#64 := by bv_omega
    have c3 : a + 128#64 + 8#64 = a + 136#64 := by bv_omega
    rw [c1, c2, c3]
    ac_rfl
  have hcap_extract : preKeyMsgAt A pmG a pm ⊢
      ⌜pmG.msg.pqCap.toNat < 2 ^ 63⌝ ∗ preKeyMsgAt A pmG a pm := by
    rw [hpkm_eq]
    have hpull : ∀ (X : SepProp),
        (a ↦₆₄ pmG.msg.pqCap) ∗ (B0 ∗ B1 ∗ B2 ∗ B3 ∗ B4 ∗ B5 ∗ H) =
        r3b_vecHeap A pmG.msg.pqCap pmG.msg.pqPtr pm.message.pqRatchet ∗
          ((a ↦₆₄ pmG.msg.pqCap) ∗ B0 ∗ B1 ∗ B2 ∗ B3 ∗ B4 ∗ B5 ∗
            (⌜macLength + 1 ≤ pm.message.serialized.length ∧ pm.message.serialized.length < 2 ^ 40 ∧
              pm.message.ciphertext.length < 2 ^ 40 ∧ pm.message.pqRatchet.length < 2 ^ 40 ∧
              (∀ ad, pm.message.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
            ⌜pmG.msg.ctPtr ≠ 0 ∧ pm.message.ciphertext.length < 2 ^ 63⌝ ∗
            (if pm.message.ciphertext = [] then emp
             else A.live pmG.msg.ctPtr pm.message.ciphertext.length 1 ∗
               (pmG.msg.ctPtr ↦ₛ pm.message.ciphertext)) ∗
            ⌜pmG.msg.serPtr ≠ 0 ∧ pm.message.serialized.length < 2 ^ 63⌝ ∗
            (if pm.message.serialized = [] then emp
             else A.live pmG.msg.serPtr pm.message.serialized.length 1 ∗
               (pmG.msg.serPtr ↦ₛ pm.message.serialized)) ∗
            ⌜pmG.serPtr ≠ 0 ∧ pm.serialized.length < 2 ^ 63⌝ ∗
            (if pm.serialized = [] then emp
             else A.live pmG.serPtr pm.serialized.length 1 ∗ (pmG.serPtr ↦ₛ pm.serialized)) ∗
            AH ∗ KH)) := fun _ => by dsimp only [H]; ac_rfl
    rw [hpull emp]
    refine Entails.trans (sepConj_mono_left (r3b_vecHeap_cap_lt A _ _ _)) ?_
    exact Entails.of_eq (by ac_rfl)
  have hB0 : B0 ⊢ r3b_Own5 (a + 8#64) B0 :=
    r3b_own5_mk (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
      (r3b_own1_u64 _ _) (r3b_own1_u64 _ _) (r3b_own1_u64 _ _)
      (r3b_own1_u64 _ _) (r3b_own1_u64 _ _)
  have hB1 : B1 ⊢ r3b_Own5 (a + 48#64) B1 :=
    r3b_own5_mk (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
      (r3b_own1_u64 _ _)
      (r3b_own1_bytes8 _ _ (by simp [hsrk_len]))
      (r3b_own1_bytes8 _ _ (by simp [hsrk_len]))
      (r3b_own1_bytes8 _ _ (by simp [hsrk_len]))
      (r3b_own1_bytes8 _ _ (by simp [hsrk_len]))
  have hB2 : B2 ⊢ r3b_Own5 (a + 88#64) B2 :=
    r3b_own5_mk (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
      hA0 hA1
      (r3b_own1_u32x2 _ _ _ _ (by bv_omega))
      (r3b_own1_u8pad7 _ _ _ (by bv_omega))
      (r3b_own1_optU32 _ _)
  have hB3 : B3 ⊢ r3b_Own5 (a + 128#64) B3 :=
    r3b_own5_mk (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
      (r3b_own1_u64 _ _) (r3b_own1_u64 _ _) hK0 hK1 hK2
  have hB4 : B4 ⊢ r3b_Own5 (a + 168#64) B4 :=
    r3b_own5_mk (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
      (r3b_own1_bytes8 _ _ (by simp [hbk_len]))
      (r3b_own1_bytes8 _ _ (by simp [hbk_len]))
      (r3b_own1_bytes8 _ _ (by simp [hbk_len]))
      (r3b_own1_bytes8 _ _ (by simp [hbk_len]))
      (r3b_own1_bytes8 _ _ (by simp [hik_len]))
  have hB5 : B5 ⊢ r3b_Own5 (a + 208#64) B5 :=
    r3b_own5_mk (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
      (r3b_own1_bytes8 _ _ (by simp [hik_len]))
      (r3b_own1_bytes8 _ _ (by simp [hik_len]))
      (r3b_own1_bytes8 _ _ (by simp [hik_len]))
      (r3b_own1_u32x2 _ _ _ _ (by bv_omega))
      (r3b_own1_u8pad7 _ _ _ (by bv_omega))
  have h30 : (B0 ∗ B1 ∗ B2 ∗ B3 ∗ B4 ∗ B5 ∗ H) ⊢
      r3b_Own30 (a + 8#64) (B0 ∗ B1 ∗ B2 ∗ B3 ∗ B4 ∗ B5 ∗ H) :=
    r3b_own30_mk (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
      hB0 hB1 hB2 hB3 hB4 hB5
  refine Entails.trans hcap_extract ?_
  apply Entails.pure_left; intro hcap
  rw [hpkm_eq]
  refine Entails.trans (sepConj_mono_right h30) ?_
  dsimp only [r3b_Own30]
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w
  refine Entails.sepExists_right w (Entails.pure_right hcap ?_)
  refine sepConj_mono_right (sepConj_mono_right (Entails.wand_intro ?_))
  exact Entails.trans
    (Entails.of_eq (show
      ((r3b_slot30 (a + 8#64) w -∗ (B0 ∗ B1 ∗ B2 ∗ B3 ∗ B4 ∗ B5 ∗ H)) ∗
        ((a ↦₆₄ pmG.msg.pqCap) ∗ r3b_slot30 (a + 8#64) w)) =
      (a ↦₆₄ pmG.msg.pqCap) ∗
        (r3b_slot30 (a + 8#64) w ∗ (r3b_slot30 (a + 8#64) w -∗ (B0 ∗ B1 ∗ B2 ∗ B3 ∗ B4 ∗ B5 ∗ H)))
      by ac_rfl))
    (sepConj_mono_right (Entails.wand_elim _ _))

theorem r3b_addr_pack (A : RustAlloc) (g : AddrGhost)
    (a a1 a2 a3 : BitVec 64) (hi : BitVec 64)
    (e1 : a + 8#64 = a1) (e2 : a + 16#64 = a2) (e3 : a + 24#64 = a3)
    (hhi : hi.setWidth 8 = g.device) :
    ((a ↦₆₄ g.name.cap) ∗ (a1 ↦₆₄ g.name.ptr) ∗
      (a2 ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗ (a3 ↦₆₄ hi) ∗
      addrNameHeap A g) ⊢
    protocolAddressAt A g a := by
  subst e1; subst e2; subst e3
  rw [protocolAddressAt_eq_parts A g a]
  have hup := r3b_words_to_addrUpperAt (a + 16#64) g hi hhi
  have ha24 : a + 16#64 + 8#64 = a + 24#64 := by bv_omega
  rw [ha24] at hup
  exact r3b_perm
    (r3b_perm_post
      (sepConj_mono hup
        (Entails.refl ((a ↦₆₄ g.name.cap) ∗ ((a + 8#64) ↦₆₄ g.name.ptr) ∗ addrNameHeap A g)))
      (by ac_rfl))
    (by ac_rfl)

theorem r3b_addr_unpack (A : RustAlloc) (g : AddrGhost)
    (a a1 a2 a3 : BitVec 64)
    (e1 : a + 8#64 = a1) (e2 : a + 16#64 = a2) (e3 : a + 24#64 = a3) :
    protocolAddressAt A g a ⊢
      ∃∗ hi : BitVec 64,
        ⌜hi.setWidth 8 = g.device⌝ ∗
        (a ↦₆₄ g.name.cap) ∗ (a1 ↦₆₄ g.name.ptr) ∗
        (a2 ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗ (a3 ↦₆₄ hi) ∗
        addrNameHeap A g := by
  subst e1; subst e2; subst e3
  rw [protocolAddressAt_eq_parts A g a]
  have hup := r3b_addrUpperAt_words (a + 16#64) g
  have ha24 : a + 16#64 + 8#64 = a + 24#64 := by bv_omega
  rw [ha24] at hup
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hup))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro hi
  simp only [sepConj_assoc]
  apply r3b_pure2; intro hhi
  exact Entails.sepExists_right hi (Entails.pure_right hhi (Entails.of_eq (by ac_rfl)))

def r3b_shufMid (w m : r3b_W30) : r3b_W30 :=
  { b0 := ⟨w.b3.w0, w.b3.w1, w.b3.w2, w.b3.w3, w.b3.w4⟩
    b1 := ⟨w.b4.w0, w.b4.w1, w.b4.w2, w.b4.w3, w.b4.w4⟩
    b2 := ⟨w.b5.w0, w.b5.w1, w.b5.w2, w.b5.w3, w.b5.w4⟩
    b3 := ⟨m.b3.w0, w.b1.w2, w.b1.w3, w.b1.w4, w.b2.w0⟩
    b4 := ⟨w.b2.w1, w.b2.w2, w.b2.w3, w.b2.w4, w.b0.w1⟩
    b5 := ⟨w.b0.w2, w.b0.w3, w.b0.w4, w.b1.w0, w.b1.w1⟩ }

end CryptoVerification.SignalSession.Cli.RunCompose
