/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.JPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5MovesLayout
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Frame
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Shared Epilogues and Layout Helpers for Budget-Threaded Arm `J`

Payload layout lemmas and shared epilogue theorems (`j_epi_jp`, `j_tail_dealloc_jp`, `j_rejPost_jp`)
on Block `579` supporting `JProofPlacedBudget`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.JProofPlacedBudgetAux

open Arm64 Arm64.Process ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (NoFsEv TraceFsSound subroutine_ok_rocl_of_withLsCodeRoLoaded withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.RustHeap (LayoutOk RustAlloc vecHeader vecU8 vecU8At)
open CryptoVerification.SignalSession (Inputs lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (RunAnswer StoresGhost)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_550)
open CryptoVerification.SignalSession.Cli.Run.Placed (blkPl_579)
open CryptoVerification.SignalSession.Cli.MainHops
  (CallW LsCodeInv RunCall calleeSavedPreserved_of_regs cliWrOk inputOf
   mainSaved mainSaved_eq_sub main_call_rocl_steps ownedBytes runResAt runResSize sepWPp_seq_codeOk
   stackAt_split_ge storesAt)
open CryptoVerification.SignalSession.Cli.MainHops.M5MovesHelpers
  (StoresWords pointsToBytes_entails_memRegion storesBytes storesBytes_length)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtRejectPlaced InRunPlaced RejectKind RunHistOk RunLocalsFromWf
   rejectMem runFsp runLocalBytes runLocals
   runLocalsFrom runLocals_rejoin_empty runPcPlaced runPcPlaced_eq runProgPlaced
   runProgPlaced_eq runSaved stackAt_run_rejoin)
open CryptoVerification.SignalSession.Cli.RunProofs (DropStoresGhost)
open CryptoVerification.SignalSession.Cli.RunSkeleton (runFrame)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget RustLayoutOk
   rustDeallocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlacedBudget
  (AllocContractsFsPlaced.dealloc_rocl)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.JPlacedBudget
  (runJoinPostPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropStoresBudget
  (dropStoresSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropStoresPlacedBudget
  (dropStoresSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunHooksPlaced dropStores_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (rustDeallocExternSpecWithStack)

/-! ## Normalization and `SepWPp` Call Helpers -/

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  conditionHolds_mi_subsPState64 conditionHolds_pl_subsPState64
  conditionHolds_eq_subsPState64 conditionHolds_gt_subsPState64
  conditionHolds_eq_addsPState64 conditionHolds_ne_addsPState64

theorem j_msb_0_jp : (0#64).msb = false := rfl
theorem j_msb_8000_jp : (0x8000000000000000#64).msb = true := rfl
theorem j_msb_8002_jp : (0x8000000000000002#64).msb = true := rfl
theorem j_msb_8003_jp : (0x8000000000000003#64).msb = true := rfl
theorem j_slt_1_0_jp : (1#64).slt 0#64 = false := rfl
theorem j_slt_1_1_jp : (1#64).slt 1#64 = false := rfl
theorem j_slt_1_2_jp : (1#64).slt 2#64 = true := rfl
theorem j_slt_1_3_jp : (1#64).slt 3#64 = true := rfl
theorem j_sp_sub_96_add_96_jp (sp0 : BitVec 64) : (sp0 - 96#64) + 96#64 = sp0 := by bv_omega

attribute [local simp, local arm64_norm, local wp_norm]
  j_msb_0_jp j_msb_8000_jp j_msb_8002_jp j_msb_8003_jp
  j_slt_1_0_jp j_slt_1_1_jp j_slt_1_2_jp j_slt_1_3_jp j_sp_sub_96_add_96_jp

theorem j_sepWPp_weaken_pre_jp {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : P ⊢ P') (hwp : SepWPp prog ret s P' Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := fun R hm hL =>
  hwp R (Satisfies.mono (sepConj_mono_left h) hm) hL

theorem j_sepWPp_mono_post_jp {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Q' Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hQ : ∀ sf Pf, Q sf Pf → Q' sf Pf)
    (hwp : SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s P Q' Qp oom := fun R hm hL => by
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨hpc, hrun, Pf, hmf, hq⟩ | hpan_oom
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, hQ sf Pf hq⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan_oom⟩

theorem j_sepWPp_pure_left_jp {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : φ → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s (⌜φ⌝ ∗ P) Q Qp oom := fun R hm hL => by
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL

theorem j_sepWPp_exists_left_jp {α : Sort _} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x : α, SepWPp prog ret s (P x) Q Qp oom) :
    SepWPp prog ret s (∃∗ x, P x) Q Qp oom := fun R hm hL => by
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨x, hmx⟩ := hm
  exact h x R hmx hL

theorem j_pull_pure_jp {φ : Prop} {A B C : SepProp} :
    A ∗ (⌜φ⌝ ∗ B) ∗ C = ⌜φ⌝ ∗ (A ∗ B ∗ C) := by sep_ac_rfl

theorem j_pull_pure_r_jp {φ : Prop} {A B C : SepProp} :
    A ∗ (B ∗ ⌜φ⌝) ∗ C = ⌜φ⌝ ∗ (A ∗ B ∗ C) := by sep_ac_rfl

theorem runJoinPostPlaced_step_free [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {g : RunCall} {st : M.σ} {evs₁ : List AllocEvent}
    {resStack : Nat} {s0 sf : State} {Pf : SepProp}
    (hfo₁ : FreeOnlyEvs evs₁)
    (hp : runJoinPostPlaced CodeOk A lim g (M.stepEvents evs₁ st) resStack s0 sf Pf) :
    runJoinPostPlaced CodeOk A lim g st resStack s0 sf Pf := by
  rcases hp with ⟨hc, hsp, hcs, htr, hstP, evs₂, a', hfo₂, hne, heq, hent⟩
  rw [← M.stepEvents_append evs₁ evs₂ st] at hent
  exact ⟨hc, hsp, hcs, htr, hstP, evs₁ ++ evs₂, a', FreeOnlyEvs.append hfo₁ hfo₂, hne, heq, hent⟩

theorem j_call_rocl_jp [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {α : Type} {H : LibsignalHooks} {entry ret retAddr : BitVec 64}
    {spec : Spec α} {x : α} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcall : subroutine_ok (runProgPlaced H) entry (withLsRoCl lsmpl spec))
    (hinv : CodeOk s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 .lr = retAddr)
    (hpre : P ⊢ spec.pre x s ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F) := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hoom : ∀ sf R, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R)) → (sf.mem ⊨ oom sf ∗ R) := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sm : State, Steps (runProgPlaced H) s sm → CodeOk sm.mem →
      sm.pc = retAddr → sm.status = .Running → sm.sp = s.sp → CalleeSavedPreserved s sm →
      SepWPp (runProgPlaced H) ret sm (spec.post x s sm ∗ F) Q Qp oom) :
    SepWPp (runProgPlaced H) ret s P Q Qp oom :=
  main_call_rocl_steps x hcall hinv hpc hrun hsp hlr hpre hpanic hexit hoom hnext

theorem j_call_lscro_jp [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {α : Type} {H : LibsignalHooks} {entry ret retAddr : BitVec 64}
    {spec : Spec α} {x : α} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcall : subroutine_ok (runProgPlaced H) entry
      (withLsCodeRoLoaded lsmpl spec))
    (hinv : CodeOk s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 .lr = retAddr)
    (hpre : P ⊢ spec.pre x s ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F) := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hoom : ∀ sf R, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R)) → (sf.mem ⊨ oom sf ∗ R) := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sm : State, Steps (runProgPlaced H) s sm → CodeOk sm.mem →
      sm.pc = retAddr → sm.status = .Running → sm.sp = s.sp → CalleeSavedPreserved s sm →
      SepWPp (runProgPlaced H) ret sm (spec.post x s sm ∗ F) Q Qp oom) :
    SepWPp (runProgPlaced H) ret s P Q Qp oom :=
  j_call_rocl_jp (subroutine_ok_rocl_of_withLsCodeRoLoaded hcall)
    hinv hpc hrun hsp hlr hpre hexit hpanic hoom hnext

abbrev j_stOf_jp {CodeOk : Memory → Prop} {s : State} (_ : CodeOk s.mem) : State := s

theorem j_inRun_step_jp [LibsignalPlacement] {CodeOk : Memory → Prop}
    {s0 s s' : State} {k k' : Nat} (h : InRunPlaced CodeOk s0 s k)
    (hpc : s'.pc = runPcPlaced k') (hrun : s'.status = .Running)
    (hsp : s'.sp = s.sp) (hfp : s'.readReg64 .fp = s.readReg64 .fp)
    (hinv : CodeOk s'.mem) (hv : calleeSavedVRegs s' = calleeSavedVRegs s) :
    InRunPlaced CodeOk s0 s' k' :=
  ⟨hpc, hrun, hsp.trans h.sp, hfp.trans h.fp, hinv, hv.trans h.vregs, h.spAligned⟩

theorem j_hist_of_eq_jp {i : Inputs} {s0 s s' : State}
    (htr : s'.trace = s.trace) (hfs : s'.fs.files = s.fs.files)
    (h : RunHistOk i s0 s) : RunHistOk i s0 s' :=
  ⟨hfs.trans h.1, by rw [htr]; exact h.2⟩

theorem j_files_of_trace_eq_jp {P : Program} (hP : TraceFsSound P) {s sm : State}
    (hsteps : Steps P s sm) (htr : sm.trace = s.trace) : sm.fs.files = s.fs.files :=
  hP.files_eq hsteps (by rw [htr]; simp) NoFsEv.nil

theorem j_ownedBytes_zero_jp (A : RustAlloc) {cap ptr len : BitVec 64}
    (bs : List (BitVec 8)) (hcap : cap = 0) :
    ownedBytes A cap ptr len bs ⊢ emp := by
  unfold ownedBytes
  simp only [hcap, ↓reduceIte]
  exact Entails.pure_left fun _ => Entails.refl emp

theorem j_ownedBytes_dealloc_jp (A : RustAlloc) {cap ptr len : BitVec 64}
    (bs : List (BitVec 8)) (hcap : cap ≠ 0) :
    ownedBytes A cap ptr len bs ⊢
      ⌜RustLayoutOk cap.toNat 1⌝ ∗ (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  unfold ownedBytes
  simp only [hcap, ↓reduceIte]
  apply Entails.pure_left
  rintro ⟨_, hle, hlt, _⟩
  have hpos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero fun h0 => hcap (BitVec.eq_of_toNat_eq h0)
  have hlay : LayoutOk cap.toNat 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
  refine Entails.pure_right ⟨hlay, by decide⟩ ?_
  refine sepConj_mono_right ?_
  have hmerge :
      memRegion ptr bs.length ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) =
      memRegion ptr cap.toNat := by
    have hsum : bs.length + (cap.toNat - bs.length) = cap.toNat := Nat.add_sub_of_le hle
    simpa only [hsum] using
      (ProofLib.memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)).symm
  rw [← hmerge]
  exact sepConj_mono_left (ProofLib.pointsToBytes_entails_memRegion ptr bs)

theorem j_call7_to_memRegion56_jp (a : BitVec 64) (w : CallW) :
    (a ↦₆₄ w.w0) ∗ ((a + 8#64) ↦₆₄ w.w1) ∗ ((a + 16#64) ↦₆₄ w.w2) ∗
      ((a + 24#64) ↦₆₄ w.w3) ∗ ((a + 32#64) ↦₆₄ w.w4) ∗
      ((a + 40#64) ↦₆₄ w.w5) ∗ ((a + 48#64) ↦₆₄ w.w6) ⊢
    memRegion a 56 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 48)
        (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 40)
        (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 32)
        (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 24)
        (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 16)
        (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 40#64) (n := 8) (k := 8)
        (b' := a + 48#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (pointsTo64_entails_memRegion _ _))))))

theorem j_fold_call_mem_assoc_jp (a : BitVec 64) (w : CallW) (Rest : SepProp) :
    (a ↦₆₄ w.w0) ∗ ((a + 8#64) ↦₆₄ w.w1) ∗ ((a + 16#64) ↦₆₄ w.w2) ∗
      ((a + 24#64) ↦₆₄ w.w3) ∗ ((a + 32#64) ↦₆₄ w.w4) ∗
      ((a + 40#64) ↦₆₄ w.w5) ∗ ((a + 48#64) ↦₆₄ w.w6) ∗ Rest ⊢
    memRegion a 56 ∗ Rest := by
  simpa only [sepConj_assoc] using
    (sepConj_mono_left (j_call7_to_memRegion56_jp a w) : _ ∗ Rest ⊢ memRegion a 56 ∗ Rest)

theorem j_cs_trans_jp {s0 s1 s2 : State}
    (h01 : CalleeSavedPreserved s0 s1) (h12 : CalleeSavedPreserved s1 s2) :
    CalleeSavedPreserved s0 s2 := by
  rcases h01 with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hfp, hv⟩
  rcases h12 with ⟨k19, k20, k21, k22, k23, k24, k25, k26, k27, k28, kfp, kv⟩
  exact ⟨k19.trans h19, k20.trans h20, k21.trans h21, k22.trans h22, k23.trans h23,
    k24.trans h24, k25.trans h25, k26.trans h26, k27.trans h27, k28.trans h28,
    kfp.trans hfp, kv.trans hv⟩

/-! ## Join Payload Layout Helpers -/

def j_joinPayloadBytes_jp (ws : StoresWords) (outCap outPtr outLen : BitVec 64) :
    List (BitVec 8) :=
  storesBytes ws ++ (unpack64 outCap ++ (unpack64 outPtr ++ unpack64 outLen))

theorem j_joinPayloadBytes_length_jp (ws : StoresWords)
    (outCap outPtr outLen : BitVec 64) :
    (j_joinPayloadBytes_jp ws outCap outPtr outLen).length = runResSize := by
  simp [j_joinPayloadBytes_jp, storesBytes_length, runResSize]

theorem j_payload_eq_parts_jp (b : BitVec 64) (ws : StoresWords)
    (outCap outPtr outLen : BitVec 64) :
    (b ↦ₛ j_joinPayloadBytes_jp ws outCap outPtr outLen) =
      ((b ↦ₛ storesBytes ws) ∗
        ((b + 0x140#64) ↦₆₄ outCap) ∗
        ((b + 0x148#64) ↦₆₄ outPtr) ∗
        ((b + 0x150#64) ↦₆₄ outLen)) := by
  unfold j_joinPayloadBytes_jp
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  simp only [storesBytes_length, unpack64_length]
  rw [← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem j_vecU8_repack_jp (A : RustAlloc) (v : BitVec 64) (outCap outPtr : BitVec 64)
    (out : List (BitVec 8)) :
    (v ↦₆₄ outCap) ∗ ((v + 0x08#64) ↦₆₄ outPtr) ∗
      ((v + 0x10#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
      ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ⊢
    vecU8 A v out := by
  unfold vecU8
  refine Entails.sepExists_right outCap (Entails.sepExists_right outPtr ?_)
  unfold vecU8At vecHeader ownedBytes
  have hpure :
      ⌜BitVec.ofNat 64 out.length = BitVec.ofNat 64 out.length ∧
        out.length ≤ outCap.toNat ∧ outCap.toNat < 2 ^ 63 ∧ outPtr ≠ 0⌝ =
      (⌜out.length ≤ outCap.toNat ∧ outCap.toNat < 2 ^ 63 ∧ outPtr ≠ 0⌝ : SepProp) := by
    simp
  rw [hpure]
  exact Entails.of_eq (by sep_ac_rfl)

theorem j_join_carve_locals_jp (fsp : BitVec 64) :
    memRegion (fsp + 0x220#64) (runLocalBytes - 0x220) ⊢
      ∃∗ u610 : BitVec 64, ∃∗ u618 : BitVec 64, ∃∗ u620 : BitVec 64,
        memRegion (fsp + 0x220#64) 0x2b0 ∗
          memRegion (fsp + 0x4d0#64) 0x140 ∗
          ((fsp + 0x610#64) ↦₆₄ u610) ∗
          ((fsp + 0x618#64) ↦₆₄ u618) ∗
          ((fsp + 0x620#64) ↦₆₄ u620) ∗
          memRegion (fsp + 0x628#64) (runLocalBytes - 0x628) := by
  have s1 := ProofLib.memRegion_split' (b := fsp + 0x220#64) (n := 0x2b0)
    (k := runLocalBytes - 0x4d0) (b' := fsp + 0x4d0#64) rfl (by bv_omega) (by decide)
  have s2 := ProofLib.memRegion_split' (b := fsp + 0x4d0#64) (n := 0x140)
    (k := runLocalBytes - 0x610) (b' := fsp + 0x610#64) rfl (by bv_omega) (by decide)
  have s3 := ProofLib.memRegion_split' (b := fsp + 0x610#64) (n := 8)
    (k := runLocalBytes - 0x618) (b' := fsp + 0x618#64) rfl (by bv_omega) (by decide)
  have s4 := ProofLib.memRegion_split' (b := fsp + 0x618#64) (n := 8)
    (k := runLocalBytes - 0x620) (b' := fsp + 0x620#64) rfl (by bv_omega) (by decide)
  have s5 := ProofLib.memRegion_split' (b := fsp + 0x620#64) (n := 8)
    (k := runLocalBytes - 0x628) (b' := fsp + 0x628#64) rfl (by bv_omega) (by decide)
  rw [show runLocalBytes - 0x220 = 0x2b0 + (runLocalBytes - 0x4d0) from rfl, s1,
      show runLocalBytes - 0x4d0 = 0x140 + (runLocalBytes - 0x610) from rfl, s2,
      show runLocalBytes - 0x610 = 8 + (runLocalBytes - 0x618) from rfl, s3,
      show runLocalBytes - 0x618 = 8 + (runLocalBytes - 0x620) from rfl, s4,
      show runLocalBytes - 0x620 = 8 + (runLocalBytes - 0x628) from rfl, s5,
      ProofLib.memRegion_eight (fsp + 0x610#64),
      ProofLib.memRegion_eight (fsp + 0x618#64),
      ProofLib.memRegion_eight (fsp + 0x620#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro u620
  apply Entails.sepExists_elim; intro u618
  apply Entails.sepExists_elim; intro u610
  exact Entails.sepExists_right u610 (Entails.sepExists_right u618
    (Entails.sepExists_right u620 (Entails.of_eq (by sep_ac_rfl))))

theorem j_join_rejoin_locals_jp (fsp : BitVec 64) (outCap outPtr outLen : BitVec 64)
    (ws : StoresWords) :
    memRegion fsp 0x208 ∗
      ((fsp + 0x208#64) ↦₆₄ outCap) ∗ ((fsp + 0x210#64) ↦₆₄ outPtr) ∗
      ((fsp + 0x218#64) ↦₆₄ outLen) ∗
      memRegion (fsp + 0x220#64) 0x2b0 ∗
      ((fsp + 0x4d0#64) ↦ₛ j_joinPayloadBytes_jp ws outCap outPtr outLen) ∗
      memRegion (fsp + 0x628#64) (runLocalBytes - 0x628) ⊢
    runLocals fsp [] := by
  have h24 :
      ((fsp + 0x208#64) ↦₆₄ outCap) ∗ ((fsp + 0x210#64) ↦₆₄ outPtr) ∗
        ((fsp + 0x218#64) ↦₆₄ outLen) ⊢
      memRegion (fsp + 0x208#64) 24 := by
    rw [ProofLib.memRegion_split' (b := fsp + 0x208#64) (n := 8) (k := 16)
          (b' := fsp + 0x210#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x210#64) (n := 8) (k := 8)
          (b' := fsp + 0x218#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (pointsTo64_entails_memRegion _ _))
  have h344 :
      ((fsp + 0x4d0#64) ↦ₛ j_joinPayloadBytes_jp ws outCap outPtr outLen) ⊢
        memRegion (fsp + 0x4d0#64) 0x158 := by
    have h := pointsToBytes_entails_memRegion
      (j_joinPayloadBytes_jp ws outCap outPtr outLen) (fsp + 0x4d0#64)
      (by simp [j_joinPayloadBytes_length_jp, runResSize])
    rwa [j_joinPayloadBytes_length_jp] at h
  have hwf : RunLocalsFromWf 0
      [(0x208, 24, memRegion (fsp + 0x208#64) 24),
       (0x4d0, 0x158, memRegion (fsp + 0x4d0#64) 0x158)] := by
    dsimp only [RunLocalsFromWf, runLocalBytes]; omega
  have hrej := runLocals_rejoin_empty fsp
    [(0x208, 24, memRegion (fsp + 0x208#64) 24),
     (0x4d0, 0x158, memRegion (fsp + 0x4d0#64) 0x158)]
    hwf (by intro c hc; simp at hc; rcases hc with rfl | rfl <;> exact Entails.refl _)
  dsimp only [runLocals, runLocalsFrom, Nat.sub_zero] at hrej ⊢
  have hz : fsp + BitVec.ofNat 64 0 = fsp := by bv_omega
  rw [hz] at hrej ⊢
  rw [show BitVec.ofNat 64 (0x208 + 24) = 0x220#64 from rfl,
      show (0x4d0 - (0x208 + 24) : Nat) = 0x2b0 from rfl,
      show BitVec.ofNat 64 (0x4d0 + 0x158) = 0x628#64 from rfl] at hrej
  refine Entails.trans (Entails.of_eq (show _ =
    memRegion fsp 0x208 ∗
      (((fsp + 0x208#64) ↦₆₄ outCap) ∗ ((fsp + 0x210#64) ↦₆₄ outPtr) ∗
        ((fsp + 0x218#64) ↦₆₄ outLen)) ∗
      (memRegion (fsp + 0x220#64) 0x2b0 ∗
        ((fsp + 0x4d0#64) ↦ₛ j_joinPayloadBytes_jp ws outCap outPtr outLen) ∗
        memRegion (fsp + 0x628#64) (runLocalBytes - 0x628)) by sep_ac_rfl)) ?_
  exact Entails.trans
    (sepConj_mono_right (sepConj_mono h24 (sepConj_mono_right (sepConj_mono_left h344)))) hrej

/-! ## Shared Return Epilogue (`R+0x2c84 → lr`) -/

theorem j_epi_jp [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {g : RunCall} {a' : RunAnswer} {s0 s : State}
    {resStack : Nat} {Qp : State → SepProp → Prop}
    (hrf : runFrame ≤ resStack) (h64 : resStack ≤ 2 ^ 64) (hs : InRunPlaced CodeOk s0 s 0x2c84)
    (htr : s0.trace <+: s.trace) (hhist : RunHistOk g.i s0 s) (ha_ne : a' ≠ none) (hans : a' = g.a) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (runResAt A.repAlloc cliWrOk g.res a' ∗ memRegion g.call 56 ∗ memRegion g.stores 320 ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ runLocals (runFsp s0) [] ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap)
      (runJoinPostPlaced CodeOk A lim g st resStack s0) Qp (fun _ => ⌜False⌝) := by
  have hpc : s.pc = runPcPlaced 0x2c84 := hs.pc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = s0.sp - 0x2a50#64 := hs.sp
  have hsp0 : s0.spAligned = true := hs.spAligned
  have hsp60_al : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 96#64 hsp0
  have hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := hs.vregs
  apply sepWPp_seq_codeOk (mid := s0.readReg64 .lr) hs.inv
  rw [show runSaved s0 = mainSaved s0 from rfl, mainSaved_eq_sub s0, runProgPlaced_eq]
  simp only [sepConj_assoc]
  simp only [runPcPlaced_eq] at hpc
  generalize hsp0_eq : s0.sp = sp0 at hsp hsp60_al ⊢
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
  intro hinv_f; subst hsp0_eq
  have hpool_eq : A.pool lim st s = A.pool lim (M.stepEvents [] st) (j_stOf_jp hinv_f) := by
    dsimp only [AllocCostModel.stepEvents, List.foldl, j_stOf_jp]
    simp only [wp_norm, arm64_norm]
  refine fun R hm _ => ⟨_, Steps.refl _, Or.inl ⟨by simp only [arm64_norm, *],
    by simp only [arm64_norm, hrun], _, hm, ?_⟩⟩
  refine ⟨hinv_f, by simp only [arm64_norm], ?_, by simpa only [arm64_norm] using htr,
    j_hist_of_eq_jp (s := s) (s' := j_stOf_jp hinv_f)
      (by simp only [j_stOf_jp, arm64_norm])
      (by simp only [j_stOf_jp, arm64_norm]) hhist, [], a', FreeOnlyEvs.nil, ha_ne, hans, ?_⟩
  · exact calleeSavedPreserved_of_regs
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (Eq.trans (by simp only [calleeSavedVRegs, arm64_norm]) hvregs)
  · have hrej := stackAt_run_rejoin s0 hrf h64
    change mainSaved s0 ∗ runLocals (runFsp s0) [] ∗
      stackAt (runFsp s0) (resStack - runFrame) ⊢ stackAt s0.sp resStack at hrej
    rw [hpool_eq]
    refine Entails.trans (Entails.of_eq (show _ =
      (mainSaved s0 ∗ runLocals (runFsp s0) [] ∗ stackAt (runFsp s0) (resStack - runFrame)) ∗
      (memRegion g.call 56 ∗ memRegion g.stores 320 ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        A.pool lim (M.stepEvents [] st) (j_stOf_jp hinv_f) ∗
        runResAt A.repAlloc cliWrOk g.res a' ∗ anyHeap) by
        rw [mainSaved_eq_sub s0]; sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hrej) (Entails.of_eq (by sep_ac_rfl))

/-! ## Shared Tail-Call Deallocation Epilogue (`R+0x180 → lr`) -/

theorem j_tail_dealloc_jp [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {g : RunCall} {ptr cap : BitVec 64} {s0 s : State}
    {resStack : Nat} {Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H) (hrf : runFrame ≤ resStack) (hext : extHookStack ≤ resStack)
    (h64 : resStack ≤ 2 ^ 64) (hs : InRunPlaced CodeOk s0 s 0x180)
    (hx0 : s.readReg64 .x0 = ptr) (hx1 : s.readReg64 .x1 = cap) (hlay : RustLayoutOk cap.toNat 1)
    (htr : s0.trace <+: s.trace) (hhist : RunHistOk g.i s0 s) (hans : g.a = some none)
    (hlr : LsRetAddr624 (s0.readReg64 .lr)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗
        runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        memRegion g.stores 320 ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
        runLocals (runFsp s0) [] ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        A.pool lim st s ∗ anyHeap)
      (runJoinPostPlaced CodeOk A lim g st resStack s0) Qp (fun _ => ⌜False⌝) := by
  have hpc : s.pc = runPcPlaced 0x180 := hs.pc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = s0.sp - 0x2a50#64 := hs.sp
  have hsp0 : s0.spAligned = true := hs.spAligned
  have hsp60_al : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 96#64 hsp0
  have hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := hs.vregs
  apply sepWPp_seq_codeOk (mid := lsρ lsRustDeallocSymCli) hs.inv
  rw [show runSaved s0 = mainSaved s0 from rfl, mainSaved_eq_sub s0, runProgPlaced_eq]
  simp only [sepConj_assoc]
  change s.pc = (blkPl_579).base + 384#64 at hpc
  generalize hsp0_eq : s0.sp = sp0 at hsp hsp0 hsp60_al ⊢
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
  intro hinv_c; subst hsp0_eq
  have hpool_c : A.pool lim st s = A.pool lim st (j_stOf_jp hinv_c) := by
    simp only [j_stOf_jp, wp_norm, arm64_norm]
  have hcs_pre : CalleeSavedPreserved s0 (j_stOf_jp hinv_c) :=
    calleeSavedPreserved_of_regs
      (by simp only [j_stOf_jp, arm64_norm]) (by simp only [j_stOf_jp, arm64_norm])
      (by simp only [j_stOf_jp, arm64_norm]) (by simp only [j_stOf_jp, arm64_norm])
      (by simp only [j_stOf_jp, arm64_norm]) (by simp only [j_stOf_jp, arm64_norm])
      (by simp only [j_stOf_jp, arm64_norm]) (by simp only [j_stOf_jp, arm64_norm])
      (by simp only [j_stOf_jp, arm64_norm]) (by simp only [j_stOf_jp, arm64_norm])
      (by simp only [j_stOf_jp, arm64_norm])
      (Eq.trans (by simp only [j_stOf_jp, calleeSavedVRegs, arm64_norm]) hvregs)
  have hrej := stackAt_run_rejoin s0 hrf h64
  change mainSaved s0 ∗ runLocals (runFsp s0) [] ∗
    stackAt (runFsp s0) (resStack - runFrame) ⊢ stackAt s0.sp resStack at hrej
  have hstk_split := stackAt_split_ge s0.sp hext h64
  refine j_call_rocl_jp
    (F := runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
      memRegion g.stores 320 ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - extHookStack) ∗
      anyHeap)
    (x := (ptr, cap.toNat, 1, st))
    (AllocContractsFsPlaced.dealloc_rocl (prog := runProgPlaced H) (i := 579) hh.allocFs) hinv_c
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    (by simpa only [State.spAligned, arm64_norm] using hsp0)
    (retAddr := s0.readReg64 .lr) (by simp only [arm64_norm]) ?_
    (hnext := fun sm _ hinv_m hpcm hrunm hspm hcsm => ?_)
  · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    simp only [sepConj_assoc]
    apply Entails.pure_right ⟨by simp only [arm64_norm, hx0], by simp only [arm64_norm, hx1],
      by simp only [arm64_norm], hlay, by simpa only [j_stOf_jp, arm64_norm] using hlr⟩
    have hsp_eq : (j_stOf_jp hinv_c).sp = s0.sp := by simp only [j_stOf_jp, arm64_norm]
    rw [hsp_eq, hpool_c]
    refine Entails.trans (Entails.of_eq (show _ =
      (mainSaved s0 ∗ runLocals (runFsp s0) [] ∗ stackAt (runFsp s0) (resStack - runFrame)) ∗
      (A.pool lim st (j_stOf_jp hinv_c) ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗
        runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        memRegion g.stores 320 ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ anyHeap) by
        rw [mainSaved_eq_sub s0]; sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left hrej) ?_
    rw [hstk_split]; exact Entails.of_eq (by sep_ac_rfl)
  · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    simp only [sepConj_assoc]
    apply j_sepWPp_pure_left_jp; intro hfs_m; apply j_sepWPp_pure_left_jp; intro htr_m
    have hsp_m : sm.sp = s0.sp := hspm.trans (by simp only [j_stOf_jp, arm64_norm])
    have htr_tot : sm.trace = s.trace := htr_m.trans (by simp only [j_stOf_jp, arm64_norm])
    have hfs_tot : sm.fs = s.fs := hfs_m.trans (by simp only [j_stOf_jp, arm64_norm])
    refine fun R hm _ => ⟨sm, Steps.refl sm, Or.inl ⟨hpcm, hrunm, _, hm, ?_⟩⟩
    refine ⟨hinv_m, hsp_m, j_cs_trans_jp hcs_pre hcsm, htr_tot ▸ htr,
      j_hist_of_eq_jp htr_tot (congrArg FsState.files hfs_tot) hhist,
      rustDeallocEvents cap.toNat 1, some none,
      FreeOnlyEvs.singleton 1 cap.toNat, by decide, hans.symm, ?_⟩
    have hsp_pre : (j_stOf_jp hinv_c).sp = s0.sp := by simp only [j_stOf_jp, arm64_norm]
    rw [hsp_pre, hstk_split]; exact Entails.of_eq (by sep_ac_rfl)

/-! ## Post-Dispatch Reject (`R+0x2c7c`) -/

theorem j_rejPost_jp [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost} {s0 s : State}
    {resStack : Nat} {Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H) (hrf : runFrame ≤ resStack)
    (h96 : 96 + extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (h64 : resStack ≤ 2 ^ 64) (hr : AtRejectPlaced CodeOk g g' .postDispatch s0 s) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (rejectMem (A.atState lim st s) g g' .postDispatch s0 resStack)
      (runJoinPostPlaced CodeOk A lim g st resStack s0) Qp (fun _ => ⌜False⌝) := by
  have hs := hr.base; dsimp only [RejectKind.pcOff] at hs
  have hpc : s.pc = runPcPlaced 0x2c7c := hs.pc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = runFsp s0 := hs.sp
  have hsp_al : s.spAligned = true := hs.spAligned_cur
  have hx19 : s.readReg64 (.gpr 19#5) = g.stores := hr.x19
  have hrej_eq :
      rejectMem (A.atState lim st s) g g' .postDispatch s0 resStack =
      (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56) ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        runSaved s0 ∗ runLocals (runFsp s0) [] ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap := rfl
  rw [hrej_eq]
  apply sepWPp_seq_codeOk (mid := (blkPl_550).base) hs.inv
  rw [runProgPlaced_eq]; simp only [runPcPlaced_eq] at hpc
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, hrun])
  intro hinv_c
  have hpool_c : A.pool lim st s = A.pool lim st (j_stOf_jp hinv_c) := by
    simp only [j_stOf_jp, wp_norm, arm64_norm]
  refine j_call_lscro_jp
    (F := runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
      (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ runLocals (runFsp s0) [] ∗ anyHeap)
    (x := (⟨g.stores, g'⟩, st))
    (dropStores_placed_ok (callerProg := runProgPlaced H) (i := 579)
      hh (resStack - runFrame) h96 hsub64) hinv_c
    (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, hrun])
    (by simpa only [State.spAligned, arm64_norm] using hsp_al)
    (retAddr := runPcPlaced 0x2c84) (by simp only [arm64_norm, runPcPlaced_eq]) ?_
    (hnext := fun sm hsteps_ds hinv_m hpcm hrunm hspm hcsm => ?_)
  · dsimp only [dropStoresSpec]; simp only [sepConj_assoc]
    apply Entails.pure_right ⟨by simp only [arm64_norm],
      by simp only [j_stOf_jp, arm64_norm, runPcPlaced_eq]; exact LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_blockPlacement_base_add 579 0x2c84#64 (by decide) (by decide)⟩
    have hsp_c : (j_stOf_jp hinv_c).sp = runFsp s0 := by simp only [j_stOf_jp, arm64_norm, hsp]
    rw [hsp_c, hpool_c]; exact Entails.of_eq (by sep_ac_rfl)
  · dsimp only [dropStoresSpec]
    rw [sepExists_sepConj_left]
    apply j_sepWPp_exists_left_jp; intro evs
    simp only [sepConj_assoc]
    apply j_sepWPp_pure_left_jp; rintro ⟨htr_m, hfo_evs⟩
    have hsp_c : (j_stOf_jp hinv_c).sp = runFsp s0 := by simp only [j_stOf_jp, arm64_norm, hsp]
    rw [hsp_c]
    have hs_m : InRunPlaced CodeOk s0 sm 0x2c84 :=
      j_inRun_step_jp hs hpcm hrunm (hspm.trans (by simp only [j_stOf_jp, arm64_norm]))
        (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [j_stOf_jp, arm64_norm])) hinv_m
        (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [j_stOf_jp, calleeSavedVRegs, arm64_norm]))
    have hfiles_m : sm.fs.files = s.fs.files :=
      (j_files_of_trace_eq_jp (hh.fs (runProgPlaced H) 579) hsteps_ds htr_m).trans
        (by simp only [j_stOf_jp, arm64_norm])
    have htr_tot : sm.trace = s.trace := htr_m.trans (by simp only [j_stOf_jp, arm64_norm])
    exact j_sepWPp_mono_post_jp (fun _ _ => runJoinPostPlaced_step_free hfo_evs)
      (j_sepWPp_weaken_pre_jp (Entails.of_eq (by sep_ac_rfl))
        (j_epi_jp hrf h64 hs_m (htr_tot ▸ hr.trace)
          (j_hist_of_eq_jp htr_tot hfiles_m hr.hist) (by decide) hr.ans.symm))

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.JProofPlacedBudgetAux
