/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.JPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5MovesLayout
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Frame
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

/-!
# Relocatable Arm `J` Proof for `signal_session::run`

Proves `run_hop_join_placed_ok : RunHopJoinPlaced CodeOk A H B S needs resStack` on Block `579`
under `[LibsignalPlacement]` and `[LsCodeInv CodeOk]`.
-/

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi Arm64.Process
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.MainHops.M5MovesHelpers
open CryptoVerification.SignalSession.Cli.RunSkeleton CryptoVerification.SignalSession.Cli.RunProofs

/-! ## Internal Helpers -/

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  conditionHolds_mi_subsPState64 conditionHolds_pl_subsPState64
  conditionHolds_eq_subsPState64 conditionHolds_gt_subsPState64
  conditionHolds_eq_addsPState64 conditionHolds_ne_addsPState64

private theorem j_msb_0_jp : (0#64).msb = false := rfl
private theorem j_msb_8000_jp : (0x8000000000000000#64).msb = true := rfl
private theorem j_msb_8002_jp : (0x8000000000000002#64).msb = true := rfl
private theorem j_msb_8003_jp : (0x8000000000000003#64).msb = true := rfl
private theorem j_slt_1_0_jp : (1#64).slt 0#64 = false := rfl
private theorem j_slt_1_1_jp : (1#64).slt 1#64 = false := rfl
private theorem j_slt_1_2_jp : (1#64).slt 2#64 = true := rfl
private theorem j_slt_1_3_jp : (1#64).slt 3#64 = true := rfl
private theorem j_sp_sub_96_add_96_jp (sp0 : BitVec 64) : (sp0 - 96#64) + 96#64 = sp0 := by bv_omega

attribute [local simp, local arm64_norm, local wp_norm]
  j_msb_0_jp j_msb_8000_jp j_msb_8002_jp j_msb_8003_jp
  j_slt_1_0_jp j_slt_1_1_jp j_slt_1_2_jp j_slt_1_3_jp j_sp_sub_96_add_96_jp

private theorem j_sepWPp_weaken_pre_jp {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : P ⊢ P') (hwp : SepWPp prog ret s P' Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := fun R hm hL =>
  hwp R (Satisfies.mono (sepConj_mono_left h) hm) hL

private theorem j_sepWPp_pure_left_jp {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : φ → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s (⌜φ⌝ ∗ P) Q Qp oom := fun R hm hL => by
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL

private theorem j_sepWPp_exists_left_jp {α : Sort _} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x : α, SepWPp prog ret s (P x) Q Qp oom) :
    SepWPp prog ret s (∃∗ x, P x) Q Qp oom := fun R hm hL => by
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨x, hmx⟩ := hm
  exact h x R hmx hL

private theorem j_pull_pure_jp {φ : Prop} {A B C : SepProp} :
    A ∗ (⌜φ⌝ ∗ B) ∗ C = ⌜φ⌝ ∗ (A ∗ B ∗ C) := by ac_rfl

private theorem j_pull_pure_r_jp {φ : Prop} {A B C : SepProp} :
    A ∗ (B ∗ ⌜φ⌝) ∗ C = ⌜φ⌝ ∗ (A ∗ B ∗ C) := by ac_rfl

private theorem j_call_rocl_jp [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {α : Type} {H : LibsignalHooks} {entry ret retAddr : BitVec 64}
    {spec : Spec α} {x : α} {s0 s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop}
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
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R)) → (sf.mem ⊨ runOom s0 sf ∗ R) := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sm : State, Steps (runProgPlaced H) s sm → CodeOk sm.mem →
      sm.pc = retAddr → sm.status = .Running → sm.sp = s.sp → CalleeSavedPreserved s sm →
      SepWPp (runProgPlaced H) ret sm (spec.post x s sm ∗ F) Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) ret s P Q Qp (runOom s0) := by
  intro R hm hL
  have hm_pre : s.mem ⊨ (spec.pre x s ∗ F) ∗ R :=
    Satisfies.mono (sepConj_mono_left hpre) hm
  have hm_rocl : s.mem ⊨ (withLsRoCl lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withLsRoCl]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨LsCodeInv.toRoCl hinv, by simpa only [sepConj_assoc] using hm_pre⟩
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm_rocl hsp hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ |
        ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · dsimp only [withLsRoCl] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hinv_m : CodeOk sm.mem := LsCodeInv.of_keepsFrozen hinv hsteps.keepsFrozen
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hinv_m hpcm hrunm hspm hcsm R hpost.2 (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsRoCl] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, spec.onPanic x s sm ∗ F,
      by simpa only [sepConj_assoc] using hpost,
      hpanic sm (F ∗ R) hpan hpost⟩)⟩
  · exact (hexit sm code (F ∗ R) hex hpost).elim
  · dsimp only [withLsRoCl] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_s, hoom sm R hoom_s hpost⟩)⟩

private theorem j_call_lscro_jp [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {α : Type} {H : LibsignalHooks} {entry ret retAddr : BitVec 64}
    {spec : Spec α} {x : α} {s0 s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok (runProgPlaced H) entry
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec))
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
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R)) → (sf.mem ⊨ runOom s0 sf ∗ R) := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sm : State, Steps (runProgPlaced H) s sm → CodeOk sm.mem →
      sm.pc = retAddr → sm.status = .Running → sm.sp = s.sp → CalleeSavedPreserved s sm →
      SepWPp (runProgPlaced H) ret sm (spec.post x s sm ∗ F) Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) ret s P Q Qp (runOom s0) :=
  j_call_rocl_jp (LibsignalPublicApi.StoreKit.subroutine_ok_rocl_of_withLsCodeRoLoaded hcall)
    hinv hpc hrun hsp hlr hpre hexit hpanic hoom hnext

private abbrev j_stOf_jp {CodeOk : Memory → Prop} {s : State} (_ : CodeOk s.mem) : State := s

private theorem j_inRun_step_jp [LibsignalPlacement] {CodeOk : Memory → Prop}
    {s0 s s' : State} {k k' : Nat} (h : InRunPlaced CodeOk s0 s k)
    (hpc : s'.pc = runPcPlaced k') (hrun : s'.status = .Running)
    (hsp : s'.sp = s.sp) (hfp : s'.readReg64 .fp = s.readReg64 .fp)
    (hinv : CodeOk s'.mem) (hv : calleeSavedVRegs s' = calleeSavedVRegs s) :
    InRunPlaced CodeOk s0 s' k' :=
  ⟨hpc, hrun, hsp.trans h.sp, hfp.trans h.fp, hinv, hv.trans h.vregs, h.spAligned⟩

private theorem j_hist_of_eq_jp {i : Inputs} {s0 s s' : State}
    (htr : s'.trace = s.trace) (hfs : s'.fs.files = s.fs.files)
    (h : RunHistOk i s0 s) : RunHistOk i s0 s' :=
  ⟨hfs.trans h.1, by rw [htr]; exact h.2⟩

private theorem j_files_of_trace_eq_jp {P : Program} (hP : TraceFsSound P) {s sm : State}
    (hsteps : Steps P s sm) (htr : sm.trace = s.trace) : sm.fs.files = s.fs.files :=
  hP.files_eq hsteps (by rw [htr]; simp) NoFsEv.nil

private theorem j_ownedBytes_zero_jp (A : RustAlloc) {cap ptr len : BitVec 64}
    (bs : List (BitVec 8)) (hcap : cap = 0) :
    ownedBytes A cap ptr len bs ⊢ emp := by
  unfold ownedBytes
  simp only [hcap, ↓reduceIte]
  exact Entails.pure_left fun _ => Entails.refl emp

private theorem j_ownedBytes_dealloc_jp (A : RustAlloc) {cap ptr len : BitVec 64}
    (bs : List (BitVec 8)) (hcap : cap ≠ 0) :
    ownedBytes A cap ptr len bs ⊢
      ⌜LayoutOk cap.toNat 1⌝ ∗ (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  unfold ownedBytes
  simp only [hcap, ↓reduceIte]
  apply Entails.pure_left
  rintro ⟨_, hle, hlt, _⟩
  have hpos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero fun h0 => hcap (BitVec.eq_of_toNat_eq h0)
  refine Entails.pure_right ⟨hpos, ⟨0, rfl⟩, by omega⟩ ?_
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

private theorem j_call7_to_memRegion56_jp (a : BitVec 64) (w : CallW) :
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
  exact sepConj_mono (RunCompose.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (RunCompose.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (RunCompose.pointsTo64_entails_memRegion _ _)
        (sepConj_mono (RunCompose.pointsTo64_entails_memRegion _ _)
          (sepConj_mono (RunCompose.pointsTo64_entails_memRegion _ _)
            (sepConj_mono (RunCompose.pointsTo64_entails_memRegion _ _)
              (RunCompose.pointsTo64_entails_memRegion _ _))))))

private theorem j_fold_call_mem_assoc_jp (a : BitVec 64) (w : CallW) (Rest : SepProp) :
    (a ↦₆₄ w.w0) ∗ ((a + 8#64) ↦₆₄ w.w1) ∗ ((a + 16#64) ↦₆₄ w.w2) ∗
      ((a + 24#64) ↦₆₄ w.w3) ∗ ((a + 32#64) ↦₆₄ w.w4) ∗
      ((a + 40#64) ↦₆₄ w.w5) ∗ ((a + 48#64) ↦₆₄ w.w6) ∗ Rest ⊢
    memRegion a 56 ∗ Rest := by
  simpa only [sepConj_assoc] using
    (sepConj_mono_left (j_call7_to_memRegion56_jp a w) : _ ∗ Rest ⊢ memRegion a 56 ∗ Rest)

private theorem j_cs_trans_jp {s0 s1 s2 : State}
    (h01 : CalleeSavedPreserved s0 s1) (h12 : CalleeSavedPreserved s1 s2) :
    CalleeSavedPreserved s0 s2 := by
  rcases h01 with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hfp, hv⟩
  rcases h12 with ⟨k19, k20, k21, k22, k23, k24, k25, k26, k27, k28, kfp, kv⟩
  exact ⟨k19.trans h19, k20.trans h20, k21.trans h21, k22.trans h22, k23.trans h23,
    k24.trans h24, k25.trans h25, k26.trans h26, k27.trans h27, k28.trans h28,
    kfp.trans hfp, kv.trans hv⟩

/-! ## Shared Return Epilogue (`R+0x2c84 → lr`) -/

private theorem j_epi_jp [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {g : RunCall} {a' : RunAnswer} {s0 s : State}
    {resStack : Nat} {Qp : State → SepProp → Prop}
    (hrf : runFrame ≤ resStack) (h64 : resStack ≤ 2 ^ 64) (hs : InRunPlaced CodeOk s0 s 0x2c84)
    (htr : s0.trace <+: s.trace) (hhist : RunHistOk g.i s0 s) (ha_ne : a' ≠ none) (hans : a' = g.a) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (runResAt A cliWrOk g.res a' ∗ memRegion g.call 56 ∗ memRegion g.stores 320 ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ runLocals (runFsp s0) [] ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      (runPostPlaced CodeOk A g resStack s0) Qp (runOom s0) := by
  have hpc : s.pc = runPcPlaced 0x2c84 := hs.pc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = s0.sp - 0x2a50#64 := hs.sp
  have hsp0 : s0.spAligned = true := hs.spAligned
  have hsp60_al : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true := ProofLib.spAligned_sub s0.sp 96#64 hsp0
  have hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := hs.vregs
  apply sepWPp_seq_codeOk (mid := s0.readReg64 .lr) hs.inv
  rw [show runSaved s0 = MainHops.mainSaved s0 from rfl, MainHops.mainSaved_eq_sub s0, runProgPlaced_eq]
  simp only [sepConj_assoc]
  simp only [runPcPlaced_eq] at hpc
  generalize hsp0_eq : s0.sp = sp0 at hsp hsp60_al ⊢
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
  intro hinv_f; subst hsp0_eq
  refine fun R hm _ => ⟨_, Steps.refl _, Or.inl ⟨by simp only [arm64_norm, *],
    by simp only [arm64_norm, hrun], _, hm, ?_⟩⟩
  refine ⟨hinv_f, by simp only [arm64_norm], ?_, by simpa only [arm64_norm] using htr,
    j_hist_of_eq_jp (s' := j_stOf_jp hinv_f) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hhist, a', ha_ne, hans, ?_⟩
  · exact MainHops.calleeSavedPreserved_of_regs
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (Eq.trans (by simp only [calleeSavedVRegs, arm64_norm]) hvregs)
  · have hrej := stackAt_run_rejoin s0 hrf h64
    change MainHops.mainSaved s0 ∗ runLocals (runFsp s0) [] ∗
      stackAt (runFsp s0) (resStack - runFrame) ⊢ stackAt s0.sp resStack at hrej
    refine Entails.trans (Entails.of_eq (show _ =
      (MainHops.mainSaved s0 ∗ runLocals (runFsp s0) [] ∗ stackAt (runFsp s0) (resStack - runFrame)) ∗
      (memRegion g.call 56 ∗ memRegion g.stores 320 ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        A.pool ∗ runResAt A cliWrOk g.res a' ∗ anyHeap) by
        rw [MainHops.mainSaved_eq_sub s0]; ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hrej) (Entails.of_eq (by ac_rfl))

/-! ## Shared Tail-Call Deallocation Epilogue (`R+0x180 → lr`) -/

private theorem j_tail_dealloc_jp [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {g : RunCall} {ptr cap : BitVec 64} {s0 s : State}
    {resStack : Nat} {Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hrf : runFrame ≤ resStack) (hext : extHookStack ≤ resStack)
    (h64 : resStack ≤ 2 ^ 64) (hs : InRunPlaced CodeOk s0 s 0x180)
    (hx0 : s.readReg64 .x0 = ptr) (hx1 : s.readReg64 .x1 = cap) (hlay : LayoutOk cap.toNat 1)
    (htr : s0.trace <+: s.trace) (hhist : RunHistOk g.i s0 s) (hans : g.a = some none) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗
        runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗ memRegion g.stores 320 ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ runLocals (runFsp s0) [] ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      (runPostPlaced CodeOk A g resStack s0) Qp (runOom s0) := by
  have hpc : s.pc = runPcPlaced 0x180 := hs.pc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = s0.sp - 0x2a50#64 := hs.sp
  have hsp0 : s0.spAligned = true := hs.spAligned
  have hsp60_al : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true := ProofLib.spAligned_sub s0.sp 96#64 hsp0
  have hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := hs.vregs
  apply sepWPp_seq_codeOk (mid := lsρ lsRustDeallocSymCli) hs.inv
  rw [show runSaved s0 = MainHops.mainSaved s0 from rfl, MainHops.mainSaved_eq_sub s0, runProgPlaced_eq]
  simp only [sepConj_assoc]
  change s.pc = (blkPl_579).base + 384#64 at hpc
  generalize hsp0_eq : s0.sp = sp0 at hsp hsp0 hsp60_al ⊢
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
  intro hinv_c; subst hsp0_eq
  have hcs_pre : CalleeSavedPreserved s0 (j_stOf_jp hinv_c) :=
    MainHops.calleeSavedPreserved_of_regs
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (Eq.trans (by simp only [calleeSavedVRegs, arm64_norm]) hvregs)
  have hrej := stackAt_run_rejoin s0 hrf h64
  change MainHops.mainSaved s0 ∗ runLocals (runFsp s0) [] ∗
    stackAt (runFsp s0) (resStack - runFrame) ⊢ stackAt s0.sp resStack at hrej
  have hstk_split := MainHops.stackAt_split_ge s0.sp hext h64
  refine j_call_rocl_jp
    (F := runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗ memRegion g.stores 320 ∗
      (g.inp ↦ₛ inputOf g.i g.c) ∗ memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - extHookStack) ∗
      anyHeap)
    (s0 := s0) (x := (ptr, cap.toNat, 1))
    (hh.allocFs.dealloc_rocl (prog := runProgPlaced H) (i := 579)) hinv_c
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    (by simpa only [State.spAligned, arm64_norm] using hsp0)
    (retAddr := s0.readReg64 .lr) (by simp only [arm64_norm]) ?_
    (hnext := fun sm _ hinv_m hpcm hrunm hspm hcsm => ?_)
  · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]; simp only [sepConj_assoc]
    apply Entails.pure_right ⟨by simp only [arm64_norm, hx0], by simp only [arm64_norm, hx1],
      by simp only [arm64_norm], hlay⟩
    have hsp_eq : (j_stOf_jp hinv_c).sp = s0.sp := by simp only [arm64_norm]
    rw [hsp_eq]
    refine Entails.trans (Entails.of_eq (show _ =
      (MainHops.mainSaved s0 ∗ runLocals (runFsp s0) [] ∗ stackAt (runFsp s0) (resStack - runFrame)) ∗
      (A.pool ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗
        runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        memRegion g.stores 320 ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ anyHeap) by
        rw [MainHops.mainSaved_eq_sub s0]; ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left hrej) ?_
    rw [hstk_split]; exact Entails.of_eq (by ac_rfl)
  · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]; simp only [sepConj_assoc]
    apply j_sepWPp_pure_left_jp; intro hfs_m; apply j_sepWPp_pure_left_jp; intro htr_m
    have hsp_m : sm.sp = s0.sp := hspm.trans (by simp only [arm64_norm])
    have htr_tot : sm.trace = s.trace := htr_m.trans (by simp only [arm64_norm])
    have hfs_tot : sm.fs = s.fs := hfs_m.trans (by simp only [arm64_norm])
    refine fun R hm _ => ⟨sm, Steps.refl sm, Or.inl ⟨hpcm, hrunm, _, hm, ?_⟩⟩
    refine ⟨hinv_m, hsp_m, j_cs_trans_jp hcs_pre hcsm, htr_tot ▸ htr,
      j_hist_of_eq_jp htr_tot (congrArg FsState.files hfs_tot) hhist, some none, by decide,
      hans.symm, ?_⟩
    have hsp_pre : (j_stOf_jp hinv_c).sp = s0.sp := by simp only [arm64_norm]
    rw [hsp_pre, hstk_split]; exact Entails.of_eq (by ac_rfl)

/-! ## Post-Dispatch Reject (`R+0x2c7c`) -/

private theorem j_rejPost_jp [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost} {s0 s : State}
    {resStack : Nat} {Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hrf : runFrame ≤ resStack)
    (h96 : 96 + extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (h64 : resStack ≤ 2 ^ 64) (hr : AtRejectPlaced CodeOk g g' .postDispatch s0 s) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (rejectMem A g g' .postDispatch s0 resStack)
      (runPostPlaced CodeOk A g resStack s0) Qp (runOom s0) := by
  have hs := hr.base; dsimp only [RejectKind.pcOff] at hs
  have hpc : s.pc = runPcPlaced 0x2c7c := hs.pc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = runFsp s0 := hs.sp
  have hsp_al : s.spAligned = true := hs.spAligned_cur
  have hx19 : s.readReg64 (.gpr 19#5) = g.stores := hr.x19
  unfold rejectMem; dsimp only
  apply sepWPp_seq_codeOk (mid := (blkPl_550).base) hs.inv
  rw [runProgPlaced_eq]; simp only [runPcPlaced_eq] at hpc
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, hrun])
  intro hinv_c
  refine j_call_lscro_jp
    (F := runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
      (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ runLocals (runFsp s0) [] ∗ anyHeap)
    (s0 := s0) (x := ⟨g.stores, g'⟩)
    (dropStores_placed_ok (callerProg := runProgPlaced H) (i := 579)
      hh (resStack - runFrame) h96 hsub64) hinv_c
    (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, hrun])
    (by simpa only [State.spAligned, arm64_norm] using hsp_al)
    (retAddr := runPcPlaced 0x2c84) (by simp only [arm64_norm, runPcPlaced_eq]) ?_
    (hnext := fun sm hsteps_ds hinv_m hpcm hrunm hspm hcsm => ?_)
  · dsimp only [dropStoresSpec]; simp only [sepConj_assoc]
    apply Entails.pure_right (by simp only [arm64_norm])
    have hsp_c : (j_stOf_jp hinv_c).sp = runFsp s0 := by simp only [arm64_norm, hsp]
    rw [hsp_c]; exact Entails.of_eq (by ac_rfl)
  · dsimp only [dropStoresSpec]; simp only [sepConj_assoc]
    apply j_sepWPp_pure_left_jp; intro htr_m
    have hsp_c : (j_stOf_jp hinv_c).sp = runFsp s0 := by simp only [arm64_norm, hsp]
    rw [hsp_c]
    have hs_m : InRunPlaced CodeOk s0 sm 0x2c84 :=
      j_inRun_step_jp hs hpcm hrunm (hspm.trans (by simp only [arm64_norm]))
        (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm])) hinv_m
        (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [calleeSavedVRegs, arm64_norm]))
    have hfiles_m : sm.fs.files = s.fs.files :=
      (j_files_of_trace_eq_jp (hh.fs (runProgPlaced H) 579) hsteps_ds htr_m).trans
        (by simp only [arm64_norm])
    have htr_tot : sm.trace = s.trace := htr_m.trans (by simp only [arm64_norm])
    refine j_sepWPp_weaken_pre_jp (Entails.of_eq (by ac_rfl))
      (j_epi_jp hrf h64 hs_m (htr_tot ▸ hr.trace)
        (j_hist_of_eq_jp htr_tot hfiles_m hr.hist) (by decide) hr.ans.symm)

/-! ## Pre-Dispatch Reject (`R+0x124`) -/

private theorem j_rejPre_from_174_jp [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {A : RustAlloc} {H : LibsignalHooks}
    {g : RunCall} {w : CallW} {bs : List (BitVec 8)} {s0 s : State} {resStack : Nat}
    {Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hrf : runFrame ≤ resStack)
    (hext : extHookStack ≤ resStack)
    (h64 : resStack ≤ 2 ^ 64)
    (hs : InRunPlaced CodeOk s0 s 0x174)
    (hx25 : s.readReg64 (.gpr 25#5) = g.call)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗
          ((g.call + 24#64) ↦₆₄ w.w3) ∗ ((g.call + 32#64) ↦₆₄ w.w4) ∗
          ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6)) ∗
        ownedBytes A w.w1 w.w2 w.w3 bs ∗
        (runResAt A cliWrOk g.res (some none) ∗ memRegion g.stores 320 ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ runLocals (runFsp s0) [] ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap))
      (runPostPlaced CodeOk A g resStack s0) Qp (runOom s0) := by
  have hpc : s.pc = runPcPlaced 0x174 := hs.pc
  have hrun : s.status = .Running := hs.run
  by_cases hcap : w.w1 = 0
  · have hcap64 : w.w1 = 0#64 := hcap
    apply j_sepWPp_weaken_pre_jp
      (sepConj_mono_right (sepConj_mono_left (j_ownedBytes_zero_jp A bs hcap)))
    rw [emp_sepConj]
    apply sepWPp_seq_codeOk (mid := runPcPlaced 0x2c84) hs.inv
    simp only [sepConj_assoc, runProgPlaced_eq, runPcPlaced_eq]
    change s.pc = (blkPl_579).base + 372#64 at hpc
    rw [hcap64]
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv_e
    have hs_e : InRunPlaced CodeOk s0 (j_stOf_jp hinv_e) 0x2c84 :=
      j_inRun_step_jp hs (by simp only [arm64_norm, runPcPlaced_eq, *])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv_e (by simp only [calleeSavedVRegs, arm64_norm])
    refine j_sepWPp_weaken_pre_jp ?_
      (j_epi_jp hrf h64 hs_e (by simpa only [arm64_norm] using htr)
        (j_hist_of_eq_jp (s' := j_stOf_jp hinv_e) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hhist)
        (by decide) hans.symm)
    rw [← hcap64]
    exact Entails.trans (j_fold_call_mem_assoc_jp g.call w _) (Entails.of_eq (by ac_rfl))
  · have hbeq : (w.w1 == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    apply j_sepWPp_weaken_pre_jp
      (sepConj_mono_right (sepConj_mono_left (j_ownedBytes_dealloc_jp A bs hcap)))
    rw [j_pull_pure_jp]
    apply j_sepWPp_pure_left_jp; intro hlay
    apply sepWPp_seq_codeOk (mid := runPcPlaced 0x180) hs.inv
    simp only [sepConj_assoc, runProgPlaced_eq, runPcPlaced_eq]
    change s.pc = (blkPl_579).base + 372#64 at hpc
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv_t
    have hs_t : InRunPlaced CodeOk s0 (j_stOf_jp hinv_t) 0x180 :=
      j_inRun_step_jp hs (by simp only [arm64_norm, runPcPlaced_eq, *])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv_t (by simp only [calleeSavedVRegs, arm64_norm])
    refine j_sepWPp_weaken_pre_jp ?_
      (j_tail_dealloc_jp hh hrf hext h64 hs_t
        (ptr := w.w2) (cap := w.w1)
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hlay
        (by simpa only [arm64_norm] using htr)
        (j_hist_of_eq_jp (s' := j_stOf_jp hinv_t) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hhist)
        hans)
    exact Entails.trans (j_fold_call_mem_assoc_jp g.call w _) (Entails.of_eq (by ac_rfl))

private theorem j_rejPre_from_160_jp [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {A : RustAlloc} {H : LibsignalHooks}
    {g : RunCall} {w : CallW} {bundle : List (BitVec 8)} {s0 s : State} {resStack : Nat}
    {Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hrf : runFrame ≤ resStack)
    (hext : extHookStack ≤ resStack)
    (h64 : resStack ≤ 2 ^ 64)
    (hs : InRunPlaced CodeOk s0 s 0x160)
    (hx25 : s.readReg64 (.gpr 25#5) = g.call)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗
          ((g.call + 24#64) ↦₆₄ w.w3) ∗ ((g.call + 32#64) ↦₆₄ w.w4) ∗
          ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6)) ∗
        ownedBytes A w.w4 w.w5 w.w6 bundle ∗
        (runResAt A cliWrOk g.res (some none) ∗ memRegion g.stores 320 ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ runLocals (runFsp s0) [] ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap))
      (runPostPlaced CodeOk A g resStack s0) Qp (runOom s0) := by
  have hpc : s.pc = runPcPlaced 0x160 := hs.pc
  have hrun : s.status = .Running := hs.run
  by_cases hcap : w.w4 = 0
  · have hcap64 : w.w4 = 0#64 := hcap
    apply j_sepWPp_weaken_pre_jp
      (sepConj_mono_right (sepConj_mono_left (j_ownedBytes_zero_jp A bundle hcap)))
    rw [emp_sepConj]
    apply sepWPp_seq_codeOk (mid := runPcPlaced 0x2c84) hs.inv
    simp only [sepConj_assoc, runProgPlaced_eq, runPcPlaced_eq]
    change s.pc = (blkPl_579).base + 352#64 at hpc
    rw [hcap64]
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv_e
    have hs_e : InRunPlaced CodeOk s0 (j_stOf_jp hinv_e) 0x2c84 :=
      j_inRun_step_jp hs (by simp only [arm64_norm, runPcPlaced_eq, *])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv_e (by simp only [calleeSavedVRegs, arm64_norm])
    refine j_sepWPp_weaken_pre_jp ?_
      (j_epi_jp hrf h64 hs_e (by simpa only [arm64_norm] using htr)
        (j_hist_of_eq_jp (s' := j_stOf_jp hinv_e) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hhist)
        (by decide) hans.symm)
    rw [← hcap64]
    exact Entails.trans (j_fold_call_mem_assoc_jp g.call w _) (Entails.of_eq (by ac_rfl))
  · have hbeq : (w.w4 == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    apply j_sepWPp_weaken_pre_jp
      (sepConj_mono_right (sepConj_mono_left (j_ownedBytes_dealloc_jp A bundle hcap)))
    rw [j_pull_pure_jp]
    apply j_sepWPp_pure_left_jp; intro hlay
    apply sepWPp_seq_codeOk (mid := runPcPlaced 0x180) hs.inv
    simp only [sepConj_assoc, runProgPlaced_eq, runPcPlaced_eq]
    change s.pc = (blkPl_579).base + 352#64 at hpc
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv_t
    have hs_t : InRunPlaced CodeOk s0 (j_stOf_jp hinv_t) 0x180 :=
      j_inRun_step_jp hs (by simp only [arm64_norm, runPcPlaced_eq, *])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv_t (by simp only [calleeSavedVRegs, arm64_norm])
    refine j_sepWPp_weaken_pre_jp ?_
      (j_tail_dealloc_jp hh hrf hext h64 hs_t
        (ptr := w.w5) (cap := w.w4)
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hlay
        (by simpa only [arm64_norm] using htr)
        (j_hist_of_eq_jp (s' := j_stOf_jp hinv_t) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hhist)
        hans)
    exact Entails.trans (j_fold_call_mem_assoc_jp g.call w _) (Entails.of_eq (by ac_rfl))

private theorem j_rejPre_init_from_134_jp [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {A : RustAlloc} {H : LibsignalHooks}
    {g : RunCall} {w : CallW} {peer : AddrV} {bundle : List (BitVec 8)}
    {s0 s : State} {resStack : Nat} {Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hrf : runFrame ≤ resStack)
    (hext_sub : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hext : extHookStack ≤ resStack)
    (h64 : resStack ≤ 2 ^ 64)
    (hs : InRunPlaced CodeOk s0 s 0x134)
    (hx25 : s.readReg64 (.gpr 25#5) = g.call)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗
          ((g.call + 24#64) ↦₆₄ w.w3) ∗ ((g.call + 32#64) ↦₆₄ w.w4) ∗
          ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6)) ∗
        (addrWords A peer w.w0 w.w1 w.w2 w.w3 ∗ ownedBytes A w.w4 w.w5 w.w6 bundle) ∗
        (runResAt A cliWrOk g.res (some none) ∗ memRegion g.stores 320 ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ runLocals (runFsp s0) [] ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap))
      (runPostPlaced CodeOk A g resStack s0) Qp (runOom s0) := by
  unfold addrWords
  have hpure_init : ∀ {P Q : Prop} {X Y Z W : SepProp},
      X ∗ (((⌜P⌝ ∗ Y) ∗ ⌜Q⌝) ∗ Z) ∗ W = ⌜P⌝ ∗ (⌜Q⌝ ∗ (X ∗ Y ∗ Z ∗ W)) := by
    intros; ac_rfl
  conv => arg 4; enter [2, 1, 1]; unfold ownedBytes
  rw [hpure_init]; clear hpure_init
  apply j_sepWPp_pure_left_jp; rintro ⟨_, hle0, hlt0, _⟩
  apply j_sepWPp_pure_left_jp; intro _
  have hpc : s.pc = runPcPlaced 0x134 := hs.pc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = runFsp s0 := hs.sp
  have hsp_al : s.spAligned = true := hs.spAligned_cur
  by_cases hcap0 : w.w0 = 0
  · simp only [hcap0, ↓reduceIte, emp_sepConj]
    conv => arg 4; enter [1, 1]; change g.call ↦₆₄ 0#64
    apply sepWPp_seq_codeOk (mid := runPcPlaced 0x160) hs.inv
    simp only [sepConj_assoc, runProgPlaced_eq, runPcPlaced_eq]
    change s.pc = (blkPl_579).base + 308#64 at hpc
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv_160
    have hs_160 : InRunPlaced CodeOk s0 (j_stOf_jp hinv_160) 0x160 :=
      j_inRun_step_jp hs (by simp only [arm64_norm, runPcPlaced_eq, *])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv_160 (by simp only [calleeSavedVRegs, arm64_norm])
    refine j_sepWPp_weaken_pre_jp ?_
      (j_rejPre_from_160_jp hh hrf hext h64 hs_160 (w := w) (bundle := bundle)
        (by simp only [arm64_norm, hx25])
        (by simpa only [arm64_norm] using htr)
        (j_hist_of_eq_jp (s' := j_stOf_jp hinv_160) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hhist)
        hans)
    rw [show w.w0 = 0#64 from hcap0]
    exact Entails.of_eq (by ac_rfl)
  · have hbeq0 : (w.w0 == 0#64) = false := beq_eq_false_iff_ne.mpr hcap0
    have hmsb0 : w.w0.msb = false := BitVec.msb_eq_false_iff_two_mul_lt.mpr (by omega)
    have hpos0 : 0 < w.w0.toNat :=
      Nat.pos_of_ne_zero fun h0 => hcap0 (BitVec.eq_of_toNat_eq h0)
    have hlay0 : LayoutOk w.w0.toNat 1 := ⟨hpos0, ⟨0, rfl⟩, by omega⟩
    have hpeer_mem :
        (if w.w0 = 0 then emp
         else A.live w.w1 w.w0.toNat 1 ∗ (w.w1 ↦ₛ peer.name) ∗
           memRegion (w.w1 + BitVec.ofNat 64 peer.name.length)
             (w.w0.toNat - peer.name.length)) ⊢
        A.live w.w1 w.w0.toNat 1 ∗ memRegion w.w1 w.w0.toNat := by
      simp only [hcap0, ↓reduceIte]
      have hmerge :
          memRegion w.w1 peer.name.length ∗
            memRegion (w.w1 + BitVec.ofNat 64 peer.name.length)
              (w.w0.toNat - peer.name.length) =
          memRegion w.w1 w.w0.toNat := by
        have hsum : peer.name.length + (w.w0.toNat - peer.name.length) = w.w0.toNat :=
          Nat.add_sub_of_le hle0
        simpa only [hsum] using
          (ProofLib.memRegion_split w.w1 peer.name.length
            (w.w0.toNat - peer.name.length) (by omega)).symm
      rw [← hmerge]
      exact sepConj_mono_right
        (sepConj_mono_left (ProofLib.pointsToBytes_entails_memRegion w.w1 peer.name))
    apply j_sepWPp_weaken_pre_jp (sepConj_mono_right (sepConj_mono_left hpeer_mem))
    apply sepWPp_seq_codeOk (mid := lsρ lsRustDeallocSymCli) hs.inv
    simp only [sepConj_assoc, runProgPlaced_eq]
    change s.pc = (blkPl_579).base + 308#64 at hpc
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv_da
    have hstk_split := MainHops.stackAt_split_ge (runFsp s0) hext_sub hsub64
    refine j_call_rocl_jp
      (F := ((g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗
          ((g.call + 24#64) ↦₆₄ w.w3) ∗ ((g.call + 32#64) ↦₆₄ w.w4) ∗
          ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6)) ∗
        ownedBytes A w.w4 w.w5 w.w6 bundle ∗
        runResAt A cliWrOk g.res (some none) ∗ memRegion g.stores 320 ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ runLocals (runFsp s0) [] ∗
        memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
          (resStack - runFrame - extHookStack) ∗
        anyHeap)
      (s0 := s0) (x := (w.w1, w.w0.toNat, 1))
      (hh.allocFs.dealloc_rocl (prog := runProgPlaced H) (i := 579)) hinv_da
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hrun])
      (by simpa only [State.spAligned, arm64_norm] using hsp_al)
      (retAddr := runPcPlaced 0x160)
      (by simp only [arm64_norm, runPcPlaced_eq, *])
      ?_
      (hnext := fun sm _ hinv_m hpcm hrunm hspm hcsm => ?_)
    · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
      simp only [sepConj_assoc]
      apply Entails.pure_right
      · exact ⟨by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], hlay0⟩
      have hsp_c : (j_stOf_jp hinv_da).sp = runFsp s0 := by simp only [arm64_norm, hsp]
      rw [hsp_c, hstk_split]
      exact Entails.of_eq (by ac_rfl)
    · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
      simp only [sepConj_assoc]
      apply j_sepWPp_pure_left_jp; intro hfs_m
      apply j_sepWPp_pure_left_jp; intro htr_m
      have hsp_c : (j_stOf_jp hinv_da).sp = runFsp s0 := by simp only [arm64_norm, hsp]
      rw [hsp_c]
      have hs_m : InRunPlaced CodeOk s0 sm 0x160 :=
        j_inRun_step_jp hs hpcm hrunm (hspm.trans (by simp only [arm64_norm]))
          (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm])) hinv_m
          (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [calleeSavedVRegs, arm64_norm]))
      have hx25_m : sm.readReg64 (.gpr 25#5) = g.call :=
        hcsm.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, hx25])
      have htr_tot : sm.trace = s.trace := htr_m.trans (by simp only [arm64_norm])
      have hfs_tot : sm.fs = s.fs := hfs_m.trans (by simp only [arm64_norm])
      refine j_sepWPp_weaken_pre_jp ?_
        (j_rejPre_from_160_jp (w := w) (bundle := bundle) hh hrf hext h64 hs_m hx25_m
          (htr_tot ▸ htr)
          (j_hist_of_eq_jp htr_tot (congrArg FsState.files hfs_tot) hhist)
          hans)
      rw [hstk_split]
      exact Entails.of_eq (by ac_rfl)

private theorem j_rejPre_addr_from_134_jp [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {A : RustAlloc} {H : LibsignalHooks} {g : RunCall} {w : CallW}
    {bs : List (BitVec 8)} {s0 s : State} {resStack : Nat} {Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hrf : runFrame ≤ resStack) (hext : extHookStack ≤ resStack)
    (h64 : resStack ≤ 2 ^ 64) (hs : InRunPlaced CodeOk s0 s 0x134)
    (hx25 : s.readReg64 (.gpr 25#5) = g.call) (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s) (hans : g.a = some none)
    (hw0 : w.w0 = 0x8000000000000000#64 ∨
      w.w0 = 0x8000000000000002#64 ∨ w.w0 = 0x8000000000000003#64) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗
          ((g.call + 24#64) ↦₆₄ w.w3) ∗ ((g.call + 32#64) ↦₆₄ w.w4) ∗
          ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6)) ∗
        ownedBytes A w.w1 w.w2 w.w3 bs ∗
        (runResAt A cliWrOk g.res (some none) ∗ memRegion g.stores 320 ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ runLocals (runFsp s0) [] ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap))
      (runPostPlaced CodeOk A g resStack s0) Qp (runOom s0) := by
  have hpc : s.pc = runPcPlaced 0x134 := hs.pc
  have hrun : s.status = .Running := hs.run
  rcases hw0 with hw0 | hw0 | hw0 <;>
  · apply sepWPp_seq_codeOk (mid := runPcPlaced 0x174) hs.inv
    simp only [sepConj_assoc, runProgPlaced_eq, runPcPlaced_eq]
    change s.pc = (blkPl_579).base + 308#64 at hpc
    rw [hw0]; wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv_174
    have hs_174 : InRunPlaced CodeOk s0 (j_stOf_jp hinv_174) 0x174 :=
      j_inRun_step_jp hs (by simp only [arm64_norm, runPcPlaced_eq, *])
        (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv_174 (by simp only [calleeSavedVRegs, arm64_norm])
    refine j_sepWPp_weaken_pre_jp ?_
      (j_rejPre_from_174_jp hh hrf hext h64 hs_174 (w := w) (bs := bs)
        (by simp only [arm64_norm, hx25]) (by simpa only [arm64_norm] using htr)
        (j_hist_of_eq_jp (s' := j_stOf_jp hinv_174) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hhist) hans)
    rw [← hw0]; exact Entails.of_eq (by ac_rfl)

private theorem j_rejPre_jp [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost} {s0 s : State}
    {resStack : Nat} {Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hrf : runFrame ≤ resStack)
    (h96 : 96 + extHookStack ≤ resStack - runFrame) (hext_sub : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64) (hext : extHookStack ≤ resStack)
    (h64 : resStack ≤ 2 ^ 64) (hr : AtRejectPlaced CodeOk g g' .preDispatch s0 s) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (rejectMem A g g' .preDispatch s0 resStack)
      (runPostPlaced CodeOk A g resStack s0) Qp (runOom s0) := by
  have hs := hr.base; dsimp only [RejectKind.pcOff] at hs
  have hpc : s.pc = runPcPlaced 0x124 := hs.pc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = runFsp s0 := hs.sp
  have hsp_al : s.spAligned = true := hs.spAligned_cur
  have hx19 : s.readReg64 (.gpr 19#5) = g.stores := hr.x19
  obtain ⟨hx20, hx25⟩ := hr.preRegs rfl
  unfold rejectMem; dsimp only
  have hres_split : memRegion g.res runResSize ⊢
      ∃∗ u0 : BitVec 64, (g.res ↦₆₄ u0) ∗ memRegion (g.res + 8#64) (runResSize - 8) := by
    rw [show runResSize = 8 + (runResSize - 8) from rfl,
        ProofLib.memRegion_split g.res 8 (runResSize - 8) (by decide),
        ProofLib.memRegion_eight g.res, sepExists_sepConj_left]
    exact Entails.refl _
  apply j_sepWPp_weaken_pre_jp (sepConj_mono_left (sepConj_mono_left hres_split))
  rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply j_sepWPp_exists_left_jp; intro u0
  apply sepWPp_seq_codeOk (mid := (blkPl_550).base) hs.inv
  simp only [sepConj_assoc, runProgPlaced_eq]; change s.pc = (blkPl_579).base + 292#64 at hpc
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, hrun])
  intro hinv_c
  refine j_call_lscro_jp
    (F := runResAt A cliWrOk g.res (some none) ∗ callAt A g.call g.c ∗
      (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ runLocals (runFsp s0) [] ∗ anyHeap)
    (s0 := s0) (x := ⟨g.stores, g'⟩)
    (dropStores_placed_ok (callerProg := runProgPlaced H) (i := 579)
      hh (resStack - runFrame) h96 hsub64) hinv_c
    (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, hrun])
    (by simpa only [State.spAligned, arm64_norm] using hsp_al)
    (retAddr := runPcPlaced 0x134) (by simp only [arm64_norm, runPcPlaced_eq]) ?_
    (hnext := fun sm hsteps_ds hinv_m hpcm hrunm hspm hcsm => ?_)
  · dsimp only [dropStoresSpec, runResAt]; simp only [sepConj_assoc]
    apply Entails.pure_right (by simp only [arm64_norm])
    have hsp_c : (j_stOf_jp hinv_c).sp = runFsp s0 := by simp only [arm64_norm, hsp]
    rw [hsp_c]; exact Entails.of_eq (by ac_rfl)
  · dsimp only [dropStoresSpec]
    simp only [sepConj_assoc]
    apply j_sepWPp_pure_left_jp; intro htr_m
    have hsp_c : (j_stOf_jp hinv_c).sp = runFsp s0 := by simp only [arm64_norm, hsp]
    rw [hsp_c]
    have hs_m : InRunPlaced CodeOk s0 sm 0x134 :=
      j_inRun_step_jp hs hpcm hrunm (hspm.trans (by simp only [arm64_norm]))
        (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm])) hinv_m
        (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [calleeSavedVRegs, arm64_norm]))
    have hx25_m : sm.readReg64 (.gpr 25#5) = g.call :=
      hcsm.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, hx25])
    have hfiles_m : sm.fs.files = s.fs.files :=
      (j_files_of_trace_eq_jp (hh.fs (runProgPlaced H) 579) hsteps_ds htr_m).trans
        (by simp only [arm64_norm])
    have htr_tot : sm.trace = s.trace := htr_m.trans (by simp only [arm64_norm])
    have htr_134 : s0.trace <+: sm.trace := htr_tot ▸ hr.trace
    have hhist_134 : RunHistOk g.i s0 sm := j_hist_of_eq_jp htr_tot hfiles_m hr.hist
    have hans_134 : g.a = some none := hr.ans
    unfold callAt
    rw [show (memRegion g.stores 320 ∗ A.pool ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        runResAt A cliWrOk g.res (some none) ∗
        (∃∗ w : CallW, (g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗
          ((g.call + 16#64) ↦₆₄ w.w2) ∗ ((g.call + 24#64) ↦₆₄ w.w3) ∗
          ((g.call + 32#64) ↦₆₄ w.w4) ∗ ((g.call + 40#64) ↦₆₄ w.w5) ∗
          ((g.call + 48#64) ↦₆₄ w.w6) ∗ callHeap A w g.c) ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ runLocals (runFsp s0) [] ∗ anyHeap) =
      (∃∗ w : CallW,
        ((g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗
            ((g.call + 24#64) ↦₆₄ w.w3) ∗ ((g.call + 32#64) ↦₆₄ w.w4) ∗
            ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6)) ∗
          callHeap A w g.c ∗
          (runResAt A cliWrOk g.res (some none) ∗ memRegion g.stores 320 ∗
            (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ runLocals (runFsp s0) [] ∗
            stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap)) by
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      exact congrArg SepProp.sepExists (funext fun _ => by ac_rfl)]
    apply j_sepWPp_exists_left_jp; intro w
    rcases hc_eq : g.c with ⟨me, n⟩ | ⟨peer, bundle⟩ | ⟨peer⟩ | ⟨peer⟩
    · dsimp only [callHeap]; unfold addrWords
      rw [← hc_eq, j_pull_pure_jp]; apply j_sepWPp_pure_left_jp; rintro ⟨hw0, _⟩
      rw [j_pull_pure_r_jp]; apply j_sepWPp_pure_left_jp; intro _
      exact j_rejPre_addr_from_134_jp hh hrf hext h64 hs_m hx25_m htr_134 hhist_134 hans_134
        (Or.inl hw0)
    · dsimp only [callHeap]; rw [← hc_eq]
      exact j_rejPre_init_from_134_jp hh hrf hext_sub hsub64 hext h64 hs_m hx25_m
        htr_134 hhist_134 hans_134
    · dsimp only [callHeap]; unfold addrWords
      rw [← hc_eq, j_pull_pure_jp]; apply j_sepWPp_pure_left_jp; intro hw0
      rw [j_pull_pure_r_jp]; apply j_sepWPp_pure_left_jp; intro _
      exact j_rejPre_addr_from_134_jp hh hrf hext h64 hs_m hx25_m htr_134 hhist_134 hans_134
        (Or.inr (Or.inl hw0))
    · dsimp only [callHeap]; unfold addrWords
      rw [← hc_eq, j_pull_pure_jp]; apply j_sepWPp_pure_left_jp; intro hw0
      rw [j_pull_pure_r_jp]; apply j_sepWPp_pure_left_jp; intro _
      exact j_rejPre_addr_from_134_jp hh hrf hext h64 hs_m hx25_m htr_134 hhist_134 hans_134
        (Or.inr (Or.inr hw0))

/-! ## Accept Join (`R+0xf8c → lr`) -/

private def j_joinPayloadBytes_jp (ws : StoresWords) (outCap outPtr outLen : BitVec 64) :
    List (BitVec 8) :=
  storesBytes ws ++ (unpack64 outCap ++ (unpack64 outPtr ++ unpack64 outLen))

private theorem j_joinPayloadBytes_length_jp (ws : StoresWords)
    (outCap outPtr outLen : BitVec 64) :
    (j_joinPayloadBytes_jp ws outCap outPtr outLen).length = runResSize := by
  simp [j_joinPayloadBytes_jp, storesBytes_length, runResSize]

private theorem j_payload_eq_parts_jp (b : BitVec 64) (ws : StoresWords)
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

private theorem j_vecU8_repack_jp (A : RustAlloc) (v : BitVec 64) (outCap outPtr : BitVec 64)
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
  exact Entails.of_eq (by ac_rfl)

private theorem j_join_carve_locals_jp (fsp : BitVec 64) :
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
    (Entails.sepExists_right u620 (Entails.of_eq (by ac_rfl))))

private theorem j_join_rejoin_locals_jp (fsp : BitVec 64) (outCap outPtr outLen : BitVec 64)
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
    exact sepConj_mono (RunCompose.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (RunCompose.pointsTo64_entails_memRegion _ _)
        (RunCompose.pointsTo64_entails_memRegion _ _))
  have h344 :
      ((fsp + 0x4d0#64) ↦ₛ j_joinPayloadBytes_jp ws outCap outPtr outLen) ⊢
        memRegion (fsp + 0x4d0#64) 0x158 := by
    have h := M5MovesHelpers.pointsToBytes_entails_memRegion
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
        memRegion (fsp + 0x628#64) (runLocalBytes - 0x628)) by ac_rfl)) ?_
  exact Entails.trans
    (sepConj_mono_right (sepConj_mono h24 (sepConj_mono_right (sepConj_mono_left h344)))) hrej

private theorem j_join_jp [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost} {out : Bytes}
    {s0 s : State} {resStack : Nat} {Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hrf : runFrame ≤ resStack)
    (hext_sub : extHookStack ≤ resStack - runFrame) (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (h64 : resStack ≤ 2 ^ 64) (hj : AtJoinPlaced CodeOk g g' out s0 s) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s (joinMem A g g' out s0 resStack)
      (runPostPlaced CodeOk A g resStack s0) Qp (runOom s0) := by
  let fsp := runFsp s0
  have hs := hj.base
  have hpc : s.pc = runPcPlaced 0xf8c := hs.pc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp
  have hsp_al : s.spAligned = true := hs.spAligned_cur
  have hx19 : s.readReg64 (.gpr 19#5) = g.stores := hj.x19
  have hx20 : s.readReg64 (.gpr 20#5) = g.res := hj.x20
  have hmc := hh.allocFs.session_memcpy_region_rocl (prog := runProgPlaced H) (i := 579)
    extHookStack (Nat.le_refl _) (by decide)
  have hstk_split := MainHops.stackAt_split_ge fsp hext_sub hsub64
  unfold joinMem; dsimp only [runLocals, runLocalsFrom, Nat.sub_zero]
  have hz : fsp + BitVec.ofNat 64 0 = fsp := by bv_omega
  rw [show runFsp s0 = fsp from rfl, hz, show BitVec.ofNat 64 (0x208 + 24) = 0x220#64 from rfl]
  apply j_sepWPp_weaken_pre_jp
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono (storesAt_unpack A g.stores g')
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono
        (sepConj_mono_right (sepConj_mono (vecU8_unpack_ownedBytes A (fsp + 0x208#64) out)
          (j_join_carve_locals_jp fsp))) (Entails.refl _)))))))
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply j_sepWPp_exists_left_jp; intro u610; apply j_sepWPp_exists_left_jp; intro u618
  apply j_sepWPp_exists_left_jp; intro u620; apply j_sepWPp_exists_left_jp; intro outCap
  apply j_sepWPp_exists_left_jp; intro outPtr; apply j_sepWPp_exists_left_jp; intro ws
  set outLen := BitVec.ofNat 64 out.length
  rw [storesStackAt_eq_bytes]
  apply sepWPp_seq_codeOk (mid := lsρ memcpyName) hs.inv
  simp only [sepConj_assoc, runProgPlaced_eq]
  change s.pc = (blkPl_579).base + 3980#64 at hpc
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
  intro hinv_mc1
  refine j_call_rocl_jp
    (F := memRegion g.res runResSize ∗ memRegion g.call 56 ∗ storesHeap A ws g' ∗
      (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion fsp 0x208 ∗
      ((fsp + 0x208#64) ↦₆₄ outCap) ∗ ((fsp + 0x210#64) ↦₆₄ outPtr) ∗
      ((fsp + 0x218#64) ↦₆₄ outLen) ∗ ownedBytes A outCap outPtr outLen out ∗
      memRegion (fsp + 0x220#64) 0x2b0 ∗ ((fsp + 0x610#64) ↦₆₄ u610) ∗
      ((fsp + 0x618#64) ↦₆₄ u618) ∗ ((fsp + 0x620#64) ↦₆₄ u620) ∗
      memRegion (fsp + 0x628#64) (runLocalBytes - 0x628) ∗
      memRegion (fsp - BitVec.ofNat 64 (resStack - runFrame)) (resStack - runFrame - extHookStack) ∗
      A.pool ∗ anyHeap)
    (s0 := s0) (x := (fsp + 0x4d0#64, g.stores, storesBytes ws)) hmc hinv_mc1
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    (by simpa only [State.spAligned, arm64_norm] using hsp_al)
    (retAddr := runPcPlaced 0xf9c) (by simp only [arm64_norm, runPcPlaced_eq]) ?_
    (hnext := fun s1 _ hinv1 hpc1 hrun1 hsp1 hcs1 => ?_)
  · dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
    simp only [sepConj_assoc]
    apply Entails.pure_right
    · exact ⟨by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm, storesBytes_length]⟩
    have hsp_c : (j_stOf_jp hinv_mc1).sp = fsp := by simp only [arm64_norm, hsp]
    rw [hsp_c, storesBytes_length, hstk_split]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by ac_rfl)
  · dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionSpec]; simp only [sepConj_assoc]
    apply j_sepWPp_pure_left_jp; intro hfs1; apply j_sepWPp_pure_left_jp; rintro ⟨_, htr1⟩
    have hsp_c : (j_stOf_jp hinv_mc1).sp = fsp := by simp only [arm64_norm, hsp]
    rw [hsp_c]
    have hs1 : InRunPlaced CodeOk s0 s1 0xf9c :=
      j_inRun_step_jp hs hpc1 hrun1 (hsp1.trans (by simp only [arm64_norm]))
        (hcs1.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm])) hinv1
        (hcs1.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [calleeSavedVRegs, arm64_norm]))
    have hx20_1 : s1.readReg64 (.gpr 20#5) = g.res := hcs1.2.1.trans (by simp only [arm64_norm, hx20])
    have htr1_eq : s1.trace = s.trace := htr1.trans (by simp only [arm64_norm])
    have hfs1_eq : s1.fs = s.fs := hfs1.trans (by simp only [arm64_norm])
    have hsp1_eq : s1.sp = fsp := hs1.sp
    have hsp1_al : s1.spAligned = true := hs1.spAligned_cur
    have hstores_mem : (g.stores ↦ₛ storesBytes ws) ⊢ memRegion g.stores 320 := by
      have h := M5MovesHelpers.pointsToBytes_entails_memRegion (storesBytes ws) g.stores
        (by simp [storesBytes_length])
      rwa [storesBytes_length] at h
    apply j_sepWPp_weaken_pre_jp (sepConj_mono_right (sepConj_mono_left hstores_mem))
    apply sepWPp_seq_codeOk (mid := lsρ memcpyName) hs1.inv
    have hpcm1 : s1.pc = runPcPlaced 0xf9c := hs1.pc
    rw [runProgPlaced_eq]
    change s1.pc = (blkPl_579).base + 3996#64 at hpcm1
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun1])
    intro hinv_mc2
    let payload := j_joinPayloadBytes_jp ws outCap outPtr outLen
    refine j_call_rocl_jp
      (F := memRegion g.stores 320 ∗ memRegion g.call 56 ∗ storesHeap A ws g' ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion fsp 0x208 ∗
        ((fsp + 0x208#64) ↦₆₄ outCap) ∗ ((fsp + 0x210#64) ↦₆₄ outPtr) ∗
        ((fsp + 0x218#64) ↦₆₄ outLen) ∗ ownedBytes A outCap outPtr outLen out ∗
        memRegion (fsp + 0x220#64) 0x2b0 ∗ memRegion (fsp + 0x628#64) (runLocalBytes - 0x628) ∗
        memRegion (fsp - BitVec.ofNat 64 (resStack - runFrame)) (resStack - runFrame - extHookStack) ∗
        A.pool ∗ anyHeap)
      (s0 := s0) (x := (g.res, fsp + 0x4d0#64, payload)) hmc hinv_mc2
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun1])
      (by simpa only [State.spAligned, arm64_norm] using hsp1_al)
      (retAddr := runPcPlaced 0xfc0) (by simp only [arm64_norm, runPcPlaced_eq]) ?_
      (hnext := fun s2 _ hinv2 hpc2 hrun2 hsp2 hcs2 => ?_)
    · dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
      simp only [sepConj_assoc]
      apply Entails.pure_right
      · exact ⟨by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm, payload, j_joinPayloadBytes_length_jp, runResSize]⟩
      have hsp_c2 : (j_stOf_jp hinv_mc2).sp = fsp := by simp only [arm64_norm, hsp1_eq]
      rw [hsp_c2]; dsimp only [payload]
      rw [j_joinPayloadBytes_length_jp, j_payload_eq_parts_jp (fsp + 0x4d0#64) ws outCap outPtr outLen]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by ac_rfl)
    · dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionSpec]; simp only [sepConj_assoc]
      apply j_sepWPp_pure_left_jp; intro hfs2; apply j_sepWPp_pure_left_jp; rintro ⟨_, htr2⟩
      have hsp_c2 : (j_stOf_jp hinv_mc2).sp = fsp := by simp only [arm64_norm, hsp1_eq]
      rw [hsp_c2]
      have hs2 : InRunPlaced CodeOk s0 s2 0xfc0 :=
        j_inRun_step_jp hs1 hpc2 hrun2 (hsp2.trans (by simp only [arm64_norm]))
          (hcs2.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm])) hinv2
          (hcs2.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [calleeSavedVRegs, arm64_norm]))
      have htr2_eq : s2.trace = s.trace := (htr2.trans (by simp only [arm64_norm])).trans htr1_eq
      have hfs2_eq : s2.fs = s.fs := (hfs2.trans (by simp only [arm64_norm])).trans hfs1_eq
      apply sepWPp_seq_codeOk (mid := runPcPlaced 0x2c84) hs2.inv
      have hpcm2 : s2.pc = runPcPlaced 0xfc0 := hs2.pc
      rw [runProgPlaced_eq, runPcPlaced_eq]
      change s2.pc = (blkPl_579).base + 4032#64 at hpcm2
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun2])
      intro hinv_e
      have hs_e : InRunPlaced CodeOk s0 (j_stOf_jp hinv_e) 0x2c84 :=
        j_inRun_step_jp hs2 (by simp only [arm64_norm, runPcPlaced_eq, *])
          (by simp only [arm64_norm, hrun2]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv_e (by simp only [calleeSavedVRegs, arm64_norm])
      have htr_e : (j_stOf_jp hinv_e).trace = s.trace :=
        (by simp only [arm64_norm] : (j_stOf_jp hinv_e).trace = s2.trace).trans htr2_eq
      have hfs_e : (j_stOf_jp hinv_e).fs = s.fs :=
        (by simp only [arm64_norm] : (j_stOf_jp hinv_e).fs = s2.fs).trans hfs2_eq
      let a' : RunAnswer := some (some (namedWrites g'.writes, out))
      have hres_repack :
          (g.res ↦ₛ payload) ∗ storesHeap A ws g' ∗ ownedBytes A outCap outPtr outLen out ⊢
          runResAt A cliWrOk g.res a' := by
        dsimp only [payload, a', runResAt, runOkAt]
        rw [j_payload_eq_parts_jp g.res ws outCap outPtr outLen, ← storesStackAt_eq_bytes]
        have hok :
            (storesStackAt g.res ws ∗ storesHeap A ws g') ∗
              (((g.res + 0x140#64) ↦₆₄ outCap) ∗ ((g.res + 0x140#64 + 0x08#64) ↦₆₄ outPtr) ∗
                ((g.res + 0x140#64 + 0x10#64) ↦₆₄ outLen) ∗
                ownedBytes A outCap outPtr outLen out) ⊢
            storesAt A g.res g' ∗ vecU8 A (g.res + 0x140#64) out :=
          sepConj_mono (storesAt_repack A g.res ws g')
            (j_vecU8_repack_jp A (g.res + 0x140#64) outCap outPtr out)
        refine Entails.trans (Entails.of_eq ?_)
          (Entails.trans hok
            (Entails.sepExists_right g' (Entails.pure_right ⟨rfl, hj.wrOk⟩ (Entails.refl _))))
        simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl
      have hloc_rejoin := j_join_rejoin_locals_jp fsp outCap outPtr outLen ws
      refine j_sepWPp_weaken_pre_jp ?_
        (j_epi_jp (a' := a') hrf h64 hs_e (htr_e ▸ hj.trace)
          (j_hist_of_eq_jp htr_e (congrArg FsState.files hfs_e) hj.hist)
          (Option.some_ne_none _) hj.ans.symm)
      rw [hstk_split]
      refine Entails.trans (Entails.of_eq (show _ =
        ((g.res ↦ₛ payload) ∗ storesHeap A ws g' ∗ ownedBytes A outCap outPtr outLen out) ∗
        (memRegion fsp 0x208 ∗ ((fsp + 0x208#64) ↦₆₄ outCap) ∗ ((fsp + 0x210#64) ↦₆₄ outPtr) ∗
          ((fsp + 0x218#64) ↦₆₄ outLen) ∗ memRegion (fsp + 0x220#64) 0x2b0 ∗
          ((fsp + 0x4d0#64) ↦ₛ payload) ∗ memRegion (fsp + 0x628#64) (runLocalBytes - 0x628)) ∗
        (memRegion g.call 56 ∗ memRegion g.stores 320 ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
          memRegion (fsp - BitVec.ofNat 64 (resStack - runFrame)) (resStack - runFrame - extHookStack) ∗
          stackAt fsp extHookStack ∗ A.pool ∗ anyHeap) by dsimp only [payload]; ac_rfl)) ?_
      refine Entails.trans (sepConj_mono hres_repack (sepConj_mono_left hloc_rejoin)) ?_
      exact Entails.of_eq (by dsimp only [fsp]; ac_rfl)

/-! ## Top-Level `run_hop_join_placed_ok` -/

theorem run_hop_join_placed_ok [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {A : RustAlloc} {H : LibsignalHooks} {B : RunBudgets}
    {S : RunSem} {needs : RunNeeds} {resStack : Nat} :
    RunHopJoinPlaced CodeOk A H B S needs resStack := by
  intro g s0 s P Qp hh hres hres64 hstate
  have hbnds := runNeed_bounds_placed hres hres64
  have hrf : runFrame ≤ resStack := by omega
  have h96 : 96 + extHookStack ≤ resStack - runFrame := by omega
  have hext_sub : extHookStack ≤ resStack - runFrame := by omega
  have hext : extHookStack ≤ resStack := by omega
  have hsub64 : resStack - runFrame ≤ 2 ^ 64 := by omega
  have h64 : resStack ≤ 2 ^ 64 := by omega
  rcases hstate with ⟨g', out, hj, rfl⟩ | ⟨g', rk, hr, rfl⟩
  · exact j_join_jp hh hrf hext_sub hsub64 h64 hj
  · cases rk with
    | preDispatch => exact j_rejPre_jp hh hrf h96 hext_sub hsub64 hext h64 hr
    | postDispatch => exact j_rejPost_jp hh hrf h96 hsub64 h64 hr

end CryptoVerification.SignalSession.Cli.RunCompose
