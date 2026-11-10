/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ModelBridge
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `signal_session::run` Arm `R1c` Placed Helpers

Relocatable (`[LibsignalPlacement]`) framing, call, deallocation, and layout helpers for
`run_hop_init3_placed_ok` on Block `579` (`runProgPlaced H`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.RunCompose.R1cPlacedHelpers

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.SignalSession.Cli.RunDrop
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon

abbrev R1cCodeOk [LibsignalPlacement] : Memory → Prop :=
  LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl

theorem r1c_perm {P P' Q : SepProp} (h : P' ⊢ Q) (heq : P = P') : P ⊢ Q :=
  heq ▸ h

theorem r1c_perm_post {P Q' Q : SepProp} (h : P ⊢ Q') (heq : Q' = Q) : P ⊢ Q :=
  heq ▸ h

theorem r1c_rewrite_front {A B : SepProp} (R : SepProp) {P Q : SepProp}
    (hab : A ⊢ B) (h1 : P = A ∗ R) (h2 : B ∗ R = Q) : P ⊢ Q :=
  h2 ▸ h1 ▸ sepConj_mono_left hab

theorem r1c_stackAt_split_ge (sp : BitVec 64) {k n : Nat}
    (hle : k ≤ n) (hn : n ≤ 2 ^ 64) :
    stackAt sp n = memRegion (sp - BitVec.ofNat 64 n) (n - k) ∗ stackAt sp k := by
  have h := ProofLib.stackAt_split_bottom sp k (n - k) (by omega)
  rwa [Nat.add_sub_of_le hle] at h

theorem r1c_split_at (fsp : BitVec 64) (a m c : Nat)
    (hm : a + m ≤ c) (hc : c ≤ runLocalBytes) :
    memRegion (fsp + BitVec.ofNat 64 a) (c - a) =
      memRegion (fsp + BitVec.ofNat 64 a) m ∗
        memRegion (fsp + BitVec.ofNat 64 (a + m)) (c - (a + m)) := by
  have hlb : runLocalBytes = 0x29f0 := rfl
  have hs := ProofLib.memRegion_split (fsp + BitVec.ofNat 64 a) m (c - (a + m)) (by omega)
  have hl : m + (c - (a + m)) = c - a := by omega
  have ha : fsp + BitVec.ofNat 64 a + BitVec.ofNat 64 m = fsp + BitVec.ofNat 64 (a + m) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  simpa only [hl, ha] using hs

theorem r1c_sepWPp_weaken_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hP : P ⊢ P') (h : SepWPp prog ret s P' Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  exact h R (Satisfies.mono (sepConj_mono_left hP) hm) hL

theorem r1c_sepWPp_exists_left {α : Sort _} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x : α, SepWPp prog ret s (P x) Q Qp oom) :
    SepWPp prog ret s (∃∗ x, P x) Q Qp oom := by
  intro R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨x, hx⟩ := hm
  exact h x R hx hL

theorem r1c_sepWPp_pure_left {P0 : Prop} {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : P0 → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s (⌜P0⌝ ∗ P) Q Qp oom := by
  intro R hm hL
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL


theorem r1c_frame_seq [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P_in P P' F : SepProp} {post : State → Prop}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : R1cCodeOk s.mem) (hP : P_in ⊢ P ∗ F)
    (h : SepWP prog mid s P (fun s1 P1 => post s1 ∧ P1 = P') (fun _ => ⌜False⌝))
    (hk : ∀ s1 : State, R1cCodeOk s1.mem → s1.pc = mid → s1.status = .Running → post s1 →
      SepWPp prog ret s1 (P' ∗ F) Q Qp oom) :
    SepWPp prog ret s P_in Q Qp oom := by
  intro R hm hL
  have hm0 : s.mem ⊨ P ∗ (F ∗ R) :=
    by simpa only [sepConj_assoc] using Satisfies.mono (sepConj_mono_left hP) hm
  rcases h.elim hm0 hL with ⟨s1, hsteps, ⟨hpc1, hrun1, P1, hm1, hpost1, rfl⟩ | ⟨_, hfalse⟩⟩
  · obtain ⟨sf, hsteps2, hout⟩ :=
      hk s1 (hinv.of_keepsFrozen hsteps.keepsFrozen) hpc1 hrun1 hpost1 R
        (by simpa only [sepConj_assoc] using hm1) (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps2, hout⟩
  · exact (not_satisfies_false_sepConj hfalse).elim

theorem r1c_call_lscro [LibsignalPlacement] {α : Type} {prog : Program}
    {callee retAddr ret : BitVec 64} {spec : Spec α} {s0 s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (x : α)
    (hcall : subroutine_ok prog callee
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec))
    (hinv : R1cCodeOk s.mem)
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
      R1cCodeOk sm.mem →
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
      s.mem ⊨ (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec).pre x s ∗ (F ∗ R) :=
    satisfies_lscro_pre hinv hm_pre
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hpre hsp hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ |
      ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps (hinv.of_keepsFrozen hsteps.keepsFrozen) hpcm hrunm hspm hcsm R hpost
        (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, spec.onPanic x s sm ∗ F,
      by simpa only [sepConj_assoc] using hpost,
      hpanic sm (F ∗ R) hpan hpost⟩)⟩
  · exact (hexit sm code (F ∗ R) hex hpost).elim
  · dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_s, hoom sm R hoom_s hpost⟩)⟩

theorem r1c_dealloc_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
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

theorem r1c_spAligned {s0 s : State} (h0 : s0.spAligned = true)
    (hsp : s.sp = runFsp s0) : s.spAligned = true := by
  have h1 : ((s0.sp - 0x2a50#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x2a50#64 h0
  show (s.sp &&& 15#64 == 0#64) = true; rwa [hsp]

theorem r1c_hist_of_eq {i : Inputs} {s0 s s' : State}
    (htr : s'.trace = s.trace) (hfs : s'.fs.files = s.fs.files)
    (h : RunHistOk i s0 s) : RunHistOk i s0 s' :=
  ⟨hfs.trans h.1, by rw [htr]; exact h.2⟩

theorem r1c_files_of_trace_eq {P : Program} (hP : TraceFsSound P) {s sm : State}
    (hsteps : Steps P s sm) (htr : sm.trace = s.trace) : sm.fs.files = s.fs.files :=
  hP.files_eq hsteps (by rw [htr]; simp) NoFsEv.nil

theorem r1c_call_dealloc [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {s0 s1 : State}
    {ptr : BitVec 64} {sz resStack retOff : Nat} {Rest : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hsp0 : s0.spAligned = true)
    (hinv1 : R1cCodeOk s1.mem)
    (hpc1 : s1.pc = lsρ lsRustDeallocSymCli)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = runFsp s0)
    (hlr1 : s1.readReg64 .lr = runPcPlaced retOff)
    (hx0 : s1.readReg64 .x0 = ptr)
    (hx1 : (s1.readReg64 .x1).toNat = sz)
    (hx2 : s1.readReg64 .x2 = 1#64)
    (hlay : LayoutOk sz 1)
    (hnext : ∀ s2 : State,
      R1cCodeOk s2.mem → s2.pc = runPcPlaced retOff → s2.status = .Running →
      s2.sp = runFsp s0 → CalleeSavedPreserved s1 s2 →
      s2.fs = s1.fs → s2.trace = s1.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
        (stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ Rest) Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s1
      ((A.live ptr sz 1 ∗ memRegion ptr sz) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ Rest) Q Qp (runOom s0) := by
  refine r1c_call_lscro (s0 := s0)
    (F := memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
      (resStack - runFrame - extHookStack) ∗ Rest)
    (ptr, sz, 1) (r1c_dealloc_ok hh) hinv1 hpc1 hrun1
    (r1c_spAligned hsp0 hsp1) hlr1 ?_
    (hnext := fun s2 _ hinv2 hpc2 hrun2 hsp2 hcs2 => ?_)
  · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
    rw [hsp1, r1c_stackAt_split_ge (runFsp s0) hext_le hsub64]
    conv => rhs; rw [sepConj_assoc]
    refine Entails.pure_right ⟨hx0, hx1, by rw [hx2]; rfl, hlay⟩ ?_
    exact Entails.of_eq (by ac_rfl)
  · refine r1c_sepWPp_weaken_pre
      (P' := ⌜s2.fs = s1.fs ∧ s2.trace = s1.trace⌝ ∗
        (stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ Rest))
      (by
        dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
        rw [hsp1, r1c_stackAt_split_ge (runFsp s0) hext_le hsub64]
        simp only [← sepConj_assoc, pure_sepConj_pure]
        exact Entails.of_eq (by ac_rfl)) ?_
    apply r1c_sepWPp_pure_left; rintro ⟨hfs2, htr2⟩
    exact hnext s2 hinv2 hpc2 hrun2 (hsp2.trans hsp1) hcs2 hfs2 htr2

theorem r1c_extractLsb_append_lo (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by bv_bits
theorem r1c_extractLsb_append_hi (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by bv_bits
theorem r1c_calleeSavedVRegs_q0 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 0#5 v) = calleeSavedVRegs s := by
  simp [calleeSavedVRegs, State.writeVReg128, VRegFile.calleeSaved, VRegFile.write, VRegFile.read]
theorem r1c_calleeSavedVRegs_q1 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 1#5 v) = calleeSavedVRegs s := by
  simp [calleeSavedVRegs, State.writeVReg128, VRegFile.calleeSaved, VRegFile.write, VRegFile.read]
theorem r1c_calleeSavedVRegs_q2 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 2#5 v) = calleeSavedVRegs s := by
  simp [calleeSavedVRegs, State.writeVReg128, VRegFile.calleeSaved, VRegFile.write, VRegFile.read]
theorem r1c_calleeSavedVRegs_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    calleeSavedVRegs (s.writeReg64 r v) = calleeSavedVRegs s := by cases s; cases r <;> rfl
theorem r1c_calleeSavedVRegs_setPC (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by cases s; rfl
theorem r1c_calleeSavedVRegs_setMem (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl
theorem r1c_calleeSavedVRegs_setPState (s : State) (ps : PState) :
    calleeSavedVRegs (s.setPState ps) = calleeSavedVRegs s := by cases s; rfl
theorem r1c_readReg64_setPState (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
theorem r1c_sp_setPState (s : State) (ps : PState) :
    (s.setPState ps).sp = s.sp := by cases s; rfl
theorem r1c_mem_setPState (s : State) (ps : PState) :
    (s.setPState ps).mem = s.mem := by cases s; rfl
theorem r1c_status_setPState (s : State) (ps : PState) :
    (s.setPState ps).status = s.status := by cases s; rfl
theorem r1c_trace_setPState (s : State) (ps : PState) :
    (s.setPState ps).trace = s.trace := by cases s; rfl
theorem r1c_symtab_setPState (s : State) (ps : PState) :
    (s.setPState ps).symtab = s.symtab := by cases s; rfl
theorem r1c_fs_setPState (s : State) (ps : PState) :
    (s.setPState ps).fs = s.fs := by cases s; rfl
theorem r1c_fs_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).fs = s.fs := by cases s; cases r <;> rfl
theorem r1c_fs_writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).fs = s.fs := by cases s; rfl
theorem r1c_fs_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).fs = s.fs := by cases s; rfl
theorem r1c_fs_setMem (s : State) (m : Memory) :
    (s.setMem m).fs = s.fs := by cases s; rfl

theorem r1c_ownedBytes_entails_nameHeap (A : RustAlloc) (cap ptr len : BitVec 64)
    (bs : List (BitVec 8)) :
    ownedBytes A cap ptr len bs ⊢
      ⌜len = BitVec.ofNat 64 bs.length⌝ ∗
        addrNameHeap A ⟨⟨cap, ptr, bs⟩, 0#8⟩ := by
  unfold ownedBytes addrNameHeap
  apply Entails.pure_left; rintro ⟨hlen, hle, hlt, hne⟩
  exact Entails.pure_right hlen (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))

theorem r1c_nameHeap_dealloc (A : RustAlloc) (g : AddrGhost) (hcap : g.name.cap ≠ 0) :
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

theorem r1c_nameHeap_zero (A : RustAlloc) (g : AddrGhost) (hcap : g.name.cap = 0) :
    addrNameHeap A g ⊢ emp := by
  unfold addrNameHeap
  simp only [hcap, ↓reduceIte]
  exact Entails.pure_left fun _ => Entails.refl emp

theorem r1c_empty_vecU8 (A : RustAlloc) (a : BitVec 64) :
    ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64)) ⊢
      vecU8 A a [] := by
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 1#64 ?_)
  dsimp only [vecU8At, vecHeader, List.length_nil]
  have hp : ([] : List (BitVec 8)).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0 := by decide
  have h0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [h0, ↓reduceIte, sepConj_emp, sepConj_assoc]
  exact r1c_perm_post (Entails.pure_right hp (Entails.refl _)) (by ac_rfl)

structure r1c_W6 where
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  w4 : BitVec 64
  w5 : BitVec 64

def r1c_slot6 (a : BitVec 64) (e : r1c_W6) : SepProp :=
  (a ↦₆₄ e.w0) ∗ ((a + 8#64) ↦₆₄ e.w1) ∗ ((a + 16#64) ↦₆₄ e.w2) ∗
    ((a + 24#64) ↦₆₄ e.w3) ∗ ((a + 32#64) ↦₆₄ e.w4) ∗ ((a + 40#64) ↦₆₄ e.w5)

theorem r1c_mem48_to_slot6 (a : BitVec 64) :
    memRegion a 48 ⊢ ∃∗ e : r1c_W6, r1c_slot6 a e := by
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
    (by dsimp only [r1c_slot6]; exact Entails.of_eq (by ac_rfl))

theorem r1c_slot6_to_mem48 (a : BitVec 64) (e : r1c_W6) :
    r1c_slot6 a e ⊢ memRegion a 48 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 40) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 32) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 24) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 16) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 8) (b' := a + 40#64) rfl (by bv_omega) (by decide)]
  dsimp only [r1c_slot6]
  exact Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (pointsTo64_entails_memRegion _ _))))))

theorem r1c_with_speOwned_words6 {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {src dst : BitVec 64} {k : RunDrop.SpeOwned} {Rest : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hk : ∀ (sw : r1c_W6) (Hspe : SepProp),
      sw.w0 + 3#64 ≠ 0#64 → sw.w0 + 2#64 ≠ 0#64 →
      (r1c_slot6 dst sw ∗ Hspe ⊢ RunDrop.speOwnedAt A dst k) →
      SepWPp prog ret s (r1c_slot6 src sw ∗ Hspe ∗ Rest) Q Qp oom) :
    SepWPp prog ret s (RunDrop.speOwnedAt A src k ∗ Rest) Q Qp oom := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨w0, w1, w2, w3, w4, w5, Hspe, hw3, hw2, hm', hrest⟩ :=
    RunProofs.Initiate.Stage5Lemmas.speOwnedAt_words6 A src dst k (Rest ∗ R) s.mem hm
  have hm'' : s.mem ⊨ (r1c_slot6 src ⟨w0, w1, w2, w3, w4, w5⟩ ∗ Hspe ∗ Rest) ∗ R := by
    dsimp only [r1c_slot6]
    exact RunProofs.Initiate.Stage5Lemmas.sat_eq (by ac_rfl) hm'
  have hrest' : r1c_slot6 dst ⟨w0, w1, w2, w3, w4, w5⟩ ∗ Hspe ⊢ RunDrop.speOwnedAt A dst k := by
    dsimp only [r1c_slot6]
    exact Entails.trans (Entails.of_eq (by ac_rfl)) hrest
  exact hk ⟨w0, w1, w2, w3, w4, w5⟩ Hspe hw3 hw2 hrest' R hm'' hL

theorem r1c_addr_unpack (A : RustAlloc) (g : AddrGhost) (a : BitVec 64) :
    protocolAddressAt A g a ⊢
      (((a ↦₆₄ g.name.cap) ∗ ((a + 8#64) ↦₆₄ g.name.ptr) ∗ memRegion (a + 16#64) 16) ∗
        addrNameHeap A g) := by
  rw [protocolAddressAt_eq_parts]
  exact r1c_perm_post
    (r1c_perm
      (sepConj_mono (addrUpperAt_entails_memRegion (a + 16#64) g)
        (Entails.refl ((a ↦₆₄ g.name.cap) ∗ ((a + 8#64) ↦₆₄ g.name.ptr) ∗ addrNameHeap A g)))
      (by ac_rfl))
    (by ac_rfl)

theorem r1c_addr_to_mem32 (A : RustAlloc) (g : AddrGhost) (a : BitVec 64) :
    protocolAddressAt A g a ⊢ memRegion a 32 ∗ addrNameHeap A g := by
  refine Entails.trans (r1c_addr_unpack A g a) (sepConj_mono_left ?_)
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 24) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16) (b' := a + 16#64) rfl (by bv_omega) (by decide)]
  exact Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))

theorem r1c_cliBundleAt_unpack (a : BitVec 64) (b : BundleV)
    (spkSigPtr kpkSigPtr kpkPtr : BitVec 64) :
    cliBundleAt a b spkSigPtr kpkSigPtr kpkPtr ⊢
      memRegion a 192 ∗ memRegion spkSigPtr 64 ∗ memRegion kpkSigPtr 64 ∗
        memRegion kpkPtr 1568 := by
  dsimp only [cliBundleAt]
  apply Entails.sepExists_elim; intro opkId
  apply Entails.pure_left; rintro ⟨hspk64, hkpk64, hkpk1568, _⟩
  have hspkB : (b.spk.bytes.toList).length = 32 := by simp
  have hidB : (b.idKey.publicKey.bytes.toList).length = 32 := by simp
  have hopk32 : (match b.opk with
      | some (_, k) => (a + 157#64) ↦ₛ k.bytes.toList
      | none => memRegion (a + 157#64) 32) ⊢ memRegion (a + 157#64) 32 := by
    cases b.opk with
    | none => exact Entails.refl _
    | some pk =>
      have hpk : pk.2.bytes.toList.length = 32 := by simp
      simpa only [hpk] using ProofLib.pointsToBytes_entails_memRegion (a + 157#64) pk.2.bytes.toList
  have hm192 :
      (a ↦₆₄ 64#64) ∗ ((a + 8#64) ↦₆₄ spkSigPtr) ∗ ((a + 16#64) ↦₆₄ 64#64) ∗
        ((a + 24#64) ↦ₛ b.spk.bytes.toList) ∗ ((a + 56#64) ↦₃₂ b.spkId) ∗ memRegion (a + 60#64) 4 ∗
        ((a + 64#64) ↦₆₄ 64#64) ∗ ((a + 72#64) ↦₆₄ kpkSigPtr) ∗ ((a + 80#64) ↦₆₄ 64#64) ∗
        ((a + 88#64) ↦₆₄ kpkPtr) ∗ ((a + 96#64) ↦₆₄ 1568#64) ∗
        ((a + 104#64) ↦₃₂ b.kpkId) ∗ memRegion (a + 108#64) 4 ∗
        ((a + 112#64) ↦₃₂ (if b.opk.isSome then 1#32 else 0#32)) ∗ ((a + 116#64) ↦₃₂ opkId) ∗
        ((a + 120#64) ↦ₛ b.idKey.publicKey.bytes.toList) ∗ ((a + 152#64) ↦₃₂ b.regId) ∗
        ((a + 156#64) ↦₈ (if b.opk.isSome then 1#32 else 0#32).truncate 8) ∗
        (match b.opk with
         | some (_, k) => (a + 157#64) ↦ₛ k.bytes.toList
         | none => memRegion (a + 157#64) 32) ∗
        ((a + 189#64) ↦₈ b.device) ∗ memRegion (a + 190#64) 2 ⊢ memRegion a 192 := by
    rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 184) (b' := a + 8#64) rfl rfl (by decide),
        ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 176) (b' := a + 16#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 168) (b' := a + 24#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 24#64) (n := 32) (k := 136) (b' := a + 56#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 56#64) (n := 4) (k := 132) (b' := a + 60#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 60#64) (n := 4) (k := 128) (b' := a + 64#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 64#64) (n := 8) (k := 120) (b' := a + 72#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 72#64) (n := 8) (k := 112) (b' := a + 80#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 80#64) (n := 8) (k := 104) (b' := a + 88#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 88#64) (n := 8) (k := 96) (b' := a + 96#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 96#64) (n := 8) (k := 88) (b' := a + 104#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 104#64) (n := 4) (k := 84) (b' := a + 108#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 108#64) (n := 4) (k := 80) (b' := a + 112#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 112#64) (n := 4) (k := 76) (b' := a + 116#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 116#64) (n := 4) (k := 72) (b' := a + 120#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 120#64) (n := 32) (k := 40) (b' := a + 152#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 152#64) (n := 4) (k := 36) (b' := a + 156#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 156#64) (n := 1) (k := 35) (b' := a + 157#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 157#64) (n := 32) (k := 3) (b' := a + 189#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 189#64) (n := 1) (k := 2) (b' := a + 190#64) rfl (by bv_omega) (by decide)]
    exact r1c_perm_post
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (by simpa only [hspkB] using ProofLib.pointsToBytes_entails_memRegion (a + 24#64) b.spk.bytes.toList)
      (sepConj_mono (ProofLib.pointsTo32_entails_memRegion _ _)
      (sepConj_mono (Entails.refl _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo32_entails_memRegion _ _)
      (sepConj_mono (Entails.refl _)
      (sepConj_mono (ProofLib.pointsTo32_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo32_entails_memRegion _ _)
      (sepConj_mono (by simpa only [hidB] using ProofLib.pointsToBytes_entails_memRegion (a + 120#64) b.idKey.publicKey.bytes.toList)
      (sepConj_mono (ProofLib.pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo8_entails_memRegion _ _)
      (sepConj_mono hopk32
      (sepConj_mono (pointsTo8_entails_memRegion _ _) (Entails.refl _)))))))))))))))))))))
      (by ac_rfl)
  have h1 : (spkSigPtr ↦ₛ b.spkSig) ⊢ memRegion spkSigPtr 64 := by
    simpa only [hspk64] using ProofLib.pointsToBytes_entails_memRegion spkSigPtr b.spkSig
  have h2 : (kpkSigPtr ↦ₛ b.kpkSig) ⊢ memRegion kpkSigPtr 64 := by
    simpa only [hkpk64] using ProofLib.pointsToBytes_entails_memRegion kpkSigPtr b.kpkSig
  have h3 : (kpkPtr ↦ₛ b.kpk) ⊢ memRegion kpkPtr 1568 := by
    simpa only [hkpk1568] using ProofLib.pointsToBytes_entails_memRegion kpkPtr b.kpk
  exact r1c_perm_post
    (r1c_perm
      (sepConj_mono hm192 (sepConj_mono h1 (sepConj_mono h2 h3)))
      (by ac_rfl))
    (by ac_rfl)

def r1c_lowGaps (fsp : BitVec 64) : SepProp :=
  memRegion fsp 0x110 ∗ memRegion (fsp + 0x118#64) 8 ∗ memRegion (fsp + 0x128#64) 16 ∗
    memRegion (fsp + 0x148#64) 16 ∗ memRegion (fsp + 0x160#64) 24 ∗ memRegion (fsp + 0x180#64) 56

def r1c_lowCells (fsp : BitVec 64) (d : Init2Data) : SepProp :=
  ((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64) ∗
    ((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗
    ((fsp + 0x158#64) ↦₆₄ 64#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr) ∗
    ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗
    ((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ∗
    r1c_lowGaps fsp

theorem r1c_lowCells_to_mem1d0 (fsp : BitVec 64) (d : Init2Data) :
    r1c_lowCells fsp d ⊢ memRegion fsp 0x1d0 := by
  dsimp only [r1c_lowCells, r1c_lowGaps]
  rw [ProofLib.memRegion_split' (b := fsp) (n := 0x110) (k := 192) (b' := fsp + 0x110#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x110#64) (n := 8) (k := 184) (b' := fsp + 0x118#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x118#64) (n := 8) (k := 176) (b' := fsp + 0x120#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x120#64) (n := 8) (k := 168) (b' := fsp + 0x128#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x128#64) (n := 16) (k := 152) (b' := fsp + 0x138#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x138#64) (n := 8) (k := 144) (b' := fsp + 0x140#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x140#64) (n := 8) (k := 136) (b' := fsp + 0x148#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x148#64) (n := 16) (k := 120) (b' := fsp + 0x158#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x158#64) (n := 8) (k := 112) (b' := fsp + 0x160#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x160#64) (n := 24) (k := 88) (b' := fsp + 0x178#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x178#64) (n := 8) (k := 80) (b' := fsp + 0x180#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x180#64) (n := 56) (k := 24) (b' := fsp + 0x1b8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x1b8#64) (n := 8) (k := 16) (b' := fsp + 0x1c0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x1c0#64) (n := 8) (k := 8) (b' := fsp + 0x1c8#64) rfl (by bv_omega) (by decide)]
  exact r1c_perm
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo64_entails_memRegion _ _)))))))))))))))
    (by ac_rfl)

def r1c_okCore (A : RustAlloc) (g : RunCall) (g' : StoresGhost) (s0 : State) : SepProp :=
  memRegion g.res runResSize ∗ memRegion g.call 56 ∗
    storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ anyHeap

def r1c_errCore (A : RustAlloc) (g : RunCall) (g' : StoresGhost) (s0 : State) : SepProp :=
  runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
    storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ anyHeap

def r1c_lowNoDir (fsp : BitVec 64) (d : Init2Data) : SepProp :=
  ((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64) ∗
    ((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗
    ((fsp + 0x158#64) ↦₆₄ 64#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr) ∗
    ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗ r1c_lowGaps fsp

def r1c_lowNoMePtr (fsp : BitVec 64) (d : Init2Data) : SepProp :=
  ((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64) ∗
    ((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗
    ((fsp + 0x158#64) ↦₆₄ 64#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr) ∗
    ((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ∗ r1c_lowGaps fsp

theorem r1c_init2Locals_unpack (A : RustAlloc) (fsp : BitVec 64) (d : Init2Data) :
    runLocals fsp (init2Cells A fsp d) ⊢
      (fsp ↦₃₂ 0#32) ∗
      protocolAddressAt A d.peerG (fsp + 0x2a0#64) ∗
      protocolAddressAt A d.meG (fsp + 0x320#64) ∗
      cliBundleAt (fsp + 0x4d0#64) d.bundle d.spkSigPtr d.kpkSigPtr d.kpkPtr ∗
      memRegion (fsp + 0x23b0#64) 48 ∗
      (memRegion (fsp + 4#64) (0x110 - 4) ∗
        ((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64) ∗
        ((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗
        ((fsp + 0x158#64) ↦₆₄ 64#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr) ∗
        ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗
        ((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ∗
        memRegion (fsp + 0x118#64) 8 ∗ memRegion (fsp + 0x128#64) 16 ∗
        memRegion (fsp + 0x148#64) 16 ∗ memRegion (fsp + 0x160#64) 24 ∗
        memRegion (fsp + 0x180#64) 56) ∗
      memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
      (memRegion (fsp + 0x2c0#64) (0x320 - 0x2c0) ∗
        memRegion (fsp + 0x340#64) (0x4d0 - 0x340) ∗
        memRegion (fsp + 0x590#64) (0x23b0 - 0x590)) ∗
      memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0) := by
  dsimp only [runLocals, runLocalsFrom, init2Cells]
  simp only [Nat.reduceAdd, Nat.reduceSub, ProofLib.memRegion_zero,
    emp_sepConj, sepConj_emp, BitVec.ofNat_eq_ofNat]
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SignalSession.Cli.RunCompose.R1cPlacedHelpers
