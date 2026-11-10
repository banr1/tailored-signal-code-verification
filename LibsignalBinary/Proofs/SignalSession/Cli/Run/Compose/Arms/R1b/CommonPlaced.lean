/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.Common
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3Helpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.Layout

/-!
# Relocatable Call, Stack-Frame, and Semantic Helpers for Arm `R1b`

Relocatable (`[LibsignalPlacement]`) counterparts of `R1b.Common` on Block `579`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Arm64.Process
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon

abbrev r1b_CodeOk [LibsignalPlacement] : Memory → Prop :=
  LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl

theorem r1b_lscro_of_rocl [LibsignalPlacement] {α : Type} {prog : Program} {callee : BitVec 64}
    {spec : Spec α}
    (h : subroutine_ok prog callee (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl spec)) :
    subroutine_ok prog callee (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) ?_ (fun _ _ _ _ hp => hp)
  intro x R s0 sf hpost
  dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

theorem r1b_shimFs_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hh : RunHooksPlaced A H) :
    subroutine_ok (runProgPlaced H) (lsρ lsRustNoAllocShimSymCli)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (withStack sessionShimSpec extHookStack).keepsFs) :=
  r1b_lscro_of_rocl (AllocContractsFsPlaced.shim_rocl (prog := runProgPlaced H) (i := 579) hh.allocFs)

theorem r1b_allocFs_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hh : RunHooksPlaced A H) :
    subroutine_ok (runProgPlaced H) (lsρ lsRustAllocSymCli)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (rustAllocSpecWithStack A extHookStack).keepsFs) :=
  r1b_lscro_of_rocl (AllocContractsFsPlaced.alloc_rocl (prog := runProgPlaced H) (i := 579) hh.allocFs)

theorem r1b_deallocFs_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hh : RunHooksPlaced A H) :
    subroutine_ok (runProgPlaced H) (lsρ lsRustDeallocSymCli)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (rustDeallocExternSpecWithStack A extHookStack).keepsFs) :=
  r1b_lscro_of_rocl (AllocContractsFsPlaced.dealloc_rocl (prog := runProgPlaced H) (i := 579) hh.allocFs)

theorem r1b_memcpyFs_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hh : RunHooksPlaced A H) :
    subroutine_ok (runProgPlaced H) (lsρ lsMemcpySym)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (sessionMemcpySpec extHookStack).keepsFs) :=
  r1b_lscro_of_rocl
    (AllocContractsFsPlaced.session_memcpy_rocl (prog := runProgPlaced H) (i := 579) hh.allocFs)

theorem r1b_memcpyRegionFs_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hh : RunHooksPlaced A H) :
    subroutine_ok (runProgPlaced H) (lsρ lsMemcpySym)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (withStack sessionMemcpyRegionSpec extHookStack).keepsFs) :=
  r1b_lscro_of_rocl
    (AllocContractsFsPlaced.session_memcpy_region_rocl (prog := runProgPlaced H) (i := 579) hh.allocFs)

theorem r1b_panic_handle_error_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hh : RunHooksPlaced A H) :
    (runProgPlaced H).externAt? (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") =
      some Rust.panicked :=
  ls_panicAt_of_cliPanic (prog := runProgPlaced H) (i := 579) hh.panics
    (sym := "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")

theorem r1b_files_eq_of_trace_eq_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hh : RunHooksPlaced A H)
    {s sf : State} (hsteps : Steps (runProgPlaced H) s sf)
    (htr : sf.trace = s.trace) :
    sf.fs.files = s.fs.files :=
  (hh.fs (runProgPlaced H) 579).files_eq hsteps (by simp [htr] : sf.trace = s.trace ++ []) NoFsEv.nil

theorem r1b_bind_state_placed [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s' : State} {P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ sm : State, sm = s' → r1b_CodeOk sm.mem → SepWPp prog ret sm P' Q Qp oom) :
    r1b_CodeOk s'.mem → SepWPp prog ret s' P' Q Qp oom :=
  fun hinv => h s' rfl hinv

theorem r1b_stackBounds_of_placed [LibsignalPlacement] {A : RustAlloc} {B : RunBudgets}
    {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (hres : runNeed B (slotsOfPlaced A S needs) ≤ resStack) (hres63 : resStack ≤ 2 ^ 63) :
    r1b_StackBounds B resStack := by
  have hb := runNeed_bounds_placed hres hres63
  exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2.1, hb.2.2.2.2.2.2.1,
    hb.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2.1,
    hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem r1b_init_path_facts_placed [LibsignalPlacement] {CodeOk : Memory → Prop} {S : RunSem}
    {g : RunCall} {peerV : AddrV} {dir : Bytes} {s0 : State}
    (he : AtRunEntryPlaced CodeOk S g s0) (hc : g.c = .init peerV dir) :
    dir.length < 2 ^ 32 ∧
      (∀ name ∈ bundleNames,
        cliWrOk (dir ++ [0x2f#8] ++ utf8 name) ∧
          (dir ++ [0x2f#8] ++ utf8 name).length < 2 ^ 32) := by
  have hall := he.init_bundlePaths_ok hc
  have hreg := hall "registration-id" (by simp [bundleNames])
  have hreg_len : (dir ++ [0x2f#8] ++ utf8 "registration-id").length < 2 ^ 32 := hreg.2
  simp only [List.length_append] at hreg_len
  refine ⟨by omega, fun name hmem => ?_⟩
  have hn := hall name hmem
  exact ⟨hn, hn.2⟩

theorem r1b_reject_of_readBundle_none_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    {S : RunSem} {g : RunCall} {d1 : Init1Data} {s0 s1 : State}
    (he : AtRunEntryPlaced CodeOk S g s0)
    (hi1 : AtInit1Placed CodeOk g d1 s0 s1)
    (hnone : readBundleV (runFiles g.i) d1.dir d1.peerV.device = none) :
    g.a = some none := by
  rcases hi1.ownSem with ⟨ownB, hget, hme⟩
  have hparse : parseArgs uuidTryParse (g.i.argv.map Process.bytesOfString) =
      some (.init d1.peerV d1.dir) :=
    hi1.callEq ▸ he.parse
  rw [he.rel.2.2.2.2.2]
  unfold runAns
  rw [hparse]
  simp [hget, hme, hnone]

theorem r1b_call_placed [LibsignalPlacement] {α : Type} {H : LibsignalHooks}
    {callee ret_pc ret : BitVec 64} {spec : Spec α} {g : RunCall} {s0 s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (x : α)
    (hcall : subroutine_ok (runProgPlaced H) callee
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec))
    (hinv : r1b_CodeOk s.mem)
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpanicK : PanicK g s0 Qp)
    (hP : P ⊢ spec.pre x s ∗ (F ∗ emp))
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') →
      runPanicProp g s0 sf := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ runOom s0 sf ∗ R') := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sf : State,
      Steps (runProgPlaced H) s sf →
      r1b_CodeOk sf.mem →
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      SepWPp (runProgPlaced H) ret sf (spec.post x s sf ∗ F) Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) ret s P Q Qp (runOom s0) := by
  intro R hm hL
  have hm_pre : s.mem ⊨ spec.pre x s ∗ (F ∗ R) := by
    have h1 := Satisfies.mono (sepConj_mono_left hP) hm
    simpa only [sepConj_emp, sepConj_assoc] using h1
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
      hpanicK sm _ (hpanic sm (F ∗ R) hpan hpost)⟩)⟩
  · exact (hexit sm code (F ∗ R) hex hpost).elim
  · dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_s, hoom sm R hoom_s hpost⟩)⟩

theorem r1b_handle_error_panic_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {ret : BitVec 64} {g : RunCall} {s0 s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hpc : s.pc = lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
    (hrun : s.status = .Running)
    (hpanicK : PanicK g s0 Qp)
    (hfail : allocFailedIn s0 s) :
    SepWPp (runProgPlaced H) ret s P Q Qp (runOom s0) := by
  intro R hm _
  let s1 := Rust.panicked s
  have hstep : Step (runProgPlaced H) s s1 :=
    Step.extern hrun (hpc ▸ r1b_panic_handle_error_placed hh) (Memory.KeepsFrozen.refl s.mem) rfl
  exact ⟨s1, Steps.step hstep (Steps.refl s1), Or.inr (Or.inl ⟨rfl, P, hm,
    hpanicK s1 P (Or.inr hfail)⟩)⟩

theorem r1b_call_dealloc_ownedBytes_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets} {g : RunCall} {s0 st_bl : State}
    {resStack retOff : Nat}
    {cap ptr len : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hbnd : r1b_StackBounds B resStack)
    (hinv : r1b_CodeOk st_bl.mem)
    (hpc : st_bl.pc = lsρ lsRustDeallocSymCli)
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hx0 : st_bl.readReg64 .x0 = ptr)
    (hx1 : st_bl.readReg64 .x1 = cap)
    (hx2 : st_bl.readReg64 .x2 = 1#64)
    (hcap : cap ≠ 0#64)
    (hpanicK : PanicK g s0 Qp)
    (hnext : ∀ sf : State,
      InRunPlaced r1b_CodeOk s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      sf.fs = st_bl.fs →
      sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F)
        Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      (ownedBytes A cap ptr len bs ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F)
      Q Qp (runOom s0) := by
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  rw [M3Helpers.ownedBytes_pure A cap ptr len bs, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨_, _, hlt_cap, _⟩ => ?_
  set fsp := runFsp s0
  refine r1b_call_placed (ptr, cap.toNat, 1) (r1b_deallocFs_placed_ok hh) hinv hpc hrun hal_bl hlr hpanicK
    (F := memRegion (fsp - BitVec.ofNat 64 (resStack - runFrame))
      (resStack - runFrame - extHookStack) ∗ F) ?_ (hnext := ?_)
  · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
    have hpure : st_bl.readReg64 .x0 = ptr ∧ (st_bl.readReg64 .x1).toNat = cap.toNat ∧
        (st_bl.readReg64 .x2).toNat = 1 ∧ LayoutOk cap.toNat 1 := by
      refine ⟨hx0, by rw [hx1], by rw [hx2]; decide,
        ⟨Nat.pos_of_ne_zero fun h0 => hcap (BitVec.eq_of_toNat_eq (by simpa using h0)),
          ⟨0, rfl⟩, by omega⟩⟩
    rw [hsp]
    change ownedBytes A cap ptr len bs ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ F ⊢ _
    rw [BundleRead.Helpers.stackAt_split_sub fsp (resStack - runFrame) extHookStack
      hbnd.hook hbnd.sub64]
    refine Entails.trans (sepConj_mono_left (M3Helpers.ownedBytes_to_dealloc A hcap)) ?_
    conv => rhs; rw [sepConj_assoc, sepConj_emp]
    apply Entails.pure_right hpure
    exact Entails.of_eq (by ac_rfl)
  · intro sf _ hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun hfs_f => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun htr_f => ?_
    have hin_f : InRunPlaced r1b_CodeOk s0 sf retOff := {
      pc := hpc_f
      run := hrun_f
      sp := hsp_f.trans hsp
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp
      inv := hinv_f
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs
      spAligned := hsp0
    }
    refine MainHops.sepWPp_weaken_pre ?_ (hnext sf hin_f hcs_f hfs_f htr_f)
    rw [hsp, BundleRead.Helpers.stackAt_split_sub fsp (resStack - runFrame) extHookStack
      hbnd.hook hbnd.sub64]
    exact Entails.of_eq (by ac_rfl)

theorem r1b_call_dropSpeOwned_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets} {g : RunCall} {s0 st_bl : State}
    {resStack retOff : Nat}
    {a : BitVec 64} {k : RunDrop.SpeOwned} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hbnd : r1b_StackBounds B resStack)
    (hinv : r1b_CodeOk st_bl.mem)
    (hpc : st_bl.pc = lsmpl.base 553)
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPcPlaced retOff)
    (hx0 : st_bl.readReg64 .x0 = a)
    (hpanicK : PanicK g s0 Qp)
    (hnext : ∀ sf : State,
      InRunPlaced r1b_CodeOk s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (memRegion a 48 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F)
        Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) st_bl
      (RunDrop.speOwnedAt A a k ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F)
      Q Qp (runOom s0) := by
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  refine r1b_call_placed ⟨a, k⟩ (hdrop (resStack - runFrame) hbnd.dropSpe hbnd.sub64)
    hinv hpc hrun hal_bl hlr hpanicK (F := F) ?_ (hnext := ?_)
  · dsimp only [RunDrop.dropSpeOwnedSpec]
    rw [hsp]
    conv => rhs; rw [sepConj_assoc, sepConj_emp]
    apply Entails.pure_right hx0
    exact Entails.of_eq (by ac_rfl)
  · intro sf hsteps hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [RunDrop.dropSpeOwnedSpec]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun htr_f => ?_
    have hin_f : InRunPlaced r1b_CodeOk s0 sf retOff := {
      pc := hpc_f
      run := hrun_f
      sp := hsp_f.trans hsp
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp
      inv := hinv_f
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs
      spAligned := hsp0
    }
    have hfiles_f := r1b_files_eq_of_trace_eq_placed hh hsteps htr_f
    refine MainHops.sepWPp_weaken_pre ?_ (hnext sf hin_f hcs_f hfiles_f htr_f)
    rw [hsp]
    exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SignalSession.Cli.RunCompose
