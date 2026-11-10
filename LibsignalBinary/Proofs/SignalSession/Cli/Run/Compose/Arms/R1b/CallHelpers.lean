/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.Common
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSites
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3Helpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanup
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.SliceHelpers

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton

/-!
# Callee `SepWPp` Wrappers for Arm `R1b`

Typed `SepWPp` call wrappers isolating allocator, `memcpy`, `Dir::path`, `read_file`, and
`bundleRead` invocations in Arm `R1b`.
-/

theorem r1b_allocFailedIn_sub {s0 s1 s2 : State}
    (hp : s0.trace <+: s1.trace) (ha : allocFailedIn s1 s2) :
    allocFailedIn s0 s2 := by
  rcases hp with ⟨k, hk⟩
  dsimp only [allocFailedIn] at ha ⊢
  rw [← hk, List.length_append, ← List.drop_drop] at ha
  exact List.mem_of_mem_drop ha

theorem r1b_call_shim {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hinv : ImgCallInv img st_bl)
    (hpc : st_bl.pc = (mProg img ext).fnAddr runName +
      bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_cli::run"))
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPc img ext retOff)
    (hpanicK : PanicK g s0 Qp)
    (hnext : ∀ sf : State,
      InRun img ext s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      sf.fs = st_bl.fs →
      sf.trace = st_bl.trace →
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        (stackAt (runFsp s0) (resStack - runFrame) ∗ F) Q Qp (runOom s0)) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) st_bl
      (stackAt (runFsp s0) (resStack - runFrame) ∗ F) Q Qp (runOom s0) := by
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  have hsplit := BundleRead.Helpers.stackAt_split_sub (runFsp s0)
    (resStack - runFrame) extHookStack hbnd.hook hbnd.sub64
  rw [hsplit, sepConj_assoc]
  set subFrame := memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
    (resStack - runFrame - extHookStack)
  refine r1b_call () (r1b_shimFs_ok hh) hinv hpc hrun hal_bl hlr hpanicK
    (F := subFrame ∗ F) ?_ (hnext := ?_)
  · dsimp only [Spec.inImage, Spec.keepsFs, withStack, sessionShimSpec]
    simp only [hsp, emp_sepConj, sepConj_assoc]
    exact Entails.pure_right hinv (Entails.of_eq (by ac_rfl))
  · intro sf _ hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [Spec.inImage, Spec.keepsFs, withStack, sessionShimSpec]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hfs_f => SepWPp.pure_elim fun htr_f => ?_
    have hin_f : InRun img ext s0 sf retOff := {
      pc := hpc_f, run := hrun_f, sp := hsp_f.trans hsp,
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp, inv := hinv_f,
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs, spAligned := hsp0
    }
    refine MainHops.sepWPp_weaken_pre ?_ (hnext sf hin_f hcs_f hfs_f htr_f)
    rw [hsp, hsplit]; exact Entails.of_eq (by ac_rfl)

theorem r1b_call_alloc {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {s0 st_bl : State} {resStack retOff size align : Nat}
    {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hinv : ImgCallInv img st_bl)
    (hpc : st_bl.pc = (mProg img ext).fnAddr runName +
      bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_cli::run"))
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPc img ext retOff)
    (hx0 : (st_bl.readReg64 .x0).toNat = size)
    (hx1 : (st_bl.readReg64 .x1).toNat = align)
    (_hpos : 0 < size)
    (hlay : LayoutOk size align)
    (hpanicK : PanicK g s0 Qp)
    (hnull : ∀ sf : State,
      InRun img ext s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      sf.readReg64 .x0 = 0#64 →
      sf.fs = st_bl.fs →
      sf.trace = st_bl.trace ++ [allocFailedEvent] →
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        (stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F) Q Qp (runOom s0))
    (hok : ∀ (sf : State) (buf : BitVec 64),
      InRun img ext s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      sf.readReg64 .x0 = buf →
      buf ≠ 0#64 →
      sf.fs = st_bl.fs →
      sf.trace = st_bl.trace →
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        (A.live buf size align ∗ memRegion buf size ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F) Q Qp (runOom s0)) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) st_bl
      (stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F) Q Qp (runOom s0) := by
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  have hsplit := BundleRead.Helpers.stackAt_split_sub (runFsp s0)
    (resStack - runFrame) extHookStack hbnd.hook hbnd.sub64
  rw [hsplit]
  set subFrame := memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
    (resStack - runFrame - extHookStack)
  refine r1b_call (size, align) (r1b_allocFs_ok hh) hinv hpc hrun hal_bl hlr hpanicK
    (F := subFrame ∗ F) ?_ (hnext := ?_)
  · dsimp only [Spec.inImage, Spec.keepsFs, rustAllocSpecWithStack, withStack, rustAllocSpec]
    simp only [hsp, sepConj_assoc]
    apply Entails.pure_right hinv
    apply Entails.pure_right ⟨hx0, hx1, hlay⟩
    exact Entails.of_eq (by ac_rfl)
  · intro sf _ hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [Spec.inImage, Spec.keepsFs, rustAllocSpecWithStack, withStack, rustAllocSpec]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hfs_f => ?_
    have hin_f : InRun img ext s0 sf retOff := {
      pc := hpc_f, run := hrun_f, sp := hsp_f.trans hsp,
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp, inv := hinv_f,
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs, spAligned := hsp0
    }
    have hz : (0 : BitVec 64) = 0#64 := rfl
    rw [hz]
    by_cases h0 : sf.readReg64 .x0 = 0#64
    · simp only [h0, ↓reduceIte]
      have hcomm :
          (A.pool ∗ stackAt st_bl.sp extHookStack ∗
            ⌜sf.trace = st_bl.trace ++ [allocFailedEvent]⌝ ∗ subFrame ∗ F) =
          (⌜sf.trace = st_bl.trace ++ [allocFailedEvent]⌝ ∗
            (A.pool ∗ stackAt st_bl.sp extHookStack ∗ subFrame ∗ F)) := by ac_rfl
      rw [hcomm]
      refine SepWPp.pure_elim fun htr_f => ?_
      refine MainHops.sepWPp_weaken_pre ?_ (hnull sf hin_f hcs_f h0 hfs_f htr_f)
      rw [hsp, hsplit]; exact Entails.of_eq (by ac_rfl)
    · simp only [h0, ↓reduceIte, sepConj_assoc]
      have hcomm :
          (A.pool ∗ stackAt st_bl.sp extHookStack ∗
            ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = st_bl.trace⌝ ∗
            A.live (sf.readReg64 .x0) size align ∗
            memRegion (sf.readReg64 .x0) size ∗ subFrame ∗ F) =
          (⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = st_bl.trace⌝ ∗
            (A.pool ∗ stackAt st_bl.sp extHookStack ∗
              A.live (sf.readReg64 .x0) size align ∗
              memRegion (sf.readReg64 .x0) size ∗ subFrame ∗ F)) := by ac_rfl
      rw [hcomm]
      refine SepWPp.pure_elim fun hp => ?_
      rcases hp with ⟨_, htr_f⟩
      refine MainHops.sepWPp_weaken_pre ?_ (hok sf (sf.readReg64 .x0) hin_f hcs_f rfl h0 hfs_f htr_f)
      rw [hsp, hsplit]; exact Entails.of_eq (by ac_rfl)

theorem r1b_call_memcpy_ro {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {g : RunCall} {s0 st_bl : State} {retOff : Nat}
    {dst src : BitVec 64} {bs : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooks img A ext)
    (hinv : ImgCallInv img st_bl)
    (hro : ∀ {m : Memory} {R : SepProp}, img.RoDataLoaded m → (m ⊨ R) → (m ⊨ (src ↦ᵣ bs) ∗ R))
    (hpc : st_bl.pc = (mProg img ext).fnAddr runName +
      bv% (ls_off% "memcpy" - ls_off% "libsignal_cli::run"))
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPc img ext retOff)
    (hx0 : st_bl.readReg64 .x0 = dst)
    (hx1 : st_bl.readReg64 .x1 = src)
    (hx2 : (st_bl.readReg64 .x2).toNat = bs.length)
    (hlen : bs.length ≤ 2 ^ 64)
    (hpanicK : PanicK g s0 Qp)
    (hnext : ∀ sf : State,
      InRun img ext s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      sf.readReg64 .x0 = dst →
      sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        ((dst ↦ₛ bs) ∗ F) Q Qp (runOom s0)) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) st_bl
      (memRegion dst bs.length ∗ F) Q Qp (runOom s0) := by
  refine r1b_sepWPp_with_ro hinv hro ?_
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  have hmc_ok : subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr runName +
        bv% (ls_off% "memcpy" - ls_off% "libsignal_cli::run"))
      (SpqrV1.Alloc.sessionMemcpyRegionROSpec.inImage img) :=
    SpqrV1.Alloc.subroutine_ok_inImage img
      (SpqrV1.Alloc.session_memcpy_region_ro_ok_at hh.memcpyRO runName
        (num% (ls_off% "memcpy" - ls_off% "libsignal_cli::run"))
        (by rw [r1b_run_fnOff, MainHops.memcpyCallee_fnOff]))
  refine r1b_call (dst, src, bs) hmc_ok hinv hpc hrun hal_bl hlr hpanicK
    (F := F) ?_ (hnext := ?_)
  · change _ ⊢
      (⌜ImgCallInv img st_bl⌝ ∗
        ⌜st_bl.readReg64 .x0 = dst ∧ st_bl.readReg64 .x1 = src ∧
          (st_bl.readReg64 .x2).toNat = bs.length ∧ bs.length ≤ 2 ^ 64⌝ ∗
        memRegion dst bs.length ∗ (src ↦ᵣ bs)) ∗ (F ∗ emp)
    simp only [sepConj_assoc, sepConj_emp]
    apply Entails.pure_right hinv
    apply Entails.pure_right ⟨hx0, hx1, hx2, hlen⟩
    exact Entails.of_eq (by ac_rfl)
  · intro sf hsteps hinv_f hpc_f hrun_f hsp_f hcs_f
    change SepWPp (mProg img ext) (s0.readReg64 .lr) sf
      ((⌜sf.readReg64 .x0 = dst ∧ sf.trace = st_bl.trace⌝ ∗
        (dst ↦ₛ bs) ∗ (src ↦ᵣ bs)) ∗ F) Q Qp (runOom s0)
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hp => ?_
    rcases hp with ⟨hr0, htr_f⟩
    have hin_f : InRun img ext s0 sf retOff := {
      pc := hpc_f, run := hrun_f, sp := hsp_f.trans hsp,
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp, inv := hinv_f,
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs, spAligned := hsp0
    }
    have hfiles_f := r1b_files_eq_of_trace_eq hh.toExt hsteps htr_f
    refine MainHops.sepWPp_weaken_pre (P' := (src ↦ᵣ bs) ∗ ((dst ↦ₛ bs) ∗ F))
      (Entails.of_eq (by ac_rfl)) ?_
    exact r1b_sepWPp_drop_left (hnext sf hin_f hcs_f hr0 hfiles_f htr_f)

theorem r1b_call_memcpy_region {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {dst src : BitVec 64} {bs : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hinv : ImgCallInv img st_bl)
    (hpc : st_bl.pc = (mProg img ext).fnAddr runName +
      bv% (ls_off% "memcpy" - ls_off% "libsignal_cli::run"))
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPc img ext retOff)
    (hx0 : st_bl.readReg64 .x0 = dst)
    (hx1 : st_bl.readReg64 .x1 = src)
    (hx2 : (st_bl.readReg64 .x2).toNat = bs.length)
    (hpanicK : PanicK g s0 Qp)
    (hnext : ∀ sf : State,
      InRun img ext s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      sf.readReg64 .x0 = dst →
      sf.fs = st_bl.fs →
      sf.trace = st_bl.trace →
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ F) Q Qp (runOom s0)) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) st_bl
      (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ F) Q Qp (runOom s0) := by
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  have hsplit := BundleRead.Helpers.stackAt_split_sub (runFsp s0)
    (resStack - runFrame) extHookStack hbnd.hook hbnd.sub64
  rw [hsplit]
  set subFrame := memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
    (resStack - runFrame - extHookStack)
  have hmc_ok := hh.allocFs.session_memcpy_region_ok_at runName
    (num% (ls_off% "memcpy" - ls_off% "libsignal_cli::run"))
    (hk := by rw [r1b_run_fnOff, MainHops.memcpyCallee_fnOff])
  refine r1b_call (dst, src, bs) hmc_ok hinv hpc hrun hal_bl hlr hpanicK
    (F := subFrame ∗ F) ?_ (hnext := ?_)
  · dsimp only [Spec.inImage, Spec.keepsFs, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
    simp only [hsp, sepConj_assoc]
    apply Entails.pure_right hinv
    apply Entails.pure_right ⟨hx0, hx1, hx2⟩
    exact Entails.of_eq (by ac_rfl)
  · intro sf _ hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [Spec.inImage, Spec.keepsFs, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hfs_f => SepWPp.pure_elim fun hp => ?_
    rcases hp with ⟨hr0, htr_f⟩
    have hin_f : InRun img ext s0 sf retOff := {
      pc := hpc_f, run := hrun_f, sp := hsp_f.trans hsp,
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp, inv := hinv_f,
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs, spAligned := hsp0
    }
    refine MainHops.sepWPp_weaken_pre ?_ (hnext sf hin_f hcs_f hr0 hfs_f htr_f)
    rw [hsp, hsplit]; exact Entails.of_eq (by ac_rfl)

theorem r1b_call_tryAlloc {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {out new align stride : BitVec 64}
    {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hinv : ImgCallInv img st_bl)
    (hpc : st_bl.pc = (mProg img ext).fnAddr runName +
      bv% ((2 ^ 64 + ls_off% "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]" -
        ls_off% "libsignal_cli::run") % 2 ^ 64))
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPc img ext retOff)
    (hx0 : st_bl.readReg64 .x0 = out)
    (hx1 : st_bl.readReg64 .x1 = new)
    (hx2 : st_bl.readReg64 .x2 = align)
    (hx3 : st_bl.readReg64 .x3 = stride)
    (hnew : 0 < new.toNat)
    (hstr : 0 < stride.toNat)
    (hlay : LayoutOk (new.toNat * stride.toNat) align.toNat)
    (hpanicK : PanicK g s0 Qp)
    (herr : ∀ sf : State,
      InRun img ext s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      sf.fs = st_bl.fs →
      sf.trace = st_bl.trace ++ [allocFailedEvent] →
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        ((out ↦₆₄ 1#64) ∗ ((out + 8#64) ↦₆₄ align) ∗
          ((out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * stride.toNat)) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F) Q Qp (runOom s0))
    (hok : ∀ (sf : State) (buf : BitVec 64),
      InRun img ext s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      buf ≠ 0#64 →
      sf.fs = st_bl.fs →
      sf.trace = st_bl.trace →
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        ((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ new) ∗ ((out + 16#64) ↦₆₄ buf) ∗
          A.live buf (new.toNat * stride.toNat) align.toNat ∗
          memRegion buf (new.toNat * stride.toNat) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F) Q Qp (runOom s0)) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) st_bl
      (memRegion out 24 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F)
      Q Qp (runOom s0) := by
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  refine r1b_call ⟨out, new, align, stride⟩
    (r1b_tryAllocateIn3_ok hh hbnd.tryAlloc hbnd.sub63)
    hinv hpc hrun hal_bl hlr hpanicK (F := F) ?_ (hnext := ?_)
  · dsimp only [Spec.inImage, Spec.keepsFs, tryAllocateInSpecOf]
    simp only [hsp, sepConj_assoc]
    apply Entails.pure_right hinv
    apply Entails.pure_right ⟨hx0, hx1, hx2, hx3, hnew, hstr, hlay⟩
    exact Entails.of_eq (by ac_rfl)
  · intro sf _ hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [Spec.inImage, Spec.keepsFs, tryAllocateInSpecOf]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hfs_f => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun tag => SepWPp.exists_elim fun buf => ?_
    have hin_f : InRun img ext s0 sf retOff := {
      pc := hpc_f, run := hrun_f, sp := hsp_f.trans hsp,
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp, inv := hinv_f,
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs, spAligned := hsp0
    }
    by_cases ht : tag = 1#64
    · subst ht
      simp only [↓reduceIte, sepConj_assoc]
      have hcomm :
          ((out ↦₆₄ 1#64) ∗ ((out + 8#64) ↦₆₄ align) ∗
            ((out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * stride.toNat)) ∗
            ⌜buf = 0#64 ∧ sf.trace = st_bl.trace ++ [allocFailedEvent]⌝ ∗
            A.pool ∗ stackAt st_bl.sp (resStack - runFrame) ∗ F) =
          (⌜buf = 0#64 ∧ sf.trace = st_bl.trace ++ [allocFailedEvent]⌝ ∗
            ((out ↦₆₄ 1#64) ∗ ((out + 8#64) ↦₆₄ align) ∗
              ((out + 16#64) ↦₆₄ BitVec.ofNat 64 (new.toNat * stride.toNat)) ∗
              stackAt st_bl.sp (resStack - runFrame) ∗ A.pool ∗ F)) := by ac_rfl
      rw [hcomm]
      refine SepWPp.pure_elim fun hp => ?_
      rw [hsp]; exact herr sf hin_f hcs_f hfs_f hp.2
    · simp only [ht, ↓reduceIte, sepConj_assoc]
      have hcomm :
          ((out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ new) ∗ ((out + 16#64) ↦₆₄ buf) ∗
            ⌜tag = 0#64 ∧ buf ≠ 0#64 ∧ buf.toNat % align.toNat = 0 ∧ sf.trace = st_bl.trace⌝ ∗
            A.live buf (new.toNat * stride.toNat) align.toNat ∗
            memRegion buf (new.toNat * stride.toNat) ∗
            A.pool ∗ stackAt st_bl.sp (resStack - runFrame) ∗ F) =
          (⌜tag = 0#64 ∧ buf ≠ 0#64 ∧ buf.toNat % align.toNat = 0 ∧ sf.trace = st_bl.trace⌝ ∗
            ((out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ new) ∗ ((out + 16#64) ↦₆₄ buf) ∗
              A.live buf (new.toNat * stride.toNat) align.toNat ∗
              memRegion buf (new.toNat * stride.toNat) ∗
              stackAt st_bl.sp (resStack - runFrame) ∗ A.pool ∗ F)) := by ac_rfl
      rw [hcomm]
      refine SepWPp.pure_elim fun hp => ?_
      rcases hp with ⟨rfl, hne, -, htr_f⟩
      rw [hsp]; exact hok sf buf hin_f hcs_f hne hfs_f htr_f

theorem r1b_call_path_ro {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {ret dirCap dirPtr nameA : BitVec 64} {dir name : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hinv : ImgCallInv img st_bl)
    (hro : ∀ {m : Memory} {R : SepProp}, img.RoDataLoaded m → (m ⊨ R) → (m ⊨ (nameA ↦ᵣ name) ∗ R))
    (hpc : st_bl.pc = (mProg img ext).fnAddr runName +
      bv% ((2 ^ 64 + ls_off% "libsignal_cli::stores::path" -
        ls_off% "libsignal_cli::run") % 2 ^ 64))
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPc img ext retOff)
    (hx0 : st_bl.readReg64 .x0 = ret)
    (hx1 : st_bl.readReg64 .x1 = dirPtr)
    (hx2 : (st_bl.readReg64 .x2).toNat = dir.length)
    (hx3 : st_bl.readReg64 .x3 = nameA)
    (hx4 : (st_bl.readReg64 .x4).toNat = name.length)
    (hdir_lt : dir.length < 2 ^ 32)
    (hname_lt : name.length < 2 ^ 32)
    (htr0 : s0.trace <+: st_bl.trace)
    (hpanicK : PanicK g s0 Qp)
    (hnext : ∀ (sf : State) (pCap pPtr : BitVec 64),
      InRun img ext s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        ((ret ↦₆₄ pCap) ∗ ((ret + 8#64) ↦₆₄ pPtr) ∗
          ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 (dir ++ [0x2f#8] ++ name).length) ∗
          ownedBytes A pCap pPtr (BitVec.ofNat 64 (dir ++ [0x2f#8] ++ name).length)
            (dir ++ [0x2f#8] ++ name) ∗
          ownedBytes A dirCap dirPtr (BitVec.ofNat 64 dir.length) dir ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F)
        Q Qp (runOom s0)) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) st_bl
      (ownedBytes A dirCap dirPtr (BitVec.ofNat 64 dir.length) dir ∗
        memRegion ret 24 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F)
      Q Qp (runOom s0) := by
  refine r1b_sepWPp_with_ro hinv hro ?_
  rw [r1b_ownedBytes_borrow A dirCap dirPtr (BitVec.ofNat 64 dir.length) dir]
  have hcomm :
      ((nameA ↦ᵣ name) ∗
        (⌜BitVec.ofNat 64 dir.length = BitVec.ofNat 64 dir.length ∧
            dir.length ≤ dirCap.toNat ∧ dirCap.toNat < 2 ^ 63 ∧ dirPtr ≠ 0⌝ ∗
          (dirPtr ↦ₛ dir) ∗ r1b_ownedRest A dirCap dirPtr dir.length) ∗
        memRegion ret 24 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F) =
      (⌜BitVec.ofNat 64 dir.length = BitVec.ofNat 64 dir.length ∧
          dir.length ≤ dirCap.toNat ∧ dirCap.toNat < 2 ^ 63 ∧ dirPtr ≠ 0⌝ ∗
        ((dirPtr ↦ₛ dir) ∗ (nameA ↦ᵣ name) ∗ memRegion ret 24 ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗
          (r1b_ownedRest A dirCap dirPtr dir.length ∗ F))) := by ac_rfl
  rw [hcomm]
  refine SepWPp.pure_elim fun hdir_inv => ?_
  rcases hdir_inv with ⟨-, hdir_le, hdir_cap, hdir_ne⟩
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  refine r1b_call
    (x := { dirA := dirPtr, dir := dir, dirRo := false,
            nameA := nameA, name := name, nameRo := true, ret := ret })
    (r1b_path_ok himg hh hbnd.path) hinv hpc hrun hal_bl hlr hpanicK
    (F := r1b_ownedRest A dirCap dirPtr dir.length ∗ F)
    ?_ (hpanic := ?_) (hnext := ?_)
  · dsimp only [Spec.inImage, pathSpec, SpqrV1.ChainProofs.bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte, hsp, sepConj_assoc]
    apply Entails.pure_right hinv
    apply Entails.pure_right ⟨hx0, hx1, hx2, hx3, hx4, hdir_lt, hname_lt⟩
    exact Entails.of_eq (by ac_rfl)
  · intro sf R' _ hpost
    dsimp only [Spec.inImage, pathSpec] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact Or.inr (r1b_allocFailedIn_sub htr0 hpost.1.1)
  · intro sf hsteps hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [Spec.inImage, pathSpec, SpqrV1.ChainProofs.bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte, List.append_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun htr_f => ?_
    have hin_f : InRun img ext s0 sf retOff := {
      pc := hpc_f, run := hrun_f, sp := hsp_f.trans hsp,
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp, inv := hinv_f,
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs, spAligned := hsp0
    }
    have hfiles_f := r1b_files_eq_of_trace_eq hh hsteps htr_f
    have hrejoin := r1b_ownedBytes_rejoin A dirCap dirPtr dir hdir_le hdir_cap hdir_ne
    have hvec := M3Helpers.vecU8_to_ownedBytes A ret (dir ++ [0x2f#8] ++ name)
    simp only [List.append_assoc] at hvec ⊢
    refine MainHops.sepWPp_weaken_pre
      (P' := (nameA ↦ᵣ name) ∗
        (∃∗ pCap : BitVec 64, ∃∗ pPtr : BitVec 64,
          (ret ↦₆₄ pCap) ∗ ((ret + 8#64) ↦₆₄ pPtr) ∗
          ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 (dir ++ ([0x2f#8] ++ name)).length) ∗
          ownedBytes A pCap pPtr (BitVec.ofNat 64 (dir ++ ([0x2f#8] ++ name)).length)
            (dir ++ ([0x2f#8] ++ name))) ∗
        ownedBytes A dirCap dirPtr (BitVec.ofNat 64 dir.length) dir ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F) ?_ ?_
    · rw [hsp]
      refine Entails.trans (Entails.of_eq (show _ =
        (nameA ↦ᵣ name) ∗ vecU8 A ret (dir ++ ([0x2f#8] ++ name)) ∗
        ((dirPtr ↦ₛ dir) ∗ r1b_ownedRest A dirCap dirPtr dir.length) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F by ac_rfl)) ?_
      exact sepConj_mono_right (sepConj_mono hvec (sepConj_mono_left hrejoin))
    · refine r1b_sepWPp_drop_left ?_
      simp only [sepExists_sepConj_left]
      refine SepWPp.exists_elim fun pCap => SepWPp.exists_elim fun pPtr => ?_
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc]
      simpa only [List.append_assoc] using hnext sf pCap pPtr hin_f hcs_f hfiles_f htr_f

theorem r1b_call_readFile {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets} {σ : RunSlots}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {pathCap pathPtr ret : BitVec 64} {path : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hc : RunCallees img A ext B σ)
    (hbnd : r1b_StackBounds B resStack)
    (hinv : ImgCallInv img st_bl)
    (hpc : st_bl.pc = (mProg img ext).fnAddr runName +
      bv% ((2 ^ 64 + ls_off% "libsignal_cli_io::read_file" -
        ls_off% "libsignal_cli::run") % 2 ^ 64))
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPc img ext retOff)
    (hx0 : st_bl.readReg64 .x0 = pathPtr)
    (hx1 : (st_bl.readReg64 .x1).toNat = path.length)
    (hx8 : st_bl.readReg64 .x8 = ret)
    (hlen : path.length < 2 ^ 32)
    (hok_p : cliWrOk path)
    (htr0 : s0.trace <+: st_bl.trace)
    (hpanicK : PanicK g s0 Qp)
    (herr : ∀ (sf : State) (w1 w2 : BitVec 64),
      InRun img ext s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      (cliIo.rd st_bl.fs.files path = .error () ∧
        sf.fs.files = st_bl.fs.files ∧ sf.trace = st_bl.trace) →
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        ((ret ↦₆₄ 0xffffffffffffffff#64) ∗ ((ret + 8#64) ↦₆₄ w1) ∗ ((ret + 16#64) ↦₆₄ w2) ∗
          ownedBytes A pathCap pathPtr (BitVec.ofNat 64 path.length) path ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F)
        Q Qp (runOom s0))
    (hok : ∀ (sf : State) (rCap rPtr : BitVec 64) (bs : List (BitVec 8)),
      InRun img ext s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      cliIo.rd st_bl.fs.files path = .ok bs →
      sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        ((ret ↦₆₄ rCap) ∗ ((ret + 8#64) ↦₆₄ rPtr) ∗
          ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ownedBytes A rCap rPtr (BitVec.ofNat 64 bs.length) bs ∗
          ownedBytes A pathCap pathPtr (BitVec.ofNat 64 path.length) path ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F)
        Q Qp (runOom s0)) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) st_bl
      (ownedBytes A pathCap pathPtr (BitVec.ofNat 64 path.length) path ∗
        memRegion ret 24 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F)
      Q Qp (runOom s0) := by
  rw [r1b_ownedBytes_borrow A pathCap pathPtr (BitVec.ofNat 64 path.length) path]
  have hsplit := BundleRead.Helpers.stackAt_split_sub (runFsp s0)
    (resStack - runFrame) B.readFile hbnd.readFile hbnd.sub64
  rw [hsplit]
  set subFrame := memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
    (resStack - runFrame - B.readFile)
  have hcomm :
      ((⌜BitVec.ofNat 64 path.length = BitVec.ofNat 64 path.length ∧
            path.length ≤ pathCap.toNat ∧ pathCap.toNat < 2 ^ 63 ∧ pathPtr ≠ 0⌝ ∗
          (pathPtr ↦ₛ path) ∗ r1b_ownedRest A pathCap pathPtr path.length) ∗
        memRegion ret 24 ∗ (subFrame ∗ stackAt (runFsp s0) B.readFile) ∗ A.pool ∗ F) =
      (⌜BitVec.ofNat 64 path.length = BitVec.ofNat 64 path.length ∧
          path.length ≤ pathCap.toNat ∧ pathCap.toNat < 2 ^ 63 ∧ pathPtr ≠ 0⌝ ∗
        ((pathPtr ↦ₛ path) ∗ memRegion ret 24 ∗ stackAt (runFsp s0) B.readFile ∗ A.pool ∗
          (r1b_ownedRest A pathCap pathPtr path.length ∗ subFrame ∗ F))) := by ac_rfl
  rw [hcomm]
  refine SepWPp.pure_elim fun hpinv => ?_
  rcases hpinv with ⟨-, hp_le, hp_cap, hp_ne⟩
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  refine r1b_call (x := { pathA := pathPtr, path := path, ret := ret })
    (r1b_readFile_ok hc) hinv hpc hrun hal_bl hlr hpanicK
    (F := r1b_ownedRest A pathCap pathPtr path.length ∗ subFrame ∗ F)
    ?_ (hpanic := ?_) (hnext := ?_)
  · dsimp only [Spec.inImage, readFileSpec]
    simp only [hsp, sepConj_assoc]
    apply Entails.pure_right hinv
    apply Entails.pure_right ⟨hx0, hx1, hx8, hlen, hok_p⟩
    exact Entails.of_eq (by ac_rfl)
  · intro sf R' _ hpost
    dsimp only [Spec.inImage, readFileSpec] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact Or.inr (r1b_allocFailedIn_sub htr0 hpost.1.1)
  · intro sf hsteps hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [Spec.inImage, readFileSpec]
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun r => ?_
    refine SepWPp.pure_elim fun hdisj => ?_
    have hin_f : InRun img ext s0 sf retOff := {
      pc := hpc_f, run := hrun_f, sp := hsp_f.trans hsp,
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp, inv := hinv_f,
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs, spAligned := hsp0
    }
    have hrejoin := r1b_ownedBytes_rejoin A pathCap pathPtr path hp_le hp_cap hp_ne
    cases r with
    | error u =>
      cases u
      dsimp only [ioVecAt]
      have hout :
          cliIo.rd st_bl.fs.files path = .error () ∧
            sf.fs.files = st_bl.fs.files ∧ sf.trace = st_bl.trace :=
        ⟨hdisj.1.symm, r1b_files_eq_of_trace_eq hh hsteps hdisj.2, hdisj.2⟩
      refine MainHops.sepWPp_weaken_pre
        (P' := (ret ↦₆₄ 0xffffffffffffffff#64) ∗
          (∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ((ret + 8#64) ↦₆₄ w1) ∗ ((ret + 16#64) ↦₆₄ w2)) ∗
          ownedBytes A pathCap pathPtr (BitVec.ofNat 64 path.length) path ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F) ?_ ?_
      · rw [hsp, hsplit]
        refine Entails.trans (Entails.of_eq (show _ =
          (ret ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (ret + 8#64) 16 ∗
          ((pathPtr ↦ₛ path) ∗ r1b_ownedRest A pathCap pathPtr path.length) ∗
          (subFrame ∗ stackAt (runFsp s0) B.readFile) ∗ A.pool ∗ F by ac_rfl)) ?_
        exact sepConj_mono_right (sepConj_mono (M3Helpers.memRegion_16_cells ret)
          (sepConj_mono_left hrejoin))
      · simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine SepWPp.exists_elim fun w1 => SepWPp.exists_elim fun w2 => ?_
        rw [sepConj_assoc]
        exact herr sf w1 w2 hin_f hcs_f hout
    | ok bs =>
      dsimp only [ioVecAt]
      rcases hdisj with ⟨hrd, htr_f⟩
      have hfiles_f := r1b_files_eq_of_trace_eq hh hsteps htr_f
      have hvec := M3Helpers.vecU8_to_ownedBytes A ret bs
      refine MainHops.sepWPp_weaken_pre
        (P' := (∃∗ rCap : BitVec 64, ∃∗ rPtr : BitVec 64,
          (ret ↦₆₄ rCap) ∗ ((ret + 8#64) ↦₆₄ rPtr) ∗
          ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ownedBytes A rCap rPtr (BitVec.ofNat 64 bs.length) bs) ∗
          ownedBytes A pathCap pathPtr (BitVec.ofNat 64 path.length) path ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F) ?_ ?_
      · rw [hsp, hsplit]
        refine Entails.trans (Entails.of_eq (show _ =
          vecU8 A ret bs ∗
          ((pathPtr ↦ₛ path) ∗ r1b_ownedRest A pathCap pathPtr path.length) ∗
          (subFrame ∗ stackAt (runFsp s0) B.readFile) ∗ A.pool ∗ F by ac_rfl)) ?_
        exact sepConj_mono hvec (sepConj_mono_left hrejoin)
      · simp only [sepExists_sepConj_left]
        refine SepWPp.exists_elim fun rCap => SepWPp.exists_elim fun rPtr => ?_
        rw [sepConj_assoc, sepConj_assoc, sepConj_assoc]
        exact hok sf rCap rPtr bs hin_f hcs_f hrd.symm hfiles_f htr_f

theorem r1b_call_bundleRead_ro {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets} {σ : RunSlots}
    {g : RunCall} {s0 st_bl : State} {resStack retOff : Nat}
    {ret dirCap dirPtr nameA : BitVec 64} {dir name : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    (hc : RunCallees img A ext B σ)
    (hbnd : r1b_StackBounds B resStack)
    (hinv : ImgCallInv img st_bl)
    (hro : ∀ {m : Memory} {R : SepProp}, img.RoDataLoaded m → (m ⊨ R) → (m ⊨ (nameA ↦ᵣ name) ∗ R))
    (hpc : st_bl.pc = (mProg img ext).fnAddr runName +
      bv% ((2 ^ 64 + ls_off% "libsignal_cli::public::read_bundle::{closure#0}" -
        ls_off% "libsignal_cli::run") % 2 ^ 64))
    (hrun : st_bl.status = .Running)
    (hsp : st_bl.sp = runFsp s0)
    (hfp : st_bl.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs st_bl = calleeSavedVRegs s0)
    (hsp0 : s0.spAligned = true)
    (hlr : st_bl.readReg64 .lr = runPc img ext retOff)
    (hx0 : st_bl.readReg64 .x0 = ret)
    (hx1 : st_bl.readReg64 .x1 = dirPtr)
    (hx2 : (st_bl.readReg64 .x2).toNat = dir.length)
    (hx3 : st_bl.readReg64 .x3 = nameA)
    (hx4 : (st_bl.readReg64 .x4).toNat = name.length)
    (hdir_lt : dir.length < 2 ^ 32)
    (hname_lt : name.length < 2 ^ 32)
    (hok_p : cliWrOk (dir ++ [0x2f#8] ++ name))
    (htr0 : s0.trace <+: st_bl.trace)
    (hpanicK : PanicK g s0 Qp)
    (herr : ∀ (sf : State) (eCap ePtr : BitVec 64) (eBs : List (BitVec 8)),
      InRun img ext s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      (cliIo.rd st_bl.fs.files (dir ++ [0x2f#8] ++ name) = .error () ∧
        sf.fs.files = st_bl.fs.files ∧ sf.trace = st_bl.trace) →
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        ((ret ↦₆₄ speWord 1) ∗
          ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
          ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
          memRegion (ret + 32#64) 16 ∗
          ownedBytes A eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
          ownedBytes A dirCap dirPtr (BitVec.ofNat 64 dir.length) dir ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F)
        Q Qp (runOom s0))
    (hok : ∀ (sf : State) (rCap rPtr : BitVec 64) (bs : List (BitVec 8)),
      InRun img ext s0 sf retOff →
      CalleeSavedPreserved st_bl sf →
      cliIo.rd st_bl.fs.files (dir ++ [0x2f#8] ++ name) = .ok bs →
      sf.fs.files = st_bl.fs.files →
      sf.trace = st_bl.trace →
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        ((ret ↦₆₄ okTagVec) ∗
          ((ret + 8#64) ↦₆₄ rCap) ∗ ((ret + 16#64) ↦₆₄ rPtr) ∗
          ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          memRegion (ret + 32#64) 16 ∗
          ownedBytes A rCap rPtr (BitVec.ofNat 64 bs.length) bs ∗
          ownedBytes A dirCap dirPtr (BitVec.ofNat 64 dir.length) dir ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F)
        Q Qp (runOom s0)) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) st_bl
      (ownedBytes A dirCap dirPtr (BitVec.ofNat 64 dir.length) dir ∗
        memRegion ret 48 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F)
      Q Qp (runOom s0) := by
  refine r1b_sepWPp_with_ro hinv hro ?_
  rw [r1b_ownedBytes_borrow A dirCap dirPtr (BitVec.ofNat 64 dir.length) dir]
  have hcomm :
      ((nameA ↦ᵣ name) ∗
        (⌜BitVec.ofNat 64 dir.length = BitVec.ofNat 64 dir.length ∧
            dir.length ≤ dirCap.toNat ∧ dirCap.toNat < 2 ^ 63 ∧ dirPtr ≠ 0⌝ ∗
          (dirPtr ↦ₛ dir) ∗ r1b_ownedRest A dirCap dirPtr dir.length) ∗
        memRegion ret 48 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F) =
      (⌜BitVec.ofNat 64 dir.length = BitVec.ofNat 64 dir.length ∧
          dir.length ≤ dirCap.toNat ∧ dirCap.toNat < 2 ^ 63 ∧ dirPtr ≠ 0⌝ ∗
        ((dirPtr ↦ₛ dir) ∗ (nameA ↦ᵣ name) ∗ memRegion ret 48 ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗
          (r1b_ownedRest A dirCap dirPtr dir.length ∗ F))) := by ac_rfl
  rw [hcomm]
  refine SepWPp.pure_elim fun hdir_inv => ?_
  rcases hdir_inv with ⟨-, hdir_le, hdir_cap, hdir_ne⟩
  have hal_bl : st_bl.spAligned = true := r1b_spAligned_of_fsp hsp hsp0
  refine r1b_call
    (x := { ret := ret, dirA := dirPtr, dir := dir, dirRo := false,
            nameA := nameA, name := name, nameRo := true })
    (r1b_bundleRead_ok himg hh hc hbnd.bundleRead) hinv hpc hrun hal_bl hlr hpanicK
    (F := r1b_ownedRest A dirCap dirPtr dir.length ∗ F)
    ?_ (hpanic := ?_) (hnext := ?_)
  · dsimp only [Spec.inImage, bundleReadSpec, SpqrV1.ChainProofs.bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte, hsp, sepConj_assoc]
    apply Entails.pure_right hinv
    apply Entails.pure_right ⟨hx0, hx1, hx2, hx3, hx4, hdir_lt, hname_lt, hok_p⟩
    exact Entails.of_eq (by ac_rfl)
  · intro sf R' _ hpost
    dsimp only [Spec.inImage, bundleReadSpec] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact Or.inr (r1b_allocFailedIn_sub htr0 hpost.1.1)
  · intro sf hsteps hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [Spec.inImage, bundleReadSpec, SpqrV1.ChainProofs.bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte, sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun r => ?_
    refine SepWPp.pure_elim fun hdisj => ?_
    have hin_f : InRun img ext s0 sf retOff := {
      pc := hpc_f, run := hrun_f, sp := hsp_f.trans hsp,
      fp := hcs_f.2.2.2.2.2.2.2.2.2.2.1.trans hfp, inv := hinv_f,
      vregs := hcs_f.2.2.2.2.2.2.2.2.2.2.2.trans hvregs, spAligned := hsp0
    }
    have hrejoin := r1b_ownedBytes_rejoin A dirCap dirPtr dir hdir_le hdir_cap hdir_ne
    cases r with
    | error u =>
      cases u
      dsimp only [getResultAt, speAt]
      have hout :
          cliIo.rd st_bl.fs.files (dir ++ [0x2f#8] ++ name) = .error () ∧
            sf.fs.files = st_bl.fs.files ∧ sf.trace = st_bl.trace :=
        ⟨hdisj.1.symm, r1b_files_eq_of_trace_eq hh hsteps hdisj.2, hdisj.2⟩
      have hstr_drop : strRefAt (ret + 32#64) (utf8 "read") ⊢
          ∃∗ fnPtr : BitVec 64, (fnPtr ↦ᵣ utf8 "read") ∗ memRegion (ret + 32#64) 16 := by
        dsimp only [strRefAt]
        refine Entails.sepExists_elim fun fnPtr => Entails.sepExists_right fnPtr ?_
        have hcells :
            ((ret + 32#64) ↦₆₄ fnPtr) ∗
              ((ret + 32#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ⊢
            memRegion (ret + 32#64) 16 := r1b_cells2_to_region16 _ _ _
        exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_right hcells)
      have hev : ((ret ↦₆₄ speWord 1) ∗ (∃∗ bs : List (BitVec 8), vecU8 A (ret + 8#64) bs)) ⊢
          ∃∗ eBs : List (BitVec 8), ∃∗ eCap : BitVec 64, ∃∗ ePtr : BitVec 64,
            (ret ↦₆₄ speWord 1) ∗
            ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
            ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
            ownedBytes A eCap ePtr (BitVec.ofNat 64 eBs.length) eBs := by
        rw [sepExists_sepConj_right]
        refine Entails.sepExists_elim fun eBs => Entails.sepExists_right eBs ?_
        have hv := M3Helpers.vecU8_to_ownedBytes A (ret + 8#64) eBs
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hv
        exact Entails.trans (sepConj_mono_right hv) (by
          simp only [sepExists_sepConj_right]
          exact Entails.sepExists_elim fun eCap => Entails.sepExists_right eCap
            (Entails.sepExists_elim fun ePtr => Entails.sepExists_right ePtr
              (Entails.of_eq (by ac_rfl))))
      refine MainHops.sepWPp_weaken_pre
        (P' := (nameA ↦ᵣ name) ∗
          (∃∗ eBs : List (BitVec 8), ∃∗ eCap : BitVec 64, ∃∗ ePtr : BitVec 64,
            (ret ↦₆₄ speWord 1) ∗
            ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
            ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
            ownedBytes A eCap ePtr (BitVec.ofNat 64 eBs.length) eBs) ∗
          (∃∗ fnPtr : BitVec 64, (fnPtr ↦ᵣ utf8 "read") ∗ memRegion (ret + 32#64) 16) ∗
          ownedBytes A dirCap dirPtr (BitVec.ofNat 64 dir.length) dir ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F) ?_ ?_
      · rw [hsp]
        refine Entails.trans (Entails.of_eq (show _ =
          (nameA ↦ᵣ name) ∗
          ((ret ↦₆₄ speWord 1) ∗ (∃∗ bs : List (BitVec 8), vecU8 A (ret + 8#64) bs)) ∗
          strRefAt (ret + 32#64) (utf8 "read") ∗
          ((dirPtr ↦ₛ dir) ∗ r1b_ownedRest A dirCap dirPtr dir.length) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F by ac_rfl)) ?_
        exact sepConj_mono_right (sepConj_mono hev (sepConj_mono hstr_drop
          (sepConj_mono_left hrejoin)))
      · refine r1b_sepWPp_drop_left ?_
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine SepWPp.exists_elim fun fnPtr =>
          SepWPp.exists_elim fun eBs =>
          SepWPp.exists_elim fun eCap =>
          SepWPp.exists_elim fun ePtr => ?_
        refine MainHops.sepWPp_weaken_pre
          (P' := (fnPtr ↦ᵣ utf8 "read") ∗
            ((ret ↦₆₄ speWord 1) ∗
              ((ret + 8#64) ↦₆₄ eCap) ∗ ((ret + 16#64) ↦₆₄ ePtr) ∗
              ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
              memRegion (ret + 32#64) 16 ∗
              ownedBytes A eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
              ownedBytes A dirCap dirPtr (BitVec.ofNat 64 dir.length) dir ∗
              stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F))
          ?_ ?_
        · exact Entails.of_eq (by ac_rfl)
        · exact r1b_sepWPp_drop_left (herr sf eCap ePtr eBs hin_f hcs_f hout)
    | ok bs =>
      dsimp only [getResultAt, vecResultAt]
      rcases hdisj with ⟨hrd, htr_f⟩
      have hfiles_f := r1b_files_eq_of_trace_eq hh hsteps htr_f
      have hvec := M3Helpers.vecU8_to_ownedBytes A (ret + 8#64) bs
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hvec
      refine MainHops.sepWPp_weaken_pre
        (P' := (nameA ↦ᵣ name) ∗
          (ret ↦₆₄ okTagVec) ∗
          (∃∗ rCap : BitVec 64, ∃∗ rPtr : BitVec 64,
            ((ret + 8#64) ↦₆₄ rCap) ∗ ((ret + 16#64) ↦₆₄ rPtr) ∗
            ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            ownedBytes A rCap rPtr (BitVec.ofNat 64 bs.length) bs) ∗
          memRegion (ret + 32#64) 16 ∗
          ownedBytes A dirCap dirPtr (BitVec.ofNat 64 dir.length) dir ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F) ?_ ?_
      · rw [hsp]
        refine Entails.trans (Entails.of_eq (show _ =
          (nameA ↦ᵣ name) ∗ (ret ↦₆₄ okTagVec) ∗ vecU8 A (ret + 8#64) bs ∗
          memRegion (ret + 32#64) 16 ∗
          ((dirPtr ↦ₛ dir) ∗ r1b_ownedRest A dirCap dirPtr dir.length) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ F by ac_rfl)) ?_
        exact sepConj_mono_right (sepConj_mono_right (sepConj_mono hvec
          (sepConj_mono_right (sepConj_mono_left hrejoin))))
      · refine r1b_sepWPp_drop_left ?_
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine SepWPp.exists_elim fun rCap => SepWPp.exists_elim fun rPtr => ?_
        refine MainHops.sepWPp_weaken_pre (Entails.of_eq (by ac_rfl))
          (hok sf rCap rPtr bs hin_f hcs_f hrd.symm hfiles_f htr_f)

end CryptoVerification.SignalSession.Cli.RunCompose
