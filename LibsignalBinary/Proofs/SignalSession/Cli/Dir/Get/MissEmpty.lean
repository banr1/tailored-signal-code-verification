/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.Hit
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.Decode
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.MissAfterRead
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# Cache-Miss Empty-Directory Path (`+164`..`+332`) for `<signal_session::stores::Dir>::get`

Verifies the `dir.path = []` cache-miss path (`name.to_owned()` followed by the `+332` → `+336` I/O
call abstracted via `PathIoContract`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Get.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SpqrV1.Alloc

ls_attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
ls_attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem cstk_le_pow64_m {cstk stk : Nat} (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64) :
    cstk ≤ 2 ^ 64 :=
  Nat.le_trans (Nat.le_add_left cstk 112) (Nat.le_trans hstk hfull)

private theorem lt_pow63_of_lt_pow32_m {n : Nat} (h : n < 2 ^ 32) : n < 2 ^ 63 :=
  Nat.lt_trans h (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 32 < 63))

private theorem lt_pow64_of_lt_pow32_m {n : Nat} (h : n < 2 ^ 32) : n < 2 ^ 64 :=
  Nat.lt_trans h (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 32 < 64))

private theorem ofNat64_toNat_of_lt32_m {n : Nat} (h : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_pow64_of_lt_pow32_m h)]

def stateOfFrozenMiss {img : Obj.Image} {st : State} (_ : img.FrozenLoaded st) : State := st

theorem false_of_fsInv_false_miss {F0 : FsFiles} {T0 : List TraceEvent} {sf : State}
    {m : Memory} {R : SepProp}
    (h : m ⊨ (⌜FsInv F0 T0 sf⌝ ∗ ⌜False⌝) ∗ R) : False := by
  rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at h
  exact h.2.1

theorem panicQp_of_fsInv_false_miss
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {A : RustAlloc} {img : Obj.Image}
    {stk : Nat} {x : DirGetGhost} {s0 sf : State} {Fr R : SepProp}
    {F0 : FsFiles} {T0 : List TraceEvent} {Frame : SepProp} :
    dirGetPanicQp rd pathOk A img stk x s0 Fr R sf ((⌜FsInv F0 T0 sf⌝ ∗ ⌜False⌝) ∗ Frame) :=
  fun hm => False.elim (false_of_fsInv_false_miss (by rw [sepConj_assoc] at hm; exact hm))

/-- Shared continuation from `+320` (`ADD X8, SP, #0; MOV X0, X21; MOV X1, X20` → `+332` `BL io` →
    `step_after_read`). -/
theorem step_miss_call_io
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {pathStk ioStk stk : Nat}
    {x : DirGetGhost} {s0 sm : State}
    {pathCap pathPtr : BitVec 64} {pth : List (BitVec 8)}
    {w0 w1 wTail : BitVec 64} {R : SepProp}
    (hC : AllocContractsX img A ext)
    (hIoCall : PathIoContract img A ext rd pathOk ioStk)
    (hstk : 112 + dirGetCalleeStk pathStk ioStk ≤ stk)
    (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hb : (img.base &&& 0xfff#64) = 0#64)
    (hpOk : pathOk (pathOf x.dir.path x.name))
    (hget_eq : x.dir.get rd s0.fs.files x.name = rd s0.fs.files (pathOf x.dir.path x.name))
    (hpth_eq : pth = pathOf x.dir.path x.name)
    (hpth_le : pth.length ≤ pathCap.toNat)
    (hpth_cap_lt : pathCap.toNat < 2 ^ 63)
    (hpth_lt32 : pth.length < 2 ^ 32)
    (hfz_m : img.FrozenLoaded sm)
    (hsym_m : sm.symtab = img.symtab)
    (hpc_m : sm.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName + 320#64)
    (hrun_m : sm.status = .Running)
    (hsp_al_m : sm.spAligned = true)
    (hsp_m : sm.sp = s0.sp - 112#64)
    (hhcs_m : HighCalleeSaved s0 sm)
    (hfs_m : sm.fs.files = s0.fs.files)
    (htr_m : sm.trace = s0.trace)
    (hx19_m : sm.readReg64 .x19 = x.ret)
    (hx20_m : sm.readReg64 .x20 = BitVec.ofNat 64 pth.length)
    (hx21_m : sm.readReg64 .x21 = pathPtr) :
    SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      (s0.readReg64 .lr) sm
      (((pathPtr ↦ₛ pth) ∗
        (if pathCap = 0 then emp
         else A.live pathPtr pathCap.toNat 1 ∗
           memRegion (pathPtr + BitVec.ofNat 64 pth.length) (pathCap.toNat - pth.length)) ∗
        ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ∗
        dirAt A x.self x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗
        stackAt (s0.sp - 112#64) (dirGetCalleeStk pathStk ioStk) ∗
        memRegion (s0.sp - 112#64) 24 ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗
        dirGetRoBundle img.base w0 w1 wTail)
      (dirGetPostQ rd pathOk A img stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk)
          (stk - (112 + dirGetCalleeStk pathStk ioStk)) ∗ R) R)
      (dirGetPanicQp rd pathOk A img stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk)
          (stk - (112 + dirGetCalleeStk pathStk ioStk)) ∗ R) R) := by
  let cstk := dirGetCalleeStk pathStk ioStk
  have hcstk_ext : extHookStack ≤ cstk := Nat.le_max_right _ _
  have hcstk_io : ioStk ≤ cstk :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hfn : libsignalSessionCode.fnOff dirGetName =
      ls_off% "<libsignal_cli::stores::Dir>::get" := dirGet_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode dirGetBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_cli::stores::Dir>::get")) 320 12
  clear hfn
  rw [stackAt_sub_split (s0.sp - 112#64) hcstk_io (cstk_le_pow64_m hstk hfull)]
  have hcstk_io_join :
      memRegion (s0.sp - 112#64 - BitVec.ofNat 64 cstk) (cstk - ioStk) ∗
        stackAt (s0.sp - 112#64) ioStk ⊢
      stackAt (s0.sp - 112#64) cstk := by
    rw [stackAt_sub_split (s0.sp - 112#64) hcstk_io (cstk_le_pow64_m hstk hfull)]
    exact Entails.refl _
  have hpth_fz : FrozenEq pth (pathOf x.dir.path x.name) := ⟨hpth_eq⟩
  clear hpth_eq
  generalize hentry_raw :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName = fnStart at *
  generalize hprog_raw :
    libsignalSessionCode.rebase img.base (Rust.withPanics ext) = prog at *
  have he : FrozenEq (prog.fnAddr dirGetName) fnStart := ⟨hentry_raw⟩
  have hp : FrozenEq (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) prog := ⟨hprog_raw⟩
  clear hentry_raw hprog_raw
  examples_hide_fetches
  refine seq_frozen_state (mid := fnStart + 332#64) hfz_m ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hfz_io
  rcases hpth_fz with ⟨hpth_eq⟩
  rcases he with ⟨rfl⟩; rcases hp with ⟨rfl⟩
  let s_io := stateOfFrozenMiss hfz_io
  have hpth_nat : (BitVec.ofNat 64 pth.length).toNat = pth.length :=
    ofNat64_toNat_of_lt32_m hpth_lt32
  have hsp_cur : s_io.sp = s0.sp - 112#64 := by simp only [s_io, stateOfFrozenMiss, wp_norm, arm64_norm, *]
  have hsym_cur : s_io.symtab = img.symtab := by simp only [s_io, stateOfFrozenMiss, wp_norm, arm64_norm, *]
  have hpc_cur : s_io.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName + 332#64 := by
    dsimp only [s_io, stateOfFrozenMiss]; wp_norm_lhs
  have hrun_cur : s_io.status = ExecStatus.Running := by simp only [s_io, stateOfFrozenMiss, wp_norm, arm64_norm, *]
  have hsp_al_cur : s_io.spAligned = true := by simpa only [s_io, stateOfFrozenMiss, wp_norm, arm64_norm] using hsp_al_m
  have hinv_cur : FsInv s0.fs.files s0.trace s_io :=
    fsInv_of_files_trace_eq (by simp only [s_io, stateOfFrozenMiss, wp_norm, arm64_norm, *])
      (by simp only [s_io, stateOfFrozenMiss, wp_norm, arm64_norm, *])
  have htr_cur : s_io.trace = s0.trace := by simp only [s_io, stateOfFrozenMiss, wp_norm, arm64_norm, *]
  have hx0_cur : s_io.readReg64 .x0 = pathPtr := by simp only [s_io, stateOfFrozenMiss, wp_norm, arm64_norm, *]
  have hx1_cur : (s_io.readReg64 .x1).toNat = pth.length := by
    simp only [s_io, stateOfFrozenMiss, wp_norm, arm64_norm, hpth_nat]
  have hx8_cur : s_io.readReg64 .x8 = s_io.sp := by simp only [s_io, stateOfFrozenMiss, wp_norm, arm64_norm, *]
  have hhcs_cur : HighCalleeSaved s0 s_io :=
    hhcs_m.of_steps
      (by simp only [s_io, stateOfFrozenMiss, wp_norm, arm64_norm])
      (by simp only [s_io, stateOfFrozenMiss, wp_norm, arm64_norm])
      (by simp only [s_io, stateOfFrozenMiss, wp_norm, arm64_norm])
      (by simp only [s_io, stateOfFrozenMiss, wp_norm, arm64_norm])
      (by simp only [s_io, stateOfFrozenMiss, calleeSavedVRegs, wp_norm, arm64_norm])
  have hx19_cur : s_io.readReg64 .x19 = x.ret := by simp only [s_io, stateOfFrozenMiss, wp_norm, arm64_norm, *]
  have hx21_cur : s_io.readReg64 .x21 = pathPtr := by simp only [s_io, stateOfFrozenMiss, wp_norm, arm64_norm, *]
  let F_io : SepProp :=
    ((if pathCap = 0 then emp
      else A.live pathPtr pathCap.toNat 1 ∗
        memRegion (pathPtr + BitVec.ofNat 64 pth.length) (pathCap.toNat - pth.length)) ∗
     ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
     ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
     ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ∗
     dirAt A x.self x.dir ∗
     SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
     memRegion x.ret 48 ∗
     memRegion (s0.sp - 112#64 - BitVec.ofNat 64 cstk) (cstk - ioStk) ∗
     savedRegsAt (s0.sp - 112#64) s0) ∗
    dirGetRoBundle img.base w0 w1 wTail
  refine SepWPp.perm
    (P' := ((pathPtr ↦ₛ pth) ∗ memRegion s_io.sp 24 ∗
      stackAt s_io.sp ioStk ∗ A.pool) ∗ F_io) ?_ (by rw [hsp_cur]; dsimp only [F_io]; sep_frame)
  refine hIoCall s0 s_io pathPtr pth F_io _ _ hfz_io
    hsym_cur hpc_cur hrun_cur hsp_al_cur hinv_cur htr_cur
    hx0_cur hx1_cur hx8_cur hpth_lt32 (by rwa [hpth_eq])
    (fun _ _ _ hsc => dirGetPanicQp_of_readPanic hsc)
    (fun sf_r hpc_r hrun_r hsp_r hcs_r hfz_r hsym_r => ?_)
  have hsp_r_al : sf_r.spAligned = true := spAligned_of_sp_eq hsp_al_cur hsp_r
  rw [hsp_cur] at hsp_r ⊢
  dsimp only [F_io]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine sepWPp_exists_left fun r_io => SepWPp.pure_left fun hres_io => ?_
  have hhcs_r : HighCalleeSaved s0 sf_r := hhcs_cur.of_calleeSaved hcs_r
  have hx19_r : sf_r.readReg64 .x19 = x.ret := hcs_r.1.trans hx19_cur
  have hx21_r : sf_r.readReg64 .x21 = pathPtr := hcs_r.2.2.1.trans hx21_cur
  let P_ar : SepProp :=
    (ioVecAt A (s0.sp - 112#64) r_io ∗
      (pathPtr ↦ₛ pth) ∗
      (if pathCap = 0 then emp
       else A.live pathPtr pathCap.toNat 1 ∗
         memRegion (pathPtr + BitVec.ofNat 64 pth.length) (pathCap.toNat - pth.length)) ∗
      ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
      ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
      ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ∗
      dirAt A x.self x.dir ∗
      SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
      memRegion x.ret 48 ∗
      savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗
    dirGetRoBundle img.base w0 w1 wTail
  refine SepWPp.perm
    (P' := (memRegion (s0.sp - 112#64 - BitVec.ofNat 64 cstk) (cstk - ioStk) ∗
      stackAt (s0.sp - 112#64) ioStk) ∗ P_ar) ?_
    (by dsimp only [P_ar]; sep_frame)
  refine sepWPp_weaken_pre (sepConj_mono hcstk_io_join (Entails.refl P_ar)) ?_
  refine SepWPp.perm
    (step_after_read (cstk := cstk) (r := r_io)
      (pathCap := pathCap) (pathPtr := pathPtr) (pth := pth)
      (w0 := w0) (w1 := w1) (wTail := wTail)
      hC hcstk_ext hstk hfull hsp0_al hb hpth_le hpth_cap_lt
      hfz_r hsym_r hpc_r hrun_r hsp_r_al hsp_r hhcs_r hx19_r hx21_r
      ⟨by rw [hres_io.1, hpth_eq, hget_eq], hres_io.2⟩)
    (by dsimp only [P_ar]; sep_frame)

/-- Miss path from `+164` when `x.dir.path = []` (`MemcpyROOkExtX`): inline `x.name.to_owned()` at `+200..+316` → `+320`. -/
theorem step_miss_empty_roX
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {pathStk ioStk stk : Nat}
    {x : DirGetGhost} {s0 s : State}
    {w0 w1 wTail : BitVec 64} {R : SepProp}
    (hC : AllocContractsX img A ext)
    (hRO : MemcpyROOkExtX img ext)
    (hIoCall : PathIoContract img A ext rd pathOk ioStk)
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hstk : 112 + dirGetCalleeStk pathStk ioStk ≤ stk)
    (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hb : (img.base &&& 0xfff#64) = 0#64)
    (hname_lt : x.name.length < 2 ^ 32)
    (hpOk : pathOk (pathOf x.dir.path x.name))
    (hdir_nil : x.dir.path = [])
    (hfz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName + 164#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = s0.sp - 112#64)
    (hhcs : HighCalleeSaved s0 s)
    (hfs : s.fs.files = s0.fs.files)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.name.length)
    (hx21 : s.readReg64 .x21 = x.self)
    (hx22 : s.readReg64 .x22 = x.nameA)
    (hall_ne : ∀ e ∈ x.dir.changed, e.1 ≠ x.name) :
    SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      (s0.readReg64 .lr) s
      ((dirAt A x.self x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗
        stackAt (s0.sp - 112#64) (dirGetCalleeStk pathStk ioStk) ∗
        memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗
        dirGetRoBundle img.base w0 w1 wTail)
      (dirGetPostQ rd pathOk A img stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk)
          (stk - (112 + dirGetCalleeStk pathStk ioStk)) ∗ R) R)
      (dirGetPanicQp rd pathOk A img stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk)
          (stk - (112 + dirGetCalleeStk pathStk ioStk)) ∗ R) R) := by
  let cstk := dirGetCalleeStk pathStk ioStk
  have hcstk_ext : extHookStack ≤ cstk := Nat.le_max_right _ _
  have hget_eq : x.dir.get rd s0.fs.files x.name =
      rd s0.fs.files (pathOf x.dir.path x.name) := by
    cases hd : x.dir with | mk p ch =>
    simp only [hd] at hall_ne ⊢
    have h1 := dirGhost_get_append_of_ne ch [] p rd s0.fs.files x.name hall_ne
    simpa [dirGhost_get_nil] using h1
  unfold dirAt strRefAt
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine sepWPp_exists_left fun dirPathPtr => ?_
  have hself32 : (x.self + 24#64) + 8#64 = x.self + 32#64 := by simp only [BitVec.add_assoc]; rfl
  rw [hself32]
  have hrepack_dir :
      RustHeap.vecOf A 48 8 (dirEntryAt A) x.self x.dir.changed ∗
        ((x.self + 24#64) ↦₆₄ dirPathPtr) ∗
        ((x.self + 32#64) ↦₆₄ BitVec.ofNat 64 x.dir.path.length) ∗
        (dirPathPtr ↦ᵣ x.dir.path) ⊢
      dirAt A x.self x.dir := by
    unfold dirAt strRefAt
    refine sepConj_mono (Entails.refl _) ?_
    refine Entails.trans ?_ (Entails.sepExists_intro dirPathPtr)
    rw [hself32]
    exact Entails.refl _
  have hbit63 : (BitVec.ofNat 64 x.name.length)[63] = false :=
    ofNat_getElem_63_false (lt_pow63_of_lt_pow32_m hname_lt)
  have hbit63_lsb : (BitVec.ofNat 64 x.name.length).getLsbD 63 = false :=
    ofNat_getLsbD_63_false (lt_pow63_of_lt_pow32_m hname_lt)
  have _ := hbit63; have _ := hbit63_lsb
  have hsp24_split :
      memRegion (s0.sp - 112#64 + 24#64) 24 =
        (∃∗ p2 : BitVec 64, ∃∗ p1 : BitVec 64, ∃∗ p0 : BitVec 64,
          ((s0.sp - 112#64 + 24#64) ↦₆₄ p0) ∗
          ((s0.sp - 112#64 + 32#64) ↦₆₄ p1) ∗
          ((s0.sp - 112#64 + 40#64) ↦₆₄ p2)) := by
    rw [memRegion_split (s0.sp - 112#64 + 24#64) 8 16 (by decide),
        memRegion_split (s0.sp - 112#64 + 24#64 + 8#64) 8 8 (by decide),
        ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  rw [hsp24_split]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine sepWPp_exists_left fun p2 => sepWPp_exists_left fun p1 =>
    sepWPp_exists_left fun p0 => ?_
  have hnm_cases : x.name = [] ∨ 0 < x.name.length := by cases x.name <;> simp
  rcases hnm_cases with hnm_nil | hnm_pos
  · have hfn : libsignalSessionCode.fnOff dirGetName =
        ls_off% "<libsignal_cli::stores::Dir>::get" := dirGet_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode dirGetBin img.base
      (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_cli::stores::Dir>::get")) 164 8
    code_fetches_range CryptoVerification.libsignalSessionCode dirGetBin img.base
      (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_cli::stores::Dir>::get")) 200 4
    code_fetches_range CryptoVerification.libsignalSessionCode dirGetBin img.base
      (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_cli::stores::Dir>::get")) 220 4
    code_fetches_range CryptoVerification.libsignalSessionCode dirGetBin img.base
      (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_cli::stores::Dir>::get")) 308 12
    clear hfn
    generalize hentry_raw :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName = fnStart at *
    generalize hprog_raw :
      libsignalSessionCode.rebase img.base (Rust.withPanics ext) = prog at *
    have he : FrozenEq (prog.fnAddr dirGetName) fnStart := ⟨hentry_raw⟩
    have hp : FrozenEq (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) prog := ⟨hprog_raw⟩
    clear hentry_raw hprog_raw
    examples_hide_fetches
    refine seq_frozen_state (mid := fnStart + 320#64) hfz ?_
    simp only [hdir_nil, hnm_nil, List.length_nil] at hx20 ⊢
    wp_steps
    have hrepack_dir0 :
        RustHeap.vecOf A 48 8 (dirEntryAt A) x.self x.dir.changed ∗
          ((x.self + 24#64) ↦₆₄ dirPathPtr) ∗
          ((x.self + 32#64) ↦₆₄ 0#64) ∗
          (dirPathPtr ↦ᵣ []) ⊢
        dirAt A x.self x.dir := by
      simpa [hdir_nil] using hrepack_dir
    apply SepWP.fold hrepack_dir0 (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hfz_m
    have heq_emp : ((1#64 : BitVec 64) ↦ₛ ([] : List (BitVec 8))) = emp := pointsToBytes_nil _
    rw [← emp_sepConj (dirAt A x.self x.dir), ← heq_emp]
    rcases he with ⟨rfl⟩; rcases hp with ⟨rfl⟩
    refine SepWPp.perm
      (step_miss_call_io (pathStk := pathStk)
        hC hIoCall hstk hfull hsp0_al hb hpOk hget_eq
        (pathCap := 0#64) (pathPtr := 1#64) (pth := [])
        (w0 := w0) (w1 := w1) (wTail := wTail)
        (by simp [hdir_nil, hnm_nil, pathOf]) (by simp) (by decide) (by decide)
        hfz_m
        (by simp only [wp_norm, arm64_norm, *])
        (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simpa only [wp_norm, arm64_norm] using hsp_al)
        (by simp only [wp_norm, arm64_norm, *])
        (hhcs.of_steps
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm]))
      (by
        have h0_ite :
            (if (0#64 : BitVec 64) = 0 then emp
             else A.live 1#64 (0#64).toNat 1 ∗
               memRegion (1#64 + BitVec.ofNat 64 ([] : List (BitVec 8)).length)
                 ((0#64).toNat - ([] : List (BitVec 8)).length)) = emp := rfl
        have h0_len : BitVec.ofNat 64 ([] : List (BitVec 8)).length = 0#64 := rfl
        rw [hnm_nil, h0_ite, h0_len]
        simp only [emp_sepConj, sepConj_emp]
        ac_rfl)
  · have hnm_ne0 : (BitVec.ofNat 64 x.name.length == 0#64) = false :=
      ofNat_beq_zero_false hnm_pos (lt_pow64_of_lt_pow32_m hname_lt)
    have _ := hnm_ne0
    have hnm_toNat : (BitVec.ofNat 64 x.name.length).toNat = x.name.length :=
      ofNat64_toNat_of_lt32_m hname_lt
    have hlay_nm : LayoutOk x.name.length 1 :=
      ⟨hnm_pos, ⟨0, rfl⟩, Nat.succ_le_of_lt (lt_pow63_of_lt_pow32_m hname_lt)⟩
    have hshim_fs := subroutine_ok_inImage_withFsInv hFs
      (hC.shim_ok_at dirGetName
        (ls_rel% "<libsignal_cli::stores::Dir>::get" "__rustc::__rust_no_alloc_shim_is_unstable_v2")
        (hk := by rw [dirGet_fnOff]; simp only [arm64_norm]))
      s0.fs.files s0.trace
    have halloc_fs := subroutine_ok_inImage_withFsInv hFs
      (hC.alloc_ok_at dirGetName
        (ls_rel% "<libsignal_cli::stores::Dir>::get" "__rustc::__rust_alloc")
        (hk := by rw [dirGet_fnOff]; simp only [arm64_norm]))
      s0.fs.files s0.trace
    have hmc_fs := subroutine_ok_inImage_withFsInv hFs
      (sessionMemcpyBytesAtInImage_ok_at_roX hC hRO x.nameRo)
      s0.fs.files s0.trace
    have hpanic := panic_at_handle_error_dirGet img.base ext
    have _ := hpanic
    have hfn : libsignalSessionCode.fnOff dirGetName =
        ls_off% "<libsignal_cli::stores::Dir>::get" := dirGet_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode dirGetBin img.base
      (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_cli::stores::Dir>::get")) 164 8
    code_fetches_range CryptoVerification.libsignalSessionCode dirGetBin img.base
      (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_cli::stores::Dir>::get")) 200 68
    code_fetches_range CryptoVerification.libsignalSessionCode dirGetBin img.base
      (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_cli::stores::Dir>::get")) 312 8
    code_fetches_range CryptoVerification.libsignalSessionCode dirGetBin img.base
      (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_cli::stores::Dir>::get")) 500 24
    dsimp only [tripleRatchetProgAtExt] at hshim_fs halloc_fs hmc_fs
    clear hfn
    rw [stackAt_sub_split (s0.sp - 112#64) hcstk_ext (cstk_le_pow64_m hstk hfull)]
    have hcstk_ext_join :
        memRegion (s0.sp - 112#64 - BitVec.ofNat 64 cstk) (cstk - extHookStack) ∗
          stackAt (s0.sp - 112#64) extHookStack ⊢
        stackAt (s0.sp - 112#64) cstk := by
      rw [stackAt_sub_split (s0.sp - 112#64) hcstk_ext (cstk_le_pow64_m hstk hfull)]
      exact Entails.refl _
    generalize hentry_raw :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName = fnStart at *
    generalize hprog_raw :
      libsignalSessionCode.rebase img.base (Rust.withPanics ext) = prog at *
    have he : FrozenEq (prog.fnAddr dirGetName) fnStart := ⟨hentry_raw⟩
    have hp : FrozenEq (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) prog := ⟨hprog_raw⟩
    clear hentry_raw hprog_raw
    examples_hide_fetches
    refine seq_frozen_state
      (mid := fnStart + bv% (ls_rel% "<libsignal_cli::stores::Dir>::get" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      hfz ?_
    simp only [hdir_nil, List.length_nil]
    wp_steps
    have hrepack_dir0 :
        RustHeap.vecOf A 48 8 (dirEntryAt A) x.self x.dir.changed ∗
          ((x.self + 24#64) ↦₆₄ dirPathPtr) ∗
          ((x.self + 32#64) ↦₆₄ 0#64) ∗
          (dirPathPtr ↦ᵣ []) ⊢
        dirAt A x.self x.dir := by
      simpa [hdir_nil] using hrepack_dir
    apply SepWP.fold hrepack_dir0 (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hfz1
    refine SepWPp.call_inImage_frame (x := ())
      (T := stackAt (s0.sp - 112#64) extHookStack)
      (hoom := fun _ _ _ ho => False.elim (false_of_fsInv_false_miss ho))
      hshim_fs hfz1 (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs)
      (by simp only [wp_norm, arm64_norm, *])
      (by simpa only [wp_norm, arm64_norm] using hsp_al)
      (by wp_norm_lhs)
      (by simp only [withFsInv, withStack, sessionShimSpec, emp_sepConj, wp_norm, hsp]; rfl)
      (fsInv_of_files_trace_eq (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]))
      (by sep_frame)
      (fun _ _ _ _ hex => false_of_fsInv_false_miss hex)
      (fun _ _ => panicQp_of_fsInv_false_miss)
      (fun sf1 hpc1 hrun1 hsp1 hcs1 hfz2 hsym2 => ?_)
    simp only [withFsInv, withStack, sessionShimSpec, wp_norm, hsp, sepConj_assoc]
    refine SepWPp.pure_left fun hfs1_inv => SepWPp.pure_left fun htr1 => ?_
    have hhcs1 : HighCalleeSaved s0 sf1 :=
      hhcs.of_step_call hcs1
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [calleeSavedVRegs, wp_norm, arm64_norm])
    have hsp1_al : sf1.spAligned = true :=
      spAligned_of_sp_eq (by simpa only [wp_norm, arm64_norm] using hsp_al) hsp1
    have hsp1_eq : sf1.sp = s0.sp - 112#64 := by rw [hsp1]; simp only [wp_norm, arm64_norm, *]
    have hx19_1 : sf1.readReg64 .x19 = x.ret := by
      have := hcs1.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx19
    have hx20_1 : sf1.readReg64 .x20 = BitVec.ofNat 64 x.name.length := by
      have := hcs1.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx20
    have hx22_1 : sf1.readReg64 .x22 = x.nameA := by
      have := hcs1.2.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx22
    have htr1_s0 : sf1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
    have hfs1 : sf1.fs.files = s0.fs.files := files_eq_of_fsInv_trace_eq hfs1_inv htr1_s0
    refine seq_frozen_state
      (mid := fnStart + bv% (ls_rel% "<libsignal_cli::stores::Dir>::get" "__rustc::__rust_alloc"))
      hfz2 ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hfz3
    refine SepWPp.call_inImage_frame (x := (x.name.length, 1))
      (T := A.pool ∗ stackAt (s0.sp - 112#64) extHookStack)
      (hoom := fun _ _ _ ho => False.elim (false_of_fsInv_false_miss ho))
      halloc_fs hfz3 (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs)
      (by simp only [wp_norm, arm64_norm, *])
      (by simpa only [wp_norm, arm64_norm] using hsp1_al)
      (by wp_norm_lhs)
      (by simp only [withFsInv, rustAllocSpecWithStack, wp_norm, hsp1_eq, pure_sepConj_pure_assoc]; rfl)
      (by refine ⟨fsInv_of_files_trace_eq (by simp only [wp_norm, arm64_norm, *])
                    (by simp only [wp_norm, arm64_norm, *]),
                  by simp only [wp_norm, arm64_norm, *],
                  by simp only [wp_norm, arm64_norm],
                  hlay_nm⟩)
      (by sep_frame)
      (fun _ _ _ _ hex => false_of_fsInv_false_miss hex)
      (fun _ _ => panicQp_of_fsInv_false_miss)
      (fun sf2 hpc2 hrun2 hsp2 hcs2 hfz4 hsym4 => ?_)
    simp only [withFsInv, rustAllocSpecWithStack, wp_norm, hsp1_eq, sepConj_assoc]
    refine SepWPp.pure_left fun hfs2_inv => ?_
    have hhcs2 : HighCalleeSaved s0 sf2 :=
      hhcs1.of_step_call hcs2
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [calleeSavedVRegs, wp_norm, arm64_norm])
    have hsp2_al : sf2.spAligned = true :=
      spAligned_of_sp_eq (by simpa only [wp_norm, arm64_norm] using hsp1_al) hsp2
    have hsp2_eq : sf2.sp = s0.sp - 112#64 := by rw [hsp2]; simp only [wp_norm, arm64_norm, *]
    have hx19_2 : sf2.readReg64 .x19 = x.ret := by
      have := hcs2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx19_1
    have hx20_2 : sf2.readReg64 .x20 = BitVec.ofNat 64 x.name.length := by
      have := hcs2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx20_1
    have hx22_2 : sf2.readReg64 .x22 = x.nameA := by
      have := hcs2.2.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx22_1
    by_cases hoom : sf2.readReg64 (Reg.gpr 0#5) = 0
    · have hoom64 : sf2.readReg64 .x0 = 0#64 := hoom
      have _ := hoom64
      rw [ite_true_eq hoom]
      refine sepWPp_pure_mid2 (P1 := A.pool) (P2 := stackAt (s0.sp - 112#64) extHookStack)
        fun htr2 => ?_
      have htr2_eq : sf2.trace = s0.trace ++ [allocFailedEvent] := by
        simpa only [wp_norm, arm64_norm, htr1_s0] using htr2
      apply SepWPp.of_sepWP
        (mid := fnStart + bv% (ls_rel% "<libsignal_cli::stores::Dir>::get" "alloc::raw_vec::handle_error"))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) ?_
      exact dirGetPanicQp_of_panicked List.prefix_rfl htr2_eq (by simp only [wp_norm, arm64_norm])
    · set buf := sf2.readReg64 (Reg.gpr 0#5)
      have hoom_ne : buf ≠ 0#64 := hoom
      have hoom_beq : (buf == 0#64) = false := beq_false_of_ne hoom_ne
      have _ := hoom_beq
      rw [ite_false_eq hoom]
      simp only [sepConj_assoc]
      refine sepWPp_pure_mid2 (P1 := A.pool) (P2 := stackAt (s0.sp - 112#64) extHookStack)
        fun ⟨_, htr2⟩ => ?_
      have htr2_s0 : sf2.trace = s0.trace := by rw [htr2]; simp only [wp_norm, arm64_norm, *]
      have hfs2 : sf2.fs.files = s0.fs.files := files_eq_of_fsInv_trace_eq hfs2_inv htr2_s0
      refine seq_frozen_state
        (mid := fnStart + bv% (ls_rel% "<libsignal_cli::stores::Dir>::get" "memcpy"))
        hfz4 ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hfz5
      refine SepWPp.call_inImage_frame (x := (buf, x.nameA, x.name))
        (T := memRegion buf x.name.length ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 112#64) extHookStack)
        (hoom := fun _ _ _ ho => False.elim (false_of_fsInv_false_miss ho))
        hmc_fs hfz5 (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simpa only [wp_norm, arm64_norm] using hsp2_al)
        (by wp_norm_lhs)
        (by simp only [withFsInv, withStack, sessionMemcpyBytesAtSpec, wp_norm, hsp2_eq,
              sepConj_assoc, pure_sepConj_pure_assoc]; rfl)
        (by refine ⟨fsInv_of_files_trace_eq (by simp only [wp_norm, arm64_norm, *])
                      (by simp only [wp_norm, arm64_norm, *]),
                    rfl, trivial, hnm_toNat,
                    Nat.le_of_lt (lt_pow64_of_lt_pow32_m hname_lt)⟩)
        (by sep_frame)
        (fun _ _ _ _ hex => false_of_fsInv_false_miss hex)
        (fun _ _ => panicQp_of_fsInv_false_miss)
        (fun sf3 hpc3 hrun3 hsp3 hcs3 hfz6 hsym6 => ?_)
      simp only [withFsInv, withStack, sessionMemcpyBytesAtSpec, wp_norm, hsp2_eq, sepConj_assoc]
      refine SepWPp.pure_left fun hfs3_inv => SepWPp.pure_left fun ⟨_, htr3⟩ => ?_
      have hhcs3 : HighCalleeSaved s0 sf3 :=
        hhcs2.of_step_call hcs3
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm])
      have hsp3_eq : sf3.sp = s0.sp - 112#64 := by rw [hsp3]; simp only [wp_norm, arm64_norm, *]
      have hsp3_al : sf3.spAligned = true :=
        spAligned_of_sp_eq (by simpa only [wp_norm, arm64_norm] using hsp2_al) hsp3
      have hx19_3 : sf3.readReg64 .x19 = x.ret := by
        have := hcs3.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx19_2
      have hx20_3 : sf3.readReg64 .x20 = BitVec.ofNat 64 x.name.length := by
        have := hcs3.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx20_2
      have hx21_3 : sf3.readReg64 .x21 = buf := by
        have := hcs3.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this
      have htr3_s0 : sf3.trace = s0.trace := by rw [htr3]; simp only [wp_norm, arm64_norm, *]
      have hfs3 : sf3.fs.files = s0.fs.files := files_eq_of_fsInv_trace_eq hfs3_inv htr3_s0
      have hcap_ne : BitVec.ofNat 64 x.name.length ≠ 0 := by
        intro h0
        have ht : (BitVec.ofNat 64 x.name.length).toNat = (0 : BitVec 64).toNat :=
          congrArg BitVec.toNat h0
        rw [hnm_toNat] at ht
        exact Nat.ne_of_gt hnm_pos ht
      refine seq_frozen_state (mid := fnStart + 320#64) hfz6 ?_
      wp_steps
      apply SepWP.fold hcstk_ext_join (by sep_frame)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hfz7
      have hrem_zero :
          memRegion (buf + BitVec.ofNat 64 x.name.length)
            ((BitVec.ofNat 64 x.name.length).toNat - x.name.length) = emp := by
        rw [hnm_toNat, Nat.sub_self, memRegion_zero]
      rw [← sepConj_emp (A.live buf x.name.length 1), ← hrem_zero]
      have hlive_eq :
          A.live buf x.name.length 1 ∗
            memRegion (buf + BitVec.ofNat 64 x.name.length)
              ((BitVec.ofNat 64 x.name.length).toNat - x.name.length) =
          (if BitVec.ofNat 64 x.name.length = 0 then emp
           else A.live buf (BitVec.ofNat 64 x.name.length).toNat 1 ∗
             memRegion (buf + BitVec.ofNat 64 x.name.length)
               ((BitVec.ofNat 64 x.name.length).toNat - x.name.length)) := by
        rw [ite_false_eq hcap_ne, hnm_toNat]
      rw [hlive_eq]
      rcases he with ⟨rfl⟩; rcases hp with ⟨rfl⟩
      refine SepWPp.perm
        (step_miss_call_io (pathStk := pathStk)
          hC hIoCall hstk hfull hsp0_al hb hpOk hget_eq
          (pathCap := BitVec.ofNat 64 x.name.length) (pathPtr := buf) (pth := x.name)
          (w0 := w0) (w1 := w1) (wTail := wTail)
          (by simp [hdir_nil, pathOf]) (by rw [hnm_toNat])
          (by rw [hnm_toNat]; exact lt_pow63_of_lt_pow32_m hname_lt) hname_lt
          hfz7
          (by simp only [wp_norm, arm64_norm, *])
          (by wp_norm_lhs)
          (by simp only [wp_norm, arm64_norm, *])
          (by simpa only [wp_norm, arm64_norm] using hsp3_al)
          (by simp only [wp_norm, arm64_norm, *])
          (hhcs3.of_steps
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]))
        (by sep_frame)

/-- Miss path from `+164` when `x.dir.path = []`: inline `x.name.to_owned()` at `+200..+316` → `+320`. -/
theorem step_miss_empty
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {pathStk ioStk stk : Nat}
    {x : DirGetGhost} {s0 s : State}
    {w0 w1 wTail : BitVec 64} {R : SepProp}
    (hC : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec)
    (hIoCall : PathIoContract img A ext rd pathOk ioStk)
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hstk : 112 + dirGetCalleeStk pathStk ioStk ≤ stk)
    (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hb : (img.base &&& 0xfff#64) = 0#64)
    (hname_lt : x.name.length < 2 ^ 32)
    (hpOk : pathOk (pathOf x.dir.path x.name))
    (hdir_nil : x.dir.path = [])
    (hfz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName + 164#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = s0.sp - 112#64)
    (hhcs : HighCalleeSaved s0 s)
    (hfs : s.fs.files = s0.fs.files)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.name.length)
    (hx21 : s.readReg64 .x21 = x.self)
    (hx22 : s.readReg64 .x22 = x.nameA)
    (hall_ne : ∀ e ∈ x.dir.changed, e.1 ≠ x.name) :
    SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      (s0.readReg64 .lr) s
      ((dirAt A x.self x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗
        stackAt (s0.sp - 112#64) (dirGetCalleeStk pathStk ioStk) ∗
        memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗
        dirGetRoBundle img.base w0 w1 wTail)
      (dirGetPostQ rd pathOk A img stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk)
          (stk - (112 + dirGetCalleeStk pathStk ioStk)) ∗ R) R)
      (dirGetPanicQp rd pathOk A img stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk)
          (stk - (112 + dirGetCalleeStk pathStk ioStk)) ∗ R) R) :=
  step_miss_empty_roX hC (memcpyROOkExtX_of_hookSat hRO) hIoCall hFs hstk hfull hsp0_al hb
    hname_lt hpOk hdir_nil hfz hsym hpc hrun hsp_al hsp hhcs hfs htr hx19 hx20 hx21 hx22 hall_ne

end CryptoVerification.SignalSession.Cli.Get.Helpers
