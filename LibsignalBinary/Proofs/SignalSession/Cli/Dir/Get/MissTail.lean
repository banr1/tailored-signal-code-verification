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
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.LoopAdv
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.MissEmpty
import ProofLib.SepLogic.WPp

/-!
# Cache-Miss Path Dispatch (`+164`..`+332`) for `<signal_session::stores::Dir>::get`

Verifies cache-miss path construction (`pathOf dir.path name`) and dispatch to the `+332` → `+336`
I/O call abstracted via `PathIoContract`.
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

/-- Miss path from `+164` (`MemcpyROOkExtX`): constructs `pathOf x.dir.path x.name` into `[sp + 24 .. sp + 48)`,
    invokes `hIoCall : PathIoContract` at `+332`, and finishes via `step_after_read`. -/
theorem step_miss_tail_roX
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {pathStk ioStk stk : Nat}
    {x : DirGetGhost} {s0 s : State}
    {w0 w1 wTail : BitVec 64} {R : SepProp}
    (hC : AllocContractsX img A ext)
    (hRO : MemcpyROOkExtX img ext)
    (hPath : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName)
      (pathSpec A img pathStk))
    (hIoCall : PathIoContract img A ext rd pathOk ioStk)
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hstk : 112 + dirGetCalleeStk pathStk ioStk ≤ stk)
    (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hb : (img.base &&& 0xfff#64) = 0#64)
    (hname_lt : x.name.length < 2 ^ 32)
    (hdir_lt : x.dir.path.length < 2 ^ 32)
    (hpOk : pathOk (pathOf x.dir.path x.name))
    (hpth_len_lt : (pathOf x.dir.path x.name).length < 2 ^ 32)
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
  have hdir_cases : x.dir.path = [] ∨ (x.dir.path ≠ [] ∧ 0 < x.dir.path.length) := by
    cases x.dir.path <;> simp
  rcases hdir_cases with hdir_nil | ⟨hdir_ne, hdir_pos⟩
  · exact step_miss_empty_roX hC hRO hIoCall hFs hstk hfull hsp0_al hb
      hname_lt hpOk hdir_nil hfz hsym hpc hrun hsp_al hsp hhcs hfs htr
      hx19 hx20 hx21 hx22 hall_ne
  · let cstk := dirGetCalleeStk pathStk ioStk
    have hcstk_path : pathStk ≤ cstk :=
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
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
    have hdir_ne0 : (BitVec.ofNat 64 x.dir.path.length == 0#64) = false :=
      ofNat_beq_zero_false hdir_pos (lt_pow64_of_lt_pow32 hdir_lt)
    have hdir_toNat : (BitVec.ofNat 64 x.dir.path.length).toNat = x.dir.path.length :=
      ofNat64_toNat_of_lt32 hdir_lt
    have hnm_toNat : (BitVec.ofNat 64 x.name.length).toNat = x.name.length :=
      ofNat64_toNat_of_lt32 hname_lt
    have _ := hdir_ne0; have _ := hdir_toNat; have _ := hnm_toNat
    have hpth_lt32 : (x.dir.path ++ [0x2f#8] ++ x.name).length < 2 ^ 32 := by
      rw [(pathOf_eq_path hdir_ne x.name).symm]
      exact hpth_len_lt
    have hpath_fs := subroutine_ok_inImage_withFsInv hFs (path_ok_at hPath) s0.fs.files s0.trace
    have hfn : libsignalSessionCode.fnOff dirGetName =
        ls_off% "<libsignal_cli::stores::Dir>::get" := dirGet_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode dirGetBin img.base
      (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_cli::stores::Dir>::get")) 164 36
    dsimp only [tripleRatchetProgAtExt] at hpath_fs
    clear hfn
    rw [stackAt_sub_split (s0.sp - 112#64) hcstk_path (cstk_le_pow64 hstk hfull)]
    have hcstk_path_join :
        memRegion (s0.sp - 112#64 - BitVec.ofNat 64 cstk) (cstk - pathStk) ∗
          stackAt (s0.sp - 112#64) pathStk ⊢
        stackAt (s0.sp - 112#64) cstk := by
      rw [stackAt_sub_split (s0.sp - 112#64) hcstk_path (cstk_le_pow64 hstk hfull)]
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
      (mid := fnStart + bv% (ls_rel% "<libsignal_cli::stores::Dir>::get" "libsignal_cli::stores::path"))
      hfz ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hfz1
    have htr_call : (stateOfFrozenMiss hfz1).trace = s0.trace := by
      simp only [stateOfFrozenMiss, wp_norm, arm64_norm, *]
    dsimp only [stateOfFrozenMiss] at htr_call
    refine SepWPp.call_inImage_frame
      (x := PathGhost.mk dirPathPtr x.dir.path true x.nameA x.name x.nameRo
        (s0.sp - 112#64 + 24#64))
      (T := (dirPathPtr ↦ᵣ x.dir.path) ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        memRegion (s0.sp - 112#64 + 24#64) 24 ∗
        stackAt (s0.sp - 112#64) pathStk ∗ A.pool)
      (hoom := fun _ _ _ ho => False.elim (false_of_fsInv_false_miss ho))
      hpath_fs hfz1 (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs)
      (by simp only [wp_norm, arm64_norm, *])
      (by simpa only [wp_norm, arm64_norm] using hsp_al)
      (by wp_norm_lhs)
      (by simp only [withFsInv, SpqrV1.ChainProofs.bytesAt_true, wp_norm, hsp,
            pure_sepConj_pure_assoc]; rfl)
      (by refine ⟨fsInv_of_files_trace_eq (by simp only [wp_norm, arm64_norm, *])
                    (by simp only [wp_norm, arm64_norm, *]),
                  trivial, trivial, hdir_toNat, trivial, hnm_toNat,
                  hdir_lt, hname_lt⟩)
      (by sep_frame)
      (fun _ _ _ _ hex => false_of_fsInv_false_miss hex)
      (fun sf_pan _ hm_pan => by
        have htmp := hm_pan
        dsimp only [withFsInv] at htmp
        simp only [sepConj_assoc, satisfies_pure_sepConj] at htmp
        rcases htmp with ⟨_, ⟨haf_p, hpfx_p⟩, _⟩
        rw [htr_call] at hpfx_p
        exact dirGetPanicQp_of_ok
          (by simpa only [allocFailedIn, htr_call] using haf_p) hpfx_p hm_pan)
      (fun sf1 hpc1 hrun1 hsp1 hcs1 hfz2 hsym2 => ?_)
    simp only [withFsInv, SpqrV1.ChainProofs.bytesAt_true, wp_norm, hsp, sepConj_assoc]
    refine SepWPp.pure_left fun hfs1_inv => SepWPp.pure_left fun htr1 => ?_
    refine sepWPp_unfold_vecU8 fun pathCap pathPtr hpth_le hpth_cap_lt _ => ?_
    have hhcs1 : HighCalleeSaved s0 sf1 :=
      hhcs.of_step_call hcs1
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [calleeSavedVRegs, wp_norm, arm64_norm])
    have hsp1_eq : sf1.sp = s0.sp - 112#64 := by rw [hsp1]; simp only [wp_norm, arm64_norm, *]
    have hsp1_al : sf1.spAligned = true :=
      spAligned_of_sp_eq (by simpa only [wp_norm, arm64_norm] using hsp_al) hsp1
    have hx19_1 : sf1.readReg64 .x19 = x.ret := by
      have := hcs1.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx19
    have htr1_s0 : sf1.trace = s0.trace := htr1.trans htr
    have hfs1 : sf1.fs.files = s0.fs.files := files_eq_of_fsInv_trace_eq hfs1_inv htr1_s0
    simp only [arm64_norm]
    refine seq_frozen_state (mid := fnStart + 320#64) hfz2 ?_
    wp_steps
    apply SepWP.fold hrepack_dir (by sep_frame)
    apply SepWP.fold hcstk_path_join (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hfz3
    rcases he with ⟨rfl⟩; rcases hp with ⟨rfl⟩
    refine SepWPp.perm
      (step_miss_call_io (pathStk := pathStk)
        hC hIoCall hstk hfull hsp0_al hb hpOk hget_eq
        (pathCap := pathCap) (pathPtr := pathPtr) (pth := x.dir.path ++ [0x2f#8] ++ x.name)
        (w0 := w0) (w1 := w1) (wTail := wTail)
        (pathOf_eq_path hdir_ne x.name).symm hpth_le hpth_cap_lt hpth_lt32
        hfz3
        (by simp only [wp_norm, arm64_norm, *])
        (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simpa only [wp_norm, arm64_norm] using hsp1_al)
        (by simp only [wp_norm, arm64_norm, *])
        (hhcs1.of_steps
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm]))
      (by simp only [arm64_norm]; sep_frame)

/-- Miss path from `+164`: constructs `pathOf x.dir.path x.name` into `[sp + 24 .. sp + 48)`,
    invokes `hIoCall : PathIoContract` at `+332`, and finishes via `step_after_read`. -/
theorem step_miss_tail
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {pathStk ioStk stk : Nat}
    {x : DirGetGhost} {s0 s : State}
    {w0 w1 wTail : BitVec 64} {R : SepProp}
    (hC : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec)
    (hPath : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName)
      (pathSpec A img pathStk))
    (hIoCall : PathIoContract img A ext rd pathOk ioStk)
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hstk : 112 + dirGetCalleeStk pathStk ioStk ≤ stk)
    (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hb : (img.base &&& 0xfff#64) = 0#64)
    (hname_lt : x.name.length < 2 ^ 32)
    (hdir_lt : x.dir.path.length < 2 ^ 32)
    (hpOk : pathOk (pathOf x.dir.path x.name))
    (hpth_len_lt : (pathOf x.dir.path x.name).length < 2 ^ 32)
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
  step_miss_tail_roX hC (memcpyROOkExtX_of_hookSat hRO) hPath hIoCall hFs hstk hfull hsp0_al hb
    hname_lt hdir_lt hpOk hpth_len_lt hfz hsym hpc hrun hsp_al hsp hhcs hfs htr
    hx19 hx20 hx21 hx22 hall_ne

end CryptoVerification.SignalSession.Cli.Get.Helpers
