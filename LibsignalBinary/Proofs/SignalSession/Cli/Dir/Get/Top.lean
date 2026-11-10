/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.Pure
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.Decode
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.LoopAdv
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.MissTail
import ProofLib.SepLogic.WPp

/-!
# Entry Prologue (`+0`..`+68`) and Top-Level Composition for `<signal_session::stores::Dir>::get`

Composes the entry prologue with `step_loop_noRO` and `step_miss_tail_roX` over an abstract
`PathIoContract`.
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

private def stateOfFrozen {img : Obj.Image} {st : State} (_ : img.FrozenLoaded st) : State := st

private theorem setup_x24_48_eq (n : Nat) :
    (BitVec.ofNat 64 n + (BitVec.ofNat 64 n <<< 1)) <<< 4 =
      BitVec.ofNat 64 (48 * n) := by
  have hb : ∀ v : BitVec 64, (v + (v <<< 1)) <<< 4 = 48#64 * v := by intro v; bv_bits
  rw [hb, Nat.mul_comm 48 n, BitVec.ofNat_mul, BitVec.mul_comm]

private theorem sub112_aligned {sp : BitVec 64} (hm : sp &&& 15#64 = 0#64) :
    (sp - 112#64) &&& 15#64 = 0#64 := by
  bv_bits

/-- Verifies `<signal_session::stores::Dir>::get` from entry `+0` given `PathIoContract`,
`DirGetRoData img`, and `< 2 ^ 32` `pathOk` lengths. -/
theorem dirGet_ok_of_ioCall_roX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {pathStk ioStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hRO : MemcpyROOkExtX img ext)
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec)
    (hPath : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName)
      (pathSpec A img pathStk))
    (hIoCall : PathIoContract img A ext rd pathOk ioStk)
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hstk : 0x70 + dirGetCalleeStk pathStk ioStk ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64)
    (hRo : DirGetRoData img)
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img stk) := by
  let cstk := dirGetCalleeStk pathStk ioStk
  have hcstk_ext : extHookStack ≤ cstk := Nat.le_max_right _ _
  have hstk112 : 112 + cstk ≤ stk := hstk
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre halign
  have hsp0_mask : (s0.sp &&& 15#64 == 0#64) = true := halign
  have hsp_sub_al : ({ s0 with sp := s0.sp - 112#64 } : State).spAligned = true :=
    beq_iff_eq.mpr (sub112_aligned (eq_of_beq hsp0_mask))
  change s0.mem ⊨
    (⌜ImgCallInv img s0⌝ ∗
      (⌜s0.readReg64 .x0 = x.ret ∧ s0.readReg64 .x1 = x.self ∧ s0.readReg64 .x2 = x.nameA ∧
        (s0.readReg64 .x3).toNat = x.name.length ∧ x.name.length < 2 ^ 32 ∧
        x.dir.path.length < 2 ^ 32 ∧ pathOk (pathOf x.dir.path x.name)⌝ ∗
        dirAt A x.self x.dir ∗ SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗ stackAt s0.sp stk ∗ A.pool)) ∗ R at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfz0, hsym0⟩,
    ⟨hx0, hx1, hx2, hx3, hname_lt, hdir_lt, hpOk⟩, hsat0⟩
  have hpth_len_lt : (pathOf x.dir.path x.name).length < 2 ^ 32 := hpathLen _ hpOk
  have hx3_bv : s0.readReg64 .x3 = BitVec.ofNat 64 x.name.length := by
    apply BitVec.eq_of_toNat_eq
    rw [hx3, ofNat64_toNat_of_lt32 hname_lt]
  have hfull : stk ≤ 2 ^ 64 :=
    stk_le_of_memRegion_sep (r := x.ret) (sp0 := s0.sp) (stk := stk)
      (F := dirAt A x.self x.dir ∗ SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗ A.pool ∗ R)
      (Satisfies.mono (Entails.of_eq (by sep_frame)) hsat0)
  obtain ⟨w0, w1, wTail, hsat_ro⟩ := hRo hfz0 hsat0
  rw [stackAt_dirGet_split s0.sp hstk112 hfull] at hsat_ro
  let P0 : SepProp :=
    (dirAt A x.self x.dir ∗
      SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
      memRegion x.ret 48 ∗
      stackAt (s0.sp - 112#64) cstk ∗
      memRegion (s0.sp - 112#64) 112 ∗
      A.pool) ∗
    dirGetRoBundle img.base w0 w1 wTail
  let Fr : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R
  refine ⟨P0, Fr, Satisfies.mono (Entails.of_eq (by dsimp only [P0, Fr]; sep_frame)) hsat_ro, ?_⟩
  dsimp only [P0, Fr, tripleRatchetProgAtExt] at hpc ⊢
  rw [frame_0x70_split (s0.sp - 112#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
  refine sepWPp_exists_left fun v0 => sepWPp_exists_left fun v1 =>
    sepWPp_exists_left fun v2 => sepWPp_exists_left fun v3 =>
    sepWPp_exists_left fun v4 => sepWPp_exists_left fun v5 =>
    sepWPp_exists_left fun v6 => sepWPp_exists_left fun v7 => ?_
  unfold dirAt RustHeap.vecOf RustHeap.vecAt
  simp only [sepExists_sepConj_left]
  refine sepWPp_exists_left fun changedCap => sepWPp_exists_left fun changedPtr => ?_
  rw [vecBuf_dirEntry_expose]
  simp only [sepConj_assoc]
  rw [← sepConj_assoc, sepConj_comm (vecHeader _ _ _ _) ⌜_⌝, sepConj_assoc]
  refine SepWPp.pure_left fun hcap_ok => ?_
  unfold vecHeader
  have hch_cases : x.dir.changed = [] ∨ (x.dir.changed ≠ [] ∧ 0 < x.dir.changed.length) := by
    cases x.dir.changed <;> simp
  rcases hch_cases with hch_nil | ⟨hch_ne, hch_pos⟩
  · -- Empty `x.dir.changed = []`: jump to `step_miss_tail` (`+164`)
    have hrepack_dir0 :
        ((x.self ↦₆₄ changedCap) ∗ ((x.self + 8#64) ↦₆₄ changedPtr) ∗
          ((x.self + 16#64) ↦₆₄ 0#64) ∗
          RustHeap.arrayAt (dirEntryAt A) 48 changedPtr [] ∗
          (if changedCap = 0 then emp
           else A.live changedPtr (changedCap.toNat * 48) 8 ∗
             memRegion (changedPtr + 0#64) ((changedCap.toNat - 0) * 48))) ∗
          strRefAt (x.self + 24#64) x.dir.path ⊢
        dirAt A x.self x.dir := by
      unfold dirAt RustHeap.vecOf RustHeap.vecAt
      refine sepConj_mono ?_ (Entails.refl _)
      refine Entails.trans ?_ (Entails.sepExists_intro changedCap)
      refine Entails.trans ?_ (Entails.sepExists_intro changedPtr)
      rw [vecBuf_dirEntry_expose]
      unfold vecHeader
      simp only [hch_nil, List.length_nil, sepConj_assoc]
      have hpure_r :
          (x.self ↦₆₄ changedCap) ∗ ((x.self + 8#64) ↦₆₄ changedPtr) ∗
            ((x.self + 16#64) ↦₆₄ 0#64) ∗
            ⌜(0 : Nat) ≤ changedCap.toNat ∧ changedCap.toNat * 48 < 2 ^ 63 ∧ changedPtr ≠ 0⌝ ∗
            RustHeap.arrayAt (dirEntryAt A) 48 changedPtr [] ∗
            (if changedCap = 0 then emp
             else A.live changedPtr (changedCap.toNat * 48) 8 ∗
               memRegion (changedPtr + 0#64) ((changedCap.toNat - 0) * 48)) =
          ⌜(0 : Nat) ≤ changedCap.toNat ∧ changedCap.toNat * 48 < 2 ^ 63 ∧ changedPtr ≠ 0⌝ ∗
            ((x.self ↦₆₄ changedCap) ∗ ((x.self + 8#64) ↦₆₄ changedPtr) ∗
              ((x.self + 16#64) ↦₆₄ 0#64) ∗
              RustHeap.arrayAt (dirEntryAt A) 48 changedPtr [] ∗
              (if changedCap = 0 then emp
               else A.live changedPtr (changedCap.toNat * 48) 8 ∗
                 memRegion (changedPtr + 0#64) ((changedCap.toNat - 0) * 48))) := by ac_rfl
      rw [hpure_r]
      exact Entails.pure_right (by simpa [hch_nil] using hcap_ok) (Entails.refl _)
    have hfn : libsignalSessionCode.fnOff dirGetName =
        ls_off% "<libsignal_cli::stores::Dir>::get" := dirGet_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode dirGetBin img.base
      (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_cli::stores::Dir>::get")) 0 48
    clear hfn
    generalize hentry_raw :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName = fnStart at *
    generalize hprog_raw :
      libsignalSessionCode.rebase img.base (Rust.withPanics ext) = prog at *
    have he : FrozenEq (prog.fnAddr dirGetName) fnStart := ⟨hentry_raw⟩
    have hp : FrozenEq (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) prog := ⟨hprog_raw⟩
    clear hentry_raw hprog_raw
    examples_hide_fetches
    refine seq_frozen_state (mid := fnStart + 164#64) hfz0 ?_
    simp only [hch_nil, List.length_nil]
    wp_steps
    apply SepWP.fold hrepack_dir0 (by sep_frame)
    apply SepWP.fold (Entails.refl (savedRegsAt (s0.sp - 112#64) s0))
      (by unfold savedRegsAt; simp only [wp_norm, arm64_norm]; sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hfz1
    let st1 := stateOfFrozen hfz1
    have hpc1 : st1.pc = fnStart + 164#64 := by dsimp only [st1, stateOfFrozen]; wp_norm_lhs
    have hrun1 : st1.status = ExecStatus.Running := by simp only [st1, stateOfFrozen, wp_norm, arm64_norm, *]
    have hsp1_al : st1.spAligned = true := by simpa only [st1, stateOfFrozen, State.spAligned, wp_norm, arm64_norm] using hsp_sub_al
    have hsp1 : st1.sp = s0.sp - 112#64 := by simp only [st1, stateOfFrozen, wp_norm, arm64_norm]
    have hhcs1 : HighCalleeSaved s0 st1 :=
      (HighCalleeSaved.refl s0).of_steps
        (by simp only [st1, stateOfFrozen, wp_norm, arm64_norm])
        (by simp only [st1, stateOfFrozen, wp_norm, arm64_norm])
        (by simp only [st1, stateOfFrozen, wp_norm, arm64_norm])
        (by simp only [st1, stateOfFrozen, wp_norm, arm64_norm])
        (by simp only [st1, stateOfFrozen, calleeSavedVRegs, wp_norm, arm64_norm])
    have hsym1 : st1.symtab = img.symtab := by simp only [st1, stateOfFrozen, wp_norm, arm64_norm, *]
    have hfs1 : st1.fs.files = s0.fs.files := by simp only [st1, stateOfFrozen, wp_norm, arm64_norm]
    have htr1 : st1.trace = s0.trace := by simp only [st1, stateOfFrozen, wp_norm, arm64_norm]
    have hx19_1 : st1.readReg64 .x19 = x.ret := by simp only [st1, stateOfFrozen, wp_norm, arm64_norm, *]
    have hx20_1 : st1.readReg64 .x20 = BitVec.ofNat 64 x.name.length := by simp only [st1, stateOfFrozen, wp_norm, arm64_norm]
    have hx21_1 : st1.readReg64 .x21 = x.self := by simp only [st1, stateOfFrozen, wp_norm, arm64_norm, *]
    have hx22_1 : st1.readReg64 .x22 = x.nameA := by simp only [st1, stateOfFrozen, wp_norm, arm64_norm, *]
    rcases he with ⟨rfl⟩; rcases hp with ⟨rfl⟩
    refine SepWPp.perm
      (step_miss_tail_roX (w0 := w0) (w1 := w1) (wTail := wTail)
        hC hRO hPath hIoCall hFs hstk112 hfull halign hb
        hname_lt hdir_lt hpOk hpth_len_lt hfz1 hsym1 hpc1 hrun1 hsp1_al hsp1 hhcs1
        hfs1 htr1 hx19_1 hx20_1 hx21_1 hx22_1
        (fun _ hm => False.elim (List.not_mem_nil (hch_nil ▸ hm))))
      (by simp only [wp_norm, arm64_norm]; sep_frame)
  · -- Non-empty `x.dir.changed ≠ []`: enter `step_loop` (`+80`)
    have hch_lt48 : x.dir.changed.length * 48 < 2 ^ 63 :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 48 hcap_ok.1) hcap_ok.2.1
    have hch_lt63 : x.dir.changed.length < 2 ^ 63 :=
      Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by decide : 0 < 48)) hch_lt48
    have hch_ne0 : (BitVec.ofNat 64 x.dir.changed.length == 0#64) = false :=
      ofNat_beq_zero_false hch_pos (lt_pow64_of_lt_pow63 hch_lt63)
    have hx24_init :
        (BitVec.ofNat 64 x.dir.changed.length + (BitVec.ofNat 64 x.dir.changed.length <<< 1)) <<< 4 =
          BitVec.ofNat 64 (48 * x.dir.changed.length) :=
      setup_x24_48_eq x.dir.changed.length
    have hfn : libsignalSessionCode.fnOff dirGetName =
        ls_off% "<libsignal_cli::stores::Dir>::get" := dirGet_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode dirGetBin img.base
      (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_cli::stores::Dir>::get")) 0 68
    clear hfn
    generalize hentry_raw :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName = fnStart at *
    generalize hprog_raw :
      libsignalSessionCode.rebase img.base (Rust.withPanics ext) = prog at *
    have he : FrozenEq (prog.fnAddr dirGetName) fnStart := ⟨hentry_raw⟩
    have hp : FrozenEq (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) prog := ⟨hprog_raw⟩
    clear hentry_raw hprog_raw
    examples_hide_fetches
    refine seq_frozen_state (mid := fnStart + 80#64) hfz0 ?_
    wp_steps
    apply SepWP.fold (Entails.refl (vecHeader x.self changedCap changedPtr x.dir.changed.length))
      (by unfold vecHeader; sep_frame)
    apply SepWP.fold (Entails.refl (savedRegsAt (s0.sp - 112#64) s0))
      (by unfold savedRegsAt; simp only [wp_norm, arm64_norm]; sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hfz1
    let st1 := stateOfFrozen hfz1
    have harr_emp : RustHeap.arrayAt (dirEntryAt A) 48 changedPtr [] = emp := rfl
    rw [← emp_sepConj (RustHeap.arrayAt (dirEntryAt A) 48 changedPtr x.dir.changed),
        ← harr_emp]
    have hsym1 : st1.symtab = img.symtab := by simp only [st1, stateOfFrozen, wp_norm, arm64_norm, *]
    have hpc1 : st1.pc = fnStart + 80#64 := by dsimp only [st1, stateOfFrozen]; wp_norm_lhs
    have hrun1 : st1.status = ExecStatus.Running := by simp only [st1, stateOfFrozen, wp_norm, arm64_norm, *]
    have hsp1_al : st1.spAligned = true := by simpa only [st1, stateOfFrozen, State.spAligned, wp_norm, arm64_norm] using hsp_sub_al
    have hsp1 : st1.sp = s0.sp - 112#64 := by simp only [st1, stateOfFrozen, wp_norm, arm64_norm]
    have hhcs1 : HighCalleeSaved s0 st1 :=
      (HighCalleeSaved.refl s0).of_steps
        (by simp only [st1, stateOfFrozen, wp_norm, arm64_norm])
        (by simp only [st1, stateOfFrozen, wp_norm, arm64_norm])
        (by simp only [st1, stateOfFrozen, wp_norm, arm64_norm])
        (by simp only [st1, stateOfFrozen, wp_norm, arm64_norm])
        (by simp only [st1, stateOfFrozen, calleeSavedVRegs, wp_norm, arm64_norm])
    have hfs1 : st1.fs.files = s0.fs.files := by simp only [st1, stateOfFrozen, wp_norm, arm64_norm]
    have htr1 : st1.trace = s0.trace := by simp only [st1, stateOfFrozen, wp_norm, arm64_norm]
    have hx19_1 : st1.readReg64 .x19 = x.ret := by simp only [st1, stateOfFrozen, wp_norm, arm64_norm, *]
    have hx20_1 : st1.readReg64 .x20 = BitVec.ofNat 64 x.name.length := by simp only [st1, stateOfFrozen, wp_norm, arm64_norm]
    have hx21_1 : st1.readReg64 .x21 = x.self := by simp only [st1, stateOfFrozen, wp_norm, arm64_norm, *]
    have hx22_1 : st1.readReg64 .x22 = x.nameA := by simp only [st1, stateOfFrozen, wp_norm, arm64_norm, *]
    have hx23_1 : st1.readReg64 .x23 = changedPtr + BitVec.ofNat 64 (48 * ([] : List (List (BitVec 8) × List (BitVec 8))).length) + 40#64 := by
      simp only [st1, stateOfFrozen, wp_norm, arm64_norm, *]
    have hx24_1 : st1.readReg64 .x24 = BitVec.ofNat 64 (48 * x.dir.changed.length) := by
      simp only [st1, stateOfFrozen, wp_norm, arm64_norm]
    rcases he with ⟨rfl⟩; rcases hp with ⟨rfl⟩
    refine SepWPp.perm
      (step_loop_noRO (cstk := cstk) (changedCap := changedCap) (changedPtr := changedPtr)
        (Extra := dirGetRoBundle img.base w0 w1 wTail)
        hC hBcmp hFs hcstk_ext hstk112 hfull halign hname_lt hcap_ok
        (fun sm hpcm hrunm hsp_alm hspm hhcsm hfzm hsymm hfsm htrm hx19m hx20m hx21m hx22m hall_ne =>
          step_miss_tail_roX (w0 := w0) (w1 := w1) (wTail := wTail)
            hC hRO hPath hIoCall hFs hstk112 hfull halign hb
            hname_lt hdir_lt hpOk hpth_len_lt hfzm hsymm hpcm hrunm hsp_alm hspm hhcsm
            hfsm htrm hx19m hx20m hx21m hx22m hall_ne)
        x.dir.changed [] st1 hch_ne rfl (fun _ hm => False.elim (List.not_mem_nil hm))
        hfz1 hsym1 hpc1 hrun1 hsp1_al hsp1 hhcs1 hfs1 htr1
        hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1)
      (by simp only [List.length_nil, Nat.mul_zero, BitVec.add_zero,
            wp_norm, arm64_norm]; sep_frame)

theorem dirGet_ok_of_ioCall {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {pathStk ioStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec)
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec)
    (hPath : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName)
      (pathSpec A img pathStk))
    (hIoCall : PathIoContract img A ext rd pathOk ioStk)
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hstk : 0x70 + dirGetCalleeStk pathStk ioStk ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64)
    (hRo : DirGetRoData img)
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img stk) :=
  dirGet_ok_of_ioCall_roX hC (memcpyROOkExtX_of_hookSat hRO) hBcmp hPath hIoCall hFs hstk hb
    hRo hpathLen

theorem dirGet_ok_of_ioCall_withStack {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {pathStk ioStk stk roStk : Nat}
    (hC : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName (sessionMemcpyRegionROSpecWithStack roStk))
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec)
    (hPath : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName)
      (pathSpec A img pathStk))
    (hIoCall : PathIoContract img A ext rd pathOk ioStk)
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hstk : 0x70 + dirGetCalleeStk pathStk ioStk ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64)
    (hRo : DirGetRoData img)
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hro : roStk ≤ extHookStack := by decide) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img stk) :=
  dirGet_ok_of_ioCall_roX hC (memcpyROOkExtX_of_withStack hro hRO) hBcmp hPath hIoCall hFs hstk hb
    hRo hpathLen

end CryptoVerification.SignalSession.Cli.Get.Helpers
