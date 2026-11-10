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
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# Entry-Scan Loop (`+80`..`+108`) for `<signal_session::stores::Dir>::get`
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

private theorem false_of_fsInv_false {F0 : FsFiles} {T0 : List TraceEvent} {sf : State}
    {m : Memory} {R : SepProp}
    (h : m ⊨ (⌜FsInv F0 T0 sf⌝ ∗ ⌜False⌝) ∗ R) : False := by
  rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at h
  exact h.2.1

private theorem panicQp_of_fsInv_false
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {A : RustAlloc} {img : Obj.Image}
    {stk : Nat} {x : DirGetGhost} {s0 sf : State} {Fr R : SepProp}
    {F0 : FsFiles} {T0 : List TraceEvent} {Frame : SepProp} :
    dirGetPanicQp rd pathOk A img stk x s0 Fr R sf ((⌜FsInv F0 T0 sf⌝ ∗ ⌜False⌝) ∗ Frame) :=
  fun hm => False.elim (false_of_fsInv_false (by rw [sepConj_assoc] at hm; exact hm))

private theorem w32_zext_beq_zero_false {v : BitVec 64} (hne : v.setWidth 32 ≠ 0#32) :
    (((v.truncate 32).zeroExtend 64) == 0#64) = false := by
  apply beq_false_of_ne
  intro hz
  apply hne
  change (v.setWidth 32).setWidth 64 = 0#64 at hz
  bv_bits

/-- Scan `suf` starting at `+80` (`suf = hd :: rest`). Either matches an entry (`w0 = 0` →
    `step_hit_exit` at `+112`) or proves every entry in `x.dir.changed` differs from `x.name`
    and hands control to `hmiss` at `+164` with `dirAt A x.self x.dir` restored and
    `s.fs.files = s0.fs.files ∧ s.trace = s0.trace` preserved. -/
theorem step_loop_noRO
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {cstk stk : Nat}
    {x : DirGetGhost} {s0 : State}
    {changedCap changedPtr : BitVec 64}
    {Extra R : SepProp}
    (hC : AllocContractsX img A ext)
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec)
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hcstk : extHookStack ≤ cstk)
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hname_lt : x.name.length < 2 ^ 32)
    (hcap_ok : x.dir.changed.length ≤ changedCap.toNat ∧
      changedCap.toNat * 48 < 2 ^ 63 ∧ changedPtr ≠ 0)
    (hmiss : ∀ sm : State,
      sm.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName + 164#64 →
      sm.status = .Running →
      sm.spAligned = true →
      sm.sp = s0.sp - 112#64 →
      HighCalleeSaved s0 sm →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.fs.files = s0.fs.files →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = x.ret →
      sm.readReg64 .x20 = BitVec.ofNat 64 x.name.length →
      sm.readReg64 .x21 = x.self →
      sm.readReg64 .x22 = x.nameA →
      (∀ e ∈ x.dir.changed, e.1 ≠ x.name) →
      SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
        (s0.readReg64 .lr) sm
        ((dirAt A x.self x.dir ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          memRegion x.ret 48 ∗
          stackAt (s0.sp - 112#64) cstk ∗
          memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
          savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗ Extra)
        (dirGetPostQ rd pathOk A img stk x s0
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
        (dirGetPanicQp rd pathOk A img stk x s0
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)) :
    ∀ (suf pre : List (List (BitVec 8) × List (BitVec 8))) (s : State),
      suf ≠ [] →
      x.dir.changed = pre ++ suf →
      (∀ e ∈ pre, e.1 ≠ x.name) →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName + 80#64 →
      s.status = .Running →
      s.spAligned = true →
      s.sp = s0.sp - 112#64 →
      HighCalleeSaved s0 s →
      s.fs.files = s0.fs.files →
      s.trace = s0.trace →
      s.readReg64 .x19 = x.ret →
      s.readReg64 .x20 = BitVec.ofNat 64 x.name.length →
      s.readReg64 .x21 = x.self →
      s.readReg64 .x22 = x.nameA →
      s.readReg64 .x23 = changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64 →
      s.readReg64 .x24 = BitVec.ofNat 64 (48 * suf.length) →
      SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
        (s0.readReg64 .lr) s
        (((vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
          RustHeap.arrayAt (dirEntryAt A) 48 changedPtr pre ∗
          RustHeap.arrayAt (dirEntryAt A) 48
            (changedPtr + BitVec.ofNat 64 (48 * pre.length)) suf ∗
          (if changedCap = 0 then emp
           else A.live changedPtr (changedCap.toNat * 48) 8 ∗
             memRegion (changedPtr + BitVec.ofNat 64 (x.dir.changed.length * 48))
               ((changedCap.toNat - x.dir.changed.length) * 48)) ∗
          strRefAt (x.self + 24#64) x.dir.path) ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          memRegion x.ret 48 ∗
          stackAt (s0.sp - 112#64) cstk ∗
          memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
          savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗ Extra)
        (dirGetPostQ rd pathOk A img stk x s0
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
        (dirGetPanicQp rd pathOk A img stk x s0
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R) := by
  intro suf
  induction suf with
  | nil =>
    intro _ _ hsuf
    exact False.elim (hsuf rfl)
  | cons hd rest ih =>
    rcases hd with ⟨hdName, hdBytes⟩
    intro pre s _ hchanged hne hfz hsym hpc hrun hsp_al hsp hhcs hfs htr
      hx19 hx20 hx21 hx22 hx23 hx24
    rw [arrayAt_dirEntry_cons]
    refine SepWPp.perm
      (P' := vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length)) hdName ∗
        (((vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
          RustHeap.arrayAt (dirEntryAt A) 48 changedPtr pre ∗
          vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) hdBytes ∗
          RustHeap.arrayAt (dirEntryAt A) 48
            (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 48#64) rest ∗
          (if changedCap = 0 then emp
           else A.live changedPtr (changedCap.toNat * 48) 8 ∗
             memRegion (changedPtr + BitVec.ofNat 64 (x.dir.changed.length * 48))
               ((changedCap.toNat - x.dir.changed.length) * 48)) ∗
          strRefAt (x.self + 24#64) x.dir.path) ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          memRegion x.ret 48 ∗
          stackAt (s0.sp - 112#64) cstk ∗
          memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
          savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗ Extra))
      ?_ (by sep_frame)
    refine sepWPp_unfold_vecU8 fun nmCap nmPtr hnm_le hnm_lt hnm_ne => ?_
    have hrepack_nm :
        ((changedPtr + BitVec.ofNat 64 (48 * pre.length)) ↦₆₄ nmCap) ∗
          ((changedPtr + BitVec.ofNat 64 (48 * pre.length) + 8#64) ↦₆₄ nmPtr) ∗
          ((changedPtr + BitVec.ofNat 64 (48 * pre.length) + 16#64) ↦₆₄
            BitVec.ofNat 64 hdName.length) ∗
          (nmPtr ↦ₛ hdName) ∗
          (if nmCap = 0 then emp
           else A.live nmPtr nmCap.toNat 1 ∗
             memRegion (nmPtr + BitVec.ofNat 64 hdName.length) (nmCap.toNat - hdName.length)) ⊢
        vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length)) hdName := by
      dsimp only [vecU8]
      refine Entails.trans ?_ (Entails.sepExists_intro nmCap)
      refine Entails.trans ?_ (Entails.sepExists_intro nmPtr)
      rw [vecU8At_expose]
      exact Entails.pure_right ⟨hnm_le, hnm_lt, hnm_ne⟩ (Entails.refl _)
    have hx23_sub24 :
        (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64) + (-24#64) =
          changedPtr + BitVec.ofNat 64 (48 * pre.length) + 16#64 := by
      simp only [BitVec.add_assoc]; rfl
    have hx23_sub32 :
        (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64) + (-32#64) =
          changedPtr + BitVec.ofNat 64 (48 * pre.length) + 8#64 := by
      simp only [BitVec.add_assoc]; rfl
    by_cases hlen_eq : hdName.length = x.name.length
    · -- Equal lengths: compare via `bcmp`
      have hfn : libsignalSessionCode.fnOff dirGetName =
          ls_off% "<libsignal_cli::stores::Dir>::get" := dirGet_fnOff
      code_fetches_range CryptoVerification.libsignalSessionCode dirGetBin img.base
        (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_cli::stores::Dir>::get")) 80 32
      clear hfn
      have hbcmp_fs := subroutine_ok_inImage_withFsInv hFs
        (Arm64.subroutine_ok_inImage img (bcmp_ok_at (b := img.base) hBcmp)) s0.fs.files s0.trace
      dsimp only [tripleRatchetProgAtExt] at hbcmp_fs
      rw [stackAt_sub_split (s0.sp - 112#64) hcstk (cstk_le_pow64 hstk hfull)]
      have hcstk_join :
          memRegion (s0.sp - 112#64 - BitVec.ofNat 64 cstk) (cstk - extHookStack) ∗
            stackAt (s0.sp - 112#64) extHookStack ⊢
          stackAt (s0.sp - 112#64) cstk := by
        rw [stackAt_sub_split (s0.sp - 112#64) hcstk (cstk_le_pow64 hstk hfull)]
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
        (mid := fnStart + bv% (ls_rel% "<libsignal_cli::stores::Dir>::get" "bcmp"))
        hfz ?_
      rw [hlen_eq]
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hfz_b
      have hx2_nat : (BitVec.ofNat 64 x.name.length).toNat = x.name.length :=
        ofNat64_toNat_of_lt32 hname_lt
      refine SepWPp.call_inImage_frame
        (x := CliBcmpCall.mk nmPtr false hdName x.nameA x.nameRo x.name)
        (T := (nmPtr ↦ₛ hdName) ∗ SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 112#64) extHookStack)
        (hoom := fun _ _ _ ho => False.elim (false_of_fsInv_false ho))
        hbcmp_fs hfz_b (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simpa only [wp_norm, arm64_norm] using hsp_al)
        (by wp_norm_lhs)
        (by simp only [withFsInv, cliBcmpSpec, SpqrV1.ChainProofs.bytesAt_false,
              wp_norm, hsp, pure_sepConj_pure_assoc]; rfl)
        (by refine ⟨fsInv_of_files_trace_eq (by simp only [wp_norm, arm64_norm, *])
                      (by simp only [wp_norm, arm64_norm, *]),
                    by simp only [wp_norm, arm64_norm, *],
                    by simp only [wp_norm, arm64_norm, *],
                    by simp only [wp_norm, arm64_norm, *],
                    hlen_eq.symm⟩)
        (by sep_frame)
        (fun _ _ _ _ hex => false_of_fsInv_false hex)
        (fun _ _ => panicQp_of_fsInv_false)
        (fun sfb hpcb hrunb hspb hcsb hfzb hsymb => ?_)
      simp only [withFsInv, cliBcmpSpec, SpqrV1.ChainProofs.bytesAt_false, wp_norm, hsp, sepConj_assoc]
      refine SepWPp.pure_left fun hfs_fb => SepWPp.pure_left fun ⟨hw0_iff, htrb⟩ => ?_
      have hhcsb : HighCalleeSaved s0 sfb :=
        hhcs.of_step_call hcsb
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm])
      have hspb_al : sfb.spAligned = true :=
        spAligned_of_sp_eq (by simpa only [wp_norm, arm64_norm] using hsp_al) hspb
      have hspb_eq : sfb.sp = s0.sp - 112#64 := by rw [hspb]; simp only [wp_norm, arm64_norm, *]
      have hx19_b : sfb.readReg64 .x19 = x.ret := by
        have := hcsb.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx19
      have hx20_b : sfb.readReg64 .x20 = BitVec.ofNat 64 x.name.length := by
        have := hcsb.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx20
      have hx21_b : sfb.readReg64 .x21 = x.self := by
        have := hcsb.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx21
      have hx22_b : sfb.readReg64 .x22 = x.nameA := by
        have := hcsb.2.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx22
      have hx23_b : sfb.readReg64 .x23 = changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64 := by
        have := hcsb.2.2.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx23
      have hx24_b : sfb.readReg64 .x24 = BitVec.ofNat 64 (48 * ((hdName, hdBytes) :: rest).length) := by
        have := hcsb.2.2.2.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx24
      have htrb_s0 : sfb.trace = s0.trace := by rw [htrb]; simp only [wp_norm, arm64_norm, *]
      have hfiles_b : sfb.fs.files = s0.fs.files := files_eq_of_fsInv_trace_eq hfs_fb htrb_s0
      rw [← hlen_eq]
      by_cases hname_eq : hdName = x.name
      · -- Match (`w0 = 0`)
        have hw0_eq : (sfb.readReg64 .x0).setWidth 32 = 0#32 := hw0_iff.mpr hname_eq
        have hw0_zext : ((sfb.readReg64 .x0).truncate 32).zeroExtend 64 = 0#64 := by
          change ((sfb.readReg64 .x0).setWidth 32).zeroExtend 64 = 0#64
          rw [hw0_eq]; rfl
        have hw0_rr : sfb.readReg .W32 .x0 = 0#64 := hw0_zext
        have _ := hw0_eq; have _ := hw0_zext; have _ := hw0_rr
        subst hname_eq
        refine seq_frozen_state (mid := fnStart + 112#64) hfzb ?_
        wp_steps
        apply SepWP.fold hrepack_nm (by sep_frame)
        apply SepWP.fold hcstk_join (by sep_frame)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hfz_hit
        rcases he with ⟨rfl⟩; rcases hp with ⟨rfl⟩
        refine SepWPp.perm
          (step_hit_exit_noRO (cstk := cstk) (changedCap := changedCap) (changedPtr := changedPtr)
            (pre := pre) (rest := rest) (bs := hdBytes) (Extra := Extra)
            hC hcstk hstk hfull hsp0_al hchanged hne hcap_ok hfz_hit
            (by simp only [wp_norm, arm64_norm, *])
            (by wp_norm_lhs)
            (by simp only [wp_norm, arm64_norm, *])
            (by simpa only [wp_norm, arm64_norm] using hspb_al)
            (by simp only [wp_norm, arm64_norm, *])
            (hhcsb.of_steps
              (by simp only [wp_norm, arm64_norm])
              (by simp only [wp_norm, arm64_norm])
              (by simp only [wp_norm, arm64_norm])
              (by simp only [wp_norm, arm64_norm])
              (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *]))
          (by sep_frame)
      · -- Mismatch (`w0 ≠ 0`)
        have hw0_ne : ((sfb.readReg64 .x0).setWidth 32 == 0#32) = false :=
          beq_false_of_ne (fun h => hname_eq (hw0_iff.mp h))
        have hw0_zext_ne : (((sfb.readReg64 .x0).truncate 32).zeroExtend 64 == 0#64) = false :=
          w32_zext_beq_zero_false (fun h => hname_eq (hw0_iff.mp h))
        have hw0_rr_ne : (sfb.readReg .W32 .x0 == 0#64) = false := hw0_zext_ne
        have _ := hw0_ne; have _ := hw0_zext_ne; have _ := hw0_rr_ne
        refine seq_frozen_state (mid := fnStart + 68#64) hfzb ?_
        wp_steps
        apply SepWP.fold hrepack_nm (by sep_frame)
        apply SepWP.fold hcstk_join (by sep_frame)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hfz_adv
        rcases he with ⟨rfl⟩; rcases hp with ⟨rfl⟩
        refine SepWPp.perm
          (step_loop_advance (cstk := cstk) (changedCap := changedCap) (changedPtr := changedPtr)
            (pre := pre) (rest := rest) (hdName := hdName) (hdBytes := hdBytes) (Extra := Extra)
            hstk hfull hcap_ok hchanged hne hname_eq hmiss ih
            hfz_adv
            (by simp only [wp_norm, arm64_norm, *])
            (by wp_norm_lhs)
            (by simp only [wp_norm, arm64_norm, *])
            (by simpa only [wp_norm, arm64_norm] using hspb_al)
            (by simp only [wp_norm, arm64_norm, *])
            (hhcsb.of_steps
              (by simp only [wp_norm, arm64_norm])
              (by simp only [wp_norm, arm64_norm])
              (by simp only [wp_norm, arm64_norm])
              (by simp only [wp_norm, arm64_norm])
              (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *]))
          (by sep_frame)
    · -- Distinct lengths
      have hfn : libsignalSessionCode.fnOff dirGetName =
          ls_off% "<libsignal_cli::stores::Dir>::get" := dirGet_fnOff
      code_fetches_range CryptoVerification.libsignalSessionCode dirGetBin img.base
        (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_cli::stores::Dir>::get")) 80 12
      clear hfn
      generalize hentry_raw :
        (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName = fnStart at *
      generalize hprog_raw :
        libsignalSessionCode.rebase img.base (Rust.withPanics ext) = prog at *
      have he : FrozenEq (prog.fnAddr dirGetName) fnStart := ⟨hentry_raw⟩
      have hp : FrozenEq (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) prog := ⟨hprog_raw⟩
      clear hentry_raw hprog_raw
      examples_hide_fetches
      have hbv_ne : BitVec.ofNat 64 hdName.length ≠ BitVec.ofNat 64 x.name.length := by
        intro heq_bv
        have hnat := congrArg BitVec.toNat heq_bv
        rw [ofNat64_toNat_of_lt63 (Nat.lt_of_le_of_lt hnm_le hnm_lt),
            ofNat64_toNat_of_lt32 hname_lt] at hnat
        exact hlen_eq hnat
      have hbne_len : (BitVec.ofNat 64 hdName.length != BitVec.ofNat 64 x.name.length) = true :=
        bne_iff_ne.mpr hbv_ne
      have hbeq_len : (BitVec.ofNat 64 hdName.length == BitVec.ofNat 64 x.name.length) = false :=
        beq_false_of_ne hbv_ne
      have _ := hbv_ne; have _ := hbne_len; have _ := hbeq_len
      have hname_ne : hdName ≠ x.name := fun heq => hlen_eq (congrArg List.length heq)
      refine seq_frozen_state (mid := fnStart + 68#64) hfz ?_
      wp_steps
      apply SepWP.fold hrepack_nm (by sep_frame)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hfz_adv
      rcases he with ⟨rfl⟩; rcases hp with ⟨rfl⟩
      refine SepWPp.perm
        (step_loop_advance (cstk := cstk) (changedCap := changedCap) (changedPtr := changedPtr)
          (pre := pre) (rest := rest) (hdName := hdName) (hdBytes := hdBytes) (Extra := Extra)
          hstk hfull hcap_ok hchanged hne hname_ne hmiss ih
          hfz_adv
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
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]))
        (by sep_frame)

theorem step_loop
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {cstk stk : Nat}
    {x : DirGetGhost} {s0 : State}
    {changedCap changedPtr : BitVec 64}
    {Extra R : SepProp}
    (hC : AllocContractsX img A ext)
    (_hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec)
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec)
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hcstk : extHookStack ≤ cstk)
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hname_lt : x.name.length < 2 ^ 32)
    (hcap_ok : x.dir.changed.length ≤ changedCap.toNat ∧
      changedCap.toNat * 48 < 2 ^ 63 ∧ changedPtr ≠ 0)
    (hmiss : ∀ sm : State,
      sm.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName + 164#64 →
      sm.status = .Running →
      sm.spAligned = true →
      sm.sp = s0.sp - 112#64 →
      HighCalleeSaved s0 sm →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.fs.files = s0.fs.files →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = x.ret →
      sm.readReg64 .x20 = BitVec.ofNat 64 x.name.length →
      sm.readReg64 .x21 = x.self →
      sm.readReg64 .x22 = x.nameA →
      (∀ e ∈ x.dir.changed, e.1 ≠ x.name) →
      SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
        (s0.readReg64 .lr) sm
        ((dirAt A x.self x.dir ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          memRegion x.ret 48 ∗
          stackAt (s0.sp - 112#64) cstk ∗
          memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
          savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗ Extra)
        (dirGetPostQ rd pathOk A img stk x s0
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
        (dirGetPanicQp rd pathOk A img stk x s0
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)) :
    ∀ (suf pre : List (List (BitVec 8) × List (BitVec 8))) (s : State),
      suf ≠ [] →
      x.dir.changed = pre ++ suf →
      (∀ e ∈ pre, e.1 ≠ x.name) →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName + 80#64 →
      s.status = .Running →
      s.spAligned = true →
      s.sp = s0.sp - 112#64 →
      HighCalleeSaved s0 s →
      s.fs.files = s0.fs.files →
      s.trace = s0.trace →
      s.readReg64 .x19 = x.ret →
      s.readReg64 .x20 = BitVec.ofNat 64 x.name.length →
      s.readReg64 .x21 = x.self →
      s.readReg64 .x22 = x.nameA →
      s.readReg64 .x23 = changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64 →
      s.readReg64 .x24 = BitVec.ofNat 64 (48 * suf.length) →
      SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
        (s0.readReg64 .lr) s
        (((vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
          RustHeap.arrayAt (dirEntryAt A) 48 changedPtr pre ∗
          RustHeap.arrayAt (dirEntryAt A) 48
            (changedPtr + BitVec.ofNat 64 (48 * pre.length)) suf ∗
          (if changedCap = 0 then emp
           else A.live changedPtr (changedCap.toNat * 48) 8 ∗
             memRegion (changedPtr + BitVec.ofNat 64 (x.dir.changed.length * 48))
               ((changedCap.toNat - x.dir.changed.length) * 48)) ∗
          strRefAt (x.self + 24#64) x.dir.path) ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          memRegion x.ret 48 ∗
          stackAt (s0.sp - 112#64) cstk ∗
          memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
          savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗ Extra)
        (dirGetPostQ rd pathOk A img stk x s0
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
        (dirGetPanicQp rd pathOk A img stk x s0
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R) :=
  step_loop_noRO hC hBcmp hFs hcstk hstk hfull hsp0_al hname_lt hcap_ok hmiss

end CryptoVerification.SignalSession.Cli.Get.Helpers
