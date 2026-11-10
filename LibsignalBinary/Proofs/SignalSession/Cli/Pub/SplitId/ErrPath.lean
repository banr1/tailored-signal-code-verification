/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitId.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitId.Decode
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitId.OkPath
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# Error Path and Top-Level Proof for `signal_session::public::split_id`

Verifies the `file.length < 4` error branch (`+172 .. +284`) and composes the prologue dispatch with
`step_ok_path` and `step_err_path` to prove `splitId_ok_of_loads`.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.SplitId.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.SignalSession.Cli

private theorem bind_sepWPp_state {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : let st := s; SepWPp prog ret st P Q Qp) :
    SepWPp prog ret s P Q Qp := h

private theorem bind_sepWP_state {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (h : let st := s; SepWP prog ret st P Q) :
    SepWP prog ret s P Q := h

private theorem sepWPp_pull_pure3 {prog : Program} {ret : BitVec 64} {s : State}
    {A1 A2 : SepProp} {φ : Prop} {Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A1 ∗ A2 ∗ Rest) Q Qp) :
    SepWPp prog ret s (A1 ∗ A2 ∗ ⌜φ⌝ ∗ Rest) Q Qp :=
  SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (SepWPp.pure_elim h)

private theorem sepWPp_realign_buf14 {prog : Program} {ret : BitVec 64} {s : State}
    {A1 A2 A3 Rest : SepProp} {buf : BitVec 64} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s
      (A1 ∗ A2 ∗ A3 ∗ (buf ↦ₛ malfHead6) ∗ (∃∗ w1 : BitVec 64, (buf + 6#64) ↦₆₄ w1) ∗ Rest)
      Q Qp) :
    SepWPp prog ret s
      (A1 ∗ A2 ∗ A3 ∗ (buf ↦₆₄ malfLo) ∗ memRegion (buf + 8#64) 6 ∗ Rest) Q Qp := by
  refine SepWPp.weaken_pre ?_ h
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (Entails.trans (Entails.of_eq (sepConj_assoc _ _ _).symm)
      (Entails.trans (sepConj_mono_left (buf14_realign buf))
        (Entails.of_eq (sepConj_assoc _ _ _))))))

@[simp, arm64_norm]
private theorem sid_sub_add (a k m : BitVec 64) : a - k + m = a - (k - m) := by
  bv_omega

@[simp, arm64_norm]
private theorem append64_extract_lo (hi lo : BitVec 64) :
    BitVec.extractLsb' 0 64 (hi ++ lo) = lo := by
  bv_bits

@[simp, arm64_norm]
private theorem append64_extract_hi (hi lo : BitVec 64) :
    BitVec.extractLsb' 64 64 (hi ++ lo) = hi := by
  bv_bits

@[simp, arm64_norm]
private theorem sp_restore_96 (sp0 : BitVec 64) :
    sp0 - 96#64 + 96#64 = sp0 := by
  bv_bits

theorem step_err_path {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    (hb : (img.base &&& 4095#64) = 0#64)
    (hC : AllocContractsX img A ext)
    (hstk : 96 + dropSpeStackX ≤ stk)
    (hstkle : stk ≤ 2 ^ 64)
    (retAddr fp : BitVec 64) (ro : Bool)
    (file : List (BitVec 8))
    (hnone : splitId file = none)
    (v24 : BitVec 64)
    {s0 s : State}
    (hal0 : s0.spAligned = true)
    (hinv : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr splitIdName + bv% (172))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = retAddr)
    (hcs : SidUpperSaved s0 s) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s
      (sidMalfRO img ∗
        ((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle") ∗
        cells (s0.sp - 96#64) 6 ∗
        sidSavedRegs s0.sp s0 v24 ∗
        stackAt (s0.sp - 96#64) dropSpeStackX ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (dropSpeStackX + 96)) ∗
        SpqrV1.ChainProofs.bytesAt ro fp file ∗
        memRegion retAddr 48 ∗
        A.pool)
      (fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ sidMalfRO img ∗
          (⌜sf.trace = s0.trace⌝ ∗
            splitIdResultAt A retAddr fp file ∗
            SpqrV1.ChainProofs.bytesAt ro fp file ∗
            stackAt s0.sp stk ∗ A.pool)))
      (SidPanicAllow s0) := by
  have hshim := sid_shim_ok hC
  have halloc := sid_alloc_ok hC
  have hpanic := sid_panic_handle_error img ext
  clear hC
  have hfn : libsignalSessionCode.fnOff splitIdName = num% (ls_off% splitIdName) :=
    splitId_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode sidDec img.base
    (Rust.withPanics ext) hfn (num% (ls_off% splitIdName)) 172 116
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hpanic hpc ⊢
  have hfn_addr :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr splitIdName =
        img.base + bv% (ls_off% "libsignal_cli::public::split_id") := by
    simp only [Program.fnAddr_rebase]
    rw [hfn]
  have hadrp_m := adrp_malf_err hb hfn_addr
  have hadrp_b := adrp_bundle_err hb hfn_addr
  clear hfn hfn_addr
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    splitIdName = fnBase
  examples_hide_fetches
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hadrp_m hadrp_b
  apply SepWPp.of_sepWP_inImage
    (mid := fnBase + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% splitIdName))
    hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  apply bind_sepWPp_state; intro s_sh
  have hal_sh : s_sh.spAligned = true := sp_sub_96_spAligned hal0 (by simp only [s_sh, arm64_norm, hsp])
  have hcs_sh : SidUpperSaved s0 s_sh := by
    rcases hcs with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs⟩
    simp only [s_sh, SidUpperSaved, arm64_norm, *]
  refine sid_call_inImage () hshim hinv1
    (by simp only [s_sh, arm64_norm, htr])
    (by simp only [s_sh, arm64_norm, *])
    (by simp only [s_sh, arm64_norm, *])
    hal_sh
    (ret_pc := fnBase + bv% (176))
    (by simp only [s_sh, arm64_norm, *])
    (F := sidMalfRO img ∗
      ((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle") ∗
      cells (s0.sp - 96#64) 6 ∗
      sidSavedRegs s0.sp s0 v24 ∗
      memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 dropSpeStackX) 32 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (dropSpeStackX + 96)) ∗
      SpqrV1.ChainProofs.bytesAt ro fp file ∗
      memRegion retAddr 48 ∗ A.pool)
    ?_ (hnext := ?_)
  · rw [stackAt_hook_split (s0.sp - 96#64)]
    dsimp only [session2ShimSpecX]
    have hsp_eq : s_sh.sp = s0.sp - 96#64 := by simp only [s_sh, arm64_norm, hsp]
    rw [hsp_eq]
    generalize dropSpeStackX = dsz
    generalize extHookStack = hsz
    exact Entails.of_eq (by ac_rfl)
  · intro s_after_sh hinv2 hpc2 hrun2 hsp2 hcsp2
    dsimp only [session2ShimSpecX]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun htr2 => ?_
    have hx19_2 : s_after_sh.readReg64 .x19 = retAddr := by
      rw [hcsp2.1]; simp only [s_sh, arm64_norm, hx19]
    have hsp2' : s_after_sh.sp = s0.sp - 96#64 := by
      rw [hsp2]; simp only [s_sh, arm64_norm, hsp]
    clear hsp2
    have htr2' : s_after_sh.trace = s0.trace := by
      rw [htr2]; simp only [s_sh, arm64_norm, htr]
    have hcs2 : SidUpperSaved s0 s_after_sh := hcs_sh.trans_calleeSaved hcsp2
    apply SepWPp.of_sepWP_inImage
      (mid := fnBase + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% splitIdName))
      hinv2
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv3
    apply bind_sepWPp_state; intro s_al
    have hal_al : s_al.spAligned = true := sp_sub_96_spAligned hal0 (by simp only [s_al, arm64_norm, hsp2'])
    have hcs_al : SidUpperSaved s0 s_al := by
      rcases hcs2 with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs⟩
      simp only [s_al, SidUpperSaved, arm64_norm, *]
    have hlay : LayoutOk 14 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
    refine sid_call_inImage (14, 1) halloc hinv3
      (by simp only [s_al, arm64_norm, htr2'])
      (by simp only [s_al, arm64_norm, *])
      (by simp only [s_al, arm64_norm, *])
      hal_al
      (ret_pc := fnBase + bv% (188))
      (by simp only [s_al, arm64_norm, *])
      (F := sidMalfRO img ∗
        ((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle") ∗
        cells (s0.sp - 96#64) 6 ∗
        sidSavedRegs s0.sp s0 v24 ∗
        memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 dropSpeStackX) 32 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (dropSpeStackX + 96)) ∗
        SpqrV1.ChainProofs.bytesAt ro fp file ∗
        memRegion retAddr 48)
      ?_ (hnext := ?_)
    · dsimp only [rustAllocSpecWithStack]
      have hpure_al :
          ((s_al.readReg64 .x0).toNat = 14 ∧ (s_al.readReg64 .x1).toNat = 1 ∧ LayoutOk 14 1) = True :=
        eq_true ⟨by simp only [s_al, arm64_norm], by simp only [s_al, arm64_norm], hlay⟩
      have hsp_eq1 : s_sh.sp = s0.sp - 96#64 := by simp only [s_sh, arm64_norm, hsp]
      have hsp_eq2 : s_al.sp = s0.sp - 96#64 := by simp only [s_al, arm64_norm, hsp2']
      rw [hpure_al, pure_true, emp_sepConj, hsp_eq1, hsp_eq2]
      generalize dropSpeStackX = dsz
      generalize extHookStack = hsz
      exact Entails.of_eq (by ac_rfl)
    · intro s_after_al hinv4 hpc4 hrun4 hsp4 hcsp4
      let _ := hinv4
      dsimp only [rustAllocSpecWithStack]
      have hx19_4 : s_after_al.readReg64 .x19 = retAddr := by
        rw [hcsp4.1]; simp only [s_al, arm64_norm, hx19_2]
      have hsp4' : s_after_al.sp = s0.sp - 96#64 := by
        rw [hsp4]; simp only [s_al, arm64_norm, hsp2']
      clear hsp4
      have hal4 : s_after_al.spAligned = true := sp_sub_96_spAligned hal0 hsp4'
      let _ := hal4
      have hcs4 : SidUpperSaved s0 s_after_al := hcs_al.trans_calleeSaved hcsp4
      by_cases hnull : s_after_al.readReg64 .x0 = 0
      ·
        have hnull64 : s_after_al.readReg64 .x0 = 0#64 := hnull
        let _ := hnull64
        simp only [hnull, ↓reduceIte, sepConj_assoc]
        refine sepWPp_pull_pure3 fun htr_oom => ?_
        have htr_al : s_al.trace = s0.trace := by simp only [s_al, arm64_norm, htr2']
        apply SepWPp.of_sepWP
          (mid := fnBase + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% splitIdName))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        refine SepWPp.panic (by simp only [arm64_norm, *])
          (by simpa only [arm64_norm] using hpanic)
          (sidPanicAllow_of_eq
            (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htr_oom, htr_al])))
      ·
        set buf := s_after_al.readReg64 .x0 with hbuf_def
        let _ := hbuf_def
        have hptr_ne : buf ≠ 0#64 := hnull
        have hptr_beq : (buf == 0#64) = false := beq_eq_false_iff_ne.mpr hptr_ne
        have hptr_bne : (buf != 0#64) = true := bne_iff_ne.mpr hptr_ne
        have _ := And.intro hptr_beq hptr_bne
        simp only [hnull, ↓reduceIte]
        rw [buf14_open_lo buf, ret48_open_err retAddr]
        unfold sidMalfRO sidSavedRegs
        cells_unfold
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        refine SepWPp.exists_elim fun w0 =>
          SepWPp.exists_elim fun c0 => SepWPp.exists_elim fun c1 =>
          SepWPp.exists_elim fun c2 => SepWPp.exists_elim fun c3 =>
          SepWPp.exists_elim fun c4 => SepWPp.exists_elim fun c5 =>
          SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
          SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 =>
          SepWPp.exists_elim fun u4 => SepWPp.exists_elim fun u5 => ?_
        refine sepWPp_pull_pure3 fun ⟨_, htr_ok⟩ => ?_
        have htr4' : s_after_al.trace = s0.trace := by
          rw [htr_ok]; simp only [s_al, arm64_norm, htr2']
        rcases hcs4 with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs⟩
        apply SepWPp.of_sepWP (mid := fnBase + bv% (236))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        have _ := And.intro hadrp_m (And.intro hadrp_b hx19_4)
        apply sepWPp_realign_buf14
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine SepWPp.exists_elim fun w1 => ?_
        apply SepWPp.of_sepWP_ret
        wp_steps
        apply bind_sepWP_state; intro sf
        apply SepWP.done (by simp only [sf, arm64_norm, *]) (by simp only [sf, arm64_norm, *])
        refine ⟨by simp only [sf, arm64_norm, *], ?_, ?_⟩
        · refine ⟨by simp only [sf, arm64_norm, *],
            by simp only [sf, arm64_norm, *],
            by simp only [sf, arm64_norm, *],
            by simp only [sf, arm64_norm, *],
            by simp only [sf, arm64_norm, *],
            by simp only [sf, arm64_norm, *],
            by simp only [sf, arm64_norm, *],
            by simp only [sf, arm64_norm, *],
            by simp only [sf, arm64_norm, *],
            by simp only [sf, arm64_norm, *],
            by simp only [sf, arm64_norm, *],
            by simp only [sf, calleeSavedVRegs, arm64_norm] at hvregs ⊢; exact hvregs⟩
        · have htrf : sf.trace = s0.trace := by simp only [sf, arm64_norm, htr4']
          rw [htrf, eq_self, pure_true, emp_sepConj]
          dsimp only [splitIdResultAt]
          rw [hnone]
          have hsp_al0 : s_al.sp = s0.sp - 96#64 := by simp only [s_al, arm64_norm, hsp2']
          have hbuf_pack : ((buf ↦ₛ malfHead6) ∗ ((buf + 6#64) ↦₆₄ malfHi)) =
              (buf ↦ₛ utf8 "malformed file") := buf14_close buf
          have hcells_back :
              (((s0.sp - 96#64) ↦₆₄ c5) ∗ ((s0.sp - 88#64) ↦₆₄ u0) ∗
                ((s0.sp - 80#64) ↦₆₄ u1) ∗ ((s0.sp - 72#64) ↦₆₄ u2) ∗
                ((s0.sp - 64#64) ↦₆₄ (img.base + bv% (ls_str% "bundle"))) ∗
                ((s0.sp - 56#64) ↦₆₄ 6#64)) ⊢ cells (s0.sp - 96#64) 6 := by
            apply cells_sub_succ_entails 96 6
            apply cells_sub_succ_entails 88 5
            apply cells_sub_succ_entails 80 4
            apply cells_sub_succ_entails 72 3
            apply cells_sub_succ_entails 64 2
            rw [cells_sub_succ s0.sp 56 1 (by decide) (by decide), Nat.sub_self, cells_zero]
            simp only [sepConj_emp]
            exact Entails.sepExists_right _ (Entails.refl _)
          have hspe_pack :
              ((retAddr ↦₆₄ speWord 1) ∗
                ((retAddr + 8#64) ↦₆₄ 14#64) ∗
                ((retAddr + 16#64) ↦₆₄ buf) ∗
                ((retAddr + 24#64) ↦₆₄ 14#64) ∗
                A.live buf 14 1 ∗
                ((buf ↦ₛ malfHead6) ∗ ((buf + 6#64) ↦₆₄ malfHi)) ∗
                ((retAddr + 32#64) ↦₆₄ (img.base + bv% (ls_str% "bundle"))) ∗
                ((retAddr + 40#64) ↦₆₄ 6#64) ∗
                ((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle")) ⊢
              speAt A (utf8 "bundle") retAddr .invalidState := by
            rw [hbuf_pack]
            exact speAt_invalidState_intro A img retAddr buf hptr_ne
          have hstk_pack :
              (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (dropSpeStackX + 96)) ∗
                (memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 dropSpeStackX) 32 ∗
                  stackAt (s0.sp - 96#64) extHookStack) ∗
                (((s0.sp - 96#64) ↦₆₄ c5) ∗ ((s0.sp - 88#64) ↦₆₄ u0) ∗
                  ((s0.sp - 80#64) ↦₆₄ u1) ∗ ((s0.sp - 72#64) ↦₆₄ u2) ∗
                  ((s0.sp - 64#64) ↦₆₄ (img.base + bv% (ls_str% "bundle"))) ∗
                  ((s0.sp - 56#64) ↦₆₄ 6#64)) ∗
                sidSavedRegs s0.sp s0 v24) ⊢
              stackAt s0.sp stk := by
            rw [← stackAt_hook_split (s0.sp - 96#64)]
            exact Entails.trans
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hcells_back)))
              (stackAt_sid_pack_cells s0.sp stk s0 v24 hstk hstkle)
          rw [hsp_al0, speWord1_eq]
          refine Entails.trans ?_
            (Entails.trans (sepConj_mono hspe_pack
              (sepConj_mono_left
                (Q := sidMalfRO img ∗ SpqrV1.ChainProofs.bytesAt ro fp file ∗ A.pool)
                hstk_pack)) ?_)
          · unfold sidMalfRO sidSavedRegs
            simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
            generalize dropSpeStackX = dsz
            generalize extHookStack = hsz
            exact Entails.of_eq (by ac_rfl)
          · unfold sidMalfRO
            simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
            generalize stackAt s0.sp stk = topStk
            exact Entails.of_eq (by ac_rfl)

private theorem cells48_open (sp0 : BitVec 64) :
    cells (sp0 - 48#64) 6 =
      ∃∗ s48 : BitVec 64, ∃∗ s40 : BitVec 64, ∃∗ s32 : BitVec 64,
      ∃∗ v24 : BitVec 64, ∃∗ s16 : BitVec 64, ∃∗ s8 : BitVec 64,
        ((sp0 - 48#64) ↦₆₄ s48) ∗ ((sp0 - 40#64) ↦₆₄ s40) ∗
        ((sp0 - 32#64) ↦₆₄ s32) ∗ ((sp0 - 24#64) ↦₆₄ v24) ∗
        ((sp0 - 16#64) ↦₆₄ s16) ∗ ((sp0 - 8#64) ↦₆₄ s8) := by
  cells_unfold

private theorem ls_ge4_raw {u : BitVec 64} (hu : 4 ≤ u.toNat) :
    ConditionHolds CondCode.LS (AddWithCarry64 u (~~~3#64) true).2 = false := by
  simp only [ConditionHolds, AddWithCarry64]
  bv_bits

private theorem ule_ge4_false {u : BitVec 64} (hu : 4 ≤ u.toNat) :
    BitVec.ule u 3#64 = false := by
  simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]
  omega

private theorem ult_ge4_true {u : BitVec 64} (hu : 4 ≤ u.toNat) :
    BitVec.ult 3#64 u = true := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]
  omega

private theorem sid_prologue_err {b : BitVec 64} {ext : String → Option (State → State)}
    {s0 : State} {ret fp : BitVec 64} {s48 s40 s32 v24 s16 s8 : BitVec 64}
    {R_frame : SepProp} {post : State → SepProp → Prop}
    (hal0 : s0.spAligned = true)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr splitIdName)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ret)
    (hx1 : s0.readReg64 .x1 = fp)
    (hx2 : s0.readReg64 .x2 = 0#64 ∨ s0.readReg64 .x2 = 1#64 ∨
      s0.readReg64 .x2 = 2#64 ∨ s0.readReg64 .x2 = 3#64)
    (hnext : ∀ (s1 : State) (P1 : SepProp),
      s1.pc = (tripleRatchetProgAtExt b ext).fnAddr splitIdName + bv% (172) →
      s1.status = .Running →
      s1.sp = s0.sp - 96#64 →
      s1.trace = s0.trace →
      s1.readReg64 .x19 = ret →
      SidUpperSaved s0 s1 →
      P1 = (sidSavedRegs s0.sp s0 v24 ∗ R_frame) →
      post s1 P1) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr splitIdName + bv% (172)) s0
      ((((s0.sp - 48#64) ↦₆₄ s48) ∗ ((s0.sp - 40#64) ↦₆₄ s40) ∗
        ((s0.sp - 32#64) ↦₆₄ s32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
        ((s0.sp - 16#64) ↦₆₄ s16) ∗ ((s0.sp - 8#64) ↦₆₄ s8)) ∗ R_frame)
      post := by
  have hfn : libsignalSessionCode.fnOff splitIdName = num% (ls_off% splitIdName) :=
    splitId_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode sidDec b
    (Rust.withPanics ext) hfn (num% (ls_off% splitIdName)) 0 32
  clear hfn
  have _ := And.intro hx0 hx1
  dsimp only [tripleRatchetProgAtExt] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    splitIdName = fnBase
  examples_hide_fetches
  rcases hx2 with hx2 | hx2 | hx2 | hx2 <;>
  · let _ := hx2
    wp_steps
    apply bind_sepWP_state; intro s1
    apply SepWP.done (by simp only [s1, arm64_norm, *]) (by simp only [s1, arm64_norm, *])
    refine hnext s1 _
      (by simp only [s1, arm64_norm])
      (by simp only [s1, arm64_norm, *])
      (by simp only [s1, arm64_norm])
      (by simp only [s1, arm64_norm])
      (by simp only [s1, arm64_norm, *])
      (by simp only [s1, SidUpperSaved, calleeSavedVRegs, arm64_norm])
      ?_
    unfold sidSavedRegs
    simp only [arm64_norm, sepConj_assoc]

private theorem sid_prologue_ok {b : BitVec 64} {ext : String → Option (State → State)}
    {s0 : State} {ret fp : BitVec 64} {n : Nat} {s48 s40 s32 v24 s16 s8 : BitVec 64}
    {R_frame : SepProp} {post : State → SepProp → Prop}
    (hal0 : s0.spAligned = true)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr splitIdName)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ret)
    (hx1 : s0.readReg64 .x1 = fp)
    (hn : n + 4 < 2 ^ 64)
    (hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 n + 4#64)
    (hnext : ∀ (s1 : State) (P1 : SepProp),
      s1.pc = (tripleRatchetProgAtExt b ext).fnAddr splitIdName + bv% (32) →
      s1.status = .Running →
      s1.sp = s0.sp - 96#64 →
      s1.trace = s0.trace →
      s1.readReg64 .x19 = ret →
      s1.readReg64 .x1 = fp →
      s1.readReg64 .x2 = BitVec.ofNat 64 n + 4#64 →
      SidUpperSaved s0 s1 →
      P1 = (sidSavedRegs s0.sp s0 v24 ∗ R_frame) →
      post s1 P1) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr splitIdName + bv% (32)) s0
      ((((s0.sp - 48#64) ↦₆₄ s48) ∗ ((s0.sp - 40#64) ↦₆₄ s40) ∗
        ((s0.sp - 32#64) ↦₆₄ s32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
        ((s0.sp - 16#64) ↦₆₄ s16) ∗ ((s0.sp - 8#64) ↦₆₄ s8)) ∗ R_frame)
      post := by
  have hfn : libsignalSessionCode.fnOff splitIdName = num% (ls_off% splitIdName) :=
    splitId_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode sidDec b
    (Rust.withPanics ext) hfn (num% (ls_off% splitIdName)) 0 32
  clear hfn
  have hge4 : 4 ≤ (BitVec.ofNat 64 n + 4#64).toNat := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hls_raw : ConditionHolds CondCode.LS
      (AddWithCarry64 (BitVec.ofNat 64 n + 4#64) (~~~3#64) true).2 = false :=
    ls_ge4_raw hge4
  have hls_norm : ConditionHolds CondCode.LS
      (AddWithCarry64 (BitVec.ofNat 64 n + 4#64) (bv% (2 ^ 64 - 4)) true).2 = false :=
    hls_raw
  have hls_ule : BitVec.ule (BitVec.ofNat 64 n + 4#64) 3#64 = false :=
    ule_ge4_false hge4
  have hls_ult : BitVec.ult 3#64 (BitVec.ofNat 64 n + 4#64) = true :=
    ult_ge4_true hge4
  have _ := And.intro hx0 (And.intro hx1
    (And.intro hx2 (And.intro hls_raw (And.intro hls_norm (And.intro hls_ule hls_ult)))))
  dsimp only [tripleRatchetProgAtExt] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    splitIdName = fnBase
  examples_hide_fetches
  wp_steps
  apply bind_sepWP_state; intro s1
  apply SepWP.done (by simp only [s1, arm64_norm, *]) (by simp only [s1, arm64_norm, *])
  refine hnext s1 _
    (by simp only [s1, arm64_norm])
    (by simp only [s1, arm64_norm, *])
    (by simp only [s1, arm64_norm])
    (by simp only [s1, arm64_norm])
    (by simp only [s1, arm64_norm, *])
    (by simp only [s1, arm64_norm, *])
    (by simp only [s1, arm64_norm, *])
    (by simp only [s1, SidUpperSaved, calleeSavedVRegs, arm64_norm])
    ?_
  unfold sidSavedRegs
  simp only [arm64_norm, sepConj_assoc]

/-- `signal_session::public::split_id` satisfies `splitIdSpec A img stk` given `Obj.Loads libsignalSessionImage img`. -/
theorem splitId_ok_of_loads {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hC : AllocContractsX img A ext)
    (hDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      ((dropSpeSpecX A).inImage img))
    (hstk : 96 + dropSpeStackX ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr splitIdName)
      (splitIdSpec A img stk) := by
  have hb : (img.base &&& 4095#64) = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hal0
  dsimp only [splitIdSpec, Spec.inImage] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hinv0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2_nat⟩, hpre⟩ := hpre
  have hfile_lt64 : x.file.length < 2 ^ 64 := hx2_nat ▸ (s0.readReg64 .x2).isLt
  have hstkle : stk ≤ 2 ^ 64 := by
    have hm_stk : s0.mem ⊨ stackAt s0.sp stk ∗
        (memRegion x.ret 48 ∗ (SpqrV1.ChainProofs.bytesAt x.ro x.fp x.file ∗ A.pool ∗ R)) := by
      refine Satisfies.mono ?_ hpre
      generalize stackAt s0.sp stk = topStk
      exact Entails.of_eq (by ac_rfl)
    exact Nat.le_of_lt (stack_lt_addr_space hm_stk (by omega))
  have hpre_ro := sidMalfRO_bundle_intro himg (Obj.Image.frozenLoaded_iff.mp hinv0.1).2.1 hpre
  clear himg
  rw [stackAt_sid_split s0.sp stk hstk hstkle, cells48_open s0.sp] at hpre_ro
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc] at hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨s48, hpre_ro⟩ := hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨s40, hpre_ro⟩ := hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨s32, hpre_ro⟩ := hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨v24, hpre_ro⟩ := hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨s16, hpre_ro⟩ := hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨s8, hpre_ro⟩ := hpre_ro
  refine ⟨(((s0.sp - 48#64) ↦₆₄ s48) ∗ ((s0.sp - 40#64) ↦₆₄ s40) ∗
        ((s0.sp - 32#64) ↦₆₄ s32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
        ((s0.sp - 16#64) ↦₆₄ s16) ∗ ((s0.sp - 8#64) ↦₆₄ s8)) ∗
      (sidMalfRO img ∗
        ((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle") ∗
        cells (s0.sp - 96#64) 6 ∗
        stackAt (s0.sp - 96#64) dropSpeStackX ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (dropSpeStackX + 96)) ∗
        SpqrV1.ChainProofs.bytesAt x.ro x.fp x.file ∗
        memRegion x.ret 48 ∗
        A.pool),
    R,
    by
      refine Satisfies.mono ?_ hpre_ro
      generalize dropSpeStackX = dsz
      exact Entails.of_eq (by ac_rfl),
    ?_⟩
  have hwp : SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s0
      ((((s0.sp - 48#64) ↦₆₄ s48) ∗ ((s0.sp - 40#64) ↦₆₄ s40) ∗
          ((s0.sp - 32#64) ↦₆₄ s32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
          ((s0.sp - 16#64) ↦₆₄ s16) ∗ ((s0.sp - 8#64) ↦₆₄ s8)) ∗
        (sidMalfRO img ∗
          ((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle") ∗
          cells (s0.sp - 96#64) 6 ∗
          stackAt (s0.sp - 96#64) dropSpeStackX ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (dropSpeStackX + 96)) ∗
          SpqrV1.ChainProofs.bytesAt x.ro x.fp x.file ∗
          memRegion x.ret 48 ∗
          A.pool))
      (fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ sidMalfRO img ∗
          (⌜sf.trace = s0.trace⌝ ∗
            splitIdResultAt A x.ret x.fp x.file ∗
            SpqrV1.ChainProofs.bytesAt x.ro x.fp x.file ∗
            stackAt s0.sp stk ∗ A.pool)))
      (SidPanicAllow s0) := by
    have hx2_bv : s0.readReg64 .x2 = BitVec.ofNat 64 x.file.length := by
      apply BitVec.eq_of_toNat_eq
      rw [hx2_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfile_lt64]
    rcases x with ⟨ret, fp, file, ro⟩
    dsimp only at *
    rcases file with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, rest⟩⟩⟩⟩
    · apply SepWPp.of_sepWP_inImage
        (mid := (tripleRatchetProgAtExt img.base ext).fnAddr splitIdName + bv% (172)) hinv0
      refine sid_prologue_err hal0 hpc hrun hx0 hx1 (Or.inl hx2_bv)
        fun s1 P1 hpc1 hrun1 hsp1 htr1 hx19_1 hcs1 hP1 hinv1 => ?_
      rw [hP1]
      refine SepWPp.weaken_pre ?_
        (step_err_path hb hC hstk hstkle ret fp ro [] rfl v24 hal0 hinv1
          hpc1 hrun1 hsp1 htr1 hx19_1 hcs1)
      generalize dropSpeStackX = dsz
      exact Entails.of_eq (by ac_rfl)
    · apply SepWPp.of_sepWP_inImage
        (mid := (tripleRatchetProgAtExt img.base ext).fnAddr splitIdName + bv% (172)) hinv0
      refine sid_prologue_err hal0 hpc hrun hx0 hx1 (Or.inr (Or.inl hx2_bv))
        fun s1 P1 hpc1 hrun1 hsp1 htr1 hx19_1 hcs1 hP1 hinv1 => ?_
      rw [hP1]
      refine SepWPp.weaken_pre ?_
        (step_err_path hb hC hstk hstkle ret fp ro [b0] rfl v24 hal0 hinv1
          hpc1 hrun1 hsp1 htr1 hx19_1 hcs1)
      generalize dropSpeStackX = dsz
      exact Entails.of_eq (by ac_rfl)
    · apply SepWPp.of_sepWP_inImage
        (mid := (tripleRatchetProgAtExt img.base ext).fnAddr splitIdName + bv% (172)) hinv0
      refine sid_prologue_err hal0 hpc hrun hx0 hx1 (Or.inr (Or.inr (Or.inl hx2_bv)))
        fun s1 P1 hpc1 hrun1 hsp1 htr1 hx19_1 hcs1 hP1 hinv1 => ?_
      rw [hP1]
      refine SepWPp.weaken_pre ?_
        (step_err_path hb hC hstk hstkle ret fp ro [b0, b1] rfl v24 hal0 hinv1
          hpc1 hrun1 hsp1 htr1 hx19_1 hcs1)
      generalize dropSpeStackX = dsz
      exact Entails.of_eq (by ac_rfl)
    · apply SepWPp.of_sepWP_inImage
        (mid := (tripleRatchetProgAtExt img.base ext).fnAddr splitIdName + bv% (172)) hinv0
      refine sid_prologue_err hal0 hpc hrun hx0 hx1 (Or.inr (Or.inr (Or.inr hx2_bv)))
        fun s1 P1 hpc1 hrun1 hsp1 htr1 hx19_1 hcs1 hP1 hinv1 => ?_
      rw [hP1]
      refine SepWPp.weaken_pre ?_
        (step_err_path hb hC hstk hstkle ret fp ro [b0, b1, b2] rfl v24 hal0 hinv1
          hpc1 hrun1 hsp1 htr1 hx19_1 hcs1)
      generalize dropSpeStackX = dsz
      exact Entails.of_eq (by ac_rfl)
    · have hrest64 : rest.length + 4 < 2 ^ 64 := by
        simp only [List.length_cons] at hfile_lt64
        omega
      have hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 rest.length + 4#64 := by
        rw [hx2_bv]
        apply BitVec.eq_of_toNat_eq
        simp only [List.length_cons, BitVec.toNat_ofNat, BitVec.toNat_add]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)]
      apply SepWPp.of_sepWP_inImage
        (mid := (tripleRatchetProgAtExt img.base ext).fnAddr splitIdName + bv% (32)) hinv0
      refine sid_prologue_ok hal0 hpc hrun hx0 hx1 hrest64 hx2
        fun s1 P1 hpc1 hrun1 hsp1 htr1 hx19_1 hx1_1 hx2_1 hcs1 hP1 hinv1 => ?_
      rw [hP1]
      refine SepWPp.weaken_pre ?_
        (step_ok_path hb hC hDrop hstk hstkle ret fp ro b0 b1 b2 b3 rest v24 hal0 hinv1
          hpc1 hrun1 hsp1 htr1 hx19_1 hx1_1 hx2_1 hcs1)
      generalize dropSpeStackX = dsz
      exact Entails.of_eq (by ac_rfl)
  intro Fr hm hL
  obtain ⟨sf, hsteps, hout⟩ := hwp Fr hm hL
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, hspf, hcsf, hent⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨hoom_s, hmo⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf,
      ⌜sf.trace = s0.trace⌝ ∗ splitIdResultAt A x.ret x.fp x.file ∗
        SpqrV1.ChainProofs.bytesAt x.ro x.fp x.file ∗ stackAt s0.sp stk ∗ A.pool,
      ?_, fun hmR => hmR, hspf, hcsf⟩⟩
    have hm1 := Satisfies.mono (sepConj_mono_left hent) hmf
    rw [sepConj_assoc] at hm1
    exact Satisfies.of_sep_right hm1
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f, hmf, hqp R⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr ⟨hoom_s, hmo⟩)⟩

end CryptoVerification.SignalSession.Cli.SplitId.Helpers
