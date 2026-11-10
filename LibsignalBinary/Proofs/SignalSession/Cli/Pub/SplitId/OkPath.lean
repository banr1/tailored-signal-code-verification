/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitId.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitId.Decode
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `Ok` Path for `signal_session::public::split_id`

Verifies the `4 ≤ file.length` branch (`+32 .. +168`, plus OOM panic `+276 .. +284`), dropping the
eagerly allocated `SignalProtocolError` and writing `splitIdResultAt` (`Ok((id, rest))`).
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
private theorem add4_sub4_64 (a : BitVec 64) :
    (a + 4#64) - 4#64 = a := by
  bv_omega

@[simp, arm64_norm]
private theorem zext32_trunc32 (u : BitVec 32) :
    (u.zeroExtend 64).truncate 32 = u := by
  bv_bits

@[simp, arm64_norm]
private theorem sp_restore_96 (sp0 : BitVec 64) :
    sp0 - 96#64 + 96#64 = sp0 := by
  bv_bits

theorem step_ok_path {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    (hb : (img.base &&& 4095#64) = 0#64)
    (hC : AllocContractsX img A ext)
    (hDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      ((dropSpeSpecX A).inImage img))
    (hstk : 96 + dropSpeStackX ≤ stk)
    (hstkle : stk ≤ 2 ^ 64)
    (retAddr fp : BitVec 64) (ro : Bool)
    (b0 b1 b2 b3 : BitVec 8) (rest : List (BitVec 8))
    (v24 : BitVec 64)
    {s0 s : State}
    (hal0 : s0.spAligned = true)
    (hinv : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr splitIdName + bv% (32))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = retAddr)
    (hx1 : s.readReg64 .x1 = fp)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 rest.length + 4#64)
    (hcs : SidUpperSaved s0 s) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s
      (sidMalfRO img ∗
        ((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle") ∗
        cells (s0.sp - 96#64) 6 ∗
        sidSavedRegs s0.sp s0 v24 ∗
        stackAt (s0.sp - 96#64) dropSpeStackX ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (dropSpeStackX + 96)) ∗
        SpqrV1.ChainProofs.bytesAt ro fp (b0 :: b1 :: b2 :: b3 :: rest) ∗
        memRegion retAddr 48 ∗
        A.pool)
      (fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ sidMalfRO img ∗
          (⌜sf.trace = s0.trace⌝ ∗
            splitIdResultAt A retAddr fp (b0 :: b1 :: b2 :: b3 :: rest) ∗
            SpqrV1.ChainProofs.bytesAt ro fp (b0 :: b1 :: b2 :: b3 :: rest) ∗
            stackAt s0.sp stk ∗ A.pool)))
      (SidPanicAllow s0) := by
  have hshim := sid_shim_ok hC
  have halloc := sid_alloc_ok hC
  have hdrop := sid_drop_ok hDrop
  have hpanic := sid_panic_handle_error img ext
  clear hC hDrop
  have hfn : libsignalSessionCode.fnOff splitIdName = num% (ls_off% splitIdName) :=
    splitId_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode sidDec img.base
    (Rust.withPanics ext) hfn (num% (ls_off% splitIdName)) 32 140
  code_fetches_range CryptoVerification.libsignalSessionCode sidDec img.base
    (Rust.withPanics ext) hfn (num% (ls_off% splitIdName)) 276 12
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hdrop hpanic hpc ⊢
  have hfn_addr :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr splitIdName =
        img.base + bv% (ls_off% "libsignal_cli::public::split_id") := by
    simp only [Program.fnAddr_rebase]
    rw [hfn]
  have hadrp_m := adrp_malf_ok hb hfn_addr
  have hadrp_b := adrp_bundle_ok hb hfn_addr
  clear hfn hfn_addr
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    splitIdName = fnBase
  examples_hide_fetches
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hadrp_m hadrp_b
  have _ := And.intro hadrp_m hadrp_b
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
    (ret_pc := fnBase + bv% (44))
    (by simp only [s_sh, arm64_norm, *])
    (F := sidMalfRO img ∗
      ((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle") ∗
      cells (s0.sp - 96#64) 6 ∗
      sidSavedRegs s0.sp s0 v24 ∗
      memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 dropSpeStackX) 32 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (dropSpeStackX + 96)) ∗
      SpqrV1.ChainProofs.bytesAt ro fp (b0 :: b1 :: b2 :: b3 :: rest) ∗
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
    let _ := And.intro hx1 hx2
    have hx20_2 : s_after_sh.readReg64 .x20 = fp := by
      rw [hcsp2.2.1]; simp only [s_sh, arm64_norm]
    have hx21_2 : s_after_sh.readReg64 .x21 = BitVec.ofNat 64 rest.length + 4#64 := by
      rw [hcsp2.2.2.1]; simp only [s_sh, arm64_norm]
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
      (ret_pc := fnBase + bv% (56))
      (by simp only [s_al, arm64_norm, *])
      (F := sidMalfRO img ∗
        ((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle") ∗
        cells (s0.sp - 96#64) 6 ∗
        sidSavedRegs s0.sp s0 v24 ∗
        memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 dropSpeStackX) 32 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (dropSpeStackX + 96)) ∗
        SpqrV1.ChainProofs.bytesAt ro fp (b0 :: b1 :: b2 :: b3 :: rest) ∗
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
      dsimp only [rustAllocSpecWithStack]
      have hx19_4 : s_after_al.readReg64 .x19 = retAddr := by
        rw [hcsp4.1]; simp only [s_al, arm64_norm, hx19_2]
      have hx20_4 : s_after_al.readReg64 .x20 = fp := by
        rw [hcsp4.2.1]; simp only [s_al, arm64_norm, hx20_2]
      have hx21_4 : s_after_al.readReg64 .x21 = BitVec.ofNat 64 rest.length + 4#64 := by
        rw [hcsp4.2.2.1]; simp only [s_al, arm64_norm, hx21_2]
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
        rw [buf14_open_lo buf]
        unfold sidMalfRO
        cells_unfold
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        refine SepWPp.exists_elim fun w0 =>
          SepWPp.exists_elim fun c0 => SepWPp.exists_elim fun c1 =>
          SepWPp.exists_elim fun c2 => SepWPp.exists_elim fun c3 =>
          SepWPp.exists_elim fun c4 => SepWPp.exists_elim fun c5 => ?_
        refine sepWPp_pull_pure3 fun ⟨_, htr_ok⟩ => ?_
        have htr4' : s_after_al.trace = s0.trace := by
          rw [htr_ok]; simp only [s_al, arm64_norm, htr2']
        apply SepWPp.of_sepWP_inImage (mid := fnBase + bv% (84)) hinv4
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        intro hinv5
        apply sepWPp_realign_buf14
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine SepWPp.exists_elim fun w1 => ?_
        apply SepWPp.of_sepWP_inImage
          (mid := fnBase + bv% ((2 ^ 64 + ls_off% cliDropSpeName - ls_off% splitIdName) % 2 ^ 64))
          hinv5
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        intro hinv6
        apply bind_sepWPp_state; intro s_dr
        have _ := hx21_4
        have hal_dr : s_dr.spAligned = true :=
          sp_sub_96_spAligned hal0 (by simp only [s_dr, arm64_norm, hsp4'])
        have hcs_dr : SidUpperSaved s0 s_dr := by
          rcases hcs4 with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs⟩
          simp only [s_dr, SidUpperSaved, arm64_norm, *]
        refine sid_call_inImage ⟨s0.sp - 96#64, utf8 "bundle", .invalidState⟩ hdrop hinv6
          (by simp only [s_dr, arm64_norm, htr4'])
          (by simp only [s_dr, arm64_norm, *])
          (by simp only [s_dr, arm64_norm, *])
          hal_dr
          (ret_pc := fnBase + bv% (132))
          (by simp only [s_dr, arm64_norm, *])
          (F := sidMalfRO img ∗
            sidSavedRegs s0.sp s0 v24 ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (dropSpeStackX + 96)) ∗
            SpqrV1.ChainProofs.bytesAt ro fp (b0 :: b1 :: b2 :: b3 :: rest) ∗
            memRegion retAddr 48)
          ?_ (hnext := ?_)
        · dsimp only [dropSpeSpecX]
          have hx0_dr : (s_dr.readReg64 .x0 = s0.sp - 96#64) = True :=
            eq_true (by simp only [s_dr, arm64_norm])
          have hsp_dr : s_dr.sp = s0.sp - 96#64 := by simp only [s_dr, arm64_norm, hsp4']
          have hsp_al0 : s_al.sp = s0.sp - 96#64 := by simp only [s_al, arm64_norm, hsp2']
          rw [hx0_dr, pure_true, emp_sepConj, hsp_dr, stackAt_hook_split (s0.sp - 96#64), hsp_al0]
          unfold sidMalfRO
          rw [speWord1_eq]
          have hbuf_pack : ((buf ↦ₛ malfHead6) ∗ ((buf + 6#64) ↦₆₄ malfHi)) =
              (buf ↦ₛ utf8 "malformed file") := buf14_close buf
          have hspe_pack :
              (((s0.sp - 96#64) ↦₆₄ speWord 1) ∗
                (((s0.sp - 96#64) + 8#64) ↦₆₄ 14#64) ∗
                (((s0.sp - 96#64) + 16#64) ↦₆₄ buf) ∗
                (((s0.sp - 96#64) + 24#64) ↦₆₄ 14#64) ∗
                A.live buf 14 1 ∗
                ((buf ↦ₛ malfHead6) ∗ ((buf + 6#64) ↦₆₄ malfHi)) ∗
                (((s0.sp - 96#64) + 32#64) ↦₆₄ (img.base + bv% (ls_str% "bundle"))) ∗
                (((s0.sp - 96#64) + 40#64) ↦₆₄ 6#64) ∗
                ((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle")) ⊢
              speAt A (utf8 "bundle") (s0.sp - 96#64) .invalidState := by
            rw [hbuf_pack]
            exact speAt_invalidState_intro A img (s0.sp - 96#64) buf hptr_ne
          refine Entails.trans ?_
            (Entails.trans (sepConj_mono_left (Q :=
              A.pool ∗
                memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 dropSpeStackX) 32 ∗
                stackAt (s0.sp - 96#64) extHookStack ∗
                sidMalfRO img ∗
                sidSavedRegs s0.sp s0 v24 ∗
                memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (dropSpeStackX + 96)) ∗
                SpqrV1.ChainProofs.bytesAt ro fp (b0 :: b1 :: b2 :: b3 :: rest) ∗
                memRegion retAddr 48) hspe_pack) ?_)
          · unfold sidMalfRO
            simp only [sid_sub_add, BitVec.reduceSub, BitVec.add_assoc, BitVec.reduceAdd,
              sepConj_assoc]
            generalize dropSpeStackX = dsz
            generalize extHookStack = hsz
            exact Entails.of_eq (by ac_rfl)
          · unfold sidMalfRO
            simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
            generalize dropSpeStackX = dsz
            generalize extHookStack = hsz
            exact Entails.of_eq (by ac_rfl)
        ·
          intro s_ep hinv7 hpc7 hrun7 hsp7 hcsp7
          let _ := hinv7
          dsimp only [dropSpeSpecX]
          rw [sepConj_assoc]
          refine SepWPp.pure_elim fun htr7 => ?_
          have hx19_7 : s_ep.readReg64 .x19 = retAddr := by
            rw [hcsp7.1]; simp only [s_dr, arm64_norm, hx19_4]
          have hx20_7 : s_ep.readReg64 .x20 = fp := by
            rw [hcsp7.2.1]; simp only [s_dr, arm64_norm, hx20_4]
          have hx21_7 : s_ep.readReg64 .x21 = BitVec.ofNat 64 rest.length := by
            rw [hcsp7.2.2.1]; simp only [s_dr, arm64_norm]
          have hsp7' : s_ep.sp = s0.sp - 96#64 := by
            rw [hsp7]; simp only [s_dr, arm64_norm, hsp4']
          clear hsp7
          have hal7 : s_ep.spAligned = true := sp_sub_96_spAligned hal0 hsp7'
          let _ := hal7
          have htr7' : s_ep.trace = s0.trace := by
            rw [htr7]; simp only [s_dr, arm64_norm, htr4']
          have hcs7 : SidUpperSaved s0 s_ep := hcs_dr.trans_calleeSaved hcsp7
          rcases hcs7 with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs⟩
          have hsdr_sp : s_dr.sp = s0.sp - 96#64 := by simp only [s_dr, arm64_norm, hsp4']
          rw [hsdr_sp, ret48_open_ok retAddr]
          unfold sidSavedRegs
          simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          refine SepWPp.exists_elim fun r0 => SepWPp.exists_elim fun r8 =>
            SepWPp.exists_elim fun r16 => SepWPp.exists_elim fun r24 => ?_
          cases ro with
          | false =>
            rw [bytesAt_cons4_false fp b0 b1 b2 b3 rest]
            simp only [sepConj_assoc]
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
            · have htrf : sf.trace = s0.trace := by simp only [sf, arm64_norm, htr7']
              rw [htrf, eq_self, pure_true, emp_sepConj]
              refine Entails.trans (Q :=
                (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (dropSpeStackX + 96)) ∗
                  stackAt (s0.sp - 96#64) dropSpeStackX ∗
                  memRegion (s0.sp - 96#64) 48 ∗
                  sidSavedRegs s0.sp s0 v24) ∗
                (sidMalfRO img ∗
                  splitIdResultAt A retAddr fp (b0 :: b1 :: b2 :: b3 :: rest) ∗
                  SpqrV1.ChainProofs.bytesAt false fp (b0 :: b1 :: b2 :: b3 :: rest) ∗
                  A.pool)) ?_ (Entails.trans
                    (sepConj_mono_left (stackAt_sid_pack_region s0.sp stk s0 v24 hstk hstkle)) ?_)
              · dsimp only [splitIdResultAt, splitId]
                rw [bytesAt_cons4_false fp b0 b1 b2 b3 rest]
                unfold sidSavedRegs
                simp only [sepConj_assoc]
                generalize dropSpeStackX = dsz
                exact Entails.of_eq (by ac_rfl)
              · unfold sidMalfRO
                rw [bytesAt_cons4_false fp b0 b1 b2 b3 rest]
                simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
                generalize stackAt s0.sp stk = topStk
                exact Entails.of_eq (by ac_rfl)
          | true =>
            rw [bytesAt_cons4_true fp b0 b1 b2 b3 rest]
            simp only [sepConj_assoc]
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
            · have htrf : sf.trace = s0.trace := by simp only [sf, arm64_norm, htr7']
              rw [htrf, eq_self, pure_true, emp_sepConj]
              refine Entails.trans (Q :=
                (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (dropSpeStackX + 96)) ∗
                  stackAt (s0.sp - 96#64) dropSpeStackX ∗
                  memRegion (s0.sp - 96#64) 48 ∗
                  sidSavedRegs s0.sp s0 v24) ∗
                (sidMalfRO img ∗
                  splitIdResultAt A retAddr fp (b0 :: b1 :: b2 :: b3 :: rest) ∗
                  SpqrV1.ChainProofs.bytesAt true fp (b0 :: b1 :: b2 :: b3 :: rest) ∗
                  A.pool)) ?_ (Entails.trans
                    (sepConj_mono_left (stackAt_sid_pack_region s0.sp stk s0 v24 hstk hstkle)) ?_)
              · dsimp only [splitIdResultAt, splitId]
                rw [bytesAt_cons4_true fp b0 b1 b2 b3 rest]
                unfold sidSavedRegs
                simp only [sepConj_assoc]
                generalize dropSpeStackX = dsz
                exact Entails.of_eq (by ac_rfl)
              · unfold sidMalfRO
                rw [bytesAt_cons4_true fp b0 b1 b2 b3 rest]
                simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
                generalize stackAt s0.sp stk = topStk
                exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SignalSession.Cli.SplitId.Helpers
