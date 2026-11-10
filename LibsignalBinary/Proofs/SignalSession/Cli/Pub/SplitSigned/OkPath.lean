/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.Decode
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.ErrPaths
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `Ok` Path and Top-Level Proof for `signal_session::public::split_signed`

Verifies the `64 ≤ rest.length` branch (`+32 .. +56` → `+212 .. +344`) and composes the prologue and
`split_id` call with all three post-`split_id` branches to prove `splitSigned_ok_of_loads`.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.SplitSigned.Helpers

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
private theorem ssg_sub_add (a k m : BitVec 64) : a - k + m = a - (k - m) := by
  bv_omega

@[simp, arm64_norm]
private theorem add64_sub64_64 (a : BitVec 64) :
    (a + 64#64) - 64#64 = a := by
  bv_omega

@[simp, arm64_norm]
private theorem awc_sub64_fst (a : BitVec 64) :
    (AddWithCarry64 (a + 64#64) (~~~64#64) true).1 = a := by
  simp only [AddWithCarry64]
  bv_bits

@[simp, arm64_norm]
private theorem add64_add_neg64 (a : BitVec 64) :
    (a + 64#64) + bv% (2 ^ 64 - 64) = a := by
  bv_omega

@[simp, arm64_norm]
private theorem zext32_trunc32 (u : BitVec 32) :
    (u.zeroExtend 64).truncate 32 = u := by
  bv_bits

@[simp, arm64_norm]
private theorem sp_restore_96 (sp0 : BitVec 64) :
    sp0 - 96#64 + 96#64 = sp0 := by
  bv_bits

private theorem cs_ge64_raw {u : BitVec 64} (hu : 64 ≤ u.toNat) :
    ConditionHolds CondCode.CS (AddWithCarry64 u (~~~64#64) true).2 = true := by
  simp only [ConditionHolds, AddWithCarry64]
  bv_bits

private theorem ule_ge64_true {u : BitVec 64} (hu : 64 ≤ u.toNat) :
    BitVec.ule 64#64 u = true := by
  simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]
  omega

private theorem ult_ge64_false {u : BitVec 64} (hu : 64 ≤ u.toNat) :
    BitVec.ult u 64#64 = false := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]
  omega

/-! ## `64 ≤ rest.length`: Drop Eager `SignalProtocolError` and Write `Ok` -/

theorem step_ok_signed_path {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {subStk stk : Nat}
    (hb : (img.base &&& 4095#64) = 0#64)
    (hC : AllocContractsX img A ext)
    (hDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      ((dropSpeSpecX A).inImage img))
    (hsub : dropSpeStackX ≤ subStk)
    (hstk : 96 + subStk ≤ stk)
    (hstkle : stk ≤ 2 ^ 64)
    (retAddr fp : BitVec 64) (ro : Bool)
    (file : List (BitVec 8)) (id : BitVec 32) (rest : List (BitVec 8))
    (hsid : splitId file = some (id, rest))
    (hrest_lt64 : rest.length < 2 ^ 64)
    (hge64 : 64 ≤ rest.length)
    {s0 s : State}
    (hal0 : s0.spAligned = true)
    (hinv : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr splitSignedName + bv% (32))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = retAddr)
    (hcs : SsgUpperSaved s0 s) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s
      (ssgMalfRO img ∗
        ((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle") ∗
        splitIdResultAt A (s0.sp - 96#64) fp file ∗
        ssgSavedRegs s0.sp s0 ∗
        stackAt (s0.sp - 96#64) subStk ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
        SpqrV1.ChainProofs.bytesAt ro fp file ∗
        memRegion retAddr 48 ∗
        A.pool)
      (fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ ssgMalfRO img ∗
          (⌜sf.trace = s0.trace⌝ ∗
            splitSignedResultAt A retAddr fp file ∗
            SpqrV1.ChainProofs.bytesAt ro fp file ∗
            stackAt s0.sp stk ∗ A.pool)))
      (SsgPanicAllow s0) := by
  have hsigned : splitSigned file =
      some (id, rest.take (rest.length - 64), rest.drop (rest.length - 64)) := by
    simp only [splitSigned, hsid, hge64, ↓reduceIte]
  have hkey_len : (rest.take (rest.length - 64)).length = rest.length - 64 := by
    rw [List.length_take]
    omega
  have hrest_bv : BitVec.ofNat 64 rest.length = BitVec.ofNat 64 (rest.length - 64) + 64#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hge_bv : 64 ≤ (BitVec.ofNat 64 (rest.length - 64) + 64#64).toNat := by
    rw [← hrest_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrest_lt64]
    exact hge64
  have hcs_raw := cs_ge64_raw hge_bv
  have hcs_norm : ConditionHolds CondCode.CS
      (AddWithCarry64 (BitVec.ofNat 64 (rest.length - 64) + 64#64) (bv% (2 ^ 64 - 65)) true).2 = true :=
    hcs_raw
  have hule := ule_ge64_true hge_bv
  have hult := ult_ge64_false hge_bv
  have _ := And.intro hcs_raw (And.intro hcs_norm (And.intro hule hult))
  have hshim := ssg_shim_ok hC
  have halloc := ssg_alloc_ok hC
  have hdrop := ssg_drop_ok hDrop
  have hpanic := ssg_panic_handle_error img ext
  clear hC hDrop
  have hal : s.spAligned = true := sp_sub_96_spAligned hal0 hsp
  let _ := hal
  have hfn : libsignalSessionCode.fnOff splitSignedName = num% (ls_off% splitSignedName) :=
    splitSigned_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode ssgDec img.base
    (Rust.withPanics ext) hfn (num% (ls_off% splitSignedName)) 32 28
  code_fetches_range CryptoVerification.libsignalSessionCode ssgDec img.base
    (Rust.withPanics ext) hfn (num% (ls_off% splitSignedName)) 212 148
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hdrop hpanic hpc ⊢
  have hfn_addr :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr splitSignedName =
        img.base + bv% (ls_off% "libsignal_cli::public::split_signed") := by
    simp only [Program.fnAddr_rebase]
    rw [hfn]
  have hadrp_m := adrp_malf_ok hb hfn_addr
  have hadrp_b := adrp_bundle_ok hb hfn_addr
  clear hfn hfn_addr
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    splitSignedName = fnBase
  examples_hide_fetches
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hadrp_m hadrp_b
  dsimp only [splitIdResultAt]
  rw [hsid]
  dsimp only
  rw [← splitOkTag_eq, hrest_bv, memRegion16_open ((s0.sp - 96#64) + 32#64)]
  simp only [ssg_sub_add, BitVec.reduceSub, sepExists_sepConj_left, sepExists_sepConj_right,
    sepConj_assoc]
  refine SepWPp.exists_elim fun z1 => SepWPp.exists_elim fun z0 => ?_
  apply SepWPp.of_sepWP_inImage
    (mid := fnBase + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% splitSignedName))
    hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  apply bind_sepWPp_state; intro s_sh
  have hal_sh : s_sh.spAligned = true := sp_sub_96_spAligned hal0 (by simp only [s_sh, arm64_norm, hsp])
  have hcs_sh : SsgUpperSaved s0 s_sh := by
    rcases hcs with ⟨h23, h24, h25, h26, h27, h28, hvregs⟩
    simp only [s_sh, SsgUpperSaved, arm64_norm, *]
  refine ssg_call_inImage () hshim hinv1
    (by simp only [s_sh, arm64_norm, htr])
    (by simp only [s_sh, arm64_norm, *])
    (by simp only [s_sh, arm64_norm, *])
    hal_sh
    (ret_pc := fnBase + bv% (220))
    (by simp only [s_sh, arm64_norm, *])
    (F := ssgMalfRO img ∗
      ((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle") ∗
      ((s0.sp - 96#64) ↦₆₄ bv% (2 ^ 64 - 2)) ∗
      ((s0.sp - 88#64) ↦₃₂ id) ∗
      memRegion (s0.sp - 84#64) 4 ∗
      ((s0.sp - 80#64) ↦₆₄ (fp + 4#64)) ∗
      ((s0.sp - 72#64) ↦₆₄ (BitVec.ofNat 64 (rest.length - 64) + 64#64)) ∗
      ((s0.sp - 64#64) ↦₆₄ z0) ∗
      ((s0.sp - 56#64) ↦₆₄ z1) ∗
      ssgSavedRegs s0.sp s0 ∗
      memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - dropSpeStackX) ∗
      memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 dropSpeStackX) 32 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
      SpqrV1.ChainProofs.bytesAt ro fp file ∗
      memRegion retAddr 48 ∗ A.pool)
    ?_ (hnext := ?_)
  · rw [stackAt_sub_split (s0.sp - 96#64) dropSpeStackX subStk hsub (by omega),
      stackAt_hook_split (s0.sp - 96#64)]
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
    have hx20_2 : s_after_sh.readReg64 .x20 = id.zeroExtend 64 := by
      rw [hcsp2.2.1]; simp only [s_sh, arm64_norm]
    have hx21_2 : s_after_sh.readReg64 .x21 = fp + 4#64 := by
      rw [hcsp2.2.2.1]; simp only [s_sh, arm64_norm]
    have hx22_2 : s_after_sh.readReg64 .x22 = BitVec.ofNat 64 (rest.length - 64) := by
      rw [hcsp2.2.2.2.1]; simp only [s_sh, arm64_norm]
    have hsp2' : s_after_sh.sp = s0.sp - 96#64 := by
      rw [hsp2]; simp only [s_sh, arm64_norm, hsp]
    clear hsp2
    have htr2' : s_after_sh.trace = s0.trace := by
      rw [htr2]; simp only [s_sh, arm64_norm, htr]
    have hcs2 : SsgUpperSaved s0 s_after_sh := hcs_sh.trans_calleeSaved hcsp2
    apply SepWPp.of_sepWP_inImage
      (mid := fnBase + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% splitSignedName))
      hinv2
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv3
    apply bind_sepWPp_state; intro s_al
    have hal_al : s_al.spAligned = true := sp_sub_96_spAligned hal0 (by simp only [s_al, arm64_norm, hsp2'])
    have hcs_al : SsgUpperSaved s0 s_al := by
      rcases hcs2 with ⟨h23, h24, h25, h26, h27, h28, hvregs⟩
      simp only [s_al, SsgUpperSaved, arm64_norm, *]
    have hlay : LayoutOk 14 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
    refine ssg_call_inImage (14, 1) halloc hinv3
      (by simp only [s_al, arm64_norm, htr2'])
      (by simp only [s_al, arm64_norm, *])
      (by simp only [s_al, arm64_norm, *])
      hal_al
      (ret_pc := fnBase + bv% (232))
      (by simp only [s_al, arm64_norm, *])
      (F := ssgMalfRO img ∗
        ((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle") ∗
        ((s0.sp - 96#64) ↦₆₄ bv% (2 ^ 64 - 2)) ∗
        ((s0.sp - 88#64) ↦₃₂ id) ∗
        memRegion (s0.sp - 84#64) 4 ∗
        ((s0.sp - 80#64) ↦₆₄ (fp + 4#64)) ∗
        ((s0.sp - 72#64) ↦₆₄ (BitVec.ofNat 64 (rest.length - 64) + 64#64)) ∗
        ((s0.sp - 64#64) ↦₆₄ z0) ∗
        ((s0.sp - 56#64) ↦₆₄ z1) ∗
        ssgSavedRegs s0.sp s0 ∗
        memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - dropSpeStackX) ∗
        memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 dropSpeStackX) 32 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
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
      dsimp only [rustAllocSpecWithStack]
      have hx19_4 : s_after_al.readReg64 .x19 = retAddr := by
        rw [hcsp4.1]; simp only [s_al, arm64_norm, hx19_2]
      have hx20_4 : s_after_al.readReg64 .x20 = id.zeroExtend 64 := by
        rw [hcsp4.2.1]; simp only [s_al, arm64_norm, hx20_2]
      have hx21_4 : s_after_al.readReg64 .x21 = fp + 4#64 := by
        rw [hcsp4.2.2.1]; simp only [s_al, arm64_norm, hx21_2]
      have hx22_4 : s_after_al.readReg64 .x22 = BitVec.ofNat 64 (rest.length - 64) := by
        rw [hcsp4.2.2.2.1]; simp only [s_al, arm64_norm, hx22_2]
      have hsp4' : s_after_al.sp = s0.sp - 96#64 := by
        rw [hsp4]; simp only [s_al, arm64_norm, hsp2']
      clear hsp4
      have hal4 : s_after_al.spAligned = true := sp_sub_96_spAligned hal0 hsp4'
      let _ := hal4
      have hcs4 : SsgUpperSaved s0 s_after_al := hcs_al.trans_calleeSaved hcsp4
      by_cases hnull : s_after_al.readReg64 .x0 = 0
      ·
        have hnull64 : s_after_al.readReg64 .x0 = 0#64 := hnull
        let _ := hnull64
        simp only [hnull, ↓reduceIte, sepConj_assoc]
        refine sepWPp_pull_pure3 fun htr_oom => ?_
        have htr_al : s_al.trace = s0.trace := by simp only [s_al, arm64_norm, htr2']
        apply SepWPp.of_sepWP
          (mid := fnBase + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% splitSignedName))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        refine SepWPp.panic (by simp only [arm64_norm, *])
          (by simpa only [arm64_norm] using hpanic)
          (ssgPanicAllow_of_eq
            (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htr_oom, htr_al])))
      ·
        set buf := s_after_al.readReg64 .x0 with hbuf_def
        let _ := hbuf_def
        have hptr_ne : buf ≠ 0#64 := hnull
        have hptr_beq : (buf == 0#64) = false := beq_eq_false_iff_ne.mpr hptr_ne
        have hptr_bne : (buf != 0#64) = true := bne_iff_ne.mpr hptr_ne
        have _ := And.intro hptr_beq (And.intro hptr_bne (And.intro hadrp_m hadrp_b))
        simp only [hnull, ↓reduceIte]
        have hw88 : (((s0.sp - 88#64) ↦₃₂ id) ∗ memRegion (s0.sp - 84#64) 4) ⊢
            ∃∗ w88 : BitVec 64, (s0.sp - 88#64) ↦₆₄ w88 := by
          have ha84 : (s0.sp - 88#64) + 4#64 = s0.sp - 84#64 := by bv_omega
          simpa only [ha84] using half32_pad_entails_cell64 (s0.sp - 88#64) id
        refine SepWPp.weaken_pre
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (Entails.trans (Entails.of_eq (sepConj_assoc _ _ _).symm)
              (sepConj_mono_left hw88)))))) ?_
        rw [buf14_open_lo buf]
        conv =>
          arg 4
          unfold ssgMalfRO
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        refine SepWPp.exists_elim fun w88 => SepWPp.exists_elim fun w0 => ?_
        refine sepWPp_pull_pure3 fun ⟨_, htr_ok⟩ => ?_
        have htr4' : s_after_al.trace = s0.trace := by
          rw [htr_ok]; simp only [s_al, arm64_norm, htr2']
        apply SepWPp.of_sepWP_inImage (mid := fnBase + bv% (256)) hinv4
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        intro hinv5
        apply sepWPp_realign_buf14
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        refine SepWPp.exists_elim fun w1 => ?_
        apply SepWPp.of_sepWP_inImage
          (mid := fnBase + bv% ((2 ^ 64 + ls_off% cliDropSpeName - ls_off% splitSignedName) % 2 ^ 64))
          hinv5
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        intro hinv6
        apply bind_sepWPp_state; intro s_dr
        have hal_dr : s_dr.spAligned = true :=
          sp_sub_96_spAligned hal0 (by simp only [s_dr, arm64_norm, hsp4'])
        have hcs_dr : SsgUpperSaved s0 s_dr := by
          rcases hcs4 with ⟨h23, h24, h25, h26, h27, h28, hvregs⟩
          simp only [s_dr, SsgUpperSaved, arm64_norm, *]
        refine ssg_call_inImage ⟨s0.sp - 96#64, utf8 "bundle", .invalidState⟩ hdrop hinv6
          (by simp only [s_dr, arm64_norm, htr4'])
          (by simp only [s_dr, arm64_norm, *])
          (by simp only [s_dr, arm64_norm, *])
          hal_dr
          (ret_pc := fnBase + bv% (300))
          (by simp only [s_dr, arm64_norm, *])
          (F := ssgMalfRO img ∗
            ssgSavedRegs s0.sp s0 ∗
            memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - dropSpeStackX) ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
            SpqrV1.ChainProofs.bytesAt ro fp file ∗
            memRegion retAddr 48)
          ?_ (hnext := ?_)
        · dsimp only [dropSpeSpecX]
          have hx0_dr : (s_dr.readReg64 .x0 = s0.sp - 96#64) = True :=
            eq_true (by simp only [s_dr, arm64_norm])
          have hsp_dr : s_dr.sp = s0.sp - 96#64 := by simp only [s_dr, arm64_norm, hsp4']
          have hsp_al0 : s_al.sp = s0.sp - 96#64 := by simp only [s_al, arm64_norm, hsp2']
          rw [hx0_dr, pure_true, emp_sepConj, hsp_dr, stackAt_hook_split (s0.sp - 96#64), hsp_al0]
          unfold ssgMalfRO
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
                ssgMalfRO img ∗
                ssgSavedRegs s0.sp s0 ∗
                memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - dropSpeStackX) ∗
                memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
                SpqrV1.ChainProofs.bytesAt ro fp file ∗
                memRegion retAddr 48) hspe_pack) ?_)
          · unfold ssgMalfRO
            dsimp only [buf, Reg.x0]
            simp only [ssg_sub_add, BitVec.reduceSub, BitVec.add_assoc, BitVec.reduceAdd,
              sepConj_assoc]
            generalize dropSpeStackX = dsz
            generalize extHookStack = hsz
            exact Entails.of_eq (by ac_rfl)
          · unfold ssgMalfRO
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
          have hx20_7 : s_ep.readReg64 .x20 = id.zeroExtend 64 := by
            rw [hcsp7.2.1]; simp only [s_dr, arm64_norm, hx20_4]
          have hx21_7 : s_ep.readReg64 .x21 = fp + 4#64 := by
            rw [hcsp7.2.2.1]; simp only [s_dr, arm64_norm, hx21_4]
          have hx22_7 : s_ep.readReg64 .x22 = BitVec.ofNat 64 (rest.length - 64) := by
            rw [hcsp7.2.2.2.1]; simp only [s_dr, arm64_norm, hx22_4]
          have hsp7' : s_ep.sp = s0.sp - 96#64 := by
            rw [hsp7]; simp only [s_dr, arm64_norm, hsp4']
          clear hsp7
          have hal7 : s_ep.spAligned = true := sp_sub_96_spAligned hal0 hsp7'
          let _ := hal7
          have htr7' : s_ep.trace = s0.trace := by
            rw [htr7]; simp only [s_dr, arm64_norm, htr4']
          have hcs7 : SsgUpperSaved s0 s_ep := hcs_dr.trans_calleeSaved hcsp7
          rcases hcs7 with ⟨h23, h24, h25, h26, h27, h28, hvregs⟩
          have hsdr_sp : s_dr.sp = s0.sp - 96#64 := by simp only [s_dr, arm64_norm, hsp4']
          rw [hsdr_sp, ret48_open_signed_ok retAddr]
          unfold ssgSavedRegs
          simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          refine SepWPp.exists_elim fun r40 => SepWPp.exists_elim fun r32 =>
            SepWPp.exists_elim fun r24 => SepWPp.exists_elim fun r16 =>
            SepWPp.exists_elim fun r8 => SepWPp.exists_elim fun r0 => ?_
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
            have hstk_pack :
                (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
                  (memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - dropSpeStackX) ∗
                    stackAt (s0.sp - 96#64) dropSpeStackX) ∗
                  memRegion (s0.sp - 96#64) 48 ∗
                  ssgSavedRegs s0.sp s0) ⊢
                stackAt s0.sp stk := by
              rw [← stackAt_sub_split (s0.sp - 96#64) dropSpeStackX subStk hsub (by omega)]
              exact stackAt_ssg_pack_region s0.sp subStk stk s0 hstk hstkle
            refine Entails.trans (Q :=
              (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
                (memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - dropSpeStackX) ∗
                  stackAt (s0.sp - 96#64) dropSpeStackX) ∗
                memRegion (s0.sp - 96#64) 48 ∗
                ssgSavedRegs s0.sp s0) ∗
              (ssgMalfRO img ∗
                splitSignedResultAt A retAddr fp file ∗
                SpqrV1.ChainProofs.bytesAt ro fp file ∗
                A.pool)) ?_
              (Entails.trans (sepConj_mono_left hstk_pack) ?_)
            · dsimp only [splitSignedResultAt]
              rw [hsigned]
              dsimp only
              rw [← splitOkTag_eq, hkey_len]
              unfold ssgSavedRegs
              simp only [sepConj_assoc]
              generalize dropSpeStackX = dsz
              exact Entails.of_eq (by ac_rfl)
            · exact Entails.of_eq (by ac_rfl)

/-! ## Prologue, `split_id` Call, and `splitSigned_ok_of_loads` -/

private theorem sepWPp_mono_post {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Q' Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hq : ∀ sf Pf, Q sf Pf → Q' sf Pf)
    (h : SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s P Q' Qp oom := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hQ⟩ | hpan | hoom_s⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, hq sf Pf hQ⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom_s)⟩

private theorem ssg_prologue {b : BitVec 64} {ext : String → Option (State → State)}
    {s0 : State} {ret fp : BitVec 64} {s48 s40 s32 s24 s16 s8 : BitVec 64}
    {R_frame : SepProp} {post : State → SepProp → Prop}
    (hal0 : s0.spAligned = true)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr splitSignedName)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ret)
    (hx1 : s0.readReg64 .x1 = fp)
    (hnext : ∀ (s1 : State) (P1 : SepProp),
      s1.pc = (tripleRatchetProgAtExt b ext).fnAddr splitSignedName +
        bv% (ls_off% splitIdName - ls_off% splitSignedName) →
      s1.status = .Running →
      s1.sp = s0.sp - 96#64 →
      s1.trace = s0.trace →
      s1.readReg64 Reg.lr = (tripleRatchetProgAtExt b ext).fnAddr splitSignedName + bv% (32) →
      s1.readReg64 .x0 = s0.sp - 96#64 →
      s1.readReg64 .x1 = fp →
      s1.readReg64 .x2 = s0.readReg64 .x2 →
      s1.readReg64 .x19 = ret →
      SsgUpperSaved s0 s1 →
      P1 = (ssgSavedRegs s0.sp s0 ∗ R_frame) →
      post s1 P1) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr splitSignedName +
        bv% (ls_off% splitIdName - ls_off% splitSignedName)) s0
      ((((s0.sp - 48#64) ↦₆₄ s48) ∗ ((s0.sp - 40#64) ↦₆₄ s40) ∗
        ((s0.sp - 32#64) ↦₆₄ s32) ∗ ((s0.sp - 24#64) ↦₆₄ s24) ∗
        ((s0.sp - 16#64) ↦₆₄ s16) ∗ ((s0.sp - 8#64) ↦₆₄ s8)) ∗ R_frame)
      post := by
  have hfn : libsignalSessionCode.fnOff splitSignedName = num% (ls_off% splitSignedName) :=
    splitSigned_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode ssgDec b
    (Rust.withPanics ext) hfn (num% (ls_off% splitSignedName)) 0 32
  clear hfn
  have _ := And.intro hx0 hx1
  dsimp only [tripleRatchetProgAtExt] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    splitSignedName = fnBase
  examples_hide_fetches
  wp_steps
  apply bind_sepWP_state; intro s1
  apply SepWP.done (by simp only [s1, arm64_norm, *]) (by simp only [s1, arm64_norm, *])
  refine hnext s1 _
    (by simp only [s1, arm64_norm])
    (by simp only [s1, arm64_norm, *])
    (by simp only [s1, arm64_norm])
    (by simp only [s1, arm64_norm])
    (by simp only [s1, arm64_norm])
    (by simp only [s1, arm64_norm])
    (by simp only [s1, arm64_norm, *])
    (by simp only [s1, arm64_norm])
    (by simp only [s1, arm64_norm, *])
    (by simp only [s1, SsgUpperSaved, calleeSavedVRegs, arm64_norm])
    ?_
  unfold ssgSavedRegs
  simp only [arm64_norm, sepConj_assoc]

/-- `signal_session::public::split_signed` satisfies `splitSignedSpec` given its callee contracts and `Obj.Loads libsignalSessionImage img`. -/
theorem splitSigned_ok_of_loads {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {splitStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hSplit : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr splitIdName)
      (splitIdSpec A img splitStk))
    (hDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      ((dropSpeSpecX A).inImage img))
    (hstk : 0x60 + max splitStk dropSpeStackX ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr splitSignedName)
      (splitSignedSpec A img stk) := by
  set subStk := max splitStk dropSpeStackX
  have hsub_sp : splitStk ≤ subStk := Nat.le_max_left _ _
  have hsub_dr : dropSpeStackX ≤ subStk := Nat.le_max_right _ _
  have hsplit := ssg_split_ok hSplit
  clear hSplit
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hal0
  dsimp only [splitSignedSpec, Spec.inImage] at hpre
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
  have hpre_ro := ssgMalfRO_bundle_intro himg (Obj.Image.frozenLoaded_iff.mp hinv0.1).2.1 hpre
  clear himg
  rw [stackAt_ssg_split s0.sp subStk stk hstk hstkle, cells48_open s0.sp] at hpre_ro
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc] at hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨s48, hpre_ro⟩ := hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨s40, hpre_ro⟩ := hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨s32, hpre_ro⟩ := hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨s24, hpre_ro⟩ := hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨s16, hpre_ro⟩ := hpre_ro
  rw [satisfies_sepExists] at hpre_ro; obtain ⟨s8, hpre_ro⟩ := hpre_ro
  refine ⟨(((s0.sp - 48#64) ↦₆₄ s48) ∗ ((s0.sp - 40#64) ↦₆₄ s40) ∗
        ((s0.sp - 32#64) ↦₆₄ s32) ∗ ((s0.sp - 24#64) ↦₆₄ s24) ∗
        ((s0.sp - 16#64) ↦₆₄ s16) ∗ ((s0.sp - 8#64) ↦₆₄ s8)) ∗
      (ssgMalfRO img ∗
        ((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle") ∗
        memRegion (s0.sp - 96#64) 48 ∗
        stackAt (s0.sp - 96#64) subStk ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
        SpqrV1.ChainProofs.bytesAt x.ro x.fp x.file ∗
        memRegion x.ret 48 ∗
        A.pool),
    R,
    by
      refine Satisfies.mono ?_ hpre_ro
      exact Entails.of_eq (by ac_rfl),
    ?_⟩
  have hwp : SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s0
      ((((s0.sp - 48#64) ↦₆₄ s48) ∗ ((s0.sp - 40#64) ↦₆₄ s40) ∗
          ((s0.sp - 32#64) ↦₆₄ s32) ∗ ((s0.sp - 24#64) ↦₆₄ s24) ∗
          ((s0.sp - 16#64) ↦₆₄ s16) ∗ ((s0.sp - 8#64) ↦₆₄ s8)) ∗
        (ssgMalfRO img ∗
          ((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle") ∗
          memRegion (s0.sp - 96#64) 48 ∗
          stackAt (s0.sp - 96#64) subStk ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
          SpqrV1.ChainProofs.bytesAt x.ro x.fp x.file ∗
          memRegion x.ret 48 ∗
          A.pool))
      (fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        ∃ G : SepProp, P_f ⊢ G ∗
          (⌜sf.trace = s0.trace⌝ ∗
            splitSignedResultAt A x.ret x.fp x.file ∗
            SpqrV1.ChainProofs.bytesAt x.ro x.fp x.file ∗
            stackAt s0.sp stk ∗ A.pool))
      (SsgPanicAllow s0) := by
    rcases x with ⟨ret, fp, file, ro⟩
    dsimp only at *
    apply SepWPp.of_sepWP_inImage
      (mid := (tripleRatchetProgAtExt img.base ext).fnAddr splitSignedName +
        bv% (ls_off% splitIdName - ls_off% splitSignedName)) hinv0
    refine ssg_prologue hal0 hpc hrun hx0 hx1
      fun s1 P1 hpc1 hrun1 hsp1 htr1 hlr1 hx0_1 hx1_1 hx2_1 hx19_1 hcs1 hP1 hinv1 => ?_
    rw [hP1]
    have hal1 : s1.spAligned = true := sp_sub_96_spAligned hal0 hsp1
    refine ssg_call_inImage ⟨s0.sp - 96#64, fp, file, ro⟩ hsplit hinv1 htr1 hpc1 hrun1 hal1 hlr1
      (F := ssgSavedRegs s0.sp s0 ∗
        ssgMalfRO img ∗
        ((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle") ∗
        memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - splitStk) ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
        memRegion ret 48)
      ?_
      (hpanic := fun sm R' _ hp => by
        dsimp only at hp
        rw [sepConj_assoc, satisfies_pure_sepConj] at hp
        exact hp.1)
      (hnext := ?_)
    · rw [stackAt_sub_split (s0.sp - 96#64) splitStk subStk hsub_sp (by omega)]
      have hpure_sp :
          (s1.readReg64 .x0 = s0.sp - 96#64 ∧ s1.readReg64 .x1 = fp ∧
            (s1.readReg64 .x2).toNat = file.length) = True :=
        eq_true ⟨hx0_1, hx1_1, hx2_1 ▸ hx2_nat⟩
      dsimp only
      rw [hpure_sp, pure_true, emp_sepConj, hsp1]
      exact Entails.of_eq (by ac_rfl)
    · intro s2 hinv2 hpc2 hrun2 hsp2 hcsp2
      dsimp only
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun htr2 => ?_
      have hx19_2 : s2.readReg64 .x19 = ret := hcsp2.1.trans hx19_1
      have hsp2' : s2.sp = s0.sp - 96#64 := hsp2.trans hsp1
      have htr2' : s2.trace = s0.trace := htr2.trans htr1
      have hcs2 : SsgUpperSaved s0 s2 := hcs1.trans_calleeSaved hcsp2
      have hpre2 :
          ((splitIdResultAt A (s0.sp - 96#64) fp file ∗
              SpqrV1.ChainProofs.bytesAt ro fp file ∗
              stackAt s1.sp splitStk ∗
              A.pool) ∗
            ssgSavedRegs s0.sp s0 ∗
            ssgMalfRO img ∗
            ((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle") ∗
            memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - splitStk) ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
            memRegion ret 48) ⊢
          (ssgMalfRO img ∗
            ((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle") ∗
            splitIdResultAt A (s0.sp - 96#64) fp file ∗
            ssgSavedRegs s0.sp s0 ∗
            stackAt (s0.sp - 96#64) subStk ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
            SpqrV1.ChainProofs.bytesAt ro fp file ∗
            memRegion ret 48 ∗
            A.pool) := by
        rw [hsp1, stackAt_sub_split (s0.sp - 96#64) splitStk subStk hsub_sp (by omega)]
        exact Entails.of_eq (by ac_rfl)
      cases hsid : splitId file with
      | none =>
        refine SepWPp.weaken_pre hpre2 ?_
        refine sepWPp_mono_post ?_
          (step_err_copy_path hstk hstkle ret fp ro file hsid hal0 hpc2 hrun2 hsp2' htr2' hx19_2 hcs2)
        intro sf P_f ⟨hspf, hcsf, hent⟩
        exact ⟨hspf, hcsf, ssgMalfRO img ∗ ((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle"),
          Entails.trans hent (Entails.of_eq (by ac_rfl))⟩
      | some p =>
        rcases p with ⟨id, rest⟩
        have hrest_lt : rest.length < 2 ^ 64 := by
          rcases file with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, tl⟩⟩⟩⟩ <;>
            simp [splitId] at hsid
          obtain ⟨_, rfl⟩ := hsid
          simp only [List.length_cons] at hfile_lt64
          omega
        by_cases hge64 : 64 ≤ rest.length
        · refine SepWPp.weaken_pre hpre2 ?_
          refine sepWPp_mono_post ?_
            (step_ok_signed_path hb hC hDrop hsub_dr hstk hstkle ret fp ro file id rest
              hsid hrest_lt hge64 hal0 hinv2 hpc2 hrun2 hsp2' htr2' hx19_2 hcs2)
          intro sf P_f ⟨hspf, hcsf, hent⟩
          exact ⟨hspf, hcsf, ssgMalfRO img, hent⟩
        · have hlt64 : rest.length < 64 := by omega
          refine SepWPp.weaken_pre hpre2 ?_
          refine sepWPp_mono_post ?_
            (step_short_err_path hb hC hsub_dr hstk hstkle ret fp ro file id rest
              hsid hlt64 hal0 hinv2 hpc2 hrun2 hsp2' htr2' hx19_2 hcs2)
          intro sf P_f ⟨hspf, hcsf, hent⟩
          exact ⟨hspf, hcsf, ssgMalfRO img, hent⟩
  intro Fr hm hL
  obtain ⟨sf, hsteps, hout⟩ := hwp Fr hm hL
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, hspf, hcsf, G, hent⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨hoom_s, hmo⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf,
      ⌜sf.trace = s0.trace⌝ ∗ splitSignedResultAt A x.ret x.fp x.file ∗
        SpqrV1.ChainProofs.bytesAt x.ro x.fp x.file ∗ stackAt s0.sp stk ∗ A.pool,
      ?_, fun hmR => hmR, hspf, hcsf⟩⟩
    have hm1 := Satisfies.mono (sepConj_mono_left hent) hmf
    rw [sepConj_assoc] at hm1
    exact Satisfies.of_sep_right hm1
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f, hmf, hqp R⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr ⟨hoom_s, hmo⟩)⟩

end CryptoVerification.SignalSession.Cli.SplitSigned.Helpers
