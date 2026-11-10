/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.Decode
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Error Paths for `signal_session::public::split_signed`

Verifies both error branches after `split_id`: propagating the 48-byte `Err` when `splitId file = none`
(`step_err_copy_path`), and constructing `InvalidState("bundle", "malformed file")` when
`splitId file = some (id, rest)` with `rest.length < 64` (`step_short_err_path`).
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
private theorem zext32_trunc32 (u : BitVec 32) :
    (u.zeroExtend 64).truncate 32 = u := by
  bv_bits

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

private theorem cs_lt64_raw {u : BitVec 64} (hu : u.toNat < 64) :
    ConditionHolds CondCode.CS (AddWithCarry64 u (~~~64#64) true).2 = false := by
  simp only [ConditionHolds, AddWithCarry64]
  bv_bits

private theorem ule_lt64_false {u : BitVec 64} (hu : u.toNat < 64) :
    BitVec.ule 64#64 u = false := by
  simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]
  omega

private theorem ult_lt64_true {u : BitVec 64} (hu : u.toNat < 64) :
    BitVec.ult u 64#64 = true := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]
  omega

/-! ## `splitId file = none`: 48-Byte `Err` Copy -/

theorem step_err_copy_path {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {subStk stk : Nat}
    (hstk : 96 + subStk ≤ stk)
    (hstkle : stk ≤ 2 ^ 64)
    (retAddr fp : BitVec 64) (ro : Bool)
    (file : List (BitVec 8))
    (hnone : splitId file = none)
    {s0 s : State}
    (hal0 : s0.spAligned = true)
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
          (((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle") ∗
            (⌜sf.trace = s0.trace⌝ ∗
              splitSignedResultAt A retAddr fp file ∗
              SpqrV1.ChainProofs.bytesAt ro fp file ∗
              stackAt s0.sp stk ∗ A.pool))))
      (SsgPanicAllow s0) := by
  have hsigned : splitSigned file = none := by
    simp only [splitSigned, hnone]
  have hal : s.spAligned = true := sp_sub_96_spAligned hal0 hsp
  let _ := hal
  rcases hcs with ⟨h23, h24, h25, h26, h27, h28, hvregs⟩
  have hfn : libsignalSessionCode.fnOff splitSignedName = num% (ls_off% splitSignedName) :=
    splitSigned_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode ssgDec img.base
    (Rust.withPanics ext) hfn (num% (ls_off% splitSignedName)) 32 16
  code_fetches_range CryptoVerification.libsignalSessionCode ssgDec img.base
    (Rust.withPanics ext) hfn (num% (ls_off% splitSignedName)) 164 48
  clear hfn
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    splitSignedName = fnBase
  examples_hide_fetches
  dsimp only [splitIdResultAt]
  rw [hnone, speAt_invalidState_copy_open A (s0.sp - 96#64), ret48_open_err retAddr]
  unfold ssgSavedRegs
  simp only [pointsTo64_split32 (retAddr + 8#64), BitVec.add_assoc, BitVec.reduceAdd,
    ssg_sub_add, BitVec.reduceSub, ← speWord1_eq,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
    SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 =>
    SepWPp.exists_elim fun u4 => SepWPp.exists_elim fun u5 =>
    SepWPp.exists_elim fun strPtr => SepWPp.exists_elim fun bs =>
    SepWPp.exists_elim fun cap => SepWPp.exists_elim fun ptr => ?_
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
  · have htrf : sf.trace = s0.trace := by simp only [sf, arm64_norm, htr]
    rw [htrf, eq_self, pure_true, emp_sepConj]
    dsimp only [splitSignedResultAt]
    rw [hsigned]
    have hspe_dst :
        ((retAddr ↦₆₄ speWord 1) ∗
          ((retAddr + 8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
          ((retAddr + 12#64) ↦₃₂ cap.extractLsb' 32 32) ∗
          ((retAddr + 16#64) ↦₆₄ ptr) ∗
          ((retAddr + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((retAddr + 32#64) ↦₆₄ strPtr) ∗
          ((retAddr + 40#64) ↦₆₄ 6#64) ∗
          speVecHeap A bs cap ptr ∗
          (strPtr ↦ᵣ utf8 "bundle")) ⊢
        speAt A (utf8 "bundle") retAddr .invalidState := by
      rw [speAt_invalidState_copy_open A retAddr]
      exact Entails.sepExists_right strPtr (Entails.sepExists_right bs
        (Entails.sepExists_right cap (Entails.sepExists_right ptr
          (Entails.of_eq (by ac_rfl)))))
    have hcells_src :
        (((s0.sp - 96#64) ↦₆₄ speWord 1) ∗
          ((s0.sp - 88#64) ↦₃₂ cap.extractLsb' 0 32) ∗
          ((s0.sp - 84#64) ↦₃₂ cap.extractLsb' 32 32) ∗
          ((s0.sp - 80#64) ↦₆₄ ptr) ∗
          ((s0.sp - 72#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((s0.sp - 64#64) ↦₆₄ strPtr) ∗
          ((s0.sp - 56#64) ↦₆₄ 6#64)) ⊢
        cells (s0.sp - 96#64) 6 := by
      refine Entails.trans ?_
        (cells6_of_words s0.sp (speWord 1) cap ptr (BitVec.ofNat 64 bs.length) strPtr 6#64)
      rw [pointsTo64_split32 (s0.sp - 88#64) cap]
      simp only [ssg_sub_add, BitVec.reduceSub]
      exact Entails.of_eq (by ac_rfl)
    have hstk_pack :
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
          stackAt (s0.sp - 96#64) subStk ∗
          (((s0.sp - 96#64) ↦₆₄ speWord 1) ∗
            ((s0.sp - 88#64) ↦₃₂ cap.extractLsb' 0 32) ∗
            ((s0.sp - 84#64) ↦₃₂ cap.extractLsb' 32 32) ∗
            ((s0.sp - 80#64) ↦₆₄ ptr) ∗
            ((s0.sp - 72#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            ((s0.sp - 64#64) ↦₆₄ strPtr) ∗
            ((s0.sp - 56#64) ↦₆₄ 6#64)) ∗
          ssgSavedRegs s0.sp s0) ⊢
        stackAt s0.sp stk :=
      Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hcells_src)))
        (stackAt_ssg_pack_cells s0.sp subStk stk s0 hstk hstkle)
    rw [speWord1_eq]
    refine Entails.trans ?_
      (Entails.trans (sepConj_mono hspe_dst
        (sepConj_mono_left
          (Q := ssgMalfRO img ∗ ((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle") ∗
            SpqrV1.ChainProofs.bytesAt ro fp file ∗ A.pool)
          hstk_pack)) ?_)
    · unfold ssgSavedRegs
      simp only [sepConj_assoc]
      exact Entails.of_eq (by ac_rfl)
    · generalize stackAt s0.sp stk = topStk
      exact Entails.of_eq (by ac_rfl)

/-! ## `rest.length < 64`: Construct `"malformed file"` Error -/

theorem step_short_err_path {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {subStk stk : Nat}
    (hb : (img.base &&& 4095#64) = 0#64)
    (hC : AllocContractsX img A ext)
    (hsub : dropSpeStackX ≤ subStk)
    (hstk : 96 + subStk ≤ stk)
    (hstkle : stk ≤ 2 ^ 64)
    (retAddr fp : BitVec 64) (ro : Bool)
    (file : List (BitVec 8)) (id : BitVec 32) (rest : List (BitVec 8))
    (hsid : splitId file = some (id, rest))
    (hlt64 : rest.length < 64)
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
  have hsigned : splitSigned file = none := by
    simp only [splitSigned, hsid, show ¬ (64 ≤ rest.length) by omega, ↓reduceIte]
  have hshim := ssg_shim_ok hC
  have halloc := ssg_alloc_ok hC
  have hpanic := ssg_panic_handle_error img ext
  clear hC
  have hal : s.spAligned = true := sp_sub_96_spAligned hal0 hsp
  let _ := hal
  have hlt_bv : (BitVec.ofNat 64 rest.length).toNat < 64 := by
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact hlt64
  have hcs_raw := cs_lt64_raw hlt_bv
  have hcs_norm : ConditionHolds CondCode.CS
      (AddWithCarry64 (BitVec.ofNat 64 rest.length) (bv% (2 ^ 64 - 65)) true).2 = false :=
    hcs_raw
  have hule := ule_lt64_false hlt_bv
  have hult := ult_lt64_true hlt_bv
  have _ := And.intro hcs_raw (And.intro hcs_norm (And.intro hule hult))
  have hfn : libsignalSessionCode.fnOff splitSignedName = num% (ls_off% splitSignedName) :=
    splitSigned_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode ssgDec img.base
    (Rust.withPanics ext) hfn (num% (ls_off% splitSignedName)) 32 132
  code_fetches_range CryptoVerification.libsignalSessionCode ssgDec img.base
    (Rust.withPanics ext) hfn (num% (ls_off% splitSignedName)) 348 12
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hpanic hpc ⊢
  have hfn_addr :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr splitSignedName =
        img.base + bv% (ls_off% "libsignal_cli::public::split_signed") := by
    simp only [Program.fnAddr_rebase]
    rw [hfn]
  have hadrp_m := adrp_malf_short hb hfn_addr
  have hadrp_b := adrp_bundle_short hb hfn_addr
  clear hfn hfn_addr
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    splitSignedName = fnBase
  examples_hide_fetches
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hadrp_m hadrp_b
  dsimp only [splitIdResultAt]
  rw [hsid, ← splitOkTag_eq, memRegion16_open ((s0.sp - 96#64) + 32#64)]
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
    (ret_pc := fnBase + bv% (64))
    (by simp only [s_sh, arm64_norm, *])
    (F := ssgMalfRO img ∗
      ((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle") ∗
      ((s0.sp - 96#64) ↦₆₄ bv% (2 ^ 64 - 2)) ∗
      ((s0.sp - 88#64) ↦₃₂ id) ∗
      memRegion (s0.sp - 84#64) 4 ∗
      ((s0.sp - 80#64) ↦₆₄ (fp + 4#64)) ∗
      ((s0.sp - 72#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗
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
      (ret_pc := fnBase + bv% (76))
      (by simp only [s_al, arm64_norm, *])
      (F := ssgMalfRO img ∗
        ((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle") ∗
        ((s0.sp - 96#64) ↦₆₄ bv% (2 ^ 64 - 2)) ∗
        ((s0.sp - 88#64) ↦₃₂ id) ∗
        memRegion (s0.sp - 84#64) 4 ∗
        ((s0.sp - 80#64) ↦₆₄ (fp + 4#64)) ∗
        ((s0.sp - 72#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗
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
      let _ := hinv4
      dsimp only [rustAllocSpecWithStack]
      have hx19_4 : s_after_al.readReg64 .x19 = retAddr := by
        rw [hcsp4.1]; simp only [s_al, arm64_norm, hx19_2]
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
        have _ := And.intro hptr_beq hptr_bne
        simp only [hnull, ↓reduceIte]
        have hw88 : (((s0.sp - 88#64) ↦₃₂ id) ∗ memRegion (s0.sp - 84#64) 4) ⊢
            ∃∗ w88 : BitVec 64, (s0.sp - 88#64) ↦₆₄ w88 := by
          have ha84 : (s0.sp - 88#64) + 4#64 = s0.sp - 84#64 := by bv_omega
          simpa only [ha84] using half32_pad_entails_cell64 (s0.sp - 88#64) id
        refine SepWPp.weaken_pre
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (Entails.trans (Entails.of_eq (sepConj_assoc _ _ _).symm)
              (sepConj_mono_left hw88)))))) ?_
        rw [buf14_open_lo buf, ret48_open_err retAddr]
        unfold ssgMalfRO ssgSavedRegs
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        refine SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
          SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 =>
          SepWPp.exists_elim fun u4 => SepWPp.exists_elim fun u5 =>
          SepWPp.exists_elim fun w88 => SepWPp.exists_elim fun w0 => ?_
        refine sepWPp_pull_pure3 fun ⟨_, htr_ok⟩ => ?_
        have htr4' : s_after_al.trace = s0.trace := by
          rw [htr_ok]; simp only [s_al, arm64_norm, htr2']
        rcases hcs4 with ⟨h23, h24, h25, h26, h27, h28, hvregs⟩
        apply SepWPp.of_sepWP (mid := fnBase + bv% (116))
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
          dsimp only [splitSignedResultAt]
          rw [hsigned]
          have hsp_al0 : s_al.sp = s0.sp - 96#64 := by simp only [s_al, arm64_norm, hsp2']
          have hbuf_pack : ((buf ↦ₛ malfHead6) ∗ ((buf + 6#64) ↦₆₄ malfHi)) =
              (buf ↦ₛ utf8 "malformed file") := buf14_close buf
          have hcells_back :
              (((s0.sp - 96#64) ↦₆₄ bv% (2 ^ 64 - 2)) ∗ ((s0.sp - 88#64) ↦₆₄ w88) ∗
                ((s0.sp - 80#64) ↦₆₄ buf) ∗ ((s0.sp - 72#64) ↦₆₄ 14#64) ∗
                ((s0.sp - 64#64) ↦₆₄ (img.base + bv% (ls_str% "bundle"))) ∗
                ((s0.sp - 56#64) ↦₆₄ 6#64)) ⊢ cells (s0.sp - 96#64) 6 :=
            cells6_of_words s0.sp (bv% (2 ^ 64 - 2)) w88 buf 14#64
              (img.base + bv% (ls_str% "bundle")) 6#64
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
              (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 96)) ∗
                (memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStk) (subStk - dropSpeStackX) ∗
                  (memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 dropSpeStackX) 32 ∗
                    stackAt (s0.sp - 96#64) extHookStack)) ∗
                (((s0.sp - 96#64) ↦₆₄ bv% (2 ^ 64 - 2)) ∗ ((s0.sp - 88#64) ↦₆₄ w88) ∗
                  ((s0.sp - 80#64) ↦₆₄ buf) ∗ ((s0.sp - 72#64) ↦₆₄ 14#64) ∗
                  ((s0.sp - 64#64) ↦₆₄ (img.base + bv% (ls_str% "bundle"))) ∗
                  ((s0.sp - 56#64) ↦₆₄ 6#64)) ∗
                ssgSavedRegs s0.sp s0) ⊢
              stackAt s0.sp stk := by
            rw [← stackAt_hook_split (s0.sp - 96#64),
              ← stackAt_sub_split (s0.sp - 96#64) dropSpeStackX subStk hsub (by omega)]
            exact Entails.trans
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hcells_back)))
              (stackAt_ssg_pack_cells s0.sp subStk stk s0 hstk hstkle)
          rw [hsp_al0, speWord1_eq]
          refine Entails.trans ?_
            (Entails.trans (sepConj_mono hspe_pack
              (sepConj_mono_left
                (Q := ssgMalfRO img ∗ SpqrV1.ChainProofs.bytesAt ro fp file ∗ A.pool)
                hstk_pack)) ?_)
          · unfold ssgMalfRO ssgSavedRegs
            dsimp only [buf, Reg.x0]
            simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
            generalize dropSpeStackX = dsz
            generalize extHookStack = hsz
            exact Entails.of_eq (by ac_rfl)
          · unfold ssgMalfRO
            simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
            generalize stackAt s0.sp stk = topStk
            exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SignalSession.Cli.SplitSigned.Helpers
