/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Dev
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Decode
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.ParseSidFs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# Binary Refinement Proof of `signal_session::address`

Proves `address_ok` against `(addressSpec A uuidTryParse resStack).inImage img` on `mProg img ext`,
discharging `ServiceId::parse_from_service_id_string` via `parseSid_okFs` and re-exporting
`MemrchrCall`, `memrchrIdx`, and `memrchrSpec`.
-/

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalPublicApi.StoreKit
open Address.Helpers

set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

private theorem bv_ult_of_lt' {i n : Nat} (hi : i < n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 i).ult (BitVec.ofNat 64 n) = true ∧
      (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 i) = false := by
  simp only [BitVec.ult, BitVec.ule, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans hi hn), Nat.mod_eq_of_lt hn]
  exact ⟨decide_eq_true hi, decide_eq_false (by omega)⟩

set_option maxHeartbeats 800000 in
private theorem address_wp_gen {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack : Nat}
    (hCF : AllocContractsFs img A ext)
    (hmemrchr : subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr "core::slice::memchr::memrchr")
      ((memrchrSpec extHookStack).inImage img))
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63)
    (x : AddressCall) (s0 : State)
    (hal0 : s0.spAligned = true)
    (hinv0 : ImgCallInv img s0)
    (hpc0 : s0.pc = (mProg img ext).fnAddr addressName)
    (hrun0 : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x.out)
    (hx1 : s0.readReg64 .x1 = x.p)
    (hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 x.bs.length)
    (hbs_lt64 : x.bs.length < 2 ^ 64) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s0
      ((x.p ↦ₛ x.bs) ∗ memRegion x.out 32 ∗ A.pool ∗ stackAt s0.sp resStack)
      (AddrGoalPost A resStack x s0)
      (AddrPanicAllow s0) := by
  try dsimp only [Reg.x0, Reg.x1, Reg.x2] at hx0 hx1 hx2
  have hstkle : resStack ≤ 2 ^ 64 := Nat.le_trans hres64 (by decide)
  have hmchr := addr_memrchr_ok hmemrchr
  have hpsid' := addr_parseSid_ok (parseSid_okFs (img := img) (ext := ext))
  have hexit := @step_none_exit img A ext resStack hres hstkle x
  have hdev := @step_dev_dispatch img A ext resStack hCF hres hstkle x
  clear hmemrchr hres64
  rw [stackAt_addr_split s0.sp resStack hres hstkle, cells64_open s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun v64 => SepWPp.exists_elim fun v56 =>
    SepWPp.exists_elim fun v48 => SepWPp.exists_elim fun v40 =>
    SepWPp.exists_elim fun v32 => SepWPp.exists_elim fun v24 =>
    SepWPp.exists_elim fun v16 => SepWPp.exists_elim fun v8 => ?_
  have hfn : libsignalSessionCode.fnOff addressName = num% (ls_off% "libsignal_cli::address") :=
    addr_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode addrDec img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli::address")) 0 44
  code_fetches_range CryptoVerification.libsignalSessionCode addrDec img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli::address")) 52 64
  clear hfn
  change s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr addressName at hpc0
  try dsimp only [tripleRatchetProgAtExt] at hmchr hpsid' hexit hdev hpc0 ⊢
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr addressName = fnBase
  examples_hide_fetches
  apply SepWPp.of_sepWP_inImage
    (mid := fnBase + bv% (ls_off% "core::slice::memchr::memrchr" -
      ls_off% "libsignal_cli::address"))
    hinv0
  wp_steps
  apply SepWP.done
    (by simp only [arm64_norm, *]; try (clear * -; bv_omega))
    (by simp only [arm64_norm, *])
  intro hinv1
  apply bind_sepWPp_state; intro s_mr
  have hal_mr : s_mr.spAligned = true :=
    sp_sub_96_spAligned hal0 (by simp only [s_mr, arm64_norm])
  have hcs_mr : AddrUpperSaved s0 s_mr := by
    simp only [s_mr, AddrUpperSaved, arm64_norm]
  refine addr_call_inImage ⟨46#8, x.p, x.bs⟩ hmchr hinv1
    (by simp only [s_mr, arm64_norm])
    (by simp only [s_mr, arm64_norm, *]; try (clear * -; bv_omega))
    (by simp only [s_mr, arm64_norm, *])
    hal_mr
    (ret_pc := fnBase + memrchrRetOff)
    (by simp only [s_mr, memrchrRetOff, arm64_norm, *])
    (F := memRegion x.out 32 ∗
      memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - (subStackSize + 96)) ∗
      memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStackSize) 80 ∗
      memRegion (s0.sp - 96#64) 32 ∗
      addrSavedRegs s0.sp s0 ∗ A.pool)
    ?_
    (hnext := ?_)
  · dsimp only [memrchrSpec]
    unfold addrSavedRegs
    have hpure_mr :
        ((s_mr.readReg64 .x0).setWidth 8 = 46#8 ∧ s_mr.readReg64 .x1 = x.p ∧
          s_mr.readReg64 .x2 = BitVec.ofNat 64 x.bs.length ∧ x.bs.length < 2 ^ 64) = True :=
      eq_true ⟨by simp only [s_mr, arm64_norm],
        by simp only [s_mr, arm64_norm, hx1],
        by simp only [s_mr, arm64_norm, hx2],
        hbs_lt64⟩
    have hsp_mr : s_mr.sp = s0.sp - 96#64 := by simp only [s_mr, arm64_norm]
    rw [hpure_mr, pure_true, emp_sepConj, hsp_mr, stackAt_sub_hook (s0.sp - 96#64)]
    generalize subStackSize = ssz
    generalize extHookStack = hsz
    exact Entails.of_eq (by ac_rfl)
  · intro s_after_mr hinv2 hpc2 hrun2 hsp2 hcsp2
    dsimp only [memrchrSpec]
    try dsimp only [memrchrRetOff] at hpc2
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun hpure2 => ?_
    rcases hpure2 with ⟨htr2, hfs2, hmr_res⟩
    have hx19_2 : s_after_mr.readReg64 (Reg.gpr 19#5) = x.out := by
      simpa only [Reg.x19] using (hcsp2.1.trans (by simp only [s_mr, arm64_norm, hx0]))
    have hx21_2 : s_after_mr.readReg64 (Reg.gpr 21#5) = x.p := by
      simpa only [Reg.x21] using (hcsp2.2.2.1.trans (by simp only [s_mr, arm64_norm, hx1]))
    have hx22_2 : s_after_mr.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 x.bs.length := by
      simpa only [Reg.x22] using (hcsp2.2.2.2.1.trans (by simp only [s_mr, arm64_norm, hx2]))
    have hsp_mr0 : s_mr.sp = s0.sp - 96#64 := by simp only [s_mr, arm64_norm]
    have hsp2' : s_after_mr.sp = s0.sp - 96#64 := hsp2.trans hsp_mr0
    clear hsp2
    have htr2' : s_after_mr.trace = s0.trace := by
      rw [htr2]; simp only [s_mr, arm64_norm]
    have hcs2 : AddrUpperSaved s0 s_after_mr := hcs_mr.trans_calleeSaved_fs hcsp2 hfs2
    clear hfs2 htr2
    have hrepack_common :
        ((x.p ↦ₛ x.bs) ∗ stackAt s_mr.sp extHookStack ∗
          (memRegion x.out 32 ∗
            memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - (subStackSize + 96)) ∗
            memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStackSize) 80 ∗
            memRegion (s0.sp - 96#64) 32 ∗
            addrSavedRegs s0.sp s0 ∗ A.pool)) ⊢
        ((x.p ↦ₛ x.bs) ∗ memRegion x.out 32 ∗ AddrFrameCommon A resStack s0) := by
      rw [hsp_mr0]
      unfold AddrFrameCommon
      rw [stackAt_sub_hook (s0.sp - 96#64)]
      generalize subStackSize = ssz
      generalize extHookStack = hsz
      exact Entails.of_eq (by ac_rfl)
    rw [sepConj_assoc]
    refine SepWPp.weaken_pre hrepack_common ?_
    cases hmr : memrchrIdx 46#8 x.bs with
    | none =>
      rw [hmr] at hmr_res
      try dsimp only [Reg.x0] at hmr_res
      have hnone : addrParse uuidTryParse x.bs = none := by
        simp only [addrParse, (memrchrIdx_none_iff_rsplitDot x.bs).mp hmr]
      apply SepWPp.of_sepWP (mid := fnBase + noneExitOff)
      wp_steps
      apply SepWP.done
        (by simp only [noneExitOff, arm64_norm, hmr_res, *]; try (clear * -; bv_omega))
        (by simp only [arm64_norm, *])
      exact hexit hnone hal0
        (by simp only [noneExitOff, arm64_norm, hmr_res, *]; try (clear * -; bv_omega))
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hsp2'])
        (by simp only [arm64_norm, htr2'])
        (by simp only [arm64_norm, hx19_2])
        (by rcases hcs2 with ⟨h25, h26, h27, h28, hvregs, hfs'⟩
            simp only [AddrUpperSaved, arm64_norm, *])
    | some idx =>
      rw [hmr] at hmr_res
      rcases hmr_res with ⟨hx0_mr, hx1_mr⟩
      try dsimp only [Reg.x0, Reg.x1] at hx0_mr hx1_mr
      obtain ⟨hidx_lt, _, hbs_split, hrsplit⟩ := memrchrIdx_some_props hmr
      set name := x.bs.take idx
      set dev := x.bs.drop (idx + 1)
      have hname_len : name.length = idx := List.length_take_of_le (Nat.le_of_lt hidx_lt)
      have hbs_eq : x.bs = name ++ (46#8 :: dev) := by simpa [List.append_assoc] using hbs_split
      have hname_lt : name.length < x.bs.length := hname_len ▸ hidx_lt
      have hx1_name : s_after_mr.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 name.length := by
        rw [hx1_mr, hname_len]
      have hbs_sep :
          (x.p ↦ₛ x.bs) =
            (x.p ↦ₛ name) ∗
              ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
              ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ₛ dev) := by
        rw [hbs_eq, pointsToBytes_append, pointsToBytes_cons]
      have hbslen_restore : ∃ bslen : Nat, bslen = x.bs.length := ⟨x.bs.length, rfl⟩
      rcases hbslen_restore with ⟨bslen, hbslen_eq⟩
      have hbslen_lt64 : bslen < 2 ^ 64 := hbslen_eq ▸ hbs_lt64
      have hname_lt' : name.length < bslen := hbslen_eq ▸ hname_lt
      have hx22_bslen : s_after_mr.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 bslen :=
        hbslen_eq ▸ hx22_2
      obtain ⟨hname_ult, hname_ule_f⟩ := bv_ult_of_lt' hname_lt' hbslen_lt64
      have hrestore_x22 : ∀ r : BitVec 64, r = BitVec.ofNat 64 bslen → r = BitVec.ofNat 64 x.bs.length :=
        fun _ hr => hr.trans (congrArg (BitVec.ofNat 64) hbslen_eq)
      clear hbslen_eq hx22_2 hname_len hx1_mr hidx_lt hbs_split hname_lt
      rw [hbs_sep]
      unfold AddrFrameCommon
      rw [scratch32_split_17 (s0.sp - 96#64)]
      simp only [sepConj_assoc]
      apply SepWPp.of_sepWP_inImage
        (mid := fnBase + bv% ((2 ^ 64 + ls_off% parseSidName -
          ls_off% "libsignal_cli::address") % 2 ^ 64))
        hinv2
      wp_steps
      apply SepWP.done
        (by simp only [arm64_norm, hx0_mr, hx1_name, hx22_bslen, *]; try (clear * -; bv_omega))
        (by simp only [arm64_norm, *])
      intro hinv3
      have hx22_2 : s_after_mr.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 x.bs.length :=
        hrestore_x22 _ hx22_bslen
      apply bind_sepWPp_state; intro s_ps
      have hal_ps : s_ps.spAligned = true :=
        sp_sub_96_spAligned hal0 (by simp only [s_ps, arm64_norm, hsp2'])
      have hcs_ps : AddrUpperSaved s0 s_ps := by
        rcases hcs2 with ⟨h25, h26, h27, h28, hvregs, hfs'⟩
        simp only [s_ps, AddrUpperSaved, arm64_norm, *]; try rfl
      have hname_toNat : (BitVec.ofNat 64 name.length).toNat = name.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine addr_call_inImage (x.p, name, (s0.sp - 96#64) + 12#64) hpsid' hinv3
        (by simp only [s_ps, arm64_norm, htr2'])
        (by simp only [s_ps, arm64_norm, *]; try (clear * -; bv_omega))
        (by simp only [s_ps, arm64_norm, *])
        hal_ps
        (ret_pc := fnBase + parseSidRetOff)
        (by simp only [s_ps, parseSidRetOff, arm64_norm, *])
        (F := ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
          ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ₛ dev) ∗
          memRegion x.out 32 ∗
          memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - (subStackSize + 96)) ∗
          memRegion (s0.sp - 96#64) 12 ∗
          memRegion ((s0.sp - 96#64) + 29#64) 3 ∗
          addrSavedRegs s0.sp s0 ∗ A.pool)
        ?_
        (hnext := ?_)
      · dsimp only [Spec.keepsFs, parseSidCodeStackSpec, parseSidSpec]
        have hpure_ps :
            (s_ps.readReg64 .x0 = x.p ∧ (s_ps.readReg64 .x1).toNat = name.length ∧
              s_ps.readReg64 .x8 = (s0.sp - 96#64) + 12#64) = True :=
          eq_true ⟨by simp only [s_ps, arm64_norm, hx21_2],
            by simp only [s_ps, arm64_norm, hx1_name, hname_toNat],
            by simp only [s_ps, arm64_norm, hsp2']⟩
        have hsp_ps : s_ps.sp = s0.sp - 96#64 := by simp only [s_ps, arm64_norm, hsp2']
        rw [hpure_ps, pure_true, emp_sepConj, hsp_ps, stackAt_sub_parseSid (s0.sp - 96#64)]
        generalize parseSidFrameStack = pf
        generalize extHookStack = hsz
        exact Entails.of_eq (by ac_rfl)
      · intro s_after_ps hinv4 hpc4 hrun4 hsp4 hcsp4
        dsimp only [Spec.keepsFs, parseSidCodeStackSpec, parseSidSpec]
        try dsimp only [parseSidRetOff] at hpc4
        simp only [sepConj_assoc]
        refine SepWPp.pure_elim fun hfs4 => ?_
        refine SepWPp.pure_elim fun htr4 => ?_
        have hx19_4 : s_after_ps.readReg64 .x19 = x.out := by
          rw [hcsp4.1]; simp only [s_ps, arm64_norm, hx19_2]
        have hx20_4 : s_after_ps.readReg64 .x20 = BitVec.ofNat 64 name.length := by
          rw [hcsp4.2.1]; simp only [s_ps, arm64_norm, hx1_name]
        have hx21_4 : s_after_ps.readReg64 .x21 = x.p := by
          rw [hcsp4.2.2.1]; simp only [s_ps, arm64_norm, hx21_2]
        have hx22_4 : s_after_ps.readReg64 .x22 = BitVec.ofNat 64 x.bs.length := by
          rw [hcsp4.2.2.2.1]; simp only [s_ps, arm64_norm, hx22_2]
        have hsp_ps0 : s_ps.sp = s0.sp - 96#64 := by simp only [s_ps, arm64_norm, hsp2']
        have hsp4' : s_after_ps.sp = s0.sp - 96#64 := hsp4.trans hsp_ps0
        clear hsp4
        have htr4' : s_after_ps.trace = s0.trace := by
          rw [htr4]; simp only [s_ps, arm64_norm, htr2']
        have hcs4 : AddrUpperSaved s0 s_after_ps := hcs_ps.trans_calleeSaved_fs hcsp4 hfs4
        clear hfs4 htr4
        have hstk_ps :
            ∀ R : SepProp,
              stackAt (s0.sp - 96#64 - 80#64) extHookStack ∗
                (stackAt (s0.sp - 96#64) parseSidFrameStack ∗ R) =
              stackAt (s0.sp - 96#64) subStackSize ∗ R := by
          intro R; rw [← sepConj_assoc, ← stackAt_sub_parseSid (s0.sp - 96#64)]
        rw [hsp_ps0, hstk_ps]
        exact hdev name dev hbs_eq hbs_lt64 hrsplit
          hal0 hinv4 hpc4 hrun4 hsp4' htr4' hx19_4 hx20_4 hx21_4 hx22_4 hcs4

/-- `signal_session::address` satisfies `addressSpec A uuidTryParse resStack` in `img`. -/
theorem address_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack : Nat}
    (hCF : AllocContractsFs img A ext)
    (hmemrchr : subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr "core::slice::memchr::memrchr")
      ((memrchrSpec extHookStack).inImage img))
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr addressName)
      ((addressSpec A uuidTryParse resStack).inImage img) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc0 hrun0 hpre0 hal0
  dsimp only [Spec.inImage, addressSpec] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨hinv0, hpre0⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hx1, hx2⟩, hm0⟩
  have hbs_lt64 : x.bs.length < 2 ^ 64 :=
    slice_lt_addr_space (by simpa only [sepConj_assoc] using hm0)
  have hwp := address_wp_gen hCF hmemrchr hres hres64
    x s0 hal0 hinv0 hpc0 hrun0 hx0 hx1 hx2 hbs_lt64
  refine ⟨_, R, hm0, fun R' hm' hL => ?_⟩
  obtain ⟨sf, hsteps, ⟨hpcsf, hruns, P_f, hm_f, hsp_f, hcs_f, hpost_f⟩ |
      ⟨hpan, P_f, hm_f, halloc_f⟩ | hoom⟩ := hwp R' hm' hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpcsf, hruns, P_f, hm_f, ?_, hsp_f, hcs_f⟩⟩
    intro hmR; dsimp only [Spec.inImage]
    exact Satisfies.mono (sepConj_mono_left hpost_f) hmR
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f, hm_f, halloc_f R⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

private example (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hookStack resStack : Nat) (hCF : AllocContractsFs img A ext)
    (hmemrchr : subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr "core::slice::memchr::memrchr")
      ((memrchrSpec extHookStack).inImage img))
    (hres : 0xB0 + extHookStack ≤ resStack) (hres64 : resStack ≤ 2 ^ 63)
    (hc : MainCallees img A ext uuidTryParse hookStack resStack) :
    let T := subroutine_ok (mProg img ext) ((mProg img ext).fnAddr addressName)
      ((addressSpec A uuidTryParse resStack).inImage img)
    (hc.address : T) = hc.address ∧ T :=
  ⟨rfl, address_ok hCF hmemrchr hres hres64⟩

end CryptoVerification.SignalSession.Cli.MainHops
