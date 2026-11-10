/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.StepsPrefix
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.Decode
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.AddressText.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
  (vecU8Buf vecU8BufRest vecU8At_eq_header_buf layoutOk_align1
   vecU8Buf_entails_slice_rest slice_rest_entails_vecU8Buf)
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession.Cli

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  frameOff shimRetOff allocRetOff memcpy0RetOff res0RetOff decRetOff res1RetOff memcpy1RetOff

/-! ## 5. Segment 3 (`176 .. 224` & `308 .. 336`): optional reserve + `memcpy` of `dec` -/

theorem cmp_hi_ult_true {cap : BitVec 64} {pfxLen decLen : Nat}
    (hpfx : pfxLen ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) (hdec : decLen ≤ 3)
    (hlt : cap.toNat < pfxLen + decLen) :
    (cap - BitVec.ofNat 64 pfxLen).ult (BitVec.ofNat 64 decLen) = true := by
  have hp : (BitVec.ofNat 64 pfxLen).toNat = pfxLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hd : (BitVec.ofNat 64 decLen).toNat = decLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hle_bv : BitVec.ofNat 64 pfxLen ≤ cap := BitVec.le_def.mpr (by omega)
  simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_sub_of_le hle_bv, hp, hd]
  omega

theorem cmp_hi_ult_false {cap : BitVec 64} {pfxLen decLen : Nat}
    (hcap : cap.toNat < 2 ^ 63) (hdec : decLen ≤ 3)
    (hle : pfxLen + decLen ≤ cap.toNat) :
    (cap - BitVec.ofNat 64 pfxLen).ult (BitVec.ofNat 64 decLen) = false := by
  have hp : (BitVec.ofNat 64 pfxLen).toNat = pfxLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hd : (BitVec.ofNat 64 decLen).toNat = decLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hle_bv : BitVec.ofNat 64 pfxLen ≤ cap := BitVec.le_def.mpr (by omega)
  simp only [BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_sub_of_le hle_bv, hp, hd]
  omega

theorem vecU8At_header_unpack (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap ptr bs) := by
  rw [vecU8At_eq_header_buf]
  refine Entails.trans (sepConj_mono_right (vecU8Buf_entails_slice_rest A cap ptr bs)) ?_
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (slice_rest_entails_vecU8Buf A cap ptr bs)))))
  unfold vecHeader
  apply entails_of_eq
  ac_rfl

theorem step_append_dec {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack subStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hRes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDoReserveName)
      ((SpqrV1.Varint.doReserveSpecOf resStack A).inImage img))
    (hres_le : resStack ≤ subStk) (hext_le : extHookStack ≤ subStk) (hsub64 : subStk ≤ 2 ^ 64)
    {x : AddrTextGhost} {R Fr : SepProp} {s0 s : State} {sp' cap1 p1 : BitVec 64}
    {Q : State → SepProp → Prop}
    (hfz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr addressTextName + decRetOff)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp')
    (hsp_al : (sp' &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hvregs : preservedTailRegs s = preservedTailRegs s0)
    (hlen32 : x.g.name.bytes.length < 2 ^ 32)
    (hcap1_34 : cap1.toNat < 2 ^ 34)
    (hnext : ∀ (sm : State) (capF ptrF dCap dPtr : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr addressTextName + memcpy1RetOff →
      sm.status = .Running →
      sm.sp = sp' →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = x.ret →
      sm.readReg64 .x20 = dPtr →
      sm.readReg64 .x21 =
        BitVec.ofNat 64 (decimalText (x.g.device.zeroExtend 32).toNat).length →
      sm.readReg64 .x22 =
        BitVec.ofNat 64 (x.g.name.bytes ++ [0x2e#8]).length →
      preservedTailRegs sm = preservedTailRegs s0 →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      (decimalText (x.g.device.zeroExtend 32).toNat).length ≤ dCap.toNat →
      dCap.toNat < 2 ^ 63 →
      dPtr ≠ 0 →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) sm
        ((sp' ↦₆₄ capF) ∗ ((sp' + 8#64) ↦₆₄ ptrF) ∗
          ((sp' + 16#64) ↦₆₄ BitVec.ofNat 64 (x.g.name.bytes ++ [0x2e#8]).length) ∗
          vecU8Buf A capF ptrF ((x.g.name.bytes ++ [0x2e#8]) ++
            decimalText (x.g.device.zeroExtend 32).toNat) ∗
          ((sp' + 24#64) ↦₆₄ dCap) ∗ ((sp' + 32#64) ↦₆₄ dPtr) ∗
          ((sp' + 40#64) ↦₆₄
            BitVec.ofNat 64 (decimalText (x.g.device.zeroExtend 32).toNat).length) ∗
          (dPtr ↦ₛ decimalText (x.g.device.zeroExtend 32).toNat) ∗
          vecU8BufRest A dCap dPtr (decimalText (x.g.device.zeroExtend 32).toNat) ∗
          stackAt sp' subStk ∗ A.pool ∗ Fr)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (addrTextSpec A img stk).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s
      (vecU8At A sp' cap1 p1 (x.g.name.bytes ++ [0x2e#8]) ∗
        vecU8 A (sp' + 24#64) (decimalText (x.g.device.zeroExtend 32).toNat) ∗
        stackAt sp' subStk ∗ A.pool ∗ Fr)
      Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (addrTextSpec A img stk).onPanic x s0 sf ∗ R)) := by
  obtain ⟨hx25, hx26, hx27, hx28, hvregs0⟩ := preservedTailRegs_elim hvregs
  have hdoRes := at_doReserve_ok hRes
  have hmemcpy := at_memcpy2_ok hC
  code_fetches_range CryptoVerification.libsignalSessionCode addrTextBin
    img.base (Rust.withPanics ext) addressText_fnOff
    (ls_off% "libsignal_cli::stores::address_text") 176 48
  code_fetches_range CryptoVerification.libsignalSessionCode addrTextBin
    img.base (Rust.withPanics ext) addressText_fnOff
    (ls_off% "libsignal_cli::stores::address_text") 308 32
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr addressTextName = entry
  examples_hide_fetches
  generalize hdec_def : decimalText (x.g.device.zeroExtend 32).toNat = dec at hnext ⊢
  generalize hpfx_def : x.g.name.bytes ++ [0x2e#8] = pfx at hnext ⊢
  have hpfx_bound : pfx.length ≤ 2 ^ 32 := by
    subst hpfx_def; rw [List.length_append, List.length_singleton]; omega
  have hdec_pos : 0 < dec.length := by
    subst hdec_def; rw [device_zeroExtend32_toNat]; exact decimalText_device_pos x.g.device
  have hdec_le3 : dec.length ≤ 3 := by
    subst hdec_def; rw [device_zeroExtend32_toNat]; exact decimalText_device_len_le_three x.g.device
  have hdec_nz_beq : (BitVec.ofNat 64 dec.length == 0#64) = false :=
    ofNat_beq_zero_false hdec_pos (by omega)
  have htoNat_pfx : (BitVec.ofNat 64 pfx.length).toNat = pfx.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have htoNat_dec : (BitVec.ofNat 64 dec.length).toNat = dec.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1_toNat : (1#64).toNat = 1 := rfl
  apply sepWPp_fold (vecU8_dec_unpack A (sp' + 24#64) dec) (by sep_focus)
  simp only [sepExists_sepConj_left]
  refine sepWPp_exists_elim fun dCap => ?_
  refine sepWPp_exists_elim fun dPtr => ?_
  rw [sepConj_assoc]
  refine SepWPp.pure_left fun ⟨hd_le, hd_63, hd_ptr⟩ => ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  by_cases hgrow : cap1.toNat < pfx.length + dec.length
  · apply sepWPp_fold (vecU8At_header_unpack A sp' cap1 p1 pfx) (by sep_focus)
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨hpfx_le1, hcap1_63, _⟩ => ?_
    have hbhi_ult :
        (cap1 - BitVec.ofNat 64 pfx.length).ult (BitVec.ofNat 64 dec.length) = true :=
      cmp_hi_ult_true hpfx_le1 hcap1_63 hdec_le3 hgrow
    refine sepWPp_of_sepWP_inv hfz hsym
      (mid := entry + bv% (2 ^ 64 +
        (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]") -
        (ls_off% "libsignal_cli::stores::address_text"))) ?_
    wp_steps
    refine SepWP.done
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) ?_
    intro hfz1 hsym1
    obtain ⟨_, hfit2, hres2_bound⟩ :=
      reserveCap2_bounds (cap1 := cap1.toNat) (len := x.g.name.bytes.length) (decLen := dec.length)
        hcap1_34 hlen32 hdec_le3
    have hres2_bound' : reserveCap cap1.toNat pfx.length dec.length + 1 ≤ 9223372036854775808 := by
      subst hpfx_def; rw [List.length_append]; exact hres2_bound
    have hres2_le : reserveCap cap1.toNat pfx.length dec.length ≤ 9223372036854775807 := by
      omega
    refine sepWPp_weaken_pre (P' :=
        vecU8At A sp' cap1 p1 pfx ∗
          ((sp' + 24#64) ↦₆₄ dCap) ∗
          ((sp' + 32#64) ↦₆₄ dPtr) ∗
          ((sp' + 40#64) ↦₆₄ BitVec.ofNat 64 dec.length) ∗
          (dPtr ↦ₛ dec) ∗ vecU8BufRest A dCap dPtr dec ∗
          stackAt sp' subStk ∗ A.pool ∗ Fr)
      (by
        rw [vecU8At_eq_header_buf]
        unfold vecHeader
        simp (config := { failIfUnchanged := false }) only [arm64_norm, *]
        apply entails_of_eq
        ac_rfl) ?_
    rw [stackAt_sub_le sp' hres_le hsub64]
    refine call_inImage_addr
      (x := DoReserveCall.mk sp' cap1 p1 pfx dec.length)
      hdoRes hfz1 hsym1
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, *])
      (ret_pc := entry + res1RetOff)
      (by simp only [arm64_norm, *])
      (T := vecU8At A sp' cap1 p1 pfx ∗ A.pool ∗ stackAt sp' resStack)
      (by
        apply same_eq
        dsimp [SpqrV1.Varint.doReserveSpecOf]
        simp (config := { failIfUnchanged := false }) only [arm64_norm, pure_true, emp_sepConj, *]
        unfold Same
        ac_rfl)
      (fun _ => onPanic_trace_eq (by simp only [arm64_norm, *]))
      ?_
    intro s2 hpc2 hrun2 hsp2 hcs2 hfz2 hsym2
    dsimp only [SpqrV1.Varint.doReserveSpecOf]
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun htr2 => ?_
    have htr2' : s2.trace = s0.trace := by rw [htr2]; simp only [arm64_norm, *]
    have hsp2' : s2.sp = sp' := by rw [hsp2]; simp only [arm64_norm, *]
    have hx19_2 : s2.readReg64 .x19 = x.ret := by rw [hcs2.1]; simp only [arm64_norm, *]
    have hx20_2 : s2.readReg64 .x20 = dPtr := by rw [hcs2.2.1]; simp only [arm64_norm, *]
    have hx21_2 : s2.readReg64 .x21 = BitVec.ofNat 64 dec.length := by
      rw [hcs2.2.2.1]; simp only [arm64_norm, *]
    have hvregs_2 : preservedTailRegs s2 = preservedTailRegs s0 :=
      preservedTailRegs_step hcs2
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [calleeSavedVRegs, arm64_norm, *])
    obtain ⟨hx25_2, hx26_2, hx27_2, hx28_2, hvregs0_2⟩ := preservedTailRegs_elim hvregs_2
    simp only [sepExists_sepConj_left]
    refine sepWPp_exists_elim fun p2 => ?_
    set cap2 : BitVec 64 := BitVec.ofNat 64 (reserveCap cap1.toNat pfx.length dec.length)
    have hcap2_toNat : cap2.toNat = reserveCap cap1.toNat pfx.length dec.length := by
      dsimp [cap2]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hle2 : pfx.length + dec.length ≤ cap2.toNat := by
      subst hpfx_def; rw [hcap2_toNat, List.length_append]; exact hfit2
    apply sepWPp_fold (vecU8At_open_slice A sp' cap2 p2 pfx dec.length hle2 hdec_pos) (by sep_focus)
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨hcap2_63, hp2_ne⟩ => ?_
    refine sepWPp_of_sepWP_inv hfz2 hsym2
      (mid := entry + BitVec.ofNat 64 (ls_rel% "libsignal_cli::stores::address_text" "memcpy")) ?_
    wp_steps
    refine SepWP.done
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) ?_
    intro hfz3 hsym3
    refine sepWPp_weaken_pre (P' :=
        memRegion (p2 + BitVec.ofNat 64 pfx.length) dec.length ∗
          (dPtr ↦ₛ dec) ∗
          (sp' ↦₆₄ cap2) ∗
          ((sp' + 8#64) ↦₆₄ p2) ∗
          ((sp' + 16#64) ↦₆₄ BitVec.ofNat 64 pfx.length) ∗
          A.live p2 cap2.toNat 1 ∗ (p2 ↦ₛ pfx) ∗
          memRegion (p2 + BitVec.ofNat 64 (pfx.length + dec.length))
            (cap2.toNat - (pfx.length + dec.length)) ∗
          ((sp' + 24#64) ↦₆₄ dCap) ∗
          ((sp' + 32#64) ↦₆₄ dPtr) ∗
          ((sp' + 40#64) ↦₆₄ BitVec.ofNat 64 dec.length) ∗
          vecU8BufRest A dCap dPtr dec ∗
          stackAt sp' subStk ∗ A.pool ∗ Fr)
      (by
        rw [stackAt_sub_le sp' hres_le hsub64]
        simp (config := { failIfUnchanged := false }) only [arm64_norm, *]
        apply entails_of_eq
        ac_rfl) ?_
    rw [stackAt_sub_le sp' hext_le hsub64]
    refine call_inImage_addr (x := (p2 + BitVec.ofNat 64 pfx.length, dPtr, dec))
      hmemcpy hfz3 hsym3
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, *])
      (ret_pc := entry + memcpy1RetOff)
      (by simp only [arm64_norm, *])
      (T := memRegion (p2 + BitVec.ofNat 64 pfx.length) dec.length ∗
        (dPtr ↦ₛ dec) ∗ stackAt sp' extHookStack)
      (by
        apply same_eq
        dsimp [session2MemcpySpecX]
        simp (config := { failIfUnchanged := false }) only [arm64_norm, pure_true, emp_sepConj, *]
        unfold Same
        ac_rfl)
      (fun _ => false_entails _) ?_
    intro s4 hpc4 hrun4 hsp4 hcs4 hfz4 hsym4
    dsimp only [session2MemcpySpecX]
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨_, htr4⟩ => ?_
    have htr4' : s4.trace = s0.trace := by rw [htr4]; simp only [arm64_norm, *]
    have hsp4' : s4.sp = sp' := by rw [hsp4]; simp only [arm64_norm, *]
    have hx19_4 : s4.readReg64 .x19 = x.ret := by rw [hcs4.1]; simp only [arm64_norm, *]
    have hx20_4 : s4.readReg64 .x20 = dPtr := by rw [hcs4.2.1]; simp only [arm64_norm, *]
    have hx21_4 : s4.readReg64 .x21 = BitVec.ofNat 64 dec.length := by
      rw [hcs4.2.2.1]; simp only [arm64_norm, *]
    have hx22_4 : s4.readReg64 .x22 = BitVec.ofNat 64 pfx.length := by
      rw [hcs4.2.2.2.1]; simp only [arm64_norm, *]
    have hvregs_4 : preservedTailRegs s4 = preservedTailRegs s0 :=
      preservedTailRegs_step hcs4
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [calleeSavedVRegs, arm64_norm, *])
    refine sepWPp_weaken_pre ?_
      (hnext s4 cap2 p2 dCap dPtr hpc4 hrun4 hsp4' htr4'
        hx19_4 hx20_4 hx21_4 hx22_4 hvregs_4 hfz4 hsym4 hd_le hd_63 hd_ptr)
    rw [stackAt_sub_le sp' hext_le hsub64, ← hcap2_toNat]
    apply step_entails (vecU8Buf_close_slice A cap2 p2 pfx dec hle2 (by omega) hcap2_63 hp2_ne)
      (by (conv_lhs => simp (config := { failIfUnchanged := false }) only [arm64_norm]); sep_focus)
    simp (config := { failIfUnchanged := false }) only [arm64_norm, *]
    apply entails_of_eq
    ac_rfl
  · have hle1 : pfx.length + dec.length ≤ cap1.toNat := by omega
    apply sepWPp_fold (vecU8At_open_slice A sp' cap1 p1 pfx dec.length hle1 hdec_pos) (by sep_focus)
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨hcap1_63, hp1_ne⟩ => ?_
    have hbhi_ult :
        (cap1 - BitVec.ofNat 64 pfx.length).ult (BitVec.ofNat 64 dec.length) = false :=
      cmp_hi_ult_false hcap1_63 hdec_le3 hle1
    refine sepWPp_of_sepWP_inv hfz hsym
      (mid := entry + BitVec.ofNat 64 (ls_rel% "libsignal_cli::stores::address_text" "memcpy")) ?_
    wp_steps
    refine SepWP.done
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) ?_
    intro hfz1 hsym1
    rw [stackAt_sub_le sp' hext_le hsub64]
    refine call_inImage_addr (x := (p1 + BitVec.ofNat 64 pfx.length, dPtr, dec))
      hmemcpy hfz1 hsym1
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, *])
      (ret_pc := entry + memcpy1RetOff)
      (by simp only [arm64_norm, *])
      (T := memRegion (p1 + BitVec.ofNat 64 pfx.length) dec.length ∗
        (dPtr ↦ₛ dec) ∗ stackAt sp' extHookStack)
      (by
        apply same_eq
        dsimp [session2MemcpySpecX]
        simp (config := { failIfUnchanged := false }) only [arm64_norm, pure_true, emp_sepConj, *]
        unfold Same
        ac_rfl)
      (fun _ => false_entails _) ?_
    intro s2 hpc2 hrun2 hsp2 hcs2 hfz2 hsym2
    dsimp only [session2MemcpySpecX]
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨_, htr2⟩ => ?_
    have htr2' : s2.trace = s0.trace := by rw [htr2]; simp only [arm64_norm, *]
    have hsp2' : s2.sp = sp' := by rw [hsp2]; simp only [arm64_norm, *]
    have hx19_2 : s2.readReg64 .x19 = x.ret := by rw [hcs2.1]; simp only [arm64_norm, *]
    have hx20_2 : s2.readReg64 .x20 = dPtr := by rw [hcs2.2.1]; simp only [arm64_norm, *]
    have hx21_2 : s2.readReg64 .x21 = BitVec.ofNat 64 dec.length := by
      rw [hcs2.2.2.1]; simp only [arm64_norm, *]
    have hx22_2 : s2.readReg64 .x22 = BitVec.ofNat 64 pfx.length := by
      rw [hcs2.2.2.2.1]; simp only [arm64_norm, *]
    have hvregs_2 : preservedTailRegs s2 = preservedTailRegs s0 :=
      preservedTailRegs_step hcs2
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [calleeSavedVRegs, arm64_norm, *])
    refine sepWPp_weaken_pre ?_
      (hnext s2 cap1 p1 dCap dPtr hpc2 hrun2 hsp2' htr2'
        hx19_2 hx20_2 hx21_2 hx22_2 hvregs_2 hfz2 hsym2 hd_le hd_63 hd_ptr)
    rw [stackAt_sub_le sp' hext_le hsub64]
    apply step_entails (vecU8Buf_close_slice A cap1 p1 pfx dec hle1 (by omega) hcap1_63 hp1_ne)
      (by (conv_lhs => simp (config := { failIfUnchanged := false }) only [arm64_norm]); sep_focus)
    simp (config := { failIfUnchanged := false }) only [arm64_norm, *]
    apply entails_of_eq
    ac_rfl

/-! ## 6. Segment 4 (`224 .. 280` + tailcall `b __rust_dealloc`) -/

theorem step_epilogue {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {subStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hstk : 112 + subStk ≤ stk) (hext_stk : extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    {x : AddrTextGhost} {R : SepProp} {s0 s : State}
    {sp' capF ptrF dCap dPtr : BitVec 64}
    (hfz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr addressTextName + memcpy1RetOff)
    (hrun : s.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp : s.sp = sp')
    (hsp_def : s0.sp - 112#64 = sp')
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = dPtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 (decimalText (x.g.device.zeroExtend 32).toNat).length)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 (x.g.name.bytes ++ [0x2e#8]).length)
    (hvregs : preservedTailRegs s = preservedTailRegs s0)
    (hd_le : (decimalText (x.g.device.zeroExtend 32).toNat).length ≤ dCap.toNat)
    (hd_63 : dCap.toNat < 2 ^ 63) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s
      ((sp' ↦₆₄ capF) ∗ ((sp' + 8#64) ↦₆₄ ptrF) ∗
        ((sp' + 16#64) ↦₆₄ BitVec.ofNat 64 (x.g.name.bytes ++ [0x2e#8]).length) ∗
        vecU8Buf A capF ptrF ((x.g.name.bytes ++ [0x2e#8]) ++
          decimalText (x.g.device.zeroExtend 32).toNat) ∗
        ((sp' + 24#64) ↦₆₄ dCap) ∗ ((sp' + 32#64) ↦₆₄ dPtr) ∗
        ((sp' + 40#64) ↦₆₄
          BitVec.ofNat 64 (decimalText (x.g.device.zeroExtend 32).toNat).length) ∗
        (dPtr ↦ₛ decimalText (x.g.device.zeroExtend 32).toNat) ∗
        vecU8BufRest A dCap dPtr (decimalText (x.g.device.zeroExtend 32).toNat) ∗
        addrCalleeSavedAt sp' s0 ∗
        protocolAddressAt A x.g x.addr ∗
        memRegion x.ret 24 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 112)) ∗
        stackAt sp' subStk ∗ A.pool)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (addrTextSpec A img stk).post x s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (addrTextSpec A img stk).onPanic x s0 sf ∗ R)) := by
  obtain ⟨hx25, hx26, hx27, hx28, hvregs0⟩ := preservedTailRegs_elim hvregs
  generalize hdec_def : decimalText (x.g.device.zeroExtend 32).toNat = dec at hx21 hd_le ⊢
  generalize hpfx_def : x.g.name.bytes ++ [0x2e#8] = pfx at hx22 ⊢
  have hdealloc := at_dealloc_ok hC
  code_fetches_range CryptoVerification.libsignalSessionCode addrTextBin
    img.base (Rust.withPanics ext) addressText_fnOff
    (ls_off% "libsignal_cli::stores::address_text") 224 60
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr addressTextName = entry
  examples_hide_fetches
  have hdec_pos : 0 < dec.length := by
    subst hdec_def; rw [device_zeroExtend32_toNat]; exact decimalText_device_pos x.g.device
  have hdCap_nz : dCap ≠ 0#64 := dCap_ne_zero hdec_pos hd_le
  have hdCap_beq : (dCap == 0#64) = false := dCap_beq_zero_false hdec_pos hd_le
  have hdCap_pos : 0 < dCap.toNat := by omega
  have hlay_d : LayoutOk dCap.toNat 1 := layoutOk_align1 hdCap_pos (by omega)
  have hlen_sum : BitVec.ofNat 64 pfx.length + BitVec.ofNat 64 dec.length =
      BitVec.ofNat 64 (pfx ++ dec).length := by
    rw [← BitVec.ofNat_add, List.length_append]
  have hsp_pop : sp' + 112#64 = s0.sp := by
    rw [← hsp_def]; exact BitVec.sub_add_cancel s0.sp 112#64
  rw [memRegion24_cells x.ret]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine sepWPp_exists_elim fun r2 => ?_
  refine sepWPp_exists_elim fun r1 => ?_
  refine sepWPp_exists_elim fun r0 => ?_
  unfold addrCalleeSavedAt
  have htail : ∀ (s1 : State),
      s1.pc = entry + BitVec.ofNat 64 (ls_rel% "libsignal_cli::stores::address_text"
        "__rustc::__rust_dealloc") →
      s1.status = .Running →
      s1.sp = s0.sp →
      s1.trace = s0.trace →
      s1.readReg64 .lr = s0.readReg64 .lr →
      s1.readReg64 .x0 = dPtr →
      s1.readReg64 .x1 = dCap →
      s1.readReg64 .x2 = 1#64 →
      CalleeSavedPreserved s0 s1 →
      img.FrozenLoaded s1 →
      s1.symtab = img.symtab →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s1
        ((A.pool ∗ A.live dPtr dCap.toNat 1 ∗ memRegion dPtr dCap.toNat ∗
          stackAt s0.sp extHookStack) ∗
        (vecU8 A x.ret (addressText x.g.val) ∗
          protocolAddressAt A x.g x.addr ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack)))
        (fun sf P_f =>
          ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (addrTextSpec A img stk).post x s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (addrTextSpec A img stk).onPanic x s0 sf ∗ R)) := by
    intro s1 hpc1 hrun1 hsp1 htr1 hlr1 hx0_1 hx1_1 hx2_1 hcs1 hfz1 hsym1
    refine SepWPp.tailcall
      (x := (dPtr, dCap.toNat, 1))
      (F := vecU8 A x.ret (addressText x.g.val) ∗
        protocolAddressAt A x.g x.addr ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack))
      hdealloc hpc1 hrun1
      (by rw [State.spAligned, hsp1]; exact hsp0)
      hlr1 ?_ ?_ ?_ ?_ ?_
    · intro R' hm
      dsimp only [Spec.inImage, rustDeallocExternSpecWithStack]
      rw [hsp1, sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hfz1, hsym1⟩, ⟨hx0_1, by rw [hx1_1], by rw [hx2_1]; rfl, hlay_d⟩, ?_⟩
      simpa only [sepConj_assoc] using hm
    · intro sf code R' _ hm
      dsimp only [Spec.inImage, rustDeallocExternSpecWithStack] at hm
      exact not_satisfies_false_sepConj hm
    · intro sf _ hmR
      dsimp only [Spec.inImage, rustDeallocExternSpecWithStack] at hmR
      rw [sepConj_assoc, satisfies_pure_sepConj] at hmR
      exact False.elim hmR.1
    · intro sf _ _ hspf hcsf
      have hsp_sf : sf.sp = s0.sp := hspf.trans hsp1
      refine ⟨?_, hsp_sf, calleeSaved_trans hcs1 hcsf⟩
      intro hm_post
      dsimp only [Spec.inImage, rustDeallocExternSpecWithStack, addrTextSpec] at hm_post ⊢
      rw [hsp1, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm_post
      rcases hm_post with ⟨htr_sf, hm_post⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨htr_sf.trans htr1, ?_⟩
      refine Satisfies.mono ?_ hm_post
      rw [stackAt_sub_le s0.sp hext_stk hstk64]
      apply entails_of_eq
      ac_rfl
    · intro sf R' _ hm
      dsimp only [Spec.inImage, rustDeallocExternSpecWithStack] at hm
      exact (not_satisfies_false_sepConj hm).elim
  refine sepWPp_of_sepWP_inv hfz hsym
    (mid := entry + BitVec.ofNat 64 (ls_rel% "libsignal_cli::stores::address_text"
      "__rustc::__rust_dealloc")) ?_
  wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) ?_
  intro hfz1 hsym1
  refine sepWPp_weaken_pre (P' :=
      (A.pool ∗ A.live dPtr dCap.toNat 1 ∗ memRegion dPtr dCap.toNat ∗
        stackAt s0.sp extHookStack) ∗
      (vecU8 A x.ret (addressText x.g.val) ∗
        protocolAddressAt A x.g x.addr ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack))) ?_
    (htail _
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      ⟨by simp only [arm64_norm, *],
       by simp only [arm64_norm, *],
       by simp only [arm64_norm, *],
       by simp only [arm64_norm, *],
       by simp only [arm64_norm, *],
       by simp only [arm64_norm, *],
       by simp only [arm64_norm, *],
       by simp only [arm64_norm, *],
       by simp only [arm64_norm, *],
       by simp only [arm64_norm, *],
       by simp only [arm64_norm, *],
       by simp only [calleeSavedVRegs, arm64_norm, *]⟩
      hfz1 hsym1)
  have hret_vec :
      (x.ret ↦₆₄ capF) ∗ ((x.ret + 8#64) ↦₆₄ ptrF) ∗
        ((x.ret + 16#64) ↦₆₄ BitVec.ofNat 64 (pfx ++ dec).length) ∗
        vecU8Buf A capF ptrF (pfx ++ dec) ⊢
      vecU8 A x.ret (addressText x.g.val) := by
    subst hpfx_def hdec_def
    rw [← addressText_val_eq x.g]
    exact vecU8_from_moved_header A x.ret capF ptrF (addressText x.g.val)
  have hsp0_cell := cells24_entails_memRegion sp' capF ptrF
    (BitVec.ofNat 64 (pfx ++ dec).length)
  have hsp24_cell := cells24_entails_memRegion (sp' + 24#64) dCap dPtr
    (BitVec.ofNat 64 dec.length)
  have hsp48_cell := addrCalleeSavedAt_entails_memRegion64 sp' s0
  unfold addrCalleeSavedAt at hsp48_cell
  have hdec_dealloc := dec_buf_to_dealloc A dCap dPtr dec hd_le hd_63 hdCap_nz
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsp24_cell
  have hstk_back :
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 112)) ∗
        stackAt sp' subStk ∗
        memRegion sp' 24 ∗
        memRegion (sp' + 24#64) 24 ∗
        memRegion (sp' + 48#64) 64 =
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗
        stackAt s0.sp extHookStack := by
    rw [← hsp_def, ← stackAt_frame112_split s0.sp hstk hstk64,
        stackAt_sub_le s0.sp hext_stk hstk64]
  apply step_entails hdec_dealloc (by sep_focus)
  apply step_entails hret_vec (by sep_focus)
  apply step_entails hsp0_cell (by sep_focus)
  apply step_entails hsp24_cell (by sep_focus)
  apply step_entails hsp48_cell (by sep_focus)
  apply step_entails (entails_of_eq hstk_back) (by sep_focus)
  simp (config := { failIfUnchanged := false }) only [arm64_norm, *]
  apply entails_of_eq
  ac_rfl

/-! ## 7. Top-level assembly: `addrText_ok_impl` -/

theorem addrText_ok_impl {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack decStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hRes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDoReserveName)
      ((SpqrV1.Varint.doReserveSpecOf resStack A).inImage img))
    (hDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decimalName)
      (decimalSpec A img decStk))
    (hstk : 0x70 + max (max resStack extHookStack) decStk ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr addressTextName)
      (addrTextSpec A img stk) := by
  apply subroutine_ok_of_sepWPp_init
  intro x R s0 hpc hrun hpre hsp0
  dsimp only [addrTextSpec, Spec.inImage] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfz0, hsym0⟩, ⟨hx0, hx1, hlen32⟩, hmem0⟩
  have hstk64 : stk ≤ 2 ^ 64 := by
    refine stk_le_two_pow_64 (m := s0.mem) (ret := x.ret) (sp := s0.sp) (stk := stk)
      (R := protocolAddressAt A x.g x.addr ∗ A.pool ∗ R) ?_
    simpa only [sepConj_assoc, sepConj_comm, sepConj_left_comm] using hmem0
  set subStk := max (max resStack extHookStack) decStk
  have hres_le : resStack ≤ subStk := le_trans (le_max_left _ _) (le_max_left _ _)
  have hext_le : extHookStack ≤ subStk := le_trans (le_max_right _ _) (le_max_left _ _)
  have hdec_le : decStk ≤ subStk := le_max_right _ _
  have hsub64 : subStk ≤ 2 ^ 64 := by omega
  have hext_stk : extHookStack ≤ stk := by omega
  have hsp_al0 : ((s0.sp - 112#64) &&& 15#64 == 0#64) = true := spAligned_sub112 hsp0
  refine ⟨protocolAddressAt A x.g x.addr ∗ memRegion x.ret 24 ∗ stackAt s0.sp stk ∗ A.pool,
    hmem0, ?_⟩
  rw [stackAt_frame112_split s0.sp hstk hstk64]
  generalize hsp_def : s0.sp - 112#64 = sp' at hsp_al0 ⊢
  apply sepWPp_fold (memRegion64_cells sp') (by sep_focus)
  simp only [sepExists_sepConj_left]
  refine sepWPp_exists_elim fun w19 => ?_
  refine sepWPp_exists_elim fun w20 => ?_
  refine sepWPp_exists_elim fun w21 => ?_
  refine sepWPp_exists_elim fun w22 => ?_
  refine sepWPp_exists_elim fun w23 => ?_
  refine sepWPp_exists_elim fun w24 => ?_
  refine sepWPp_exists_elim fun w30 => ?_
  refine sepWPp_exists_elim fun w29 => ?_
  rw [memRegion24_cells sp']
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine sepWPp_exists_elim fun w2 => ?_
  refine sepWPp_exists_elim fun w1 => ?_
  refine sepWPp_exists_elim fun w0 => ?_
  apply sepWPp_fold (protocolAddressAt_open A x.g x.addr) (by sep_focus)
  rw [sepConj_assoc]
  refine SepWPp.pure_left fun ⟨_, _, _⟩ => ?_
  refine sepWPp_weaken_pre (P' :=
      (((sp' ↦₆₄ w0) ∗ ((sp' + 8#64) ↦₆₄ w1) ∗ ((sp' + 16#64) ↦₆₄ w2)) ∗
      (((sp' + 48#64) ↦₆₄ w29) ∗ ((sp' + 56#64) ↦₆₄ w30) ∗
        ((sp' + 64#64) ↦₆₄ w24) ∗ ((sp' + 72#64) ↦₆₄ w23) ∗
        ((sp' + 80#64) ↦₆₄ w22) ∗ ((sp' + 88#64) ↦₆₄ w21) ∗
        ((sp' + 96#64) ↦₆₄ w20) ∗ ((sp' + 104#64) ↦₆₄ w19)) ∗
      ((x.addr + 8#64) ↦₆₄ x.g.name.ptr) ∗
      ((x.addr + 16#64) ↦₆₄ BitVec.ofNat 64 x.g.name.bytes.length) ∗
      (x.g.name.ptr ↦ₛ x.g.name.bytes) ∗
      ((x.addr + 24#64) ↦₈ x.g.device) ∗
      stackAt sp' subStk ∗ A.pool ∗
      ((x.addr ↦₆₄ x.g.name.cap) ∗
        (vecU8BufRest A x.g.name.cap x.g.name.ptr x.g.name.bytes ∗ memRegion (x.addr + 25#64) 7) ∗
        memRegion x.ret 24 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 112)) ∗
        memRegion (sp' + 24#64) 24)))
    (by apply entails_of_eq; ac_rfl) ?_
  code_fetches CryptoVerification.libsignalSessionCode addrTextBin
    img.base (Rust.withPanics ext) addressText_fnOff
    (ls_off% "libsignal_cli::stores::address_text") 4
  generalize_entry hentry0 : (tripleRatchetProgAtExt img.base ext).fnAddr addressTextName = entry0
  examples_hide_fetches
  refine sepWPp_of_sepWP_inv hfz0 hsym0 (mid := entry0 + frameOff) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_
  intro hfz0' hsym0'
  rw [← hentry0] at *
  refine step_prologue_to_owned hC hext_le hsub64 hfz0' hsym0'
    (by simp only [arm64_norm])
    (by simp only [arm64_norm, hrun])
    (by simp only [arm64_norm])
    hsp_al0
    (by simp only [arm64_norm])
    (by simp only [arm64_norm, hx0])
    (by simp only [arm64_norm, hx1])
    (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    (preservedTailRegs_mk
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [calleeSavedVRegs, arm64_norm]))
    hlen32 ?_
  intro s1 p0 hpc1 hrun1 hsp1 htr1 hlr1 hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx19_1 hx20_1 hvregs_1 hfz1 hsym1
  refine sepWPp_weaken_pre (P' :=
      vecU8At A sp' (BitVec.ofNat 64 x.g.name.bytes.length) p0 x.g.name.bytes ∗
      memRegion (sp' + 24#64) 24 ∗
      ((x.addr + 24#64) ↦₈ x.g.device) ∗
      stackAt sp' subStk ∗ A.pool ∗
      (addrCalleeSavedAt sp' s0 ∗
        (x.addr ↦₆₄ x.g.name.cap) ∗
        ((x.addr + 8#64) ↦₆₄ x.g.name.ptr) ∗
        ((x.addr + 16#64) ↦₆₄ BitVec.ofNat 64 x.g.name.bytes.length) ∗
        (x.g.name.ptr ↦ₛ x.g.name.bytes) ∗
        (vecU8BufRest A x.g.name.cap x.g.name.ptr x.g.name.bytes ∗ memRegion (x.addr + 25#64) 7) ∗
        memRegion x.ret 24 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 112))))
    (by apply entails_of_eq; ac_rfl) ?_
  refine step_dot_and_decimal hRes hDec hres_le hdec_le hsub64
    hfz1 hsym1 hpc1 hrun1 hsp1 hsp_al0 htr1 hlr1
    hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx19_1 hx20_1 hvregs_1 hlen32 ?_
  intro s2 cap1 p1 hpc2 hrun2 hsp2 htr2 hx19_2 hvregs_2 hfz2 hsym2 hcap1_34
  refine sepWPp_weaken_pre (P' :=
      vecU8At A sp' cap1 p1 (x.g.name.bytes ++ [0x2e#8]) ∗
      vecU8 A (sp' + 24#64) (decimalText (x.g.device.zeroExtend 32).toNat) ∗
      stackAt sp' subStk ∗ A.pool ∗
      (addrCalleeSavedAt sp' s0 ∗
        protocolAddressAt A x.g x.addr ∗
        memRegion x.ret 24 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 112)))) ?_ ?_
  · apply step_entails (protocolAddressAt_close A x.g x.addr) (by sep_focus)
    apply entails_of_eq
    ac_rfl
  refine step_append_dec hC hRes hres_le hext_le hsub64
    hfz2 hsym2 hpc2 hrun2 hsp2 hsp_al0 htr2 hx19_2 hvregs_2 hlen32 hcap1_34 ?_
  intro s3 capF ptrF dCap dPtr hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3
    hvregs_3 hfz3 hsym3 hd_le hd_63 _
  refine sepWPp_weaken_pre (P' :=
      (sp' ↦₆₄ capF) ∗ ((sp' + 8#64) ↦₆₄ ptrF) ∗
      ((sp' + 16#64) ↦₆₄ BitVec.ofNat 64 (x.g.name.bytes ++ [0x2e#8]).length) ∗
      vecU8Buf A capF ptrF ((x.g.name.bytes ++ [0x2e#8]) ++
        decimalText (x.g.device.zeroExtend 32).toNat) ∗
      ((sp' + 24#64) ↦₆₄ dCap) ∗ ((sp' + 32#64) ↦₆₄ dPtr) ∗
      ((sp' + 40#64) ↦₆₄
        BitVec.ofNat 64 (decimalText (x.g.device.zeroExtend 32).toNat).length) ∗
      (dPtr ↦ₛ decimalText (x.g.device.zeroExtend 32).toNat) ∗
      vecU8BufRest A dCap dPtr (decimalText (x.g.device.zeroExtend 32).toNat) ∗
      addrCalleeSavedAt sp' s0 ∗
      protocolAddressAt A x.g x.addr ∗
      memRegion x.ret 24 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 112)) ∗
      stackAt sp' subStk ∗ A.pool)
    (by apply entails_of_eq; ac_rfl) ?_
  exact step_epilogue hC hstk hext_stk hstk64
    hfz3 hsym3 hpc3 hrun3 hsp0 hsp3 hsp_def htr3 hx19_3 hx20_3 hx21_3 hx22_3 hvregs_3 hd_le hd_63

end CryptoVerification.SignalSession.Cli.AddressText.Helpers
