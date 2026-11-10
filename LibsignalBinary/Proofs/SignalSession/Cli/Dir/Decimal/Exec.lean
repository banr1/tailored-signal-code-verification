/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Specs
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommon
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.Digits
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Decimal.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Varint

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

gen_decodes CryptoVerification.libsignalSessionCode_tree decBin
  [(ls_off% "libsignal_cli::stores::decimal") → (ls_off% "libsignal_cli::stores::decimal" + 188)]

private theorem cliDoReserve_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr decimalName -
      bv% (ls_rel% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]" "libsignal_cli::stores::decimal") =
      (tripleRatchetProgAtExt b ext).fnAddr cliDoReserveName := by
  have h1 := decimal_fnOff
  have h2 := cliDoReserve_fnOff
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, decimalName, cliDoReserveName, h1, h2]
  bv_omega

def decimalBoundedRawSpec (A : RustAlloc) (k resStack : Nat) : Spec DecimalGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg32 .x1 = x.n ∧ x.n.toNat < 10 ^ k⌝ ∗
      memRegion x.ret 24 ∗ stackAt s.sp (k * 0x50 + resStack) ∗ A.pool
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ vecU8 A x.ret (decimalText x.n.toNat) ∗
      stackAt s0.sp (k * 0x50 + resStack) ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def decimalBoundedSpec (A : RustAlloc) (img : Obj.Image) (k resStack : Nat) : Spec DecimalGhost :=
  (decimalBoundedRawSpec A k resStack).inImage img

private def DecimalCalleeSaved (s0 s : State) : Prop :=
  s.readReg64 (Reg.gpr 22#5) = s0.readReg64 (Reg.gpr 22#5) ∧
  s.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) ∧
  s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) ∧
  s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) ∧
  s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
  s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
  s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0 ∧
  (∀ img : Obj.Image, ImgCallInv img s0 → ImgCallInv img s)

private theorem DecimalCalleeSaved.refl (s0 : State) : DecimalCalleeSaved s0 s0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ h => h⟩

private theorem DecimalCalleeSaved.trans {s0 s1 s2 : State}
    (h01 : DecimalCalleeSaved s0 s1) (h12 : DecimalCalleeSaved s1 s2) :
    DecimalCalleeSaved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.1,
   fun img h => h12.2.2.2.2.2.2.2.2 img (h01.2.2.2.2.2.2.2.2 img h)⟩

private theorem DecimalCalleeSaved.of_calleeSavedPreserved {s1 s2 : State}
    (hcs : CalleeSavedPreserved s1 s2)
    (hinv : ∀ img : Obj.Image, ImgCallInv img s1 → ImgCallInv img s2) :
    DecimalCalleeSaved s1 s2 :=
  ⟨hcs.2.2.2.1, hcs.2.2.2.2.1, hcs.2.2.2.2.2.1, hcs.2.2.2.2.2.2.1,
   hcs.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.2.1,
   hcs.2.2.2.2.2.2.2.2.2.2.2, hinv⟩

private theorem stackAt_decimal_frame {m : Nat} (hm : m + 0x50 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (m + 0x50) =
      stackAt (sp - 80#64) m ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
         ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
          ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗ ((sp - 64#64) ↦₆₄ v2) ∗
          ((sp - 56#64) ↦₆₄ v3) ∗ ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗
          ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗ ((sp - 16#64) ↦₆₄ v8) ∗
          ((sp - 8#64) ↦₆₄ v9)) := by
  have h1 := ProofLib.stackAt_split_cells sp m 10 (by omega)
  have hc10 : cells (sp - 80#64) 10 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗ ((sp - 64#64) ↦₆₄ v2) ∗
        ((sp - 56#64) ↦₆₄ v3) ∗ ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗
        ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗ ((sp - 16#64) ↦₆₄ v8) ∗
        ((sp - 8#64) ↦₆₄ v9)) := by
    cells_unfold
  rw [show m + 0x50 = m + 8 * 10 by omega, h1, hc10]

private theorem step_push_epilogue {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {k resStack : Nat}
    (hk : 1 ≤ k) (hstk64 : k * 0x50 + resStack ≤ 2 ^ 64)
    {x : DecimalGhost} {R : SepProp} {s0 s : State}
    (cap ptr v0 v7 o0 o1 o2 : BitVec 64) (bs : List (BitVec 8))
    (hlt : bs.length < cap.toNat)
    (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0)
    (hbs : bs ++ [BitVec.ofNat 8 (0x30 + x.n.toNat % 10)] = decimalText x.n.toNat)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decimalName + 76#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.zeroExtend 64 x.n)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 bs.length)
    (hcs : DecimalCalleeSaved s0 s) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s
      (vecU8At A (s0.sp - 72#64) cap ptr bs ∗
        ((s0.sp - 80#64) ↦₆₄ v0) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 24#64) ↦₆₄ v7) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
        (x.ret ↦₆₄ o0) ∗ ((x.ret + 8#64) ↦₆₄ o1) ∗ ((x.ret + 16#64) ↦₆₄ o2) ∗
        stackAt (s0.sp - 80#64) ((k - 1) * 0x50 + resStack) ∗ A.pool)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (decimalBoundedSpec A img k resStack).post x s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (decimalBoundedSpec A img k resStack).onPanic x s0 sf ∗ R)) := by
  code_fetches_range CryptoVerification.libsignalSessionCode decBin img.base (Rust.withPanics ext)
    decimal_fnOff (ls_off% "libsignal_cli::stores::decimal") 76 72
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr decimalName = fnBase
  examples_hide_fetches
  rcases hcs with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs, _⟩
  rw [stack_slot_open_one A s0.sp cap ptr bs hlt hcap hptr]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun b0 => ?_
  apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine ⟨?_, by simp only [arm64_norm, *], by simp only [CalleeSavedPreserved, arm64_norm, *]⟩
  intro hPR
  rw [digit_byte_eq x.n] at hPR
  have hsnoc := vecU8At_snoc_sret A x.ret cap ptr bs (BitVec.ofNat 8 (0x30 + x.n.toNat % 10))
    hlt hcap hptr
  have hframe := stackAt_decimal_frame (m := (k - 1) * 0x50 + resStack) (by omega) s0.sp
  have hstk_eq : (k - 1) * 0x50 + resStack + 0x50 = k * 0x50 + resStack := by omega
  rw [hstk_eq] at hframe
  dsimp only [decimalBoundedSpec, Spec.inImage, decimalBoundedRawSpec]
  rw [vecU8, hframe, ← hbs]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨v0, cap, ptr, BitVec.ofNat 64 bs.length,
    s0.readReg64 .fp, s0.readReg64 .lr, s0.readReg64 .x21, v7,
    s0.readReg64 .x20, s0.readReg64 .x19, cap, ptr, by simp only [arm64_norm, *], ?_⟩
  rw [← hsnoc]
  convert hPR using 1
  ac_rfl

private theorem step_reserve_and_finish {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {k resStack : Nat}
    (hRes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDoReserveName)
      ((SpqrV1.Varint.doReserveSpecOf resStack A).inImage img))
    (hk : 1 ≤ k) (hstk64 : k * 0x50 + resStack ≤ 2 ^ 64)
    {x : DecimalGhost} {R : SepProp} {s0 s : State}
    (himg0 : ImgCallInv img s0)
    (cap ptr v0 v7 o0 o1 o2 : BitVec 64) (bs : List (BitVec 8))
    (hcap_eq : cap.toNat = bs.length)
    (hlen9 : bs.length ≤ 9)
    (hbs : bs ++ [BitVec.ofNat 8 (0x30 + x.n.toNat % 10)] = decimalText x.n.toNat)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decimalName + 168#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs.length)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.zeroExtend 64 x.n)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 bs.length)
    (hcs : DecimalCalleeSaved s0 s) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s
      (vecU8At A (s0.sp - 72#64) cap ptr bs ∗
        ((s0.sp - 80#64) ↦₆₄ v0) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 24#64) ↦₆₄ v7) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
        (x.ret ↦₆₄ o0) ∗ ((x.ret + 8#64) ↦₆₄ o1) ∗ ((x.ret + 16#64) ↦₆₄ o2) ∗
        stackAt (s0.sp - 80#64) ((k - 1) * 0x50 + resStack) ∗ A.pool)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (decimalBoundedSpec A img k resStack).post x s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (decimalBoundedSpec A img k resStack).onPanic x s0 sf ∗ R)) := by
  code_fetches_range CryptoVerification.libsignalSessionCode decBin img.base (Rust.withPanics ext)
    decimal_fnOff (ls_off% "libsignal_cli::stores::decimal") 168 24
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr decimalName = fnBase
  examples_hide_fetches
  apply SepWPp.of_sepWP_cs (mid := (tripleRatchetProgAtExt img.base ext).fnAddr cliDoReserveName)
  wp_steps
  apply SepWP.done
    (by simp only [arm64_norm, ← cliDoReserve_fnAddr_eq, hentry]; bv_omega)
    (by simp only [arm64_norm, *])
  intro hinv_pre
  set sc := _
  have hcs_call : DecimalCalleeSaved s0 sc :=
    hcs.trans ⟨by simp only [sc, arm64_norm], by simp only [sc, arm64_norm],
      by simp only [sc, arm64_norm], by simp only [sc, arm64_norm],
      by simp only [sc, arm64_norm], by simp only [sc, arm64_norm],
      by simp only [sc, arm64_norm], by simp only [sc, arm64_norm], hinv_pre⟩
  have hsp_sc : sc.sp = s0.sp - 80#64 := by simp only [sc, arm64_norm, *]
  have htr_sc : sc.trace = s0.trace := by simp only [sc, arm64_norm, *]
  have hsp_aligned : sc.spAligned = true := by
    simp only [State.spAligned, hsp_sc, beq_iff_eq]
    exact SpqrV1.Varint.sp_sub_80_aligned halign
  have hsplit_bot : stackAt (s0.sp - 80#64) ((k - 1) * 0x50 + resStack) =
      memRegion (s0.sp - 80#64 - BitVec.ofNat 64 ((k - 1) * 0x50 + resStack)) ((k - 1) * 0x50) ∗
        stackAt (s0.sp - 80#64) resStack := by
    have h1 := ProofLib.stackAt_split_bottom (s0.sp - 80#64) resStack ((k - 1) * 0x50) (by omega)
    simpa only [Nat.add_comm resStack ((k - 1) * 0x50)] using h1
  set F_res : SepProp :=
    ((s0.sp - 80#64) ↦₆₄ v0) ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((s0.sp - 24#64) ↦₆₄ v7) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
    (x.ret ↦₆₄ o0) ∗ ((x.ret + 8#64) ↦₆₄ o1) ∗ ((x.ret + 16#64) ↦₆₄ o2) ∗
    memRegion (s0.sp - 80#64 - BitVec.ofNat 64 ((k - 1) * 0x50 + resStack)) ((k - 1) * 0x50)
  refine SepWPp.call_cs
    (x := DoReserveCall.mk (s0.sp - 72#64) cap ptr bs 1)
    (ret_pc := fnBase + bv% (188))
    (F := F_res)
    hRes
    (by simp only [arm64_norm, ← cliDoReserve_fnAddr_eq, hentry]; bv_omega)
    (by simp only [arm64_norm, *])
    hsp_aligned
    (by simp only [arm64_norm, *])
    ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hsplit_bot] at hm
    simp only [Spec.inImage, SpqrV1.Varint.doReserveSpecOf, sepConj_assoc,
      satisfies_pure_sepConj]
    have hx1_sc : (sc.readReg64 .x1).toNat = bs.length := by
      have : sc.readReg64 .x1 = BitVec.ofNat 64 bs.length := by simp only [sc, arm64_norm, *]
      rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hx2_sc : (sc.readReg64 .x2).toNat = 1 := by
      have : sc.readReg64 .x2 = 1#64 := by simp only [sc, arm64_norm]
      rw [this]; rfl
    refine ⟨hcs_call.2.2.2.2.2.2.2.2 img himg0,
      ⟨by simp only [arm64_norm], hx1_sc, hx2_sc, by simp only [arm64_norm],
        by simp only [arm64_norm], by dsimp [reserveCap]; omega⟩, ?_⟩
    simp only [arm64_norm] at hm
    simp only [arm64_norm, hsp]
    dsimp only [F_res]
    convert hm using 1
    ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [Spec.inImage, SpqrV1.Varint.doReserveSpecOf, doReserveSpec,
      decimalBoundedSpec, decimalBoundedRawSpec, allocFailedIn] at hm ⊢
    rw [htr_sc] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp_sc] at hspm
    dsimp only [Spec.inImage, SpqrV1.Varint.doReserveSpecOf]
    rw [hsp_sc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun newPtr => ?_
    set newCap := BitVec.ofNat 64 (reserveCap cap.toNat bs.length 1)
    rw [stack_slot_eq_header_rest A s0.sp newCap newPtr bs]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hle_new, hcap_new, hptr_new⟩ => ?_
    have hlt_new : bs.length < newCap.toNat := by
      dsimp only [newCap, reserveCap]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have htrm' : sm.trace = s0.trace := htrm.trans htr_sc
    have hcs_sm : DecimalCalleeSaved s0 sm :=
      hcs_call.trans (DecimalCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)
    have hx19m : sm.readReg64 .x19 = x.ret := by
      rw [hcsm.1]; simp only [arm64_norm, *]
    have hx20m : sm.readReg64 .x20 = BitVec.zeroExtend 64 x.n := by
      rw [hcsm.2.1]; simp only [arm64_norm, *]
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 bs.length := by
      rw [hcsm.2.2.1]; simp only [arm64_norm, *]
    apply SepWPp.of_sepWP_cs (mid := fnBase + bv% (76))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_jmp
    refine SepWPp.weaken_pre ?_
      (step_push_epilogue (img := img) hk hstk64 newCap newPtr v0 v7 o0 o1 o2 bs
        hlt_new hcap_new hptr_new hbs
        (by rw [hentry]; simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs_sm.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [arm64_norm], hinv_jmp⟩))
    dsimp only [F_res]
    rw [← stack_slot_of_header_rest A s0.sp newCap newPtr bs hle_new hcap_new hptr_new, hsplit_bot]
    exact Entails.of_eq (by ac_rfl)

private theorem decimal_bounded_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack : Nat}
    (hRes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDoReserveName)
      ((SpqrV1.Varint.doReserveSpecOf resStack A).inImage img)) :
    ∀ k : Nat, 1 ≤ k →
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr decimalName)
        (decimalBoundedSpec A img k resStack) := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    apply subroutine_ok_of_sepWPp
    intro x R s0 hpc hrun hpre halign
    change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ (decimalBoundedRawSpec A (k + 1) resStack).pre x s0) ∗ R at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨himg0, hpre⟩
    refine ⟨(decimalBoundedRawSpec A (k + 1) resStack).pre x s0, R, hpre, ?_⟩
    have hstk64 : (k + 1) * 0x50 + resStack ≤ 2 ^ 64 := by
      have hm_sub : s0.mem ⊨ memRegion x.ret 24 ∗ stackAt s0.sp ((k + 1) * 0x50 + resStack) ∗
          (⌜s0.readReg64 .x0 = x.ret ∧ s0.readReg32 .x1 = x.n ∧ x.n.toNat < 10 ^ (k + 1)⌝ ∗
            A.pool ∗ R) := by
        dsimp only [decimalBoundedRawSpec] at hpre
        convert hpre using 1
        ac_rfl
      exact stk_le_pow64_of_pre hm_sub
    have halign64 : s0.sp &&& 15#64 = 0#64 := by
      simpa only [State.spAligned, beq_iff_eq] using halign
    dsimp only [decimalBoundedRawSpec]
    refine SepWPp.pure_elim fun ⟨hx0, hx1, hn_lt⟩ => ?_
    have hx1' : BitVec.truncate 32 (s0.readReg64 (Reg.gpr 1#5)) = x.n := hx1
    have hframe0 := stackAt_decimal_frame (m := k * 0x50 + resStack) (by omega) s0.sp
    have hstk_eq0 : k * 0x50 + resStack + 0x50 = (k + 1) * 0x50 + resStack := by omega
    rw [hstk_eq0] at hframe0
    rw [memRegion_24_cells x.ret, hframe0]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun v0 => ?_
    refine SepWPp.exists_elim fun v1 => ?_
    refine SepWPp.exists_elim fun v2 => ?_
    refine SepWPp.exists_elim fun v3 => ?_
    refine SepWPp.exists_elim fun v4 => ?_
    refine SepWPp.exists_elim fun v5 => ?_
    refine SepWPp.exists_elim fun v6 => ?_
    refine SepWPp.exists_elim fun v7 => ?_
    refine SepWPp.exists_elim fun v8 => ?_
    refine SepWPp.exists_elim fun v9 => ?_
    refine SepWPp.exists_elim fun o2 => ?_
    refine SepWPp.exists_elim fun o1 => ?_
    refine SepWPp.exists_elim fun o0 => ?_
    code_fetches CryptoVerification.libsignalSessionCode decBin img.base (Rust.withPanics ext)
      decimal_fnOff (ls_off% "libsignal_cli::stores::decimal") 168
    generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr decimalName = fnBase
    examples_hide_fetches
    by_cases hle9 : x.n.toNat ≤ 9
    · have hule := ule_nine_true hle9
      apply SepWPp.of_sepWP_cs (mid := fnBase + bv% (168))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_pro
      have hbs0 : ([] : List (BitVec 8)) ++ [BitVec.ofNat 8 (0x30 + x.n.toNat % 10)] =
          decimalText x.n.toNat := by
        rw [List.nil_append, Nat.mod_eq_of_lt (by omega), decimalText_digit x.n.toNat (by omega)]
      refine SepWPp.weaken_pre ?_
        (step_reserve_and_finish (k := k + 1) hRes (by omega) hstk64 himg0
          0#64 1#64 v0 v7 o0 o1 o2 [] rfl (by decide) hbs0
          (by rw [hentry]; simp only [arm64_norm]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) halign64 (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ((DecimalCalleeSaved.refl s0).trans ⟨by simp only [arm64_norm], by simp only [arm64_norm],
            by simp only [arm64_norm], by simp only [arm64_norm],
            by simp only [arm64_norm], by simp only [arm64_norm],
            by simp only [arm64_norm], by simp only [arm64_norm], hinv_pro⟩))
      rw [← stack_slot_empty_vecU8At A s0.sp]
      exact Entails.of_eq (by simp only [Nat.add_sub_cancel]; ac_rfl)
    · have hge10 : 10 ≤ x.n.toNat := by omega
      have hk1 : 1 ≤ k := by
        rcases k with _ | k'
        · exfalso; omega
        · omega
      have hdiv_lt : (x.n.toNat / 10) < 10 ^ k := by
        have hp : 10 ^ (k + 1) = 10 ^ k * 10 := rfl
        omega
      have hih := ih hk1
      have hule := ule_nine_false hge10
      apply SepWPp.of_sepWP_cs (mid := fnBase)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv_rec_pre
      set sr := _
      have hcs_sr : DecimalCalleeSaved s0 sr :=
        (DecimalCalleeSaved.refl s0).trans ⟨by simp only [sr, arm64_norm], by simp only [sr, arm64_norm],
          by simp only [sr, arm64_norm], by simp only [sr, arm64_norm],
          by simp only [sr, arm64_norm], by simp only [sr, arm64_norm],
          by simp only [sr, arm64_norm], by simp only [sr, arm64_norm], hinv_rec_pre⟩
      have hsp_sr : sr.sp = s0.sp - 80#64 := by simp only [sr, arm64_norm]
      have htr_sr : sr.trace = s0.trace := by simp only [sr, arm64_norm]
      have hsp_sr_aligned : sr.spAligned = true := by
        simp only [State.spAligned, hsp_sr, beq_iff_eq]
        exact SpqrV1.Varint.sp_sub_80_aligned halign64
      set F_rec : SepProp :=
        ((s0.sp - 80#64) ↦₆₄ v0) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 24#64) ↦₆₄ v7) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
        (x.ret ↦₆₄ o0) ∗ ((x.ret + 8#64) ↦₆₄ o1) ∗ ((x.ret + 16#64) ↦₆₄ o2)
      refine SepWPp.call_cs
        (x := DecimalGhost.mk (BitVec.ofNat 32 (x.n.toNat / 10)) (s0.sp - 72#64))
        (ret_pc := fnBase + bv% (60))
        (F := F_rec)
        hih
        (by simp only [arm64_norm])
        (by simp only [arm64_norm, *])
        hsp_sr_aligned
        (by simp only [arm64_norm])
        ?_ ?_ ?_ ?_
      · intro R' hm
        have hm' : sr.mem ⊨
            memRegion (s0.sp - 72#64) 24 ∗ stackAt (s0.sp - 80#64) (k * 0x50 + resStack) ∗
              A.pool ∗ F_rec ∗ R' := by
          have hv8 : s0.sp - 72#64 + 8#64 = s0.sp - 64#64 := by bv_omega
          have hv16 : s0.sp - 72#64 + 16#64 = s0.sp - 56#64 := by bv_omega
          rw [memRegion_24_cells (s0.sp - 72#64), hv8, hv16]
          simp only [sepExists_sepConj_left, satisfies_sepExists]
          refine ⟨v3, v2, v1, ?_⟩
          dsimp only [F_rec]
          convert hm using 1
          ac_rfl
        simp only [decimalBoundedSpec, Spec.inImage, decimalBoundedRawSpec,
          sepConj_assoc, satisfies_pure_sepConj]
        have hx1_sr : sr.readReg32 .x1 = BitVec.ofNat 32 (x.n.toNat / 10) := by
          change BitVec.truncate 32 (sr.readReg64 (Reg.gpr 1#5)) = _
          simp only [sr, arm64_norm]
          exact div10_trunc32 x.n
        have hn_sub_lt : (BitVec.ofNat 32 (x.n.toNat / 10)).toNat < 10 ^ k := by
          have hn32 : x.n.toNat < 2 ^ 32 := x.n.isLt
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          exact hdiv_lt
        exact ⟨hcs_sr.2.2.2.2.2.2.2.2 img himg0,
          ⟨by simp only [arm64_norm], hx1_sr, hn_sub_lt⟩, hm'⟩
      · intro sf code R' _ hm
        exact allowPanic_not_exited hm
      · intro sf _ hm
        dsimp only [decimalBoundedSpec, Spec.inImage, decimalBoundedRawSpec, allocFailedIn] at hm ⊢
        rw [htr_sr] at hm
        exact allowPanic_frame id hm
      · intro sm hpcm hrunm hspm hcsm hinv_call
        rw [hsp_sr] at hspm
        have hq_nat : (BitVec.ofNat 32 (x.n.toNat / 10)).toNat = x.n.toNat / 10 := by
          have hn32 : x.n.toNat < 2 ^ 32 := x.n.isLt
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        conv =>
          arg 4
          dsimp only [decimalBoundedSpec, Spec.inImage, decimalBoundedRawSpec]
          rw [hsp_sr, hq_nat, vecU8]
          simp only [sepConj_assoc]
        refine SepWPp.pure_elim fun htrm => ?_
        conv =>
          arg 4
          simp only [sepExists_sepConj_left]
        refine SepWPp.exists_elim fun subCap => ?_
        refine SepWPp.exists_elim fun subPtr => ?_
        set subBs := decimalText (x.n.toNat / 10)
        conv =>
          arg 4
          rw [stack_slot_eq_header_rest A s0.sp subCap subPtr subBs]
          simp only [sepConj_assoc]
        refine SepWPp.pure_elim fun ⟨hle_sub, hcap_sub, hptr_sub⟩ => ?_
        have htrm' : sm.trace = s0.trace := htrm.trans htr_sr
        have hcs_sm : DecimalCalleeSaved s0 sm :=
          hcs_sr.trans (DecimalCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)
        have hx19m : sm.readReg64 .x19 = x.ret := by
          rw [hcsm.1]; simp only [arm64_norm]
        have hx20m : sm.readReg64 .x20 = BitVec.zeroExtend 64 x.n := by
          rw [hcsm.2.1]; simp only [arm64_norm]
        have hbs_rec : subBs ++ [BitVec.ofNat 8 (0x30 + x.n.toNat % 10)] =
            decimalText x.n.toNat :=
          (decimalText_ge10 x.n.toNat hge10).symm
        have hlen_sub9 : subBs.length ≤ 9 := by
          have hn32 : x.n.toNat < 2 ^ 32 := x.n.isLt
          exact decimalText_length_le 9 (x.n.toNat / 10) (by omega) (by omega)
        by_cases hlt_sub : subBs.length < subCap.toNat
        · have hbeq_f := Helpers.cap_beq_len_false hlt_sub
          apply SepWPp.of_sepWP_cs (mid := fnBase + bv% (76))
          wp_steps
          apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          intro hinv_chk
          refine SepWPp.weaken_pre ?_
            (step_push_epilogue (A := A) (img := img) (k := k + 1) (R := R) (by omega) hstk64
              subCap subPtr v0 v7 o0 o1 o2 subBs
              hlt_sub hcap_sub hptr_sub hbs_rec
              (by rw [hentry]; simp only [arm64_norm]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) halign64 (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *])
              (hcs_sm.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm],
                by simp only [arm64_norm], by simp only [arm64_norm],
                by simp only [arm64_norm], by simp only [arm64_norm],
                by simp only [arm64_norm], by simp only [arm64_norm], hinv_chk⟩))
          dsimp only [F_rec]
          rw [← stack_slot_of_header_rest A s0.sp subCap subPtr subBs hle_sub hcap_sub hptr_sub]
          exact Entails.of_eq (by simp only [Nat.add_sub_cancel]; ac_rfl)
        · have hcap_eq_sub : subCap.toNat = subBs.length := by omega
          have hbeq_t := Helpers.cap_beq_len_true hcap_eq_sub
          apply SepWPp.of_sepWP_cs (mid := fnBase + bv% (168))
          wp_steps
          apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          intro hinv_chk
          refine SepWPp.weaken_pre ?_
            (step_reserve_and_finish (k := k + 1) (R := R) hRes (by omega) hstk64 himg0
              subCap subPtr v0 v7 o0 o1 o2 subBs
              hcap_eq_sub hlen_sub9 hbs_rec
              (by rw [hentry]; simp only [arm64_norm]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) halign64 (by simp only [arm64_norm, *])
              (by simp only [arm64_norm]; exact beq_iff_eq.mp hbeq_t) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (hcs_sm.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm],
                by simp only [arm64_norm], by simp only [arm64_norm],
                by simp only [arm64_norm], by simp only [arm64_norm],
                by simp only [arm64_norm], by simp only [arm64_norm], hinv_chk⟩))
          dsimp only [F_rec]
          rw [← stack_slot_of_header_rest A s0.sp subCap subPtr subBs hle_sub hcap_sub hptr_sub]
          exact Entails.of_eq (by simp only [Nat.add_sub_cancel]; ac_rfl)

theorem decimal_ok_main {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack stk : Nat}
    (hRes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDoReserveName)
      ((SpqrV1.Varint.doReserveSpecOf resStack A).inImage img))
    (hstk : 10 * 0x50 + resStack ≤ stk)
    (_hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decimalName)
      (decimalSpec A img stk) := by
  have h10 := decimal_bounded_ok (img := img) (A := A) (ext := ext) hRes 10 (by omega)
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre halign => ?_
  have hstk64 : stk ≤ 2 ^ 64 := by
    have hm_sub : s0.mem ⊨ memRegion x.ret 24 ∗ stackAt s0.sp stk ∗
        (⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
          ⌜s0.readReg64 .x0 = x.ret ∧ s0.readReg32 .x1 = x.n⌝ ∗ A.pool ∗ R) := by
      dsimp only [decimalSpec, Spec.inImage] at hpre
      convert hpre using 1
      ac_rfl
    exact stk_le_pow64_of_pre hm_sub
  have hsplit : stackAt s0.sp stk =
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (10 * 0x50 + resStack)) ∗
        stackAt s0.sp (10 * 0x50 + resStack) := by
    have h1 := ProofLib.stackAt_split_bottom s0.sp (10 * 0x50 + resStack)
      (stk - (10 * 0x50 + resStack)) (by omega)
    rwa [Nat.add_sub_of_le hstk] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (10 * 0x50 + resStack)) ∗ R
  have hn10 : x.n.toNat < 10 ^ 10 := by
    have := x.n.isLt
    omega
  have hpre' : s0.mem ⊨ (decimalBoundedSpec A img 10 resStack).pre x s0 ∗ R' := by
    dsimp only [decimalSpec, decimalBoundedSpec, Spec.inImage, decimalBoundedRawSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    refine ⟨hpre.1, ⟨hpre.2.1.1, hpre.2.1.2, hn10⟩, ?_⟩
    convert hpre.2.2 using 1
    ac_rfl
  refine h10.mono_outcome x R' s0 hpc hrun hpre' halign fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [decimalSpec, decimalBoundedSpec, Spec.inImage, decimalBoundedRawSpec, R'] at hpost ⊢
    rw [hsplit]
    convert hpost using 1
    ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [decimalSpec, decimalBoundedSpec, Spec.inImage, decimalBoundedRawSpec, R'] at hpost ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hex).elim
  · exact (allowPanic_not_exited hoom).elim

end CryptoVerification.SignalSession.Cli.Decimal.Helpers
