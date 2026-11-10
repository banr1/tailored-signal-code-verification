/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags123
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.AllocContracts4KExt
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.Alloc.FinishGrow
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.Mac.Addresses
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarint
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.TripleRatchet.Statements

/-!
# `<SignalMessage>::new` Segment 1 (`+0x054 .. +0x218`)

Proves `AllocContracts4K` and `AllocContractsX` segment lemmas for address/ratchet-key
serialization, ciphertext copy, serialized buffer allocation, and protobuf tag 1 encoding in
`<SignalMessage>::new`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalTripleRatchet.ExtSignalMsgNewSeg1

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.Cli.LibsignalSpqrV1.M4
open CryptoVerification.InImageLift
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `4K` Callee Discharges -/

private theorem shim_opt_of_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv none (shimSpecWithStack allocHookStack)) := by
  apply subroutine_ok_to_optNone
  refine Arm64.subroutine_ok_mono
    (subroutine_ok_withStack_of_subroutine_ok (hA.shim_ok_at name k hk) allocHookStack)
    (fun _ _ _ hpre => ?_) (fun _ _ _ _ hpost => hpost)
  dsimp only [withStack, sessionShimSpec, shimSpecWithStack] at hpre ⊢
  simpa only [emp_sepConj, sepConj_assoc] using hpre

theorem finish_grow_ok_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName)
      (finishGrowSpec A) :=
  subroutine_ok_of_optNone <|
    finish_grow_ok_of_hooks_opt (by decide)
      (shim_opt_of_4k hA finishGrowName
        (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))
      (subroutine_ok_to_optNone (hA.alloc_ok_at finishGrowName
        (num% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]"))))
      (subroutine_ok_to_optNone
        (rustReallocExternWithStack_of_rustRealloc
          (hA.realloc_ok_at finishGrowName
            (num% (ls_off% "__rustc::__rust_realloc" -
              ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))
          (by decide) (by decide)))

theorem do_reserve_ok_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr doReserveName)
      (doReserveSpec A) :=
  subroutine_ok_of_optNone <|
    do_reserve_ok_of_fg_opt (hookStack := allocHookStack) (by decide)
      (subroutine_ok_to_optNone (finish_grow_ok_4k hA))

theorem encodeVarint_ok_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    EncodeVarintOkExt b A ext :=
  Prost.encodeVarint_ok_ext b A ext (do_reserve_ok_4k hA)

theorem new_shim_ok_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName +
        bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
      sessionShimSpec :=
  hA.shim_ok_at signalMessageNewName
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))

theorem new_alloc_ok_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName +
        bv% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
      (rustAllocSpec A) :=
  hA.alloc_ok_at signalMessageNewName
    (num% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))

theorem new_memcpy_ok_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName +
        bv% (ls_off% "memcpy" -
          ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
      (withStack sessionMemcpyRegionSpec allocHookStack) :=
  hA.session_memcpy_region_ok_at signalMessageNewName
    (num% (ls_off% "memcpy" -
      ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))

theorem stackAt_encodeVarint_to_allocHook (sp : BitVec 64) :
    stackAt sp encodeVarintStack =
      stackAt sp allocHookStack ∗ memRegion (sp - 4256#64) 160 := by
  simp only [stackAt, encodeVarintStack, doReserveStack, finishGrowStack, allocHookStack]
  rw [show (4096 + 48 + 48 + 64 : Nat) = 160 + 4096 by decide,
    ProofLib.memRegion_split _ 160 4096 (by decide)]
  have e1 : sp - BitVec.ofNat 64 (160 + 4096) = sp - 4256#64 := by bv_arith
  have e2 : sp - 4256#64 + BitVec.ofNat 64 160 = sp - BitVec.ofNat 64 4096 := by bv_arith
  rw [e1, e2, sepConj_comm]

theorem sessionMemcpyRegion4K_pre_eq (dst src : BitVec 64) (bs : List (BitVec 8))
    (s : State) (sp_cur : BitVec 64)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hlen : bs.length < 2 ^ 64)
    (hsp : s.sp = sp_cur) :
    (withStack sessionMemcpyRegionSpec allocHookStack).pre (dst, src, bs) s =
      ((src ↦ₛ bs) ∗ memRegion dst bs.length ∗ stackAt sp_cur allocHookStack) := by
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen]
  simp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, hx0, hx1, hx2, hsp,
    htoNat, and_self, pure_true, emp_sepConj, sepConj_assoc]
  ac_rfl

/-! ## `ciphertext` Copy (`+0x07c / +0x0f0 → +0x0a8 / +0x0fc`) -/

theorem new_ct_copy_wpp_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (x : SignalMessageNewGhost) (sp0 rkPtr w400 : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (s : State)
    (hpc : s.pc =
      (if BitVec.ofNat 64 x.ciphertext.length = 0#64 then
        (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 240#64
       else
        (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 124#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = x.ciphertextA)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 252#64
       else
        (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 168#64)
      s
      (((sp0 - 400#64) ↦₆₄ w400) ∗
       (x.ciphertextA ↦ₛ x.ciphertext) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = x.senderRatchetKeyA ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = x.ciphertextA ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗
          (x.ciphertextA ↦ₛ x.ciphertext) ∗
          signalMessageNew_vecU8Buf A (BitVec.ofNat 64 x.ciphertext.length) (sm.readReg64 .x26) x.ciphertext ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  simp only [arm64_norm] at hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx28 hx29
  by_cases hct0 : BitVec.ofNat 64 x.ciphertext.length = 0#64
  · simp only [hct0, ↓reduceIte] at hpc
    new_fetches_range b (Rust.withPanics ext) 0xf0 0xf8
    generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.done ?_ (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · by_cases hpq : BitVec.ofNat 64 x.pqRatchet.length = 0#64 <;>
        simp only [beq_iff_eq, ↓reduceIte, wp_norm, arm64_norm, *]
    · simp only [State.spAligned, wp_norm, arm64_norm, *]
    · unfold signalMessageNew_vecU8Buf
      simp only [hct0, ↓reduceIte, sepConj_emp, arm64_norm]
      refine Entails.pure_right (by omega) ?_
      exact NewPrologueCallees.entails_of_sep_focus (by sep_focus)
  · simp only [hct0, ↓reduceIte] at hpc
    have hct_pos : 0 < x.ciphertext.length := by
      by_contra hle; simp [Nat.le_zero.mp (Nat.not_lt.mp hle)] at hct0
    have hct_toNat : (BitVec.ofNat 64 x.ciphertext.length).toNat = x.ciphertext.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hct_msb : (BitVec.ofNat 64 x.ciphertext.length).getLsbD 63 = false := by
      rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat, hct_toNat]
      exact Nat.testBit_lt_two_pow (by omega)
    have hshim := new_shim_ok_4k hA
    have halloc := new_alloc_ok_4k hA
    have hmemcpy := new_memcpy_ok_4k hA
    have ho864 := @oom_at_864_ext b ext
    new_fetches_range b (Rust.withPanics ext) 0x7c 0xa4
    generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPp.call (x := ()) (F := ((sp0 - 400#64) ↦₆₄ w400) ∗
        (x.ciphertextA ↦ₛ x.ciphertext) ∗ A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      hshim (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      simp only [sessionShimSpec, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact NewPrologueCallees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf1 hpc1 hrun1 hsp1 hcs1
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
    simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
    simp only [sessionShimSpec]
    refine SepWPp.pure_elim fun htr1 => ?_
    simp only [wp_norm, arm64_norm] at htr1
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPp.call (x := (x.ciphertext.length, 1))
      (F := ((sp0 - 400#64) ↦₆₄ w400) ∗ (x.ciphertextA ↦ₛ x.ciphertext) ∗
            memRegion (sp0 - 416#64 - 4624#64) 528)
      halloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      rw [stackAt_computeMac_to_allocHook (sp0 - 416#64)] at hm
      simp only [rustAllocSpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
      refine ⟨⟨hct_pos, ⟨0, rfl⟩, by omega⟩, ?_⟩
      exact NewPrologueCallees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf2 hpc2 hrun2 hsp2 hcs2
    rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
    simp only [wp_norm, arm64_norm, *] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
    by_cases hoom : sf2.readReg64 .x0 = 0#64
    · have hoom0 : (sf2.readReg64 .x0 = 0) = True := eq_true hoom
      simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_oom]
      refine SepWPp.pure_elim fun htr2 => ?_
      simp only [wp_norm, arm64_norm, htr1] at htr2 hoom
      apply SepWPp.of_sepWP (mid := entry + bv% (2148))
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      exact ho864 (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
    · have hoom0 : (sf2.readReg64 .x0 = 0) = False := eq_false hoom
      simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_ok]
      refine SepWPp.pure_elim fun ⟨halign_ptr, htr2⟩ => ?_
      have hoom_beq : (sf2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
      simp only [wp_norm, arm64_norm, htr1] at htr2 hoom hoom_beq
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine SepWPp.call (x := ⟨sf2.readReg64 .x0, x.ciphertextA, x.ciphertext⟩)
        (F := ((sp0 - 400#64) ↦₆₄ w400) ∗
              A.live (sf2.readReg64 .x0) x.ciphertext.length 1 ∗
              A.pool ∗
              memRegion (sp0 - 416#64 - 4624#64) 528)
        hmemcpy (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align])
        (by simp only [arm64_norm]; rfl) ?_
        (fun _ _ _ _ he => not_satisfies_false_sepConj he)
        (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
      · intro R' hm
        simp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, sepConj_assoc,
          wp_norm, arm64_norm, *] at hm ⊢
        exact NewPrologueCallees.satisfies_of_sep_focus hm (by sep_focus)
      intro sf3 hpc3 hrun3 hsp3 hcs3
      rcases hcs3 with ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3⟩
      simp only [wp_norm, arm64_norm, *] at hsp3 h19_3 h20_3 h21_3 h22_3 h23_3 h24_3 h25_3 h26_3 h27_3 h28_3 hfp_3
      simp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hx0_3, htr3⟩ => ?_
      simp only [wp_norm, arm64_norm, htr2] at hx0_3 htr3
      apply SepWPp.of_sepWP_ret
      wp_steps
      refine SepWP.done ?_ (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
      · by_cases hpq : BitVec.ofNat 64 x.pqRatchet.length = 0#64 <;>
          simp only [beq_iff_eq, ↓reduceIte, wp_norm, arm64_norm, *]
      · simp only [State.spAligned, wp_norm, arm64_norm, *]
      · unfold signalMessageNew_vecU8Buf
        have h26_eq : sf3.readReg64 (Reg.gpr 26#5) = sf2.readReg64 (Reg.gpr 0#5) := by
          simp only [wp_norm, arm64_norm, *]
        rw [stackAt_computeMac_to_allocHook (sp0 - 416#64)]
        simp only [hct0, ↓reduceIte, h26_eq, hsp2, arm64_norm]
        refine Entails.pure_right ⟨by omega, hoom⟩ ?_
        exact NewPrologueCallees.entails_of_sep_focus (by sep_focus)

/-! ## Encode Tag 1 (`+0x1b8 → +0x218`) -/

theorem new_encode_tag1_wpp_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (hVarint : EncodeVarintOkExt b A ext)
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 440#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 =
      BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 536#64)
      s
      (((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
       wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
       vecU8At A (sp0 - 176#64)
         (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
         serPtr x.serPrefix0 ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 =
           BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9) ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = 36#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = pqCopyPtr ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          vecU8At A (sp0 - 176#64)
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr (x.serPrefix1 uuidTryParse) ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) := by
  have hvar := encodeVarint_ok_at_new_ext hVarint
  have hmemcpy := new_memcpy_ok_4k hA; clear hA hVarint
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  have ⟨henc_lo, henc_hi⟩ := encode_protoMsg_length_bounds x hct_le hpq_lt
  have ⟨htot_toNat, htot_lt, h0_len, hcmp1, hvar1_lt, hvar1_fit, hbs1a_len, hcmp_rk, hrk_len, hrk_ne, hp1_eq, _, _, _, _, _, _, _, _, _, _⟩ :=
    tag123_pure_facts x (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length rfl henc_lo henc_hi
  rw [serVec_expose_one A sp0 (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
        serPtr 1#64 (serPtr + 2#64) x.serPrefix0 (by omega) htot_lt hserPtr (by simp [h0_len]) (by bv_kernel)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; refine SepWPp.exists_elim fun b1 => ?_
  new_fetches_range b (Rust.withPanics ext) 0x1b8 0x214
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
  examples_hide_fetches; apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))); wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  refine SepWPp.call (x := ⟨33#64, sp0 - 176#64, BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9), serPtr, x.serPrefix0 ++ [0x0a#8]⟩)
    (F := ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr) (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          memRegion (sp0 - 416#64 - 4624#64) 368)
    hvar (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align]) (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => by simpa only [encodeVarintSpec, allocFailedIn, State.trace_setMem, State.trace_setPC, State.trace_setPState, State.trace_writeReg64, arm64_norm] using allowPanic_frame id hm) ?_
  · intro R' hm; rw [stackAt_computeMac_to_encodeVarint (sp0 - 416#64)] at hm
    rw [NewEncodeTags123Callees.encodeVarintSpec_pre_eq A _ _ (sp0 - 416#64) (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) hvar1_lt (by simp only [wp_norm, arm64_norm, hsp]),
        ← serVec_pack_one A sp0 (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
          serPtr 1#64 2#64 (serPtr + 2#64) x.serPrefix0 0x0a#8 (by omega) htot_lt hserPtr (by simp [h0_len]) rfl (by bv_kernel)]
    simp only [State.mem_setMem, sepConj_assoc] at hm ⊢; exact NewEncodeTags123Callees.satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 hpc1 hrun1 hsp1 ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, hsp, hx19, hx20, hx21, hx22, hx24, hx25, hx26, hx27, hx28, hx29]
    at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  rw [NewEncodeTags123Callees.encodeVarintSpec_post_eq A _ _ sf1 (sp0 - 416#64) (by simp only [wp_norm, arm64_norm, hsp])]; simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_; simp only [wp_norm, arm64_norm] at htr1; simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' => SepWPp.pure_elim fun ⟨_, hno_grow⟩ => ?_
  rcases hno_grow hvar1_fit with ⟨hcap', hptr'⟩; subst cap' ptr'
  rw [serVec_expose_slice A sp0 (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
        serPtr 3#64 33#64 (serPtr + 36#64) ((x.serPrefix0 ++ [0x0a#8]) ++ encodeVarint 33#64) 33
        (by omega) htot_lt hserPtr (by decide) rfl rfl (by bv_kernel),
      wireSignalMessageAt_expose_rk A x rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr (sp0 - 288#64)]
  simp only [sepConj_assoc]; apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")); wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
  refine SepWPp.call (x := (serPtr + 3#64, rkPtr, x.senderRatchetKey.serialize))
    (F := ((sp0 - 176#64) ↦₆₄ BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)) ∗
          ((sp0 - 168#64) ↦₆₄ serPtr) ∗ ((sp0 - 160#64) ↦₆₄ 3#64) ∗
          A.live serPtr (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)).toNat 1 ∗
          (serPtr ↦ₛ ((x.serPrefix0 ++ [0x0a#8]) ++ encodeVarint 33#64)) ∗
          memRegion (serPtr + 36#64) ((BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)).toNat -
            ((x.serPrefix0 ++ [0x0a#8]) ++ encodeVarint 33#64).length - 33) ∗
          A.pool ∗ memRegion (sp0 - 416#64 - 4256#64) 160 ∗ ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          (((sp0 - 288#64) ↦₆₄ 33#64) ∗ (((sp0 - 288#64) + 8#64) ↦₆₄ rkPtr) ∗ (((sp0 - 288#64) + 16#64) ↦₆₄ 33#64) ∗
           ⌜rkPtr ≠ 0#64 ∧ x.senderRatchetKey.serialize.length < 2 ^ 63⌝ ∗ A.live rkPtr x.senderRatchetKey.serialize.length 1 ∗
           optVecU8At A ⟨BitVec.ofNat 64 x.ciphertext.length, ctCopyPtr⟩ ((sp0 - 288#64) + 0x18#64) (some x.ciphertext) ∗
           optVecU8At A ⟨pqCap, pqCopyPtr⟩ ((sp0 - 288#64) + 0x30#64) (if x.pqRatchet.isEmpty then none else some x.pqRatchet) ∗
           optVecU8At A ⟨addrCap, addrPtr⟩ ((sp0 - 288#64) + 0x48#64) (x.addresses uuidTryParse) ∗
           optU32At ((sp0 - 288#64) + 0x60#64) (some x.counter) ∗ optU32At ((sp0 - 288#64) + 0x68#64) (some x.previousCounter)) ∗
          memRegion (sp0 - 416#64 - 4624#64) 368)
    hmemcpy (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align]) (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm
    rw [stackAt_encodeVarint_to_allocHook (sp0 - 416#64)] at hm
    rw [sessionMemcpyRegion4K_pre_eq _ _ _ _ (sp0 - 416#64)
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrk_len])
      (by omega)
      (by simp only [wp_norm, arm64_norm, hsp1])]
    simp only [State.mem_setPC, State.mem_setPState, State.mem_writeReg64, hrk_len, sepConj_assoc] at hm ⊢
    exact NewEncodeTags123Callees.satisfies_of_sep_focus hm (by sep_focus)
  intro sf2 hpc2 hrun2 hsp2 ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
  simp only [wp_norm, arm64_norm, hsp1, h19_1, h21_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1]
    at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
  simp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx0_2, htr2⟩ => ?_
  simp only [wp_norm, arm64_norm, htr1] at htr2; apply SepWPp.of_sepWP_ret; wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun2]) ⟨?_, ?_⟩
  · simp only [wp_norm, arm64_norm, hsp2, hsp0_align, h19_2, h20_2, h21_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2, htr2, and_self]
  · rw [stackAt_computeMac_to_encodeVarint (sp0 - 416#64), stackAt_encodeVarint_to_allocHook (sp0 - 416#64), ← hp1_eq,
        ← serVec_pack_slice A sp0 (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr 3#64 33#64 36#64 (serPtr + 36#64) ((x.serPrefix0 ++ [0x0a#8]) ++ encodeVarint 33#64) x.senderRatchetKey.serialize
            (by omega) htot_lt hserPtr hrk_ne rfl (by rw [hrk_len]) rfl (by bv_kernel), hrk_len]
    simp only [sepConj_assoc]; exact NewEncodeTags123Callees.entails_of_sep_focus (by sep_focus)

/-! ## `encoded_len` and `serialized` Allocation (`+0x13c → +0x1b8`) -/

theorem new_alloc_ser_wpp_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (hEncLen : EncodedLenOkExt b A ext)
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr w176 w168 w160 : BitVec 64)
    (w384 w380 verW32 : BitVec 32)
    (hver : verW32.setWidth 8 = x.messageVersion)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 316#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp0 - 288#64)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 440#64)
      s
      (((sp0 - 384#64) ↦₃₂ w384) ∗
       ((sp0 - 380#64) ↦₃₂ w380) ∗
       ((sp0 - 332#64) ↦₃₂ verW32) ∗
       wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
       ((sp0 - 176#64) ↦₆₄ w176) ∗
       ((sp0 - 168#64) ↦₆₄ w168) ∗
       ((sp0 - 160#64) ↦₆₄ w160) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9) ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 ≠ 0#64 ∧
         sm.readReg64 .x23 = 1#64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = pqCopyPtr ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 384#64) ↦₃₂ x.counter) ∗
          ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          ((sp0 - 332#64) ↦₃₂ verW32) ∗
          wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          vecU8At A (sp0 - 176#64)
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            (sm.readReg64 .x22) x.serPrefix0 ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) := by
  have henc := encodedLen_ok_at_new_ext hEncLen
  have hshim := new_shim_ok_4k hA
  have halloc := new_alloc_ok_4k hA
  have ho15c := @oom_at_15c_ext b ext; clear hA hEncLen
  have hfit := wireLengthsFit_protoMsg x hct_bound hpq_bound
  have ⟨henc_lo, henc_hi⟩ := encode_protoMsg_length_bounds x hct_bound hpq_bound
  have ⟨h_adds1, h_cmp9, h_tbz, h_hi, h_add9_eq, h_add9_toNat⟩ := encLen_overflow_checks henc_lo henc_hi
  have h_pos9 : 0 < (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9 := by omega
  have h_le9 : (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9 ≤ 9223372036854775807 := by omega
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  new_fetches_range b (Rust.withPanics ext) 0x13c 0x1b4
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
  examples_hide_fetches; apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")); wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  refine SepWPp.call (x := ⟨sp0 - 288#64, x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr, x.protoMsg uuidTryParse⟩)
    (F := ((sp0 - 384#64) ↦₃₂ w384) ∗ ((sp0 - 380#64) ↦₃₂ w380) ∗ ((sp0 - 332#64) ↦₃₂ verW32) ∗
          ((sp0 - 176#64) ↦₆₄ w176) ∗ ((sp0 - 168#64) ↦₆₄ w168) ∗ ((sp0 - 160#64) ↦₆₄ w160) ∗
          A.pool ∗ memRegion (sp0 - 416#64 - 4624#64) 4608)
    henc (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align]) (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm; rw [stackAt_computeMac_to_encodedLen (sp0 - 416#64)] at hm
    rw [NewEncodeTags123Callees.encodedLenSpec_pre_eq A _ _ (sp0 - 416#64) (by simp only [wp_norm, arm64_norm, hx0]) hfit (by simp only [wp_norm, arm64_norm, hsp])]
    simp only [State.mem_setPC, State.mem_writeReg64, sepConj_assoc] at hm ⊢; exact NewEncodeTags123Callees.satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 hpc1 hrun1 hsp1 ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29]
    at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  simp only [encodedLenSpec, wp_norm, arm64_norm, hsp, sepConj_assoc]; refine SepWPp.pure_elim fun ⟨hx0_1, htr1⟩ => ?_
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")); wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
  refine SepWPp.call (x := ())
    (F := wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr) (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          stackAt (sp0 - 416#64) encodedLenStack ∗ ((sp0 - 384#64) ↦₃₂ x.counter) ∗ ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          ((sp0 - 332#64) ↦₃₂ verW32) ∗ ((sp0 - 176#64) ↦₆₄ w176) ∗ ((sp0 - 168#64) ↦₆₄ w168) ∗ ((sp0 - 160#64) ↦₆₄ w160) ∗
          A.pool ∗ memRegion (sp0 - 416#64 - 4624#64) 4608)
    hshim (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align]) (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm; simp only [sessionShimSpec, sepConj_assoc, emp_sepConj, State.mem_setMem] at hm ⊢
    exact NewEncodeTags123Callees.satisfies_of_sep_focus hm (by sep_focus)
  intro sf2 hpc2 hrun2 hsp2 ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
  simp only [wp_norm, arm64_norm, hsp1, h19_1, h21_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1]
    at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
  simp only [sessionShimSpec]; refine SepWPp.pure_elim fun htr2 => ?_; simp only [wp_norm, arm64_norm, htr1] at htr2
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")); wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun2])
  refine SepWPp.call (x := ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9, 1))
    (F := wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr) (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          ((sp0 - 384#64) ↦₃₂ x.counter) ∗ ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗ ((sp0 - 332#64) ↦₃₂ verW32) ∗
          ((sp0 - 176#64) ↦₆₄ w176) ∗ ((sp0 - 168#64) ↦₆₄ w168) ∗ ((sp0 - 160#64) ↦₆₄ w160) ∗
          memRegion (sp0 - 416#64 - 4624#64) 528)
    halloc (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun2])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align]) (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm; rw [NewEncodeTags123Callees.h4608_split sp0] at hm
    rw [NewEncodeTags123Callees.rustAllocSpec_pre_eq A _ _ (sp0 - 416#64) (by simp only [wp_norm, arm64_norm, h_add9_toNat])
          (by simp only [wp_norm, arm64_norm]) h_pos9 h_le9 (by simp only [wp_norm, arm64_norm, hsp2]),
        NewEncodeTags123Callees.stackAt_allocHook_eq sp0]
    simp only [State.mem_setPC, State.mem_writeReg64, sepConj_assoc] at hm ⊢; exact NewEncodeTags123Callees.satisfies_of_sep_focus hm (by sep_focus)
  intro sf3 hpc3 hrun3 hsp3 ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3⟩
  simp only [wp_norm, arm64_norm, hsp2, h19_2, h20_2, h21_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2]
    at hsp3 h19_3 h20_3 h21_3 h22_3 h23_3 h24_3 h25_3 h26_3 h27_3 h28_3 hfp_3
  by_cases hoom : sf3.readReg64 .x0 = 0#64
  · have hoom0 : (sf3.readReg64 .x0 = 0) = True := eq_true hoom
    simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_oom]; refine SepWPp.pure_elim fun htr3 => ?_
    simp only [wp_norm, arm64_norm, htr2] at htr3; apply SepWPp.of_sepWP (mid := entry + bv% (348)); wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun3])
    exact ho15c (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun3]) (by simp only [wp_norm, arm64_norm, htr3])
  · have hoom0 : (sf3.readReg64 .x0 = 0) = False := eq_false hoom
    simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_ok]; refine SepWPp.pure_elim fun ⟨halign_ptr, htr3⟩ => ?_
    simp only [wp_norm, arm64_norm, htr2] at htr3
    have hoom_beq : (sf3.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
    simp only [arm64_norm] at hoom hoom_beq
    rw [memRegion_split_one (sf3.readReg64 (Reg.gpr 0#5)) ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9) (by omega) (by omega)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; refine SepWPp.exists_elim fun b0 => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")); wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun3])
    refine SepWPp.call (x := ⟨sp0 - 288#64, x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr, x.protoMsg uuidTryParse⟩)
      (F := A.live (sf3.readReg64 (Reg.gpr 0#5)) ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9) 1 ∗
            ((sf3.readReg64 (Reg.gpr 0#5)) ↦₈ versionByte x.messageVersion) ∗
            memRegion (sf3.readReg64 (Reg.gpr 0#5) + 1#64) ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 8) ∗
            A.pool ∗ ((sp0 - 384#64) ↦₃₂ x.counter) ∗ ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗ ((sp0 - 332#64) ↦₃₂ verW32) ∗
            ((sp0 - 176#64) ↦₆₄ BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)) ∗
            ((sp0 - 168#64) ↦₆₄ sf3.readReg64 (Reg.gpr 0#5)) ∗ ((sp0 - 160#64) ↦₆₄ 1#64) ∗
            memRegion (sp0 - 416#64 - 4624#64) 4608)
      henc (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun3])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp3, hsp0_align]) (by simp only [wp_norm, arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      have hv : BitVec.zeroExtend 8 (4#64 ||| BitVec.zeroExtend 64 (verW32 <<< 4)) = versionByte x.messageVersion := by
        have _ := hx20; rw [← hver]; unfold versionByte currentVersion; bv_kernel
      rw [NewEncodeTags123Callees.encodedLenSpec_pre_eq A _ _ (sp0 - 416#64) (by simp only [wp_norm, arm64_norm]) hfit (by simp only [wp_norm, arm64_norm, hsp3])]
      simp only [wp_norm, arm64_norm, hsp2] at hm; rw [NewEncodeTags123Callees.stackAt_allocHook_eq sp0, hv] at hm; rw [NewEncodeTags123Callees.h4608_split sp0]
      simp only [sepConj_assoc] at hm ⊢; exact NewEncodeTags123Callees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf4 hpc4 hrun4 hsp4 ⟨h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, hfp_4⟩
    simp only [wp_norm, arm64_norm, hsp3, h19_3, h20_3, h21_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3]
      at hsp4 h19_4 h20_4 h21_4 h22_4 h23_4 h24_4 h25_4 h26_4 h27_4 h28_4 hfp_4
    simp only [encodedLenSpec, wp_norm, arm64_norm, hsp3, htr3, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0_4, htr4⟩ => ?_; apply SepWPp.of_sepWP_ret; wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun4]) ⟨?_, ?_⟩
    · simp only [wp_norm, arm64_norm, hsp4, hsp0_align, h19_4, h20_4, h21_4, h22_4, ne_eq, eq_false hoom,
        not_false_eq_true, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, hfp_4, htr4, and_self]
    · rw [stackAt_computeMac_to_encodedLen (sp0 - 416#64)]; unfold SignalMessageNewGhost.serPrefix0
      simp only [wp_norm, arm64_norm, h22_4]
      rw [← pack_serPrefix0 A sp0 (sf3.readReg64 (Reg.gpr 0#5)) x.messageVersion
            (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length henc_lo henc_hi hoom]
      simp only [sepConj_assoc]; exact NewEncodeTags123Callees.entails_of_sep_focus (by sep_focus)

/-! ## `serialize_addresses` and `PublicKey::serialize` (`+0x054 → +0x07c / +0x0f0`) -/

private theorem pkSerialize_ok_at_new_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName +
        bv% (ls_off% "<libsignal_core::curve::PublicKey>::serialize" -
          ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
      ((publicKeySerializeSpecX A).inImage img) :=
  sub_ok_at_of_fnAddr (Glue.publicKeySerializeOk_ext_x hA) signalMessageNewName
    (num% (ls_off% "<libsignal_core::curve::PublicKey>::serialize" -
      ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
    (by fnoff_eq)

private theorem serAddresses_ok_at_new_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName +
        bv% (2 ^ 64 + ls_off% "<libsignal_protocol::protocol::SignalMessage>::serialize_addresses" -
          ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
      ((serializeAddressesSpecX A uuidTryParse).inImage img) :=
  serializeAddresses_ok_at_new_ext_x
    (serializeAddresses_subroutine_ok_of_contracts_x img A ext hA
      (Statements.uuidTryParseWithStack_inImage_ok img ext))

theorem new_addr_and_rk_wpp_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (x : SignalMessageNewGhost) (sp0 : BitVec 64)
    (s : State)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName + 84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx3 : s.readReg64 .x3 = (if x.loc.isSome then x.locA else 0#64))
    (hloc_ne : x.loc.isSome → x.locA ≠ 0#64)
    (hx4 : s.readReg64 .x4 = x.remA)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = x.ciphertextA)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      (if BitVec.ofNat 64 x.ciphertext.length = 0#64 then
        (tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName + 240#64
       else
        (tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName + 124#64)
      s
      (optAddrAt A x.locA x.loc ∗
       protocolAddressAt A x.rem x.remA ∗
       (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
       memRegion (sp0 - 312#64) 24 ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStackX)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = x.senderRatchetKeyA ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = x.ciphertextA ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          optAddrAt A x.locA x.loc ∗
          protocolAddressAt A x.rem x.remA ∗
          (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
          optSerializeAddressesAt A (sp0 - 312#64) (x.addresses uuidTryParse) ∗
          boxU8Buf A (sm.readReg64 .x28) x.senderRatchetKey.serialize ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStackX))
      (PanicAllocPost s) := by
  have hpk := pkSerialize_ok_at_new_ext_x hA
  have hinv : OptCallInv (some img) s := ⟨hF, hsym⟩
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  simp only [arm64_norm] at hx3 hx4 hx19 hx20 hx22 hx23 hx24 hx25 hx27 hx29
  cases hloc : x.loc with
  | none =>
    simp only [hloc, Bool.false_eq_true, ↓reduceIte] at hx3
    simp only [hloc, optAddrAt, SignalMessageNewGhost.addresses, Option.bind_none, emp_sepConj,
      memRegion_24_split_8_16 (sp0 - 312#64), bv_sub_add_lit sp0 312 8,
      sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun w312 => ?_
    new_fetches_range img.base (Rust.withPanics ext) 0x54 0x54
    new_fetches_range img.base (Rust.withPanics ext) 0xd4 0xec
    generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP_optImage (mid := entry + bv% (ls_off% "<libsignal_core::curve::PublicKey>::serialize" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) hinv
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hinv0
    refine signalMessageNew_call_opt (oimg := some img)
      (x := ⟨x.senderRatchetKeyA, x.senderRatchetKey⟩)
      (F := protocolAddressAt A x.rem x.remA ∗
            ((sp0 - 312#64) ↦₆₄ noneCap) ∗
            memRegion (sp0 - 304#64) 16 ∗
            memRegion (sp0 - 416#64 - 16912#64) 496)
      hinv0 hpk (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ R' hm => by
        simpa only [publicKeySerializeSpecX, allocFailedIn, State.trace_setPC,
          State.trace_writeReg64, State.trace_setMem, arm64_norm] using allowPanic_frame id hm) ?_
    · intro R' hm
      rw [stackAt_computeMacX_to_publicKeySerializeX (sp0 - 416#64)] at hm
      simp only [publicKeySerializeSpecX, noneCap, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact NewPrologueCallees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf1 _ hpc1 hrun1 hsp1 hcs1
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
    simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
    simp only [publicKeySerializeSpecX, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx1_1, htr1⟩ => ?_
    simp only [wp_norm, arm64_norm] at hx1_1 htr1
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.done ?_ (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · by_cases hc : BitVec.ofNat 64 x.ciphertext.length = 0#64 <;>
        simp only [beq_iff_eq, ↓reduceIte, wp_norm, arm64_norm, *]
    · simp only [State.spAligned, wp_norm, arm64_norm, *]
    · rw [stackAt_computeMacX_to_publicKeySerializeX (sp0 - 416#64)]
      simp only [optSerializeAddressesAt, noneCap, hsp, bv_sub_add_lit sp0 312 8, arm64_norm]
      exact NewPrologueCallees.entails_of_sep_focus (by sep_focus)
  | some l =>
    have hloc_ne' : x.locA ≠ 0#64 := hloc_ne (by simp [hloc])
    have hloc_beq : (x.locA == 0#64) = false := beq_eq_false_iff_ne.mpr hloc_ne'
    simp only [hloc, ↓reduceIte] at hx3
    simp only [hloc, optAddrAt, SignalMessageNewGhost.addresses, Option.bind_some]
    have hser := serAddresses_ok_at_new_ext_x hA
    new_fetches_range img.base (Rust.withPanics ext) 0x54 0x78
    generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP_optImage (mid := entry + bv% (2 ^ 64 + ls_off% "<libsignal_protocol::protocol::SignalMessage>::serialize_addresses" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) hinv
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hinv0
    refine signalMessageNew_call_opt (oimg := some img)
      (x := ⟨sp0 - 312#64, x.locA, l, x.remA, x.rem⟩)
      (F := (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
            memRegion (sp0 - 416#64 - 16912#64) 128)
      hinv0 hser (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ R' hm => by
        simpa only [serializeAddressesSpecX, allocFailedIn, State.trace_setPC,
          State.trace_writeReg64, arm64_norm] using allowPanic_frame id hm) ?_
    · intro R' hm
      rw [stackAt_computeMacX_to_serializeAddressesX (sp0 - 416#64)] at hm
      simp only [serializeAddressesSpecX, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact NewPrologueCallees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf1 hinv1 hpc1 hrun1 hsp1 hcs1
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
    simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
    simp only [serializeAddressesSpecX, sepConj_assoc]
    refine SepWPp.pure_elim fun htr1 => ?_
    simp only [wp_norm, arm64_norm] at htr1
    apply SepWPp.of_sepWP_optImage (mid := entry + bv% (ls_off% "<libsignal_core::curve::PublicKey>::serialize" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) hinv1
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hinv1'
    refine signalMessageNew_call_opt (oimg := some img)
      (x := ⟨x.senderRatchetKeyA, x.senderRatchetKey⟩)
      (F := protocolAddressAt A l x.locA ∗
            protocolAddressAt A x.rem x.remA ∗
            optSerializeAddressesAt A (sp0 - 312#64) (serializeAddresses (serviceIdParse uuidTryParse) l x.rem) ∗
            memRegion (sp0 - 416#64 - 16784#64) 368 ∗
            memRegion (sp0 - 416#64 - 16912#64) 128)
      hinv1' hpk (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ R' hm => by
        simpa only [publicKeySerializeSpecX, htr1, allocFailedIn, State.trace_setPC,
          State.trace_writeReg64, arm64_norm] using allowPanic_frame id hm) ?_
    · intro R' hm
      rw [stackAt_serializeAddressesX_to_publicKeySerializeX] at hm
      simp only [publicKeySerializeSpecX, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact NewPrologueCallees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf2 _ hpc2 hrun2 hsp2 hcs2
    rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
    simp only [wp_norm, arm64_norm, *] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
    simp only [publicKeySerializeSpecX, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx1_2, htr2⟩ => ?_
    simp only [wp_norm, arm64_norm, htr1] at hx1_2 htr2
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.done ?_ (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · by_cases hc : BitVec.ofNat 64 x.ciphertext.length = 0#64 <;>
        simp only [beq_iff_eq, ↓reduceIte, wp_norm, arm64_norm, *]
    · simp only [State.spAligned, wp_norm, arm64_norm, *]
    · rw [stackAt_computeMacX_to_serializeAddressesX (sp0 - 416#64),
        stackAt_serializeAddressesX_to_publicKeySerializeX (sp0 - 416#64)]
      simp only [hsp1, arm64_norm]
      exact NewPrologueCallees.entails_of_sep_focus (by sep_focus)

end CryptoVerification.Cli.LibsignalTripleRatchet.ExtSignalMsgNewSeg1
