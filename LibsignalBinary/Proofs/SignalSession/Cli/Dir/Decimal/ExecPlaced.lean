/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.Digits
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymD
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `[LibsignalPlacement]` `signal_session::stores::decimal` (Block `597`)
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Decimal.Helpers

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.CodeLayout CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Varint
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

def decimalBoundedRawSpecP (A : RustAlloc) (k resStack : Nat) : Spec DecimalGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg32 .x1 = x.n ∧ x.n.toNat < 10 ^ k⌝ ∗
      memRegion x.ret 24 ∗ stackAt s.sp (k * 0x50 + resStack) ∗ A.pool
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ vecU8 A x.ret (decimalText x.n.toNat) ∗
      stackAt s0.sp (k * 0x50 + resStack) ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def decimalBoundedSpecPlaced [LibsignalPlacement] (A : RustAlloc) (k resStack : Nat) : Spec DecimalGhost :=
  StoreKit.withLsCodeRoLoaded lsmpl (decimalBoundedRawSpecP A k resStack)

private def DecimalCalleeSavedP (s0 s : State) : Prop :=
  s.readReg64 (Reg.gpr 22#5) = s0.readReg64 (Reg.gpr 22#5) ∧
  s.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) ∧
  s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) ∧
  s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) ∧
  s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
  s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
  s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

private theorem DecimalCalleeSavedP.refl (s0 : State) : DecimalCalleeSavedP s0 s0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem DecimalCalleeSavedP.trans {s0 s1 s2 : State}
    (h01 : DecimalCalleeSavedP s0 s1) (h12 : DecimalCalleeSavedP s1 s2) :
    DecimalCalleeSavedP s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.trans h01.2.2.2.2.2.2.2⟩

private theorem sepWPp_let_state {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp}
    {post onPanic : State → SepProp → Prop}
    (h : let sc := s; SepWPp prog target_pc sc P post onPanic) :
    SepWPp prog target_pc s P post onPanic := h

private theorem DecimalCalleeSavedP.of_calleeSavedPreserved {s1 s2 : State}
    (hcs : CalleeSavedPreserved s1 s2) :
    DecimalCalleeSavedP s1 s2 :=
  ⟨hcs.2.2.2.1, hcs.2.2.2.2.1, hcs.2.2.2.2.2.1, hcs.2.2.2.2.2.2.1,
   hcs.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.2.1,
   hcs.2.2.2.2.2.2.2.2.2.2.2⟩

private theorem stackAt_decimal_frame_p {m : Nat} (hm : m + 0x50 ≤ 2 ^ 64) (sp : BitVec 64) :
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

private theorem step_push_epilogue_p [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {k resStack : Nat}
    (hk : 1 ≤ k) (hstk64 : k * 0x50 + resStack ≤ 2 ^ 64)
    {x : DecimalGhost} {R : SepProp} {s0 s : State}
    (cap ptr v0 v7 o0 o1 o2 : BitVec 64) (bs : List (BitVec 8))
    (hlt : bs.length < cap.toNat)
    (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0)
    (hbs : bs ++ [BitVec.ofNat 8 (0x30 + x.n.toNat % 10)] = decimalText x.n.toNat)
    (hpc : s.pc = (blkPl_597).base + 76#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64)
    (_halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.zeroExtend 64 x.n)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 bs.length)
    (hcs : DecimalCalleeSavedP s0 s) :
    SepWPp (lsProg_597 H) (s0.readReg64 .lr) s
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
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (decimalBoundedSpecPlaced A k resStack).post x s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (decimalBoundedSpecPlaced A k resStack).onPanic x s0 sf ∗ R)) := by
  rcases hcs with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs⟩
  rw [stack_slot_open_one A s0.sp cap ptr bs hlt hcap hptr]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun b0 => ?_
  apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
  apply SepWPp.done (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
  refine ⟨?_, by simp only [arm64_norm, wp_norm, *], by simp only [CalleeSavedPreserved, arm64_norm, wp_norm, *]⟩
  intro hPR
  rw [digit_byte_eq x.n] at hPR
  have hsnoc := vecU8At_snoc_sret A x.ret cap ptr bs (BitVec.ofNat 8 (0x30 + x.n.toNat % 10))
    hlt hcap hptr
  have hframe := stackAt_decimal_frame_p (m := (k - 1) * 0x50 + resStack) (by omega) s0.sp
  have hstk_eq : (k - 1) * 0x50 + resStack + 0x50 = k * 0x50 + resStack := by omega
  rw [hstk_eq] at hframe
  dsimp only [decimalBoundedSpecPlaced, StoreKit.withLsCodeRoLoaded, decimalBoundedRawSpecP]
  rw [vecU8, hframe, ← hbs]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨v0, cap, ptr, BitVec.ofNat 64 bs.length,
    s0.readReg64 .fp, s0.readReg64 .lr, s0.readReg64 .x21, v7,
    s0.readReg64 .x20, s0.readReg64 .x19, cap, ptr, by simp only [arm64_norm, wp_norm, *], ?_⟩
  rw [← hsnoc]
  convert hPR using 1
  ac_rfl

private theorem step_reserve_and_finish_p [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {k resStack : Nat}
    (hRes : subroutine_ok (lsProg_597 H) (lsmpl.base 561)
      (StoreKit.withLsCodeRoLoaded lsmpl (SpqrV1.Varint.doReserveSpecOf resStack A)))
    (hk : 1 ≤ k) (hstk64 : k * 0x50 + resStack ≤ 2 ^ 64)
    {x : DecimalGhost} {R : SepProp} {s0 s : State}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (cap ptr v0 v7 o0 o1 o2 : BitVec 64) (bs : List (BitVec 8))
    (hcap_eq : cap.toNat = bs.length)
    (hlen9 : bs.length ≤ 9)
    (hbs : bs ++ [BitVec.ofNat 8 (0x30 + x.n.toNat % 10)] = decimalText x.n.toNat)
    (hpc : s.pc = (blkPl_597).base + 168#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs.length)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.zeroExtend 64 x.n)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 bs.length)
    (hcs : DecimalCalleeSavedP s0 s) :
    SepWPp (lsProg_597 H) (s0.readReg64 .lr) s
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
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (decimalBoundedSpecPlaced A k resStack).post x s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (decimalBoundedSpecPlaced A k resStack).onPanic x s0 sf ∗ R)) := by
  apply StoreKit.sepWPp_seq_lscro hcrl (mid := lsmpl.base 561)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by simp only [arm64_norm, wp_norm, *])
  intro hcrl_sc
  apply sepWPp_let_state; intro sc
  have hcs_call : DecimalCalleeSavedP s0 sc :=
    hcs.trans ⟨by simp only [sc, arm64_norm, wp_norm], by simp only [sc, arm64_norm, wp_norm],
      by simp only [sc, arm64_norm, wp_norm], by simp only [sc, arm64_norm, wp_norm],
      by simp only [sc, arm64_norm, wp_norm], by simp only [sc, arm64_norm, wp_norm],
      by simp only [sc, arm64_norm, wp_norm], by simp only [sc, arm64_norm, wp_norm]⟩
  have hsp_sc : sc.sp = s0.sp - 80#64 := by simp only [sc, arm64_norm, wp_norm, *]
  have htr_sc : sc.trace = s0.trace := by simp only [sc, arm64_norm, wp_norm, *]
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
  refine SepWPp.call_lscro
    (x := DoReserveCall.mk (s0.sp - 72#64) cap ptr bs 1)
    (ret_pc := (blkPl_597).base + 188#64)
    (F := F_res)
    hRes hcrl_sc
    (by simp only [sc]; wp_norm_goal)
    (by simp only [sc, arm64_norm, wp_norm, *])
    hsp_aligned
    (by simp only [sc, arm64_norm, wp_norm, *])
    ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hsplit_bot] at hm
    simp only [SpqrV1.Varint.doReserveSpecOf, sepConj_assoc, satisfies_pure_sepConj]
    have hx1_sc : (sc.readReg64 .x1).toNat = bs.length := by
      have : sc.readReg64 .x1 = BitVec.ofNat 64 bs.length := by simp only [sc, arm64_norm, wp_norm, *]
      rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hx2_sc : (sc.readReg64 .x2).toNat = 1 := by
      have : sc.readReg64 .x2 = 1#64 := by simp only [sc, arm64_norm, wp_norm]
      rw [this]; rfl
    refine ⟨⟨by simp only [sc, arm64_norm, wp_norm, *], hx1_sc, hx2_sc,
      by simp only [sc, arm64_norm, wp_norm], by simp only [sc, arm64_norm, wp_norm],
      by dsimp [reserveCap]; omega⟩, ?_⟩
    simp only [hsp_sc]
    dsimp only [F_res]
    convert hm using 1
    ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [SpqrV1.Varint.doReserveSpecOf, doReserveSpec,
      decimalBoundedSpecPlaced, StoreKit.withLsCodeRoLoaded, decimalBoundedRawSpecP, allocFailedIn] at hm ⊢
    rw [htr_sc] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm _hcrl_sm
    rw [hsp_sc] at hspm
    dsimp only [SpqrV1.Varint.doReserveSpecOf]
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
    have hcs_sm : DecimalCalleeSavedP s0 sm :=
      hcs_call.trans (DecimalCalleeSavedP.of_calleeSavedPreserved hcsm)
    have hx19m : sm.readReg64 .x19 = x.ret := by
      rw [hcsm.1]; simp only [sc, arm64_norm, wp_norm, *]
    have hx20m : sm.readReg64 .x20 = BitVec.zeroExtend 64 x.n := by
      rw [hcsm.2.1]; simp only [sc, arm64_norm, wp_norm, *]
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 bs.length := by
      rw [hcsm.2.2.1]; simp only [sc, arm64_norm, wp_norm, *]
    apply SepWPp.of_sepWP (mid := (blkPl_597).base + 76#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
    refine SepWPp.weaken_pre ?_
      (step_push_epilogue_p hk hstk64 newCap newPtr v0 v7 o0 o1 o2 bs
        hlt_new hcap_new hptr_new hbs
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *]) halign (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (hcs_sm.trans ⟨by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
          by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
          by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
          by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm]⟩))
    dsimp only [F_res]
    rw [← stack_slot_of_header_rest A s0.sp newCap newPtr bs hle_new hcap_new hptr_new, hsplit_bot]
    exact Entails.of_eq (by ac_rfl)

theorem decimal_bounded_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resStack : Nat}
    (hRes : subroutine_ok (lsProg_597 H) (lsmpl.base 561)
      (StoreKit.withLsCodeRoLoaded lsmpl (SpqrV1.Varint.doReserveSpecOf resStack A))) :
    ∀ k : Nat, 1 ≤ k →
      subroutine_ok (lsProg_597 H) (blkPl_597).base
        (decimalBoundedSpecPlaced A k resStack) := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    apply subroutine_ok_of_sepWPp
    intro x R s0 hpc hrun hpre halign
    obtain ⟨hcrl0, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
    refine ⟨(decimalBoundedRawSpecP A (k + 1) resStack).pre x s0, R, hpre, ?_⟩
    have hstk64 : (k + 1) * 0x50 + resStack ≤ 2 ^ 64 := by
      have hm_sub : s0.mem ⊨ stackAt s0.sp ((k + 1) * 0x50 + resStack) ∗
          (⌜s0.readReg64 .x0 = x.ret ∧ s0.readReg32 .x1 = x.n ∧ x.n.toNat < 10 ^ (k + 1)⌝ ∗
            memRegion x.ret 24 ∗ A.pool ∗ R) := by
        dsimp only [decimalBoundedRawSpecP] at hpre
        convert hpre using 1
        ac_rfl
      exact stk_le_pow64_of_roLoaded hcrl0.2 hm_sub
    have halign64 : s0.sp &&& 15#64 = 0#64 := by
      simpa only [State.spAligned, beq_iff_eq] using halign
    dsimp only [decimalBoundedRawSpecP]
    refine SepWPp.pure_elim fun ⟨hx0, hx1, hn_lt⟩ => ?_
    have hx1' : BitVec.truncate 32 (s0.readReg64 (Reg.gpr 1#5)) = x.n := hx1
    have hframe0 := stackAt_decimal_frame_p (m := k * 0x50 + resStack) (by omega) s0.sp
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
    by_cases hle9 : x.n.toNat ≤ 9
    · have hule := ule_nine_true hle9
      apply StoreKit.sepWPp_seq_lscro hcrl0 (mid := (blkPl_597).base + 168#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      intro hcrl_pro
      have hbs0 : ([] : List (BitVec 8)) ++ [BitVec.ofNat 8 (0x30 + x.n.toNat % 10)] =
          decimalText x.n.toNat := by
        rw [List.nil_append, Nat.mod_eq_of_lt (by omega), decimalText_digit x.n.toNat (by omega)]
      refine SepWPp.weaken_pre ?_
        (step_reserve_and_finish_p (k := k + 1) hRes (by omega) hstk64 hcrl_pro
          0#64 1#64 v0 v7 o0 o1 o2 [] rfl (by decide) hbs0
          (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, *])
          (by simp only [arm64_norm, wp_norm, *]) halign64 (by simp only [arm64_norm, wp_norm, *])
          (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
          (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
          ((DecimalCalleeSavedP.refl s0).trans ⟨by simp only [arm64_norm, wp_norm],
            by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
            by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
            by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
            by simp only [arm64_norm, wp_norm]⟩))
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
      have hih : subroutine_ok (lsProg_597 H) (blkPl_597).base
          (StoreKit.withLsCodeRoLoaded lsmpl (decimalBoundedRawSpecP A k resStack)) := ih hk1
      have hule := ule_nine_false hge10
      apply StoreKit.sepWPp_seq_lscro hcrl0 (mid := (blkPl_597).base)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      intro hcrl_sr
      apply sepWPp_let_state; intro sr
      have hcs_sr : DecimalCalleeSavedP s0 sr :=
        (DecimalCalleeSavedP.refl s0).trans ⟨by simp only [sr, arm64_norm, wp_norm],
          by simp only [sr, arm64_norm, wp_norm], by simp only [sr, arm64_norm, wp_norm],
          by simp only [sr, arm64_norm, wp_norm], by simp only [sr, arm64_norm, wp_norm],
          by simp only [sr, arm64_norm, wp_norm], by simp only [sr, arm64_norm, wp_norm],
          by simp only [sr, arm64_norm, wp_norm]⟩
      have hsp_sr : sr.sp = s0.sp - 80#64 := by simp only [sr, arm64_norm, wp_norm]
      have htr_sr : sr.trace = s0.trace := by simp only [sr, arm64_norm, wp_norm]
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
      refine SepWPp.call_lscro
        (x := DecimalGhost.mk (BitVec.ofNat 32 (x.n.toNat / 10)) (s0.sp - 72#64))
        (ret_pc := (blkPl_597).base + 60#64)
        (F := F_rec)
        hih hcrl_sr
        (by simp only [sr, arm64_norm, wp_norm])
        (by simp only [sr, arm64_norm, wp_norm, *])
        hsp_sr_aligned
        (by simp only [sr, arm64_norm, wp_norm])
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
        simp only [decimalBoundedRawSpecP, hsp_sr, sepConj_assoc, satisfies_pure_sepConj]
        have hx1_sr : sr.readReg32 .x1 = BitVec.ofNat 32 (x.n.toNat / 10) := by
          change BitVec.truncate 32 (sr.readReg64 (Reg.gpr 1#5)) = _
          simp only [sr, arm64_norm, wp_norm]
          exact div10_trunc32 x.n
        have hn_sub_lt : (BitVec.ofNat 32 (x.n.toNat / 10)).toNat < 10 ^ k := by
          have hn32 : x.n.toNat < 2 ^ 32 := x.n.isLt
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          exact hdiv_lt
        exact ⟨⟨by simp only [sr, arm64_norm, wp_norm], hx1_sr, hn_sub_lt⟩, hm'⟩
      · intro sf code R' _ hm
        exact allowPanic_not_exited hm
      · intro sf _ hm
        dsimp only [decimalBoundedSpecPlaced, StoreKit.withLsCodeRoLoaded, decimalBoundedRawSpecP,
          allocFailedIn] at hm ⊢
        rw [htr_sr] at hm
        exact allowPanic_frame id hm
      · intro sm hpcm hrunm hspm hcsm hcrl_sm
        rw [hsp_sr] at hspm
        have hq_nat : (BitVec.ofNat 32 (x.n.toNat / 10)).toNat = x.n.toNat / 10 := by
          have hn32 : x.n.toNat < 2 ^ 32 := x.n.isLt
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        conv =>
          arg 4
          dsimp only [decimalBoundedRawSpecP]
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
        have hcs_sm : DecimalCalleeSavedP s0 sm :=
          hcs_sr.trans (DecimalCalleeSavedP.of_calleeSavedPreserved hcsm)
        have hx19m : sm.readReg64 .x19 = x.ret := by
          rw [hcsm.1]; simp only [sr, arm64_norm, wp_norm]
        have hx20m : sm.readReg64 .x20 = BitVec.zeroExtend 64 x.n := by
          rw [hcsm.2.1]; simp only [sr, arm64_norm, wp_norm]
        have hbs_rec : subBs ++ [BitVec.ofNat 8 (0x30 + x.n.toNat % 10)] =
            decimalText x.n.toNat :=
          (decimalText_ge10 x.n.toNat hge10).symm
        have hlen_sub9 : subBs.length ≤ 9 := by
          have hn32 : x.n.toNat < 2 ^ 32 := x.n.isLt
          exact decimalText_length_le 9 (x.n.toNat / 10) (by omega) (by omega)
        by_cases hlt_sub : subBs.length < subCap.toNat
        · have hbeq_f := Helpers.cap_beq_len_false hlt_sub
          apply SepWPp.of_sepWP (mid := (blkPl_597).base + 76#64)
          wp_steps
          apply SepWP.done (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
          refine SepWPp.weaken_pre ?_
            (step_push_epilogue_p (A := A) (k := k + 1) (R := R) (by omega) hstk64
              subCap subPtr v0 v7 o0 o1 o2 subBs
              hlt_sub hcap_sub hptr_sub hbs_rec
              (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, *])
              (by simp only [arm64_norm, wp_norm, *]) halign64 (by simp only [arm64_norm, wp_norm, *])
              (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
              (by simp only [arm64_norm, wp_norm, *])
              (hcs_sm.trans ⟨by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
                by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
                by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
                by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm]⟩))
          dsimp only [F_rec]
          rw [← stack_slot_of_header_rest A s0.sp subCap subPtr subBs hle_sub hcap_sub hptr_sub]
          exact Entails.of_eq (by simp only [Nat.add_sub_cancel]; ac_rfl)
        · have hcap_eq_sub : subCap.toNat = subBs.length := by omega
          have hbeq_t := Helpers.cap_beq_len_true hcap_eq_sub
          apply StoreKit.sepWPp_seq_lscro hcrl_sm (mid := (blkPl_597).base + 168#64)
          wp_steps
          apply SepWP.done (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
          intro hcrl_chk
          refine SepWPp.weaken_pre ?_
            (step_reserve_and_finish_p (k := k + 1) (R := R) hRes (by omega) hstk64 hcrl_chk
              subCap subPtr v0 v7 o0 o1 o2 subBs
              hcap_eq_sub hlen_sub9 hbs_rec
              (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, *])
              (by simp only [arm64_norm, wp_norm, *]) halign64 (by simp only [arm64_norm, wp_norm, *])
              (by simp only [arm64_norm, wp_norm]; exact beq_iff_eq.mp hbeq_t)
              (by simp only [arm64_norm, wp_norm, *])
              (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
              (hcs_sm.trans ⟨by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
                by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
                by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
                by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm]⟩))
          dsimp only [F_rec]
          rw [← stack_slot_of_header_rest A s0.sp subCap subPtr subBs hle_sub hcap_sub hptr_sub]
          exact Entails.of_eq (by simp only [Nat.add_sub_cancel]; ac_rfl)

theorem decimal_placed_ok_main [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resStack stk : Nat}
    (hRes : subroutine_ok (lsProg_597 H) (lsmpl.base 561)
      (StoreKit.withLsCodeRoLoaded lsmpl (SpqrV1.Varint.doReserveSpecOf resStack A)))
    (hstk : 10 * 0x50 + resStack ≤ stk) :
    subroutine_ok (lsProg_597 H) (lsmpl.base 597)
      (decimalSpecPlaced A stk) := by
  have h10 := decimal_bounded_placed_ok hRes 10 (by omega)
  change subroutine_ok (lsProg_597 H) (blkPl_597).base _
  intro x R s0 hpc hrun hpre halign hL
  obtain ⟨hcrl0, hpre0⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  have hstk64 : stk ≤ 2 ^ 64 := by
    have hm_sub : s0.mem ⊨ stackAt s0.sp stk ∗
        (⌜s0.readReg64 .x0 = x.ret ∧ s0.readReg32 .x1 = x.n⌝ ∗ memRegion x.ret 24 ∗ A.pool ∗ R) := by
      dsimp only [decimalSpecPlaced] at hpre0
      convert hpre0 using 1
      ac_rfl
    exact stk_le_pow64_of_roLoaded hcrl0.2 hm_sub
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
  have hpre' : s0.mem ⊨ (decimalBoundedSpecPlaced A 10 resStack).pre x s0 ∗ R' := by
    refine satisfies_lscro_pre hcrl0 ?_
    dsimp only [decimalSpecPlaced, decimalBoundedRawSpecP, R'] at hpre0 ⊢
    rw [hsplit] at hpre0
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
    refine ⟨⟨hpre0.1.1, hpre0.1.2, hn10⟩, ?_⟩
    convert hpre0.2 using 1
    ac_rfl
  obtain ⟨sf, hs, ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩⟩ :=
    h10 x R' s0 hpc hrun hpre' halign hL
  · refine ⟨sf, hs, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [decimalSpecPlaced, decimalBoundedSpecPlaced, StoreKit.withLsCodeRoLoaded,
      decimalBoundedRawSpecP, R'] at hpost ⊢
    rw [hsplit]
    convert hpost using 1
    ac_rfl
  · refine ⟨sf, hs, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [decimalSpecPlaced, decimalBoundedSpecPlaced, StoreKit.withLsCodeRoLoaded,
      decimalBoundedRawSpecP, R'] at hpost ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hex).elim
  · exact (allowPanic_not_exited hoom).elim

end CryptoVerification.SignalSession.Cli.Decimal.Helpers
