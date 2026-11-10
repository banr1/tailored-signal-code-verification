/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.AllocPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

@[expose] public section

set_option autoImplicit false

/-!
# Relocatable Multi-Digit Accumulator Loop for `signal_session::address` (`[LibsignalPlacement]`, Block `580`)
-/

namespace CryptoVerification.SignalSession.Cli.MainHops.Address.Helpers

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed

set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option maxHeartbeats 800000 in
theorem step_digit_loop_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resStack : Nat}
    (hFs : AllocContractsFsPlaced A H)
    (hpan : H lsHandleErrorSym580 = some Rust.panicked)
    (hstk : 0xB0 + extHookStack ≤ resStack)
    (hstkle : resStack ≤ 2 ^ 64)
    (x : AddressCall)
    (name dev ds : List (BitVec 8))
    (sidRes : Bool × List.Vector (BitVec 8) 16)
    (ptr0 : BitVec 64)
    (hbs_eq : x.bs = name ++ (46#8 :: dev))
    (hrsplit : rsplitDot x.bs = some (name, dev))
    (hsid : serviceIdParse uuidTryParse name = some sidRes)
    (hds : ds = stripPlus dev)
    (hds_ne : ds ≠ [])
    (hds_lt64 : ds.length < 2 ^ 64)
    (hdev_repack : ∀ P_ds : SepProp, (P_ds ⊢ (ptr0 ↦ₛ ds)) →
      P_ds ∗ (if dev.head? = some 43#8 then ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦₈ 43#8)
        else emp) ⊢ ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ₛ dev))
    (rem : List (BitVec 8)) :
    ∀ (done : List (BitVec 8)) (ptr : BitVec 64) {s0 s : State},
      ds = done ++ rem →
      let acc := done.foldl (fun a c => 10 * a + (c.toNat - 48)) 0
      acc ≤ 255 →
      (∀ c ∈ done, isDigit c = true) →
      ptr = ptr0 + BitVec.ofNat 64 done.length →
      s0.spAligned = true →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = (blkPl_580).base + loopHeadOff →
      s.status = .Running →
      s.sp = s0.sp - 96#64 →
      s.trace = s0.trace →
      s.readReg64 .x8 = ptr →
      s.readReg64 .x9 = BitVec.ofNat 64 rem.length →
      s.readReg64 .x19 = x.out →
      s.readReg64 .x20 = BitVec.ofNat 64 name.length →
      s.readReg64 .x21 = x.p →
      s.readReg64 .x24 = BitVec.ofNat 64 acc →
      AddrUpperSaved s0 s →
      SepWPp ((blkPC_580).rebase (blkPl_580).base H) (s0.readReg64 .lr) s
        ((ptr0 ↦ₛ done) ∗ (ptr ↦ₛ rem) ∗
          (if dev.head? = some 43#8 then ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦₈ 43#8)
           else emp) ∗
          ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
          (x.p ↦ₛ name) ∗
          memRegion x.out 32 ∗ AddrFrameCommon A resStack s0)
        (AddrGoalPost A resStack x s0)
        (AddrPanicAllow s0) := by
  have hexit := @step_none_exit_placed _ A H resStack hstk hstkle x
  have halloc := @step_sxtb_and_alloc_placed _ A H resStack hFs hpan hstk hstkle x name dev sidRes
  dsimp only []
  induction rem with
  | nil =>
    intro done ptr s0 s hds_eq hacc_le hdone_dig hptr hal0 hcrl hpc hrun hsp htr
      hx8 hx9 hx19 hx20 hx21 hx24 hcs
    set acc := done.foldl (fun a c => 10 * a + (c.toNat - 48)) 0
    try dsimp only [loopHeadOff] at hpc
    try dsimp only [Reg.x8, Reg.x9, Reg.x19, Reg.x20, Reg.x21, Reg.x24] at hx8 hx9 hx19 hx20 hx21 hx24
    have hdone_eq : ds = done := by simpa using hds_eq
    have hparse_dev : parseUnsigned 255 dev = some acc := by
      have h1 := parseUnsigned_some_of_all_digits hds hds_ne
        (by rw [hdone_eq]; exact hdone_dig) (by rw [hdone_eq]; exact hacc_le)
      rwa [hdone_eq] at h1
    apply sepWPp_of_sepWP_lscro (mid := (blkPl_580).base + sxtbCheckOff) hcrl
    wp_steps
    apply SepWP.done
      (by simp only [sxtbCheckOff, arm64_norm, *]; try (clear * -; bv_omega))
      (by simp only [arm64_norm, *])
    intro hcrl'
    have hpack_all :
        ((ptr0 ↦ₛ done) ∗ (ptr ↦ₛ []) ∗
          (if dev.head? = some 43#8 then ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦₈ 43#8)
           else emp) ∗
          ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
          (x.p ↦ₛ name) ∗
          memRegion x.out 32 ∗ AddrFrameCommon A resStack s0) ⊢
        ((x.p ↦ₛ name) ∗ ((x.p + BitVec.ofNat 64 name.length) ↦ₛ (46#8 :: dev)) ∗
          memRegion x.out 32 ∗ AddrFrameCommon A resStack s0) := by
      have hd1 := hdev_repack ((ptr0 ↦ₛ done) ∗ (ptr ↦ₛ []))
        (by rw [pointsToBytes_nil, sepConj_emp, ← hdone_eq]; exact Entails.refl _)
      have hdot :
          (((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
            ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ₛ dev)) =
            ((x.p + BitVec.ofNat 64 name.length) ↦ₛ (46#8 :: dev)) :=
        (pointsToBytes_cons _ _ _).symm
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_left (Entails.trans (sepConj_mono_right hd1)
          (Entails.of_eq hdot))))
      exact Entails.of_eq (by ac_rfl)
    refine SepWPp.weaken_pre hpack_all ?_
    exact halloc acc hbs_eq hrsplit hsid
      hparse_dev hacc_le hal0 hcrl'
      (by simp only [sxtbCheckOff, arm64_norm, *]; try (clear * -; bv_omega))
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, hx19])
      (by simp only [arm64_norm, hx20])
      (by simp only [arm64_norm, hx21])
      (by simp only [arm64_norm, hx24])
      (by rcases hcs with ⟨h25, h26, h27, h28, hvregs, hfs⟩; simp only [AddrUpperSaved, arm64_norm, *])
  | cons b rest ih =>
    intro done ptr s0 s hds_eq hacc_le hdone_dig hptr hal0 hcrl hpc hrun hsp htr
      hx8 hx9 hx19 hx20 hx21 hx24 hcs
    set acc := done.foldl (fun a c => 10 * a + (c.toNat - 48)) 0
    try dsimp only [loopHeadOff] at hpc
    try dsimp only [Reg.x8, Reg.x9, Reg.x19, Reg.x20, Reg.x21, Reg.x24] at hx8 hx9 hx19 hx20 hx21 hx24
    have hrem_pos : 0 < (b :: rest).length := by simp
    have hrem_lt64 : (b :: rest).length < 2 ^ 64 := by
      have : ds.length = done.length + (b :: rest).length := by simp [hds_eq]
      omega
    have hx9_ne0 : BitVec.ofNat 64 (b :: rest).length ≠ 0#64 := by
      intro h
      have ht := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrem_lt64] at ht
      change (b :: rest).length = 0 at ht
      omega
    have hx9_beq0 : (BitVec.ofNat 64 (b :: rest).length == 0#64) = false :=
      beq_eq_false_iff_ne.mpr hx9_ne0
    have hpack_none :
        ((ptr0 ↦ₛ done) ∗ (ptr ↦ₛ (b :: rest)) ∗
          (if dev.head? = some 43#8 then ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦₈ 43#8)
           else emp) ∗
          ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
          (x.p ↦ₛ name) ∗
          memRegion x.out 32 ∗ AddrFrameCommon A resStack s0) ⊢
        ((x.p ↦ₛ x.bs) ∗ memRegion x.out 32 ∗ AddrFrameCommon A resStack s0) := by
      have hjoin_ds : ((ptr0 ↦ₛ done) ∗ (ptr ↦ₛ (b :: rest))) = (ptr0 ↦ₛ ds) := by
        rw [hds_eq, pointsToBytes_append, ← hptr]
      have hd1 := hdev_repack ((ptr0 ↦ₛ done) ∗ (ptr ↦ₛ (b :: rest))) (Entails.of_eq hjoin_ds)
      have hbs_all :
          ((x.p ↦ₛ name) ∗ (((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
            ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦ₛ dev))) = (x.p ↦ₛ x.bs) := by
        rw [← pointsToBytes_cons, ← pointsToBytes_append, ← hbs_eq]
      refine Entails.trans ?_
        (sepConj_mono_left (Entails.trans
          (sepConj_mono_right (sepConj_mono_right hd1)) (Entails.of_eq hbs_all)))
      exact Entails.of_eq (by ac_rfl)
    obtain ⟨hmul_ovf, hmul_val⟩ := loop_mul10_overflow acc hacc_le
    have hmul_z := loop_mul10_eq0 acc hacc_le
    have htrunc24 : (BitVec.ofNat 64 acc).truncate 32 = BitVec.ofNat 32 acc := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat]
    have htrunc8_24 : (BitVec.ofNat 64 acc).truncate 8 = (BitVec.ofNat 32 acc).truncate 8 := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat]
    by_cases h26 : 26 ≤ acc
    · have hnone : addrParse uuidTryParse x.bs = none := by
        simp only [addrParse, hrsplit, hsid, parseUnsigned_acc26_none hds hds_eq h26]
      have htst : ((((BitVec.ofNat 32 acc &&& 0xff#32) +
          ((BitVec.ofNat 32 acc &&& 0xff#32) <<< 2)) <<< 1) &&& 0xf00#32 != 0#32) = true := by
        rw [hmul_ovf]; exact decide_eq_true h26
      have htst_eq0 : (((((BitVec.ofNat 32 acc &&& 0xff#32) +
          ((BitVec.ofNat 32 acc &&& 0xff#32) <<< 2)) <<< 1) &&& 0xf00#32) == 0#32) = false := by
        rw [hmul_z]; exact decide_eq_false (by omega)
      apply SepWPp.of_sepWP (mid := (blkPl_580).base + noneExitOff)
      wp_steps
      apply SepWP.done
        (by simp only [noneExitOff, arm64_norm, *]; try (clear * -; bv_omega))
        (by simp only [arm64_norm, *])
      refine SepWPp.weaken_pre hpack_none ?_
      exact hexit hnone hal0
        (by simp only [noneExitOff, arm64_norm, *]; try (clear * -; bv_omega))
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, hsp])
        (by simp only [arm64_norm, htr])
        (by simp only [arm64_norm, hx19])
        (by rcases hcs with ⟨h25, h26', h27, h28, hvregs, hfs⟩; simp only [AddrUpperSaved, arm64_norm, *])
    · have hle25 : acc ≤ 25 := by omega
      have htst_f : ((((BitVec.ofNat 32 acc &&& 0xff#32) +
          ((BitVec.ofNat 32 acc &&& 0xff#32) <<< 2)) <<< 1) &&& 0xf00#32 != 0#32) = false := by
        rw [hmul_ovf]; exact decide_eq_false h26
      have htst_eq0 : (((((BitVec.ofNat 32 acc &&& 0xff#32) +
          ((BitVec.ofNat 32 acc &&& 0xff#32) <<< 2)) <<< 1) &&& 0xf00#32) == 0#32) = true := by
        rw [hmul_z]; exact decide_eq_true hle25
      have hw10_eq : ((((BitVec.ofNat 32 acc &&& 0xff#32) +
          ((BitVec.ofNat 32 acc &&& 0xff#32) <<< 2)) <<< 1) &&& 0xff#32) =
          BitVec.ofNat 32 (10 * acc) := hmul_val hle25
      rw [pointsToBytes_cons ptr b rest, sepConj_assoc]
      rw [show (ptr ↦₈ b) = ((ptr0 + BitVec.ofNat 64 done.length) ↦₈ b) by rw [hptr]]
      by_cases hb : isDigit b = true
      · have hhi_f : (9#32).ult (b.zeroExtend 32 - 0x30#32) = false := by
          simpa only [digitSub32] using (not_isDigit_iff_hi9 b).trans (by simp [hb])
        have hule_t : (b.zeroExtend 32 - 0x30#32).ule 9#32 = true := by
          simpa only [digitSub32] using (isDigit_iff_sub32_ule9 b).trans hb
        obtain ⟨hw24_eq, hcarry⟩ := loop_step_carry acc b hle25 hb
        have hw24_raw : BitVec.ofNat 32 (10 * acc) + ((b.zeroExtend 32 - 0x30#32) &&& 0xff#32) =
            BitVec.ofNat 32 (10 * acc + (b.toNat - 48)) := hw24_eq
        set acc' := 10 * acc + (b.toNat - 48)
        have hacc'_259 : acc' ≤ 259 := by
          have vb := digit_val_le9 b hb
          omega
        have hsub9 : BitVec.ofNat 64 (b :: rest).length - 1#64 = BitVec.ofNat 64 rest.length := by
          have h1 : (b :: rest).length = rest.length + 1 := rfl
          rw [h1] at hrem_lt64 ⊢
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_sub, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt hrem_lt64, Nat.mod_eq_of_lt (Nat.lt_of_succ_lt hrem_lt64)]
          omega
        by_cases hle255' : acc' ≤ 255
        · have hbit1 : BitVec.truncate 1 (BitVec.ofNat 32 acc' >>> 8) = 0#1 := by
            rw [carry_bit1_of_acc' acc' hacc'_259]; simp [hle255']
          have htbz_t : (((BitVec.ofNat 32 acc' >>> 8) &&& 1#32) == 0#32) = true := by
            rw [← hw24_eq, hcarry]; exact decide_eq_true hle255'
          apply sepWPp_of_sepWP_lscro (mid := (blkPl_580).base + loopHeadOff) hcrl
          wp_steps
          apply SepWP.done
            (by simp only [loopHeadOff, arm64_norm, *]; try (clear * -; bv_omega))
            (by simp only [arm64_norm, *])
          intro hcrl_next
          rw [show ((ptr0 + BitVec.ofNat 64 done.length) ↦₈ b) = (ptr ↦₈ b) by rw [hptr]]
          have hdone_snoc : ((ptr0 ↦ₛ done) ∗ (ptr ↦₈ b)) = (ptr0 ↦ₛ (done ++ [b])) := by
            rw [pointsToBytes_append, hptr, pointsToBytes_singleton]
          have hpack_next :
              ((ptr0 ↦ₛ done) ∗ (ptr ↦₈ b) ∗ ((ptr + 1#64) ↦ₛ rest) ∗
                (if dev.head? = some 43#8 then ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦₈ 43#8)
                 else emp) ∗
                ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
                (x.p ↦ₛ name) ∗
                memRegion x.out 32 ∗ AddrFrameCommon A resStack s0) ⊢
              ((ptr0 ↦ₛ (done ++ [b])) ∗ ((ptr + 1#64) ↦ₛ rest) ∗
                (if dev.head? = some 43#8 then ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦₈ 43#8)
                 else emp) ∗
                ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
                (x.p ↦ₛ name) ∗
                memRegion x.out 32 ∗ AddrFrameCommon A resStack s0) := by
            rw [← sepConj_assoc, hdone_snoc]
            exact Entails.of_eq (by ac_rfl)
          refine SepWPp.weaken_pre hpack_next ?_
          have hdig_next : ∀ c ∈ done ++ [b], isDigit c = true := by
            intro c hc
            rcases List.mem_append.mp hc with hc | hc
            · exact hdone_dig c hc
            · simp only [List.mem_singleton] at hc; subst hc; exact hb
          have hptr_next : ptr + 1#64 = ptr0 + BitVec.ofNat 64 (done ++ [b]).length := by
            have hd_lt : done.length + 1 < 2 ^ 64 := by
              have : ds.length = done.length + (b :: rest).length := by simp [hds_eq]
              omega
            have hadd1 : BitVec.ofNat 64 done.length + 1#64 = BitVec.ofNat 64 (done.length + 1) := by
              apply BitVec.eq_of_toNat_eq
              simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt hd_lt, Nat.mod_eq_of_lt (Nat.lt_of_succ_lt hd_lt)]
            rw [hptr, List.length_append, List.length_singleton, BitVec.add_assoc, hadd1]
          have hzext_acc' : (BitVec.ofNat 32 acc').zeroExtend 64 = BitVec.ofNat 64 acc' :=
            zext64_ofNat32 acc' (by omega)
          exact ih (done ++ [b]) (ptr + 1#64)
            (by simp [hds_eq])
            (by simpa [List.foldl_append, acc', acc] using hle255')
            hdig_next
            hptr_next
            hal0 hcrl_next
            (by simp only [loopHeadOff, arm64_norm, *]; try (clear * -; bv_omega))
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, hsp])
            (by simp only [arm64_norm, htr])
            (by simp only [arm64_norm, hx8, hptr])
            (by simp only [arm64_norm, hx9, hsub9]; try (clear * - hrem_lt64; simp only [List.length_cons] at hrem_lt64 ⊢; bv_omega))
            (by simp only [arm64_norm, hx19])
            (by simp only [arm64_norm, hx20])
            (by simp only [arm64_norm, hx21])
            (by simp only [List.foldl_append, List.foldl, arm64_norm, hx24,
              htrunc24, htrunc8_24, hw10_eq, hw24_raw, hzext_acc']; rfl)
            (by rcases hcs with ⟨h25, h26', h27, h28, hvregs, hfs⟩
                simp only [AddrUpperSaved, arm64_norm, *])
        · have h256' : 256 ≤ (done ++ [b]).foldl (fun a c => 10 * a + (c.toNat - 48)) 0 := by
            simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]; omega
          have hnone : addrParse uuidTryParse x.bs = none := by
            simp only [addrParse, hrsplit, hsid,
              parseUnsigned_overflow_prefix hds (rem := rest) (by simp [hds_eq]) h256']
          have hbit1 : BitVec.truncate 1 (BitVec.ofNat 32 acc' >>> 8) = 1#1 := by
            rw [carry_bit1_of_acc' acc' hacc'_259]; simp [hle255']
          have htbz_f : (((BitVec.ofNat 32 acc' >>> 8) &&& 1#32) == 0#32) = false := by
            rw [← hw24_eq, hcarry]; exact decide_eq_false hle255'
          apply SepWPp.of_sepWP (mid := (blkPl_580).base + noneExitOff)
          wp_steps
          apply SepWP.done
            (by simp only [noneExitOff, arm64_norm, *]; try (clear * -; bv_omega))
            (by simp only [arm64_norm, *])
          rw [show ((ptr0 + BitVec.ofNat 64 done.length) ↦₈ b) = (ptr ↦₈ b) by rw [hptr]]
          have hrestore1 :
              ((ptr0 ↦ₛ done) ∗ (ptr ↦₈ b) ∗ ((ptr + 1#64) ↦ₛ rest) ∗
                (if dev.head? = some 43#8 then ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦₈ 43#8)
                 else emp) ∗
                ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
                (x.p ↦ₛ name) ∗
                memRegion x.out 32 ∗ AddrFrameCommon A resStack s0) =
              ((ptr0 ↦ₛ done) ∗ (ptr ↦ₛ (b :: rest)) ∗
                (if dev.head? = some 43#8 then ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦₈ 43#8)
                 else emp) ∗
                ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
                (x.p ↦ₛ name) ∗
                memRegion x.out 32 ∗ AddrFrameCommon A resStack s0) := by
            rw [pointsToBytes_cons ptr b rest, sepConj_assoc]
          rw [hrestore1]
          refine SepWPp.weaken_pre hpack_none ?_
          exact hexit hnone hal0
            (by simp only [noneExitOff, arm64_norm, *]; try (clear * -; bv_omega))
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, hsp])
            (by simp only [arm64_norm, htr])
            (by simp only [arm64_norm, hx19])
            (by rcases hcs with ⟨h25, h26', h27, h28, hvregs, hfs⟩
                simp only [AddrUpperSaved, arm64_norm, *])
      · have hb_f : isDigit b = false := Bool.eq_false_iff.mpr hb
        have hnone : addrParse uuidTryParse x.bs = none := by
          have hmem : b ∈ ds := by simp [hds_eq]
          simp only [addrParse, hrsplit, hsid, parseUnsigned_bad_digit hds hmem hb_f]
        have hhi_t : (9#32).ult (b.zeroExtend 32 - 0x30#32) = true := by
          simpa only [digitSub32] using (not_isDigit_iff_hi9 b).trans (by simp [hb_f])
        have hule_f : (b.zeroExtend 32 - 0x30#32).ule 9#32 = false := by
          simpa only [digitSub32] using (isDigit_iff_sub32_ule9 b).trans hb_f
        apply SepWPp.of_sepWP (mid := (blkPl_580).base + noneExitOff)
        wp_steps
        apply SepWP.done
          (by simp only [noneExitOff, arm64_norm, *]; try (clear * -; bv_omega))
          (by simp only [arm64_norm, *])
        rw [show ((ptr0 + BitVec.ofNat 64 done.length) ↦₈ b) = (ptr ↦₈ b) by rw [hptr]]
        have hrestore2 :
            ((ptr0 ↦ₛ done) ∗ (ptr ↦₈ b) ∗ ((ptr + 1#64) ↦ₛ rest) ∗
              (if dev.head? = some 43#8 then ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦₈ 43#8)
               else emp) ∗
              ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
              (x.p ↦ₛ name) ∗
              memRegion x.out 32 ∗ AddrFrameCommon A resStack s0) =
            ((ptr0 ↦ₛ done) ∗ (ptr ↦ₛ (b :: rest)) ∗
              (if dev.head? = some 43#8 then ((x.p + BitVec.ofNat 64 name.length + 1#64) ↦₈ 43#8)
               else emp) ∗
              ((x.p + BitVec.ofNat 64 name.length) ↦₈ 46#8) ∗
              (x.p ↦ₛ name) ∗
              memRegion x.out 32 ∗ AddrFrameCommon A resStack s0) := by
          rw [pointsToBytes_cons ptr b rest, sepConj_assoc]
        rw [hrestore2]
        refine SepWPp.weaken_pre hpack_none ?_
        exact hexit hnone hal0
          (by simp only [noneExitOff, arm64_norm, *]; try (clear * -; bv_omega))
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, hsp])
          (by simp only [arm64_norm, htr])
          (by simp only [arm64_norm, hx19])
          (by rcases hcs with ⟨h25, h26', h27, h28, hvregs, hfs⟩
              simp only [AddrUpperSaved, arm64_norm, *])

end CryptoVerification.SignalSession.Cli.MainHops.Address.Helpers
