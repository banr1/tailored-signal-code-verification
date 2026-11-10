/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.BasePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Alloc
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

@[expose] public section

set_option autoImplicit false

/-!
# Relocatable Exit and Allocation Paths for `signal_session::address` (`[LibsignalPlacement]`, Block `580`)
-/

namespace CryptoVerification.SignalSession.Cli.MainHops.Address.Helpers

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

private theorem serviceIdParse_bv_props_p {name : List (BitVec 8)}
    {res : Bool × List.Vector (BitVec 8) 16}
    (h : serviceIdParse uuidTryParse name = some res) :
    0 < name.length ∧
      name.length < 2 ^ 63 ∧
      BitVec.extractLsb' 63 1 (BitVec.ofNat 64 name.length) = 0#1 ∧
      BitVec.ofNat 64 name.length ≠ 0#64 ∧
      (BitVec.ofNat 64 name.length == 0#64) = false ∧
      (BitVec.ofNat 64 name.length).toNat = name.length ∧
      LayoutOk name.length 1 := by
  rcases serviceIdParse_length h with hlen | hlen <;> rw [hlen] <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide,
      ⟨by decide, ⟨0, rfl⟩, by decide⟩⟩

/-! ## `None` Exit (`step_none_exit_placed`) -/

theorem step_none_exit_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resStack : Nat}
    (hstk : 0xB0 + extHookStack ≤ resStack)
    (hstkle : resStack ≤ 2 ^ 64)
    (x : AddressCall)
    (hnone : addrParse uuidTryParse x.bs = none)
    {s0 s : State}
    (hal0 : s0.spAligned = true)
    (hpc : s.pc = (blkPl_580).base + noneExitOff)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.out)
    (hcs : AddrUpperSaved s0 s) :
    SepWPp ((blkPC_580).rebase (blkPl_580).base H) (s0.readReg64 .lr) s
      ((x.p ↦ₛ x.bs) ∗ memRegion x.out 32 ∗ AddrFrameCommon A resStack s0)
      (AddrGoalPost A resStack x s0)
      (AddrPanicAllow s0) := by
  have _hal : s.spAligned = true := sp_sub_96_spAligned hal0 hsp
  dsimp only [noneExitOff] at hpc ⊢
  rcases hcs with ⟨h25, h26, h27, h28, hvregs, hfs⟩
  rw [out32_open_none x.out]
  unfold AddrFrameCommon
  rw [addrSavedRegs_at_frame hsp s0]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w0 => ?_
  apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine ⟨by simp only [arm64_norm, *], by simp only [CalleeSavedPreserved, arm64_norm, *], ?_⟩
  dsimp only [addressSpec]
  rw [hnone]
  dsimp only []
  have hpack := stackAt_addr_pack s0.sp resStack s0 hstk hstkle
  rw [addrSavedRegs_at_frame hsp s0] at hpack
  refine Entails.pure_right ⟨by simp only [arm64_norm, htr], by simp only [arm64_norm, hfs]⟩ ?_
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hpack)))
  rw [← addrSavedRegs_at_frame hsp s0]
  generalize subStackSize = ssz
  exact Entails.of_eq (by ac_rfl)

/-! ## Sign-Extension and Allocation (`step_sxtb_and_alloc_placed`) -/

set_option maxHeartbeats 800000 in
theorem step_sxtb_and_alloc_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resStack : Nat}
    (hFs : AllocContractsFsPlaced A H)
    (hpan : H lsHandleErrorSym580 = some Rust.panicked)
    (hstk : 0xB0 + extHookStack ≤ resStack)
    (hstkle : resStack ≤ 2 ^ 64)
    (x : AddressCall)
    (name dev : List (BitVec 8))
    (sidRes : Bool × List.Vector (BitVec 8) 16)
    (d : Nat)
    (hbs_eq : x.bs = name ++ (46#8 :: dev))
    (hrsplit : rsplitDot x.bs = some (name, dev))
    (hsid : serviceIdParse uuidTryParse name = some sidRes)
    (hdev : parseUnsigned 255 dev = some d)
    (hd255 : d ≤ 255)
    {s0 s : State}
    (hal0 : s0.spAligned = true)
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_580).base + sxtbCheckOff)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 name.length)
    (hx21 : s.readReg64 .x21 = x.p)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 d)
    (hcs : AddrUpperSaved s0 s) :
    SepWPp ((blkPC_580).rebase (blkPl_580).base H) (s0.readReg64 .lr) s
      ((x.p ↦ₛ name) ∗ ((x.p + BitVec.ofNat 64 name.length) ↦ₛ (46#8 :: dev)) ∗
        memRegion x.out 32 ∗ AddrFrameCommon A resStack s0)
      (AddrGoalPost A resStack x s0)
      (AddrPanicAllow s0) := by
  by_cases hd127 : 1 ≤ d ∧ d ≤ 127
  · have hsome : addrParse uuidTryParse x.bs = some ⟨name, BitVec.ofNat 8 d⟩ := by
      simp [addrParse, hrsplit, hsid, hdev, hd127]
    obtain ⟨hpos, hlt63, htbz63, hne0, hbeq0, htoNat, hlay⟩ := serviceIdParse_bv_props_p hsid
    have htrunc_d8 : (BitVec.ofNat 64 d).truncate 8 = BitVec.ofNat 8 d := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat]
    have hsle_f : ((BitVec.ofNat 8 d).signExtend 32).sle 0#32 = false := by
      rw [← htrunc_d8, sxtb_le_zero_iff d hd255]
      exact decide_eq_false (not_not.mpr hd127)
    have hshim := hFs.shim2_rocl (prog := lsProg_580 H) (i := 580)
    have halloc := hFs.alloc_rocl (prog := lsProg_580 H) (i := 580)
    have hmemcpy := hFs.memcpy2_rocl (prog := lsProg_580 H) (i := 580)
    have hpanic := addr_panic_handle_error_placed (H := H) hpan
    clear hFs hpan
    dsimp only [lsProg_580, sxtbCheckOff] at hshim halloc hmemcpy hpanic hpc ⊢
    apply sepWPp_of_sepWP_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcrl1
    apply bind_sepWPp_state; intro s_sh
    have hal_sh : s_sh.spAligned = true :=
      sp_sub_96_spAligned hal0 (by simp only [s_sh, arm64_norm, hsp])
    have hcs_sh : AddrUpperSaved s0 s_sh := by
      rcases hcs with ⟨h25, h26, h27, h28, hvregs, hfs⟩
      simp only [s_sh, AddrUpperSaved, arm64_norm, *]
    refine addr_call_rocl () hshim hcrl1
      (by simp only [s_sh, arm64_norm, htr])
      (by simp only [s_sh, arm64_norm, *])
      (by simp only [s_sh, arm64_norm, *])
      hal_sh
      (ret_pc := (blkPl_580).base + shimRetOff)
      (by simp only [s_sh, shimRetOff, arm64_norm, *])
      (F := (x.p ↦ₛ name) ∗ ((x.p + BitVec.ofNat 64 name.length) ↦ₛ (46#8 :: dev)) ∗
        memRegion x.out 32 ∗
        memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - (subStackSize + 96)) ∗
        memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStackSize) 80 ∗
        memRegion (s0.sp - 96#64) 32 ∗
        addrSavedRegs s0.sp s0 ∗ A.pool)
      ?_ (hnext := ?_)
    · unfold AddrFrameCommon
      rw [stackAt_sub_hook (s0.sp - 96#64)]
      dsimp only [Spec.keepsFs, session2ShimSpecX]
      have hsp_sh : s_sh.sp = s0.sp - 96#64 := by simp only [s_sh, arm64_norm, hsp]
      rw [hsp_sh]
      generalize subStackSize = ssz
      generalize extHookStack = hsz
      exact Entails.of_eq (by ac_rfl)
    · intro s_after_sh hcrl2 hpc2 hrun2 hsp2 hcsp2
      dsimp only [Spec.keepsFs, session2ShimSpecX]
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun hfs2 => ?_
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun htr2 => ?_
      have hx19_2 : s_after_sh.readReg64 .x19 = x.out := by
        rw [hcsp2.1]; simp only [s_sh, arm64_norm, hx19]
      have hx20_2 : s_after_sh.readReg64 .x20 = BitVec.ofNat 64 name.length := by
        rw [hcsp2.2.1]; simp only [s_sh, arm64_norm, hx20]
      have hx21_2 : s_after_sh.readReg64 .x21 = x.p := by
        rw [hcsp2.2.2.1]; simp only [s_sh, arm64_norm, hx21]
      have hx24_2 : s_after_sh.readReg64 .x24 = BitVec.ofNat 64 d := by
        rw [hcsp2.2.2.2.2.2.1]; simp only [s_sh, arm64_norm, hx24]
      have hsp2' : s_after_sh.sp = s0.sp - 96#64 := by
        rw [hsp2]; simp only [s_sh, arm64_norm, hsp]
      clear hsp2
      have htr2' : s_after_sh.trace = s0.trace := by
        rw [htr2]; simp only [s_sh, arm64_norm, htr]
      have hcs2 : AddrUpperSaved s0 s_after_sh := hcs_sh.trans_calleeSaved_fs hcsp2 hfs2
      clear hfs2 htr2
      dsimp only [shimRetOff] at hpc2
      apply sepWPp_of_sepWP_lscro (mid := lsρ lsRustAllocSymCli) hcrl2
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcrl3
      apply bind_sepWPp_state; intro s_al
      have hal_al : s_al.spAligned = true :=
        sp_sub_96_spAligned hal0 (by simp only [s_al, arm64_norm, hsp2'])
      have hcs_al : AddrUpperSaved s0 s_al := by
        rcases hcs2 with ⟨h25, h26, h27, h28, hvregs, hfs'⟩
        simp only [s_al, AddrUpperSaved, arm64_norm, *]
      refine addr_call_rocl (name.length, 1) halloc hcrl3
        (by simp only [s_al, arm64_norm, htr2'])
        (by simp only [s_al, arm64_norm, *])
        (by simp only [s_al, arm64_norm, *])
        hal_al
        (ret_pc := (blkPl_580).base + allocRetOff)
        (by simp only [s_al, allocRetOff, arm64_norm, *])
        (F := (x.p ↦ₛ name) ∗ ((x.p + BitVec.ofNat 64 name.length) ↦ₛ (46#8 :: dev)) ∗
          memRegion x.out 32 ∗
          memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - (subStackSize + 96)) ∗
          memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStackSize) 80 ∗
          memRegion (s0.sp - 96#64) 32 ∗
          addrSavedRegs s0.sp s0)
        ?_ (hnext := ?_)
      · dsimp only [Spec.keepsFs, rustAllocSpecWithStack]
        have hpure_al :
            ((s_al.readReg64 .x0).toNat = name.length ∧
              (s_al.readReg64 .x1).toNat = 1 ∧ LayoutOk name.length 1) = True :=
          eq_true ⟨by simp only [s_al, arm64_norm, htoNat],
            by simp only [s_al, arm64_norm], hlay⟩
        have hsp_sh0 : s_sh.sp = s0.sp - 96#64 := by simp only [s_sh, arm64_norm, hsp]
        have hsp_al0 : s_al.sp = s0.sp - 96#64 := by simp only [s_al, arm64_norm, hsp2']
        rw [hpure_al, pure_true, emp_sepConj, hsp_sh0, hsp_al0]
        generalize subStackSize = ssz
        generalize extHookStack = hsz
        exact Entails.of_eq (by ac_rfl)
      · intro s_after_al hcrl4 hpc4 hrun4 hsp4 hcsp4
        dsimp only [Spec.keepsFs, rustAllocSpecWithStack]
        dsimp only [allocRetOff] at hpc4
        rw [sepConj_assoc]
        refine SepWPp.pure_elim fun hfs4 => ?_
        have hx19_4 : s_after_al.readReg64 .x19 = x.out := by
          rw [hcsp4.1]; simp only [s_al, arm64_norm, hx19_2]
        have hx20_4 : s_after_al.readReg64 .x20 = BitVec.ofNat 64 name.length := by
          rw [hcsp4.2.1]; simp only [s_al, arm64_norm, hx20_2]
        have hx21_4 : s_after_al.readReg64 .x21 = x.p := by
          rw [hcsp4.2.2.1]; simp only [s_al, arm64_norm, hx21_2]
        have hx23_4 : s_after_al.readReg64 .x23 = 1#64 := by
          rw [hcsp4.2.2.2.2.1]; simp only [s_al, arm64_norm]
        have hx24_4 : s_after_al.readReg64 .x24 = BitVec.ofNat 64 d := by
          rw [hcsp4.2.2.2.2.2.1]; simp only [s_al, arm64_norm, hx24_2]
        have hsp4' : s_after_al.sp = s0.sp - 96#64 := by
          rw [hsp4]; simp only [s_al, arm64_norm, hsp2']
        clear hsp4
        have hcs4 : AddrUpperSaved s0 s_after_al := hcs_al.trans_calleeSaved_fs hcsp4 hfs4
        clear hfs4
        by_cases hnull : s_after_al.readReg64 .x0 = 0
        · have hnull64 : s_after_al.readReg64 .x0 = 0#64 := hnull
          let _ := hnull64
          let _ := hx23_4
          simp only [hnull, ↓reduceIte, sepConj_assoc]
          refine sepWPp_pull_pure3 fun htr_oom => ?_
          have htr_al : s_al.trace = s0.trace := by simp only [s_al, arm64_norm, htr2']
          apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym580)
          wp_steps
          apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          refine SepWPp.panic (by simp only [arm64_norm, *])
            (by simpa only [arm64_norm] using hpanic)
            (addrPanicAllow_of_eq
              (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htr_oom, htr_al])).1)
        · set ptr := s_after_al.readReg64 .x0 with hptr_def
          have hptr_ne : ptr ≠ 0#64 := hnull
          have hptr_beq : (ptr == 0#64) = false := beq_eq_false_iff_ne.mpr hptr_ne
          have hptr_bne : (ptr != 0#64) = true := bne_iff_ne.mpr hptr_ne
          have _ := And.intro hptr_beq hptr_bne
          simp only [hnull, ↓reduceIte, sepConj_assoc]
          refine sepWPp_pull_pure3 fun ⟨_, htr_ok⟩ => ?_
          have htr4' : s_after_al.trace = s0.trace := by
            rw [htr_ok]; simp only [s_al, arm64_norm, htr2']
          apply sepWPp_of_sepWP_lscro (mid := lsρ memcpyName) hcrl4
          wp_steps
          apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          intro hcrl5
          apply bind_sepWPp_state; intro s_cp
          have hal_cp : s_cp.spAligned = true :=
            sp_sub_96_spAligned hal0 (by simp only [s_cp, arm64_norm, hsp4'])
          have hcs_cp : AddrUpperSaved s0 s_cp := by
            rcases hcs4 with ⟨h25, h26, h27, h28, hvregs, hfs'⟩
            simp only [s_cp, AddrUpperSaved, arm64_norm, *]
          refine addr_call_rocl (ptr, x.p, name) hmemcpy hcrl5
            (by simp only [s_cp, arm64_norm, htr4'])
            (by simp only [s_cp, arm64_norm, *])
            (by simp only [s_cp, arm64_norm, *])
            hal_cp
            (ret_pc := (blkPl_580).base + memcpyRetOff)
            (by simp only [s_cp, memcpyRetOff, arm64_norm, *])
            (F := A.pool ∗ A.live ptr name.length 1 ∗
              ((x.p + BitVec.ofNat 64 name.length) ↦ₛ (46#8 :: dev)) ∗
              memRegion x.out 32 ∗
              memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - (subStackSize + 96)) ∗
              memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStackSize) 80 ∗
              memRegion (s0.sp - 96#64) 32 ∗
              addrSavedRegs s0.sp s0)
            ?_ (hnext := ?_)
          · dsimp only [Spec.keepsFs, session2MemcpySpecX]
            have hpure_cp :
                (s_cp.readReg64 .x0 = ptr ∧ s_cp.readReg64 .x1 = x.p ∧
                  (s_cp.readReg64 .x2).toNat = name.length) = True :=
              eq_true ⟨by simp only [s_cp, arm64_norm, hptr_def.symm],
                by simp only [s_cp, arm64_norm],
                by simp only [s_cp, arm64_norm, htoNat]⟩
            have hsp_al0 : s_al.sp = s0.sp - 96#64 := by simp only [s_al, arm64_norm, hsp2']
            have hsp_cp0 : s_cp.sp = s0.sp - 96#64 := by simp only [s_cp, arm64_norm, hsp4']
            rw [hpure_cp, pure_true, emp_sepConj, hsp_al0, hsp_cp0]
            generalize subStackSize = ssz
            generalize extHookStack = hsz
            exact Entails.of_eq (by ac_rfl)
          · intro s_ep hcrl6 hpc6 hrun6 hsp6 hcsp6
            let _ := hcrl6
            dsimp only [Spec.keepsFs, session2MemcpySpecX]
            dsimp only [memcpyRetOff] at hpc6
            rw [sepConj_assoc]
            refine SepWPp.pure_elim fun hfs6 => ?_
            rw [sepConj_assoc]
            refine SepWPp.pure_elim fun ⟨_, htr6⟩ => ?_
            have hx19_6 : s_ep.readReg64 .x19 = x.out := by
              rw [hcsp6.1]; simp only [s_cp, arm64_norm, hx19_4]
            have hx20_6 : s_ep.readReg64 .x20 = BitVec.ofNat 64 name.length := by
              rw [hcsp6.2.1]; simp only [s_cp, arm64_norm, hx20_4]
            have hx22_6 : s_ep.readReg64 .x22 = ptr := by
              rw [hcsp6.2.2.2.1]; simp only [s_cp, arm64_norm, hptr_def.symm]
            have hx24_6 : s_ep.readReg64 .x24 = BitVec.ofNat 64 d := by
              rw [hcsp6.2.2.2.2.2.1]; simp only [s_cp, arm64_norm, hx24_4]
            have hsp6' : s_ep.sp = s0.sp - 96#64 := by
              rw [hsp6]; simp only [s_cp, arm64_norm, hsp4']
            clear hsp6
            have _hal6 : s_ep.spAligned = true := sp_sub_96_spAligned hal0 hsp6'
            have htr6' : s_ep.trace = s0.trace := by
              rw [htr6]; simp only [s_cp, arm64_norm, htr4']
            have hcs6 : AddrUpperSaved s0 s_ep := hcs_cp.trans_calleeSaved_fs hcsp6 hfs6
            clear hfs6 htr6
            rcases hcs6 with ⟨h25, h26, h27, h28, hvregs, hfs6'⟩
            let _ := And.intro hx19_6 (And.intro hx20_6 (And.intro hx22_6 hx24_6))
            rw [out32_open_some x.out, addrSavedRegs_at_frame hsp6' s0]
            simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
            refine SepWPp.exists_elim fun b24 =>
              SepWPp.exists_elim fun w2 =>
              SepWPp.exists_elim fun w1 =>
              SepWPp.exists_elim fun w0 => ?_
            apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
            wp_steps
            apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            refine ⟨by simp only [arm64_norm, *],
              by simp only [CalleeSavedPreserved, arm64_norm, *], ?_⟩
            have hsp_cp0 : s_cp.sp = s0.sp - 96#64 := by simp only [s_cp, arm64_norm, hsp4']
            rw [hsp_cp0, ← hptr_def]
            let g : AddrGhost := ⟨⟨BitVec.ofNat 64 name.length, ptr, name⟩, BitVec.ofNat 8 d⟩
            have hpa := protocolAddressAt_pos_init A x.out ptr name (BitVec.ofNat 8 d)
              hpos hlt63 hptr_ne
            have hpack := stackAt_addr_pack s0.sp resStack s0 hstk hstkle
            rw [addrSavedRegs_at_frame hsp6' s0] at hpack
            have hbs_join :
                ((x.p ↦ₛ name) ∗ ((x.p + BitVec.ofNat 64 name.length) ↦ₛ (46#8 :: dev))) =
                  (x.p ↦ₛ x.bs) := by
              rw [hbs_eq, pointsToBytes_append]
            dsimp only [addressSpec]
            rw [hsome]
            dsimp only []
            refine Entails.pure_right
              ⟨by simp only [arm64_norm, htr6'], by simp only [arm64_norm, hfs6']⟩ ?_
            have hg_pure :
                (g.name.bytes = name ∧ g.name.cap = BitVec.ofNat 64 name.length ∧
                  g.device = BitVec.ofNat 8 d) := ⟨rfl, rfl, rfl⟩
            refine Entails.trans ?_
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (Entails.sepExists_right g (Entails.pure_right hg_pure hpa)))))
            refine Entails.trans ?_
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hpack)))
            rw [← addrSavedRegs_at_frame hsp6' s0, ← hbs_join, stackAt_sub_hook (s0.sp - 96#64)]
            generalize subStackSize = ssz
            generalize extHookStack = hsz
            exact Entails.of_eq (by ac_rfl)
  · have hnone : addrParse uuidTryParse x.bs = none := by
      simp [addrParse, hrsplit, hsid, hdev, hd127]
    have htrunc_d8 : (BitVec.ofNat 64 d).truncate 8 = BitVec.ofNat 8 d := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat]
    have hsle : ((BitVec.ofNat 8 d).signExtend 32).sle 0#32 = true := by
      rw [← htrunc_d8, sxtb_le_zero_iff d hd255]
      exact decide_eq_true hd127
    clear hFs hpan hcrl
    dsimp only [sxtbCheckOff] at hpc ⊢
    apply SepWPp.of_sepWP (mid := (blkPl_580).base + noneExitOff)
    wp_steps
    apply SepWP.done
      (by simp only [noneExitOff, arm64_norm, *])
      (by simp only [arm64_norm, *])
    have hbs_join :
        ((x.p ↦ₛ name) ∗ ((x.p + BitVec.ofNat 64 name.length) ↦ₛ (46#8 :: dev))) =
          (x.p ↦ₛ x.bs) := by
      rw [hbs_eq, pointsToBytes_append]
    refine SepWPp.weaken_pre (by rw [← sepConj_assoc, hbs_join]; exact Entails.refl _) ?_
    exact step_none_exit_placed hstk hstkle x hnone hal0
      (by simp only [noneExitOff, arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, hx19])
      (by rcases hcs with ⟨h25, h26, h27, h28, hvregs, hfs⟩; simp only [AddrUpperSaved, arm64_norm, *])

end CryptoVerification.SignalSession.Cli.MainHops.Address.Helpers
