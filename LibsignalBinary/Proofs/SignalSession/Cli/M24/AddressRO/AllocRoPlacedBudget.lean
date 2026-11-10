/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRO.AllocRoBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.AllocPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Placed Budgeted Read-Only `argv` Exit and Allocation Paths for `signal_session::address`

Establishes `step_none_exit_ro_placed` and `step_sxtb_and_alloc_ro_placed` on Block `580` against
`M24.CalleesRO.addressSpecRO` for read-only (`↦ᵣ`) input slices.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRO.AllocRoPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack memcpyName withStack)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost serviceIdParse uuidTryParse)
open CryptoVerification.RustHeap (LayoutOk)
open CryptoVerification.SignalSession (lsRustAllocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddressCall addrParse parseUnsigned rsplitDot serviceIdParse_length)
open CryptoVerification.SignalSession.Cli.MainHops.Address.Helpers
  (AddrUpperSaved addrSavedRegs addrSavedRegs_at_frame allocRetOff bind_sepWPp_state
   memcpyRetOff noneExitOff out32_open_none out32_open_some protocolAddressAt_pos_init
   sepWPp_of_sepWP_lscro sepWPp_pull_pure3 shimRetOff sp_sub_96_spAligned stackAt_addr_pack
   stackAt_sub_hook subStackSize sxtbCheckOff sxtb_le_zero_iff)
open CryptoVerification.SignalSession.Cli.Placed (blkLib_eq_580 blkPC_580 blkPl_580 lsProg_580)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyRegionROSpec)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
   VmPreserved not_nullAllowed_of_fitsAllocEvents rustAllocEvents)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliAllocBudgetSpecWithStack)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWPp_seg_ls_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRO.AllocRoBudget (AddrGoalPostRO)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (addressSpecRO)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
  (AddressEnv addressEvents fitsEvents_address_of_fitsEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.AllocBudget (AddrFrameCommon)
open scoped LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.AllocPlacedBudget
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.AllocPlacedBudget
  (AddrPanicFalse addr_call_rocl_nopan)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsFsPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (session2ShimBudgetSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustAllocSpecWithStack)

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## Read-only `memcpy` call-site specification -/

/-- Read-only-source twin of `session2MemcpyBudgetSpecX` (`src ↦ᵣ bs`, `dst ↦ₛ bs`). -/
def session2MemcpyROBudgetSpecX : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗ (src ↦ᵣ bs) ∗ stackAt s0.sp extHookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ᵣ bs) ∗ stackAt s0.sp extHookStack

theorem memcpy2_ro_rocl [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {H : LibsignalHooks}
    {prog : Program} {i : Nat} [IsLsBlockProg prog i H]
    (hA : AllocContractsFsPlaced A lim H) (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ memcpyName)
      (withLsRoCl lsmpl session2MemcpyROBudgetSpecX.keepsFs) := by
  refine subroutine_ok_mono
    (LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlacedBudget.AllocContractsFsPlaced.session_memcpy_region_ro_rocl
      hA extHookStack (by decide) (by decide) hi) ?_ ?_
  · intro ⟨dst, src, bs⟩ R s0 hp
    dsimp only [withLsRoCl, Spec.keepsFs, withStack, withVmPreserved,
      sessionMemcpyRegionROSpec, session2MemcpyROBudgetSpecX] at hp ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    rcases hp with ⟨⟨hx0, hx1, hx2⟩, hrest⟩
    have hlen : bs.length ≤ 2 ^ 64 := by
      have hlt : (s0.readReg64 .x2).toNat < 2 ^ 64 := (s0.readReg64 .x2).isLt
      omega
    exact ⟨⟨hx0, hx1, hx2, hlen⟩, hrest⟩
  · intro ⟨dst, src, bs⟩ R s0 sf hq
    dsimp only [withLsRoCl, Spec.keepsFs, withStack, withVmPreserved,
      sessionMemcpyRegionROSpec, session2MemcpyROBudgetSpecX] at hq ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hro, hfs, hvm, ⟨hx0, htr⟩, hrest⟩
    exact ⟨hro, hfs, ⟨hx0, htr, hvm⟩, hrest⟩

private theorem serviceIdParse_bv_props_ro {name : List (BitVec 8)}
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

/-! ## Error-exit block (`+352 .. +380`) -/

theorem step_none_exit_ro_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
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
      ((x.p ↦ᵣ x.bs) ∗ memRegion x.out 32 ∗ AddrFrameCommon A lim resStack st s0 s)
      (AddrGoalPostRO A lim resStack x st s0)
      AddrPanicFalse := by
  have _hal : s.spAligned = true := sp_sub_96_spAligned hal0 hsp
  dsimp only [noneExitOff] at hpc ⊢
  rcases hcs with ⟨h25, h26, h27, h28, hvregs, hfs⟩
  rw [out32_open_none x.out]
  unfold AddrFrameCommon
  rw [addrSavedRegs_at_frame hsp s0]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w0 => ?_
  apply sepWPp_seg_ls_vm (Q := (blkPC_580).rebase (blkPl_580).base (hooksException H))
    blkLib_eq_580 (mid := s0.readReg64 .lr)
  intro _m_strip
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    fun _m_real _hnsp => ?_
  refine ProofLib.SepWPp.transport_budgetPool
    (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])) (hnext := ?_)
  apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine ⟨by simp only [arm64_norm, *], by simp only [CalleeSavedPreserved, arm64_norm, *], ?_⟩
  dsimp only [addressSpecRO]
  apply Entails.sepExists_right ([] : List AllocEvent)
  have hstep_nil : M.stepEvents ([] : List AllocEvent) st = st := by
    simp [AllocCostModel.stepEvents]
  rw [hstep_nil, hnone]
  dsimp only []
  have hpack := stackAt_addr_pack s0.sp resStack s0 hstk hstkle
  have henv : AddressEnv uuidTryParse x [] := by
    simp [AddressEnv, addressEvents, hnone]
  refine Entails.pure_right
    ⟨by simp only [arm64_norm, htr], by simp only [arm64_norm, hfs], henv⟩ ?_
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hpack)))
  dsimp only [addrSavedRegs]
  generalize subStackSize = ssz
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## Allocation and copy blocks (`+256 .. +284` and `+384 .. +468`) -/

set_option maxHeartbeats 800000 in
theorem step_sxtb_and_alloc_ro_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {resStack : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hstk : 0xB0 + extHookStack ≤ resStack)
    (hstkle : resStack ≤ 2 ^ 64)
    (x : AddressCall)
    (hfit : FitsEnv M lim st (AddressEnv uuidTryParse x))
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
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
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
      ((x.p ↦ᵣ name) ∗ ((x.p + BitVec.ofNat 64 name.length) ↦ᵣ (46#8 :: dev)) ∗
        memRegion x.out 32 ∗ AddrFrameCommon A lim resStack st s0 s)
      (AddrGoalPostRO A lim resStack x st s0)
      AddrPanicFalse := by
  by_cases hd127 : 1 ≤ d ∧ d ≤ 127
  · have hsome : addrParse uuidTryParse x.bs = some ⟨name, BitVec.ofNat 8 d⟩ := by
      simp [addrParse, hrsplit, hsid, hdev, hd127]
    have hfit_ev : FitsEvents M lim st (rustAllocEvents name.length 1) := by
      have hf := fitsEvents_address_of_fitsEnv M lim st uuidTryParse x hfit
      simpa [addressEvents, hsome] using hf
    obtain ⟨hpos, hlt63, htbz63, hne0, hbeq0, htoNat, hlay⟩ := serviceIdParse_bv_props_ro hsid
    have hrlay : RustLayoutOk name.length 1 := ⟨hlay, by decide⟩
    have htrunc_d8 : (BitVec.ofNat 64 d).truncate 8 = BitVec.ofNat 8 d := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat]
    have hsle_f : ((BitVec.ofNat 8 d).signExtend 32).sle 0#32 = false := by
      rw [← htrunc_d8, sxtb_le_zero_iff d hd255]
      exact decide_eq_false (not_not.mpr hd127)
    have hshim := LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlacedBudget.AllocContractsFsPlaced.shim2_rocl
      hFs (prog := lsProg_580 H) (i := 580)
    have halloc := LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlacedBudget.AllocContractsFsPlaced.alloc_rocl
      hFs (prog := lsProg_580 H) (i := 580)
    have hmemcpy := memcpy2_ro_rocl hFs (prog := lsProg_580 H) (i := 580)
    clear hFs
    dsimp only [lsProg_580, sxtbCheckOff] at hshim halloc hmemcpy hpc ⊢
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
    have hvm_sh : VmPreserved s s_sh := by simp only [s_sh, arm64_norm]
    refine addr_call_rocl_nopan () hshim hcrl1
      (by simp only [s_sh, arm64_norm, *])
      (by simp only [s_sh, arm64_norm, *])
      hal_sh
      (ret_pc := (blkPl_580).base + shimRetOff)
      (by simp only [s_sh, shimRetOff, arm64_norm, *])
      (F := (x.p ↦ᵣ name) ∗ ((x.p + BitVec.ofNat 64 name.length) ↦ᵣ (46#8 :: dev)) ∗
        memRegion x.out 32 ∗
        memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - (subStackSize + 96)) ∗
        memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStackSize) 80 ∗
        memRegion (s0.sp - 96#64) 32 ∗
        addrSavedRegs s0.sp s0 ∗ A.pool lim st s_sh)
      ?_ (hnext := ?_)
    · unfold AddrFrameCommon
      rw [A.pool_of_vmPreserved hvm_sh, stackAt_sub_hook (s0.sp - 96#64)]
      dsimp only [Spec.keepsFs, session2ShimBudgetSpecX]
      have hsp_sh : s_sh.sp = s0.sp - 96#64 := by simp only [s_sh, arm64_norm, hsp]
      rw [hsp_sh]
      generalize subStackSize = ssz
      generalize extHookStack = hsz
      exact Entails.of_eq (by sep_ac_rfl)
    · intro s_after_sh hcrl2 hpc2 hrun2 hsp2 hcsp2
      dsimp only [Spec.keepsFs, session2ShimBudgetSpecX]
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun hfs2 => ?_
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨htr2, hvm2⟩ => ?_
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
      have hvm_sh_al : VmPreserved s_sh s_al :=
        hvm2.trans (by simp only [s_al, arm64_norm])
      refine addr_call_rocl_nopan (name.length, 1, st) halloc hcrl3
        (by simp only [s_al, arm64_norm, *])
        (by simp only [s_al, arm64_norm, *])
        hal_al
        (ret_pc := (blkPl_580).base + allocRetOff)
        (by simp only [s_al, allocRetOff, arm64_norm, *])
        (F := (x.p ↦ᵣ name) ∗ ((x.p + BitVec.ofNat 64 name.length) ↦ᵣ (46#8 :: dev)) ∗
          memRegion x.out 32 ∗
          memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - (subStackSize + 96)) ∗
          memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStackSize) 80 ∗
          memRegion (s0.sp - 96#64) 32 ∗
          addrSavedRegs s0.sp s0)
        ?_ (hoom := ?_) (hnext := ?_)
      · dsimp only [Spec.keepsFs, rustAllocSpecWithStack, rustCliAllocBudgetSpecWithStack]
        have hpure_al :
            ((s_al.readReg64 .x0).toNat = name.length ∧
              (s_al.readReg64 .x1).toNat = 1 ∧ RustLayoutOk name.length 1 ∧
              _root_.LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624
                (s_al.readReg64 .lr)) = True :=
          eq_true ⟨by simp only [s_al, arm64_norm, htoNat],
            by simp only [s_al, arm64_norm], hrlay,
            by
              rw [show s_al.readReg64 .lr = (blkPl_580).base + 408#64 by
                simp only [s_al, arm64_norm, *]]
              simpa only [blkPl_580] using
                _root_.LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_blockPlacement_base_add
                  580 408#64 (by decide) (by decide)⟩
        have hsp_sh0 : s_sh.sp = s0.sp - 96#64 := by simp only [s_sh, arm64_norm, hsp]
        have hsp_al0 : s_al.sp = s0.sp - 96#64 := by simp only [s_al, arm64_norm, hsp2']
        rw [A.pool_of_vmPreserved hvm_sh_al, hpure_al, pure_true, emp_sepConj, hsp_sh0, hsp_al0]
        generalize subStackSize = ssz
        generalize extHookStack = hsz
        exact Entails.of_eq (by sep_ac_rfl)
      · intro sf R' _ hoom_m
        dsimp only [Spec.keepsFs, rustAllocSpecWithStack, rustCliAllocBudgetSpecWithStack] at hoom_m
        rw [satisfies_pure_sepConj] at hoom_m
        exact hoom_m.1.1 hfit_ev
      · intro s_after_al hcrl4 hpc4 hrun4 hsp4 hcsp4
        dsimp only [Spec.keepsFs, rustAllocSpecWithStack, rustCliAllocBudgetSpecWithStack]
        dsimp only [allocRetOff] at hpc4
        rw [sepConj_assoc]
        refine SepWPp.pure_elim fun hfs4 => ?_
        rw [sepConj_assoc]
        refine SepWPp.pure_elim fun hacp4 => ?_
        have hx19_4 : s_after_al.readReg64 .x19 = x.out := by
          rw [hcsp4.1]; simp only [s_al, arm64_norm, hx19_2]
        have hx20_4 : s_after_al.readReg64 .x20 = BitVec.ofNat 64 name.length := by
          rw [hcsp4.2.1]; simp only [s_al, arm64_norm, hx20_2]
        have hx21_4 : s_after_al.readReg64 .x21 = x.p := by
          rw [hcsp4.2.2.1]; simp only [s_al, arm64_norm, hx21_2]
        have hx24_4 : s_after_al.readReg64 .x24 = BitVec.ofNat 64 d := by
          rw [hcsp4.2.2.2.2.2.1]; simp only [s_al, arm64_norm, hx24_2]
        have hsp4' : s_after_al.sp = s0.sp - 96#64 := by
          rw [hsp4]; simp only [s_al, arm64_norm, hsp2']
        clear hsp4
        have htr4' : s_after_al.trace = s0.trace := by
          rw [hacp4.2.1]; simp only [s_al, arm64_norm, htr2']
        have hcs4 : AddrUpperSaved s0 s_after_al := hcs_al.trans_calleeSaved_fs hcsp4 hfs4
        clear hfs4 hacp4
        by_cases hnull : s_after_al.readReg64 .x0 = 0
        · simp only [hnull, ↓reduceIte, sepConj_assoc]
          refine sepWPp_pull_pure3 fun hna => ?_
          exact (not_nullAllowed_of_fitsAllocEvents hrlay hfit_ev hna).elim
        · set ptr := s_after_al.readReg64 .x0 with hptr_def
          have hptr_ne : ptr ≠ 0#64 := hnull
          have hptr_beq : (ptr == 0#64) = false := beq_eq_false_iff_ne.mpr hptr_ne
          have hptr_bne : (ptr != 0#64) = true := bne_iff_ne.mpr hptr_ne
          have _ := And.intro hptr_beq hptr_bne
          let st' := M.stepEvents (rustAllocEvents name.length 1) st
          simp only [hnull, ↓reduceIte, Bool.false_eq_true, sepConj_assoc]
          refine sepWPp_pull_pure3 fun _ => ?_
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
          have hvm_al_cp : VmPreserved s_after_al s_cp := by
            simp only [s_cp, arm64_norm]
          refine addr_call_rocl_nopan (ptr, x.p, name) hmemcpy hcrl5
            (by simp only [s_cp, arm64_norm, *])
            (by simp only [s_cp, arm64_norm, *])
            hal_cp
            (ret_pc := (blkPl_580).base + memcpyRetOff)
            (by simp only [s_cp, memcpyRetOff, arm64_norm, *])
            (F := A.pool lim st' s_cp ∗ A.live ptr name.length 1 ∗
              ((x.p + BitVec.ofNat 64 name.length) ↦ᵣ (46#8 :: dev)) ∗
              memRegion x.out 32 ∗
              memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - (subStackSize + 96)) ∗
              memRegion ((s0.sp - 96#64) - BitVec.ofNat 64 subStackSize) 80 ∗
              memRegion (s0.sp - 96#64) 32 ∗
              addrSavedRegs s0.sp s0)
            ?_ (hnext := ?_)
          · dsimp only [Spec.keepsFs, session2MemcpyROBudgetSpecX]
            have hpure_cp :
                (s_cp.readReg64 .x0 = ptr ∧ s_cp.readReg64 .x1 = x.p ∧
                  (s_cp.readReg64 .x2).toNat = name.length) = True :=
              eq_true ⟨by simp only [s_cp, arm64_norm, hptr_def.symm],
                by simp only [s_cp, arm64_norm],
                by simp only [s_cp, arm64_norm, htoNat]⟩
            have hsp_al0 : s_al.sp = s0.sp - 96#64 := by simp only [s_al, arm64_norm, hsp2']
            have hsp_cp0 : s_cp.sp = s0.sp - 96#64 := by simp only [s_cp, arm64_norm, hsp4']
            rw [A.pool_of_vmPreserved hvm_al_cp, hpure_cp, pure_true, emp_sepConj, hsp_al0, hsp_cp0]
            generalize subStackSize = ssz
            generalize extHookStack = hsz
            exact Entails.of_eq (by sep_ac_rfl)
          · intro s_ep hcrl6 hpc6 hrun6 hsp6 hcsp6
            let _ := hcrl6
            dsimp only [Spec.keepsFs, session2MemcpyROBudgetSpecX]
            dsimp only [memcpyRetOff] at hpc6
            rw [sepConj_assoc]
            refine SepWPp.pure_elim fun hfs6 => ?_
            rw [sepConj_assoc]
            refine SepWPp.pure_elim fun ⟨_, htr6, hvm6⟩ => ?_
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
            rw [← A.pool_of_vmPreserved hvm6, out32_open_some x.out, addrSavedRegs_at_frame hsp6' s0]
            simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
            refine SepWPp.exists_elim fun b24 =>
              SepWPp.exists_elim fun w2 =>
              SepWPp.exists_elim fun w1 =>
              SepWPp.exists_elim fun w0 => ?_
            apply sepWPp_seg_ls_vm (Q := (blkPC_580).rebase (blkPl_580).base (hooksException H))
              blkLib_eq_580 (mid := s0.readReg64 .lr)
            intro _m_strip
            wp_steps
            refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              fun _m_real _hnsp => ?_
            refine ProofLib.SepWPp.transport_budgetPool
              (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])) (hnext := ?_)
            apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            refine ⟨by simp only [arm64_norm, *],
              by simp only [CalleeSavedPreserved, arm64_norm, *], ?_⟩
            have hsp_cp0 : s_cp.sp = s0.sp - 96#64 := by simp only [s_cp, arm64_norm, hsp4']
            rw [hsp_cp0, ← hptr_def]
            let g : AddrGhost := ⟨⟨BitVec.ofNat 64 name.length, ptr, name⟩, BitVec.ofNat 8 d⟩
            have hpa := protocolAddressAt_pos_init A.repAlloc x.out ptr name (BitVec.ofNat 8 d)
              hpos hlt63 hptr_ne
            have hpack := stackAt_addr_pack s0.sp resStack s0 hstk hstkle
            have hbs_join :
                ((x.p ↦ᵣ name) ∗ ((x.p + BitVec.ofNat 64 name.length) ↦ᵣ (46#8 :: dev))) =
                  (x.p ↦ᵣ x.bs) := by
              rw [hbs_eq, pointsToBytesRO_append]
            dsimp only [addressSpecRO]
            apply Entails.sepExists_right (rustAllocEvents name.length 1)
            rw [hsome]
            dsimp only []
            have henv : AddressEnv uuidTryParse x (rustAllocEvents name.length 1) := by
              simp [AddressEnv, addressEvents, hsome]
            refine Entails.pure_right
              ⟨by simp only [arm64_norm, htr6'], by simp only [arm64_norm, hfs6'], henv⟩ ?_
            have hg_pure :
                (g.name.bytes = name ∧ g.name.cap = BitVec.ofNat 64 name.length ∧
                  g.device = BitVec.ofNat 8 d) := ⟨rfl, rfl, rfl⟩
            refine Entails.trans ?_
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (Entails.sepExists_right g (Entails.pure_right hg_pure hpa)))))
            refine Entails.trans ?_
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hpack)))
            dsimp only [addrSavedRegs]
            rw [← hbs_join, stackAt_sub_hook (s0.sp - 96#64),
              show s0.sp - 96#64 - BitVec.ofNat 64 subStackSize = s0.sp - 16560#64 by
                clear * -; dsimp only [subStackSize, extHookStack]; bv_omega]
            generalize subStackSize = ssz
            generalize extHookStack = hsz
            exact Entails.of_eq (by sep_ac_rfl)
  · have hnone : addrParse uuidTryParse x.bs = none := by
      simp [addrParse, hrsplit, hsid, hdev, hd127]
    have htrunc_d8 : (BitVec.ofNat 64 d).truncate 8 = BitVec.ofNat 8 d := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat]
    have hsle : ((BitVec.ofNat 8 d).signExtend 32).sle 0#32 = true := by
      rw [← htrunc_d8, sxtb_le_zero_iff d hd255]
      exact decide_eq_true hd127
    clear hFs hcrl hfit
    dsimp only [sxtbCheckOff] at hpc ⊢
    apply SepWPp.of_sepWP (mid := (blkPl_580).base + noneExitOff)
    wp_steps
    apply SepWP.done
      (by simp only [noneExitOff, arm64_norm, *])
      (by simp only [arm64_norm, *])
    transport_addr_frame
    have hbs_join :
        ((x.p ↦ᵣ name) ∗ ((x.p + BitVec.ofNat 64 name.length) ↦ᵣ (46#8 :: dev))) =
          (x.p ↦ᵣ x.bs) := by
      rw [hbs_eq, pointsToBytesRO_append]
    refine SepWPp.weaken_pre (by rw [← sepConj_assoc, hbs_join]; exact Entails.refl _) ?_
    exact step_none_exit_ro_placed hstk hstkle x hnone hal0
      (by simp only [noneExitOff, arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, hx19])
      (by rcases hcs with ⟨h25, h26, h27, h28, hvregs, hfs⟩; simp only [AddrUpperSaved, arm64_norm, *])

end LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRO.AllocRoPlacedBudget
