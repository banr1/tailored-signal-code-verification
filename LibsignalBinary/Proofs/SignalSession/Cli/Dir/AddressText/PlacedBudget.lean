/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.PlacedBudgetAux
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
public meta import ProofLib.SepLogic.WP -- shake: keep
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup

/-!
# Budget-Threaded `[LibsignalPlacement]` `signal_session::stores::address_text`

Verifies the epilogue and top-level budget-threaded contracts (`addrText_placed_ok_of_deps` and
`addrText_placed_caller_ok_of_deps`) for `signal_session::stores::address_text` (Block 594) against
`SpecsPlacedBudget.addrTextSpecPlaced`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.PlacedBudget

open Arm64 ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsmpl lsρ)
open CryptoVerification.RustHeap (vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt)
open CryptoVerification.LibsignalTripleRatchet (extHookStack reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Wire
  (layoutOk_align1 vecU8Buf vecU8BufRest)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded extract_withLsCodeRoLoaded sepWPp_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli
  (AddrTextGhost addressText decimalText)
open CryptoVerification.SignalSession.Cli.Placed
  (blkLib_eq_594 blkPC_594 blkPl_594 lsProg_594)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
  (ls_transfer_lscro satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.AddressText.Helpers
  (addrCalleeSavedAt addrCalleeSavedAt_entails_memRegion64 addressText_val_eq
   allocRetOff cells24_entails_memRegion dCap_beq_zero_false dCap_ne_zero
   decRetOff dec_buf_to_dealloc decimalText_device_pos device_zeroExtend32_toNat
   entails_of_eq frameOff memRegion24_cells memRegion64_cells memcpy0RetOff
   memcpy1RetOff preservedTailRegs preservedTailRegs_elim preservedTailRegs_mk
   protocolAddressAt_close protocolAddressAt_open res0RetOff res1RetOff
   sepWPp_exists_elim sepWPp_fold sepWPp_weaken_pre shimRetOff
   spAligned_sub112 stackAt_frame112_split stackAt_sub_le step_entails
   stk_le_two_pow_64 vecU8_from_moved_header)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget RustLayoutOk rustDeallocEvents)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget
  (doReserveSpecOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.StepsPrefixBudget
  (decimalInnerSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced addrTextSpecPlaced decimalSpecPlaced)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
  (dealloc_lscro_of_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.PlacedBudgetAux
  (addrDecReserveEvents addrDotReserveEvents addrTextEnv_intro addrToOwnedEvents
   blk594_noSvc0 fits_toOwned_of_addrTextEnv sepWPp_weaken_pre_state stepEvents_addrText
   step_append_dec_p step_dot_and_decimal_p step_prologue_to_owned_p)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  frameOff shimRetOff allocRetOff memcpy0RetOff res0RetOff decRetOff res1RetOff memcpy1RetOff

abbrev AddrTextEnv := PlacedBudgetAux.AddrTextEnv

private theorem calleeSaved_trans {s0 s1 s2 : State}
    (h1 : CalleeSavedPreserved s0 s1) (h2 : CalleeSavedPreserved s1 s2) :
    CalleeSavedPreserved s0 s2 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
   h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.1.trans h1.2.2.2.2.1,
   h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1, h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2.2.2.2.2.2⟩

local macro "wp_steps_sync_594 " mid:term : tactic => `(tactic| (
  apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
    (Q := (blkPC_594).rebase (blkPl_594).base
      (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException _))
    blkLib_eq_594 blk594_noSvc0 (mid := $mid)
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm, *]))
    (hnext := ?_)
  refine ProofLib.SepWP.done
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) ?_
))

/-! ## 1. Segment 4 (`224 .. 280` + tailcall `b __rust_dealloc`) -/

private theorem step_epilogue_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {H : LibsignalHooks} {subStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hstk : 112 + subStk ≤ stk) (hext_stk : extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    {x : AddrTextGhost} {st0 : M.σ} {evsDec : List AllocEvent}
    {R : SepProp} {s0 s : State}
    {sp' capF ptrF dCap dPtr : BitVec 64}
    (hDecEv : DecEnv (x.g.device.zeroExtend 32) evsDec)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_594).base + memcpy1RetOff)
    (hrun : s.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hsp : s.sp = sp')
    (hsp_def : s0.sp - 112#64 = sp')
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = dPtr)
    (hx21 : s.readReg64 .x21 =
      BitVec.ofNat 64 (decimalText (x.g.device.zeroExtend 32).toNat).length)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 (x.g.name.bytes ++ [0x2e#8]).length)
    (hvregs : preservedTailRegs s = preservedTailRegs s0)
    (hd_le : (decimalText (x.g.device.zeroExtend 32).toNat).length ≤ dCap.toNat)
    (hd_63 : dCap.toNat < 2 ^ 63)
    (hlr0 : LsRetAddr624 (s0.readReg64 .x30)) :
    SepWPp (lsProg_594 H) (s0.readReg64 .lr) s
      ((sp' ↦₆₄ capF) ∗ ((sp' + 8#64) ↦₆₄ ptrF) ∗
        ((sp' + 16#64) ↦₆₄ BitVec.ofNat 64 (x.g.name.bytes ++ [0x2e#8]).length) ∗
        vecU8Buf A.repAlloc capF ptrF ((x.g.name.bytes ++ [0x2e#8]) ++
          decimalText (x.g.device.zeroExtend 32).toNat) ∗
        ((sp' + 24#64) ↦₆₄ dCap) ∗ ((sp' + 32#64) ↦₆₄ dPtr) ∗
        ((sp' + 40#64) ↦₆₄
          BitVec.ofNat 64 (decimalText (x.g.device.zeroExtend 32).toNat).length) ∗
        (dPtr ↦ₛ decimalText (x.g.device.zeroExtend 32).toNat) ∗
        vecU8BufRest A.repAlloc dCap dPtr (decimalText (x.g.device.zeroExtend 32).toNat) ∗
        addrCalleeSavedAt sp' s0 ∗
        protocolAddressAt A.repAlloc x.g x.addr ∗
        memRegion x.ret 24 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 112)) ∗
        stackAt sp' subStk ∗
        A.pool lim
          (M.stepEvents (addrDecReserveEvents x.g.name.bytes x.g.device)
            (M.stepEvents evsDec
              (M.stepEvents (addrDotReserveEvents x.g.name.bytes)
                (M.stepEvents (addrToOwnedEvents x.g.name.bytes) st0)))) s)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (addrTextSpecPlaced A lim (AddrTextEnv DecEnv) stk).post (x, st0) s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (addrTextSpecPlaced A lim (AddrTextEnv DecEnv) stk).onPanic (x, st0) s0 sf ∗ R)) := by
  obtain ⟨hx25, hx26, hx27, hx28, hvregs0⟩ := preservedTailRegs_elim hvregs
  generalize hdec_def : decimalText (x.g.device.zeroExtend 32).toNat = dec at hx21 hd_le ⊢
  generalize hpfx_def : x.g.name.bytes ++ [0x2e#8] = pfx at hx22 ⊢
  have hdealloc := dealloc_lscro_of_cli (callerProg := lsProg_594 H) hC
  have hdec_pos : 0 < dec.length := by
    subst hdec_def; rw [device_zeroExtend32_toNat]; exact decimalText_device_pos x.g.device
  have hdCap_nz : dCap ≠ 0#64 := dCap_ne_zero hdec_pos hd_le
  have hdCap_beq : (dCap == 0#64) = false := dCap_beq_zero_false hdec_pos hd_le
  have hdCap_pos : 0 < dCap.toNat := by omega
  have hlay_d : RustLayoutOk dCap.toNat 1 := ⟨layoutOk_align1 hdCap_pos (by omega), by decide⟩
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
      s1.pc = lsρ lsRustDeallocSymCli →
      s1.status = .Running →
      s1.sp = s0.sp →
      s1.trace = s0.trace →
      s1.readReg64 .lr = s0.readReg64 .lr →
      s1.readReg64 .x0 = dPtr →
      s1.readReg64 .x1 = dCap →
      s1.readReg64 .x2 = 1#64 →
      CalleeSavedPreserved s0 s1 →
      LibsignalCodeRoLoaded lsmpl s1.mem →
      SepWPp (lsProg_594 H) (s0.readReg64 .lr) s1
        ((A.pool lim
            (M.stepEvents (addrDecReserveEvents x.g.name.bytes x.g.device)
              (M.stepEvents evsDec
                (M.stepEvents (addrDotReserveEvents x.g.name.bytes)
                  (M.stepEvents (addrToOwnedEvents x.g.name.bytes) st0)))) s1 ∗
          A.repAlloc.live dPtr dCap.toNat 1 ∗ memRegion dPtr dCap.toNat ∗
          stackAt s0.sp extHookStack) ∗
        (vecU8 A.repAlloc x.ret (addressText x.g.val) ∗
          protocolAddressAt A.repAlloc x.g x.addr ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack)))
        (fun sf P_f =>
          ((sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (addrTextSpecPlaced A lim (AddrTextEnv DecEnv) stk).post (x, st0) s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨
              (addrTextSpecPlaced A lim (AddrTextEnv DecEnv) stk).onPanic (x, st0) s0 sf ∗ R)) := by
    intro s1 hpc1 hrun1 hsp1 htr1 hlr1 hx0_1 hx1_1 hx2_1 hcs1 hcrl1
    refine SepWPp.tailcall
      (x := (dPtr, dCap.toNat, 1,
        M.stepEvents (addrDecReserveEvents x.g.name.bytes x.g.device)
          (M.stepEvents evsDec
            (M.stepEvents (addrDotReserveEvents x.g.name.bytes)
              (M.stepEvents (addrToOwnedEvents x.g.name.bytes) st0)))))
      (F := vecU8 A.repAlloc x.ret (addressText x.g.val) ∗
        protocolAddressAt A.repAlloc x.g x.addr ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack))
      hdealloc hpc1 hrun1
      (by rw [State.spAligned, hsp1]; exact hsp0)
      hlr1 ?_ ?_ ?_ ?_ ?_
    · intro R' hm
      apply satisfies_lscro_pre hcrl1
      dsimp only [rustDeallocExternSpecWithStack,
        LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
        LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
      rw [hsp1, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0_1, by rw [hx1_1], by rw [hx2_1]; rfl, hlay_d, by rw [hlr1]; exact hlr0⟩, ?_⟩
      simpa only [RustCliAllocBudget.repAlloc_live, sepConj_assoc] using hm
    · intro sf code R' _ hm
      dsimp only [withLsCodeRoLoaded, rustDeallocExternSpecWithStack,
        LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
        LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at hm
      exact not_satisfies_false_sepConj hm
    · intro sf _ hmR
      dsimp only [withLsCodeRoLoaded, rustDeallocExternSpecWithStack,
        LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
        LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at hmR
      rw [sepConj_assoc] at hmR
      exact (not_satisfies_false_sepConj hmR).elim
    · intro sf _ _ hspf hcsf
      have hsp_sf : sf.sp = s0.sp := hspf.trans hsp1
      refine ⟨?_, hsp_sf, calleeSaved_trans hcs1 hcsf⟩
      intro hm_post
      dsimp only [withLsCodeRoLoaded, rustDeallocExternSpecWithStack,
        LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
        LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at hm_post
      dsimp only [addrTextSpecPlaced, withLsCodeRoLoaded]
      rw [hsp1, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm_post
      rcases hm_post with ⟨htr_sf, hm_post⟩
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨addrToOwnedEvents x.g.name.bytes ++
        (addrDotReserveEvents x.g.name.bytes ++
          (evsDec ++
            (addrDecReserveEvents x.g.name.bytes x.g.device ++
              rustDeallocEvents dCap.toNat 1))), ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨htr_sf.trans htr1, addrTextEnv_intro hDecEv dCap.toNat⟩, ?_⟩
      rw [stepEvents_addrText]
      refine Satisfies.mono ?_ hm_post
      rw [stackAt_sub_le s0.sp hext_stk hstk64]
      apply entails_of_eq
      sep_ac_rfl
    · intro sf R' _ hm
      dsimp only [withLsCodeRoLoaded, rustDeallocExternSpecWithStack,
        LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
        LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at hm
      exact (not_satisfies_false_sepConj hm).elim
  apply sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
  wp_steps_sync_594 (lsρ lsRustDeallocSymCli)
  intro hcrl1
  refine sepWPp_weaken_pre_state (P' := fun s_cur =>
      (A.pool lim
          (M.stepEvents (addrDecReserveEvents x.g.name.bytes x.g.device)
            (M.stepEvents evsDec
              (M.stepEvents (addrDotReserveEvents x.g.name.bytes)
                (M.stepEvents (addrToOwnedEvents x.g.name.bytes) st0)))) s_cur ∗
        A.repAlloc.live dPtr dCap.toNat 1 ∗ memRegion dPtr dCap.toNat ∗
        stackAt s0.sp extHookStack) ∗
      (vecU8 A.repAlloc x.ret (addressText x.g.val) ∗
        protocolAddressAt A.repAlloc x.g x.addr ∗
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
      hcrl1)
  have hret_vec :
      (x.ret ↦₆₄ capF) ∗ ((x.ret + 8#64) ↦₆₄ ptrF) ∗
        ((x.ret + 16#64) ↦₆₄ BitVec.ofNat 64 (pfx ++ dec).length) ∗
        vecU8Buf A.repAlloc capF ptrF (pfx ++ dec) ⊢
      vecU8 A.repAlloc x.ret (addressText x.g.val) := by
    subst hpfx_def hdec_def
    rw [← addressText_val_eq x.g]
    exact vecU8_from_moved_header A.repAlloc x.ret capF ptrF (addressText x.g.val)
  have hsp0_cell := cells24_entails_memRegion sp' capF ptrF
    (BitVec.ofNat 64 (pfx ++ dec).length)
  have hsp24_cell := cells24_entails_memRegion (sp' + 24#64) dCap dPtr
    (BitVec.ofNat 64 dec.length)
  have hsp48_cell := addrCalleeSavedAt_entails_memRegion64 sp' s0
  unfold addrCalleeSavedAt at hsp48_cell
  have hdec_dealloc := dec_buf_to_dealloc A.repAlloc dCap dPtr dec hd_le hd_63 hdCap_nz
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
  sep_ac_rfl

/-! ## 2. Top-Level Relocatable Theorems -/

/-- Budget-threaded relocatable `[LibsignalPlacement]` `address_text` contract on `lsProg_594 H`. -/
theorem addrText_placed_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {H : LibsignalHooks} {resProg decProg : Program} {resBlk decBlk : Nat}
    [IsLsBlockProg resProg resBlk H] [IsLsBlockProg decProg decBlk H]
    {resStack decStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hRes : subroutine_ok resProg (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (doReserveSpecOf resStack A lim)))
    (hDec : subroutine_ok decProg (lsmpl.base 597) (decimalSpecPlaced A lim DecEnv decStk))
    (hstk : 0x70 + max (max resStack extHookStack) decStk ≤ stk)
    (hresBlk : resBlk < 619 := by decide)
    (hresUnmut : (resBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hdecBlk : decBlk < 619 := by decide)
    (hdecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_594 H) (lsmpl.base 594)
      (addrTextSpecPlaced A lim (AddrTextEnv DecEnv) stk) := by
  have hdoRes : subroutine_ok (lsProg_594 H) (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (doReserveSpecOf resStack A lim)) :=
    ls_transfer_lscro (callerProg := lsProg_594 H) hRes (by decide) hresBlk hresUnmut
  have hdecCall : subroutine_ok (lsProg_594 H) (lsmpl.base 597)
      (withLsCodeRoLoaded lsmpl (decimalInnerSpec A lim DecEnv decStk)) :=
    ls_transfer_lscro (callerProg := lsProg_594 H) hDec (by decide) hdecBlk hdecUnmut
  change subroutine_ok (lsProg_594 H) (blkPl_594).base
    (addrTextSpecPlaced A lim (AddrTextEnv DecEnv) stk)
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨x, st0⟩ R s0 hpc hrun hpre hsp0
  obtain ⟨hcrl0, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  change s0.mem ⊨
    (⌜s0.readReg64 .x0 = x.ret ∧ s0.readReg64 .x1 = x.addr ∧ x.g.name.bytes.length < 2 ^ 32 ∧
        LibsignalBinary.Heap.FitsEnv M lim st0 (AddrTextEnv DecEnv x.g) ∧
        LsRetAddr624 (s0.readReg64 .x30)⌝ ∗
      protocolAddressAt A.repAlloc x.g x.addr ∗ memRegion x.ret 24 ∗
      stackAt s0.sp stk ∗ A.pool lim st0 s0) ∗ R
    at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hx1, hlen32, hfit, hlr0⟩, hmem0⟩
  have hstk64 : stk ≤ 2 ^ 64 := by
    refine stk_le_two_pow_64 (m := s0.mem) (ret := x.ret) (sp := s0.sp) (stk := stk)
      (R := protocolAddressAt A.repAlloc x.g x.addr ∗ A.pool lim st0 s0 ∗ R) ?_
    simpa only [sepConj_assoc, sepConj_comm, sepConj_left_comm] using hmem0
  set subStk := max (max resStack extHookStack) decStk
  have hres_le : resStack ≤ subStk := le_trans (le_max_left _ _) (le_max_left _ _)
  have hext_le : extHookStack ≤ subStk := le_trans (le_max_right _ _) (le_max_left _ _)
  have hdec_le : decStk ≤ subStk := le_max_right _ _
  have hsub64 : subStk ≤ 2 ^ 64 := by omega
  have hext_stk : extHookStack ≤ stk := by omega
  have hsp_al0 : ((s0.sp - 112#64) &&& 15#64 == 0#64) = true := spAligned_sub112 hsp0
  refine ⟨protocolAddressAt A.repAlloc x.g x.addr ∗ memRegion x.ret 24 ∗
    stackAt s0.sp stk ∗ A.pool lim st0 s0, hmem0, ?_⟩
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
  apply sepWPp_fold (protocolAddressAt_open A.repAlloc x.g x.addr) (by sep_focus)
  rw [sepConj_assoc]
  refine SepWPp.pure_left fun ⟨_, _, _⟩ => ?_
  apply sepWPp_seq_lscro (mid := (blkPl_594).base + frameOff) hcrl0
  wp_steps_sync_594 ((blkPl_594).base + frameOff)
  intro hcrl0'
  refine sepWPp_weaken_pre (by apply entails_of_eq; sep_ac_rfl)
    (step_prologue_to_owned_p (s0 := s0)
      (w0 := w0) (w1 := w1) (w2 := w2)
      (w19 := w19) (w20 := w20) (w21 := w21) (w22 := w22)
      (w23 := w23) (w24 := w24) (w30 := w30) (w29 := w29)
      (Fr := (x.addr ↦₆₄ x.g.name.cap) ∗
        (vecU8BufRest A.repAlloc x.g.name.cap x.g.name.ptr x.g.name.bytes ∗
          memRegion (x.addr + 25#64) 7) ∗
        memRegion x.ret 24 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 112)) ∗
        memRegion (sp' + 24#64) 24)
      hC hext_le hsub64 (fits_toOwned_of_addrTextEnv hfit) hcrl0'
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
      hlen32 ?_)
  intro s1 p0 hpc1 hrun1 hsp1 htr1 hlr1 hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx19_1 hx20_1 hvregs_1 hcrl1
  refine sepWPp_weaken_pre (P' :=
      vecU8At A.repAlloc sp' (BitVec.ofNat 64 x.g.name.bytes.length) p0 x.g.name.bytes ∗
      memRegion (sp' + 24#64) 24 ∗
      ((x.addr + 24#64) ↦₈ x.g.device) ∗
      stackAt sp' subStk ∗
      A.pool lim (M.stepEvents (addrToOwnedEvents x.g.name.bytes) st0) s1 ∗
      (addrCalleeSavedAt sp' s0 ∗
        (x.addr ↦₆₄ x.g.name.cap) ∗
        ((x.addr + 8#64) ↦₆₄ x.g.name.ptr) ∗
        ((x.addr + 16#64) ↦₆₄ BitVec.ofNat 64 x.g.name.bytes.length) ∗
        (x.g.name.ptr ↦ₛ x.g.name.bytes) ∗
        (vecU8BufRest A.repAlloc x.g.name.cap x.g.name.ptr x.g.name.bytes ∗
          memRegion (x.addr + 25#64) 7) ∗
        memRegion x.ret 24 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 112))))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine step_dot_and_decimal_p hdoRes hdecCall hres_le hdec_le hsub64
    hfit hcrl1 hpc1 hrun1 hsp1 hsp_al0 htr1 hlr1
    hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx19_1 hx20_1 hvregs_1 hlen32 ?_
  intro s2 cap1 p1 evsDec hpc2 hrun2 hsp2 htr2 hx19_2 hvregs_2 hcrl2 hcap1_eq hcap1_34 hDecEv
  refine sepWPp_weaken_pre (P' :=
      vecU8At A.repAlloc sp' cap1 p1 (x.g.name.bytes ++ [0x2e#8]) ∗
      vecU8 A.repAlloc (sp' + 24#64) (decimalText (x.g.device.zeroExtend 32).toNat) ∗
      stackAt sp' subStk ∗
      A.pool lim
        (M.stepEvents evsDec
          (M.stepEvents (addrDotReserveEvents x.g.name.bytes)
            (M.stepEvents (addrToOwnedEvents x.g.name.bytes) st0))) s2 ∗
      (addrCalleeSavedAt sp' s0 ∗
        protocolAddressAt A.repAlloc x.g x.addr ∗
        memRegion x.ret 24 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 112)))) ?_ ?_
  · apply step_entails (protocolAddressAt_close A.repAlloc x.g x.addr) (by sep_focus)
    apply entails_of_eq
    sep_ac_rfl
  refine step_append_dec_p hC hdoRes hres_le hext_le hsub64
    hfit hDecEv hcrl2 hpc2 hrun2 hsp2 hsp_al0 htr2 hx19_2 hvregs_2 hlen32 hcap1_eq hcap1_34 ?_
  intro s3 capF ptrF dCap dPtr hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3
    hvregs_3 hcrl3 hd_le hd_63 _
  refine sepWPp_weaken_pre (P' :=
      (sp' ↦₆₄ capF) ∗ ((sp' + 8#64) ↦₆₄ ptrF) ∗
      ((sp' + 16#64) ↦₆₄ BitVec.ofNat 64 (x.g.name.bytes ++ [0x2e#8]).length) ∗
      vecU8Buf A.repAlloc capF ptrF ((x.g.name.bytes ++ [0x2e#8]) ++
        decimalText (x.g.device.zeroExtend 32).toNat) ∗
      ((sp' + 24#64) ↦₆₄ dCap) ∗ ((sp' + 32#64) ↦₆₄ dPtr) ∗
      ((sp' + 40#64) ↦₆₄
        BitVec.ofNat 64 (decimalText (x.g.device.zeroExtend 32).toNat).length) ∗
      (dPtr ↦ₛ decimalText (x.g.device.zeroExtend 32).toNat) ∗
      vecU8BufRest A.repAlloc dCap dPtr (decimalText (x.g.device.zeroExtend 32).toNat) ∗
      addrCalleeSavedAt sp' s0 ∗
      protocolAddressAt A.repAlloc x.g x.addr ∗
      memRegion x.ret 24 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (subStk + 112)) ∗
      stackAt sp' subStk ∗
      A.pool lim
        (M.stepEvents (addrDecReserveEvents x.g.name.bytes x.g.device)
          (M.stepEvents evsDec
            (M.stepEvents (addrDotReserveEvents x.g.name.bytes)
              (M.stepEvents (addrToOwnedEvents x.g.name.bytes) st0)))) s3)
    (by apply entails_of_eq; sep_ac_rfl) ?_
  exact step_epilogue_p hC hstk hext_stk hstk64 hDecEv
    hcrl3 hpc3 hrun3 hsp0 hsp3 hsp_def htr3 hx19_3 hx20_3 hx21_3 hx22_3 hvregs_3 hd_le hd_63 hlr0

/-- Caller-transferable budget-threaded `[LibsignalPlacement]` `address_text` contract for any block `< 619`. -/
theorem addrText_placed_caller_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {H : LibsignalHooks} {callerProg resProg decProg : Program} {i resBlk decBlk : Nat}
    [IsLsBlockProg callerProg i H] [IsLsBlockProg resProg resBlk H]
    [IsLsBlockProg decProg decBlk H]
    {resStack decStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hRes : subroutine_ok resProg (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (doReserveSpecOf resStack A lim)))
    (hDec : subroutine_ok decProg (lsmpl.base 597) (decimalSpecPlaced A lim DecEnv decStk))
    (hstk : 0x70 + max (max resStack extHookStack) decStk ≤ stk)
    (hi : i < 619 := by decide)
    (hresBlk : resBlk < 619 := by decide)
    (hresUnmut : (resBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hdecBlk : decBlk < 619 := by decide)
    (hdecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 594)
      (addrTextSpecPlaced A lim (AddrTextEnv DecEnv) stk) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 594)
    (addrText_placed_ok_of_deps hC hRes hDec hstk hresBlk hresUnmut hdecBlk hdecUnmut) hi

end LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.PlacedBudget
