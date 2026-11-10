/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymD
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.Steps
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.StepsPrefixBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
public meta import ProofLib.SepLogic.WP -- shake: keep
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup

/-!
# Budget-Threaded `[LibsignalPlacement]` `address_text` Segments 1–3

Defines the `AddrTextEnv` allocator event envelope for `signal_session::stores::address_text`
(Block 594) and verifies Segments 1–3 (`name.to_owned()`, `"."` + `decimal(device)`, and appending
the decimal string) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.PlacedBudgetAux

open Arm64 ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall extHookStack memcpyName reserveCap sessionMemcpyRegionSpec
   sessionShimSpec withStack)
open CryptoVerification.LibsignalTripleRatchet.Wire
  (layoutOk_align1 vecU8At_eq_header_buf vecU8Buf vecU8BufRest)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded sepWPp_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.SignalSession
  (lsRustAllocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli
  (AddrTextGhost DecimalGhost decimalText)
open CryptoVerification.SignalSession.Cli.Placed
  (blkLib_594 blkLib_eq_594 blkPC_594 blkPl_594 lsProg_594)
open CryptoVerification.SignalSession.Cli.AddressText.Helpers
  (Same addrCalleeSavedAt allocRetOff cmp_hi_ult_false cmp_hi_ult_true decRetOff
   decimalText_device_len_le_three decimalText_device_pos device_zeroExtend32_toNat
   entails_of_eq frameOff memcpy0RetOff memcpy1RetOff ofNat_beq_zero_false
   ofNat_getElem_63_false ofNat_getLsbD_63_false preservedTailRegs preservedTailRegs_elim
   preservedTailRegs_mk preservedTailRegs_of_cs preservedTailRegs_step res0RetOff res1RetOff
   reserveCap1_bounds reserveCap2_bounds same_eq sepWPp_exists_elim sepWPp_fold
   sepWPp_weaken_pre shimRetOff stackAt_sub_le step_entails
   vecU8At_close_one vecU8At_header_unpack vecU8At_open_one vecU8At_open_slice
   vecU8At_pos_init vecU8At_zero_init vecU8Buf_close_slice vecU8_dec_unpack)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget
   RustLayoutOk SeqEnv VmPreserved rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (DoReserveEnv doReserveEvents fitsEnv_doReserve_iff)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (rustAllocNoOomExternSpecWithStack)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget
  (doReserveSpecOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.StepsPrefixBudget
  (decimalInnerSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
  (allocNoOomExtern_lscro_of_cli session_memcpy_region_lscro_of_cli shim_lscro_of_cli)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  frameOff shimRetOff allocRetOff memcpy0RetOff res0RetOff decRetOff res1RetOff memcpy1RetOff

/-! ## 1. `AddrTextEnv` & Event-Step Helpers -/

/-- Exact allocator events emitted by `g.name.to_owned()` in Segment 1. -/
def addrToOwnedEvents (bs : List (BitVec 8)) : List AllocEvent :=
  if bs.length = 0 then [] else rustAllocEvents bs.length 1

/-- Exact allocator events emitted by `do_reserve_and_handle` for `"."` in Segment 2. -/
def addrDotReserveEvents (bs : List (BitVec 8)) : List AllocEvent :=
  doReserveEvents (DoReserveCall.mk 0#64 (BitVec.ofNat 64 bs.length) 0#64 bs 1)

/-- Exact allocator events emitted by the optional `do_reserve_and_handle` for `dec` in Segment 3. -/
def addrDecReserveEvents (bs : List (BitVec 8)) (device : BitVec 8) : List AllocEvent :=
  let cap1 := BitVec.ofNat 64 (reserveCap bs.length bs.length 1)
  let pfx := bs ++ [0x2e#8]
  let dec := decimalText (device.zeroExtend 32).toNat
  if cap1.toNat < pfx.length + dec.length then
    doReserveEvents (DoReserveCall.mk 0#64 cap1 0#64 pfx dec.length)
  else []

/-- Allocator event envelope of `signal_session::stores::address_text`, parameterized by
`decimal`'s event envelope `DecEnv`. -/
def AddrTextEnv (DecEnv : BitVec 32 → List AllocEvent → Prop)
    (g : AddrGhost) : List AllocEvent → Prop :=
  SeqEnv (· = addrToOwnedEvents g.name.bytes)
    (SeqEnv (· = addrDotReserveEvents g.name.bytes)
      (SeqEnv (DecEnv (g.device.zeroExtend 32))
        (SeqEnv (· = addrDecReserveEvents g.name.bytes g.device) FreeOnlyEvs)))

theorem addrTextEnv_intro {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {g : AddrGhost} {evsDec : List AllocEvent}
    (hDec : DecEnv (g.device.zeroExtend 32) evsDec) (dCapSz : Nat) :
    AddrTextEnv DecEnv g
      (addrToOwnedEvents g.name.bytes ++
        (addrDotReserveEvents g.name.bytes ++
          (evsDec ++
            (addrDecReserveEvents g.name.bytes g.device ++ rustDeallocEvents dCapSz 1)))) :=
  SeqEnv.append rfl
    (SeqEnv.append rfl
      (SeqEnv.append hDec
        (SeqEnv.append rfl (FreeOnlyEvs.singleton 1 dCapSz))))

theorem stepEvents_addrText {M : AllocCostModel} (st0 : M.σ)
    (e1 e2 e3 e4 e5 : List AllocEvent) :
    M.stepEvents (e1 ++ (e2 ++ (e3 ++ (e4 ++ e5)))) st0 =
      M.stepEvents e5
        (M.stepEvents e4
          (M.stepEvents e3
            (M.stepEvents e2 (M.stepEvents e1 st0)))) := by
  simp only [AllocCostModel.stepEvents_append]

theorem doReserveEvents_dot_eq (sp' p0 : BitVec 64) (bs : List (BitVec 8)) :
    doReserveEvents (DoReserveCall.mk sp' (BitVec.ofNat 64 bs.length) p0 bs 1) =
      addrDotReserveEvents bs :=
  rfl

theorem doReserveEvents_dec_grow_eq (sp' p1 : BitVec 64) (bs : List (BitVec 8)) (device : BitVec 8)
    (hgrow : (BitVec.ofNat 64 (reserveCap bs.length bs.length 1)).toNat <
      (bs ++ [0x2e#8]).length + (decimalText (device.zeroExtend 32).toNat).length) :
    doReserveEvents
        (DoReserveCall.mk sp' (BitVec.ofNat 64 (reserveCap bs.length bs.length 1)) p1
          (bs ++ [0x2e#8]) (decimalText (device.zeroExtend 32).toNat).length) =
      addrDecReserveEvents bs device := by
  simp only [addrDecReserveEvents, hgrow, ↓reduceIte]; rfl

theorem addrDecReserveEvents_not_grow (bs : List (BitVec 8)) (device : BitVec 8)
    (hngrow : ¬ (BitVec.ofNat 64 (reserveCap bs.length bs.length 1)).toNat <
      (bs ++ [0x2e#8]).length + (decimalText (device.zeroExtend 32).toNat).length) :
    addrDecReserveEvents bs device = [] := by
  simp only [addrDecReserveEvents, hngrow, ↓reduceIte]

theorem fits_toOwned_of_addrTextEnv {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {DecEnv : BitVec 32 → List AllocEvent → Prop} {g : AddrGhost}
    (hfit : FitsEnv M lim st0 (AddrTextEnv DecEnv g)) :
    FitsEvents M lim st0 (addrToOwnedEvents g.name.bytes) :=
  FitsEnv.eq_iff.mp hfit.seq_left

theorem fits_dotReserve_of_addrTextEnv {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {DecEnv : BitVec 32 → List AllocEvent → Prop} {g : AddrGhost} (sp' p0 : BitVec 64)
    (hfit : FitsEnv M lim st0 (AddrTextEnv DecEnv g)) :
    FitsEnv M lim (M.stepEvents (addrToOwnedEvents g.name.bytes) st0)
      (DoReserveEnv (DoReserveCall.mk sp' (BitVec.ofNat 64 g.name.bytes.length)
        p0 g.name.bytes 1)) :=
  (fitsEnv_doReserve_iff _).mpr (FitsEnv.eq_iff.mp (hfit.seq_right rfl).seq_left)

theorem fits_decimal_of_addrTextEnv {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {DecEnv : BitVec 32 → List AllocEvent → Prop} {g : AddrGhost}
    (hfit : FitsEnv M lim st0 (AddrTextEnv DecEnv g)) :
    FitsEnv M lim
      (M.stepEvents (addrDotReserveEvents g.name.bytes)
        (M.stepEvents (addrToOwnedEvents g.name.bytes) st0))
      (DecEnv (g.device.zeroExtend 32)) :=
  ((hfit.seq_right rfl).seq_right rfl).seq_left

theorem fits_decReserve_of_addrTextEnv {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {DecEnv : BitVec 32 → List AllocEvent → Prop} {g : AddrGhost} {evsDec : List AllocEvent}
    (sp' p1 : BitVec 64)
    (hfit : FitsEnv M lim st0 (AddrTextEnv DecEnv g))
    (hDec : DecEnv (g.device.zeroExtend 32) evsDec)
    (hgrow : (BitVec.ofNat 64 (reserveCap g.name.bytes.length g.name.bytes.length 1)).toNat <
      (g.name.bytes ++ [0x2e#8]).length +
        (decimalText (g.device.zeroExtend 32).toNat).length) :
    FitsEnv M lim
      (M.stepEvents evsDec
        (M.stepEvents (addrDotReserveEvents g.name.bytes)
          (M.stepEvents (addrToOwnedEvents g.name.bytes) st0)))
      (DoReserveEnv
        (DoReserveCall.mk sp'
          (BitVec.ofNat 64 (reserveCap g.name.bytes.length g.name.bytes.length 1))
          p1 (g.name.bytes ++ [0x2e#8])
          (decimalText (g.device.zeroExtend 32).toNat).length)) := by
  rw [fitsEnv_doReserve_iff, doReserveEvents_dec_grow_eq sp' p1 g.name.bytes g.device hgrow]
  exact FitsEnv.eq_iff.mp (((hfit.seq_right rfl).seq_right rfl).seq_right hDec).seq_left

/-! ## 2. Block-594 Pool-Syncing Stepper & Total-Callee `SepWPp.call_lscro` Wrapper -/

theorem blk594_noSvc0 : VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib_594.text = true := by
  decide +kernel

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

theorem sepWPp_weaken_pre_state {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {P' : State → SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P ⊢ P' s) (h : SepWPp prog ret s (P' s) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  sepWPp_weaken_pre hent h

theorem call_lscro_addr [LibsignalPlacement] {α : Type}
    {prog : Program} {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α}
    {s : State} {P T F R : SepProp} {Q : State → SepProp → Prop}
    {PanPost : State → SepProp}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre_eq : spec.pre x s = T)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ PanPost sf ∗ R)))
    (hP : P = T ∗ F := by
      (conv_lhs => simp (config := { failIfUnchanged := false }) only [arm64_norm, *]); sep_focus)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ PanPost sf ∗ R)) := by
  refine CryptoVerification.SignalSession.Cli.Store.PlacedCommon.SepWPp.call_lscro (x := x) (F := F)
    hcall hcrl hpc hrun hsp hlr ?_ ?_ ?_ hnext ?_
  · intro R' hm
    rw [hP, ← hpre_eq, sepConj_assoc] at hm
    exact hm
  · intro sf code R' _ hm
    rw [hexit_eq] at hm
    exact not_satisfies_false_sepConj hm
  · intro sf _ hm
    rw [hpan_eq, sepConj_assoc] at hm
    exact (not_satisfies_false_sepConj hm).elim
  · intro R' sf _ hm
    rw [hoom_eq] at hm
    exact (not_satisfies_false_sepConj hm).elim

/-! ## 3. Segment 1 (`4 .. 140`): register saves + `name.to_owned()` up to first `cliDoReserve` -/

theorem step_prologue_to_owned_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {subStk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hext_le : extHookStack ≤ subStk) (hsub64 : subStk ≤ 2 ^ 64)
    {x : AddrTextGhost} {st0 : M.σ} {R Fr : SepProp} {s0 s : State} {sp' : BitVec 64}
    {Q : State → SepProp → Prop} {PanPost : State → SepProp}
    (hfit0 : FitsEvents M lim st0 (addrToOwnedEvents x.g.name.bytes))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_594).base + frameOff)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp')
    (hsp_al : (sp' &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = x.ret)
    (hx1 : s.readReg64 .x1 = x.addr)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx21 : s.readReg64 .x21 = s0.readReg64 .x21)
    (hx22 : s.readReg64 .x22 = s0.readReg64 .x22)
    (hx23 : s.readReg64 .x23 = s0.readReg64 .x23)
    (hx24 : s.readReg64 .x24 = s0.readReg64 .x24)
    (hx29 : s.readReg64 .x29 = s0.readReg64 .x29)
    (hx30 : s.readReg64 .x30 = s0.readReg64 .x30)
    (hvregs : preservedTailRegs s = preservedTailRegs s0)
    (hlen32 : x.g.name.bytes.length < 2 ^ 32)
    {w0 w1 w2 w19 w20 w21 w22 w23 w24 w30 w29 : BitVec 64}
    (hnext : ∀ (sm : State) (p0 : BitVec 64),
      sm.pc = lsmpl.base 561 →
      sm.status = .Running →
      sm.sp = sp' →
      sm.trace = s0.trace →
      sm.readReg64 .lr = (blkPl_594).base + res0RetOff →
      sm.readReg64 .x0 = sp' →
      sm.readReg64 .x1 = BitVec.ofNat 64 x.g.name.bytes.length →
      sm.readReg64 .x2 = 1#64 →
      sm.readReg64 .x3 = 1#64 →
      sm.readReg64 .x4 = 1#64 →
      sm.readReg64 .x19 = x.ret →
      sm.readReg64 .x20 = x.addr →
      preservedTailRegs sm = preservedTailRegs s0 →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp (lsProg_594 H) (s0.readReg64 .lr) sm
        (vecU8At A.repAlloc sp' (BitVec.ofNat 64 x.g.name.bytes.length) p0 x.g.name.bytes ∗
          addrCalleeSavedAt sp' s0 ∗
          ((x.addr + 8#64) ↦₆₄ x.g.name.ptr) ∗
          ((x.addr + 16#64) ↦₆₄ BitVec.ofNat 64 x.g.name.bytes.length) ∗
          (x.g.name.ptr ↦ₛ x.g.name.bytes) ∗
          ((x.addr + 24#64) ↦₈ x.g.device) ∗
          stackAt sp' subStk ∗
          A.pool lim (M.stepEvents (addrToOwnedEvents x.g.name.bytes) st0) sm ∗ Fr)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ PanPost sf ∗ R))) :
    SepWPp (lsProg_594 H) (s0.readReg64 .lr) s
      (((sp' ↦₆₄ w0) ∗ ((sp' + 8#64) ↦₆₄ w1) ∗ ((sp' + 16#64) ↦₆₄ w2)) ∗
        (((sp' + 48#64) ↦₆₄ w29) ∗ ((sp' + 56#64) ↦₆₄ w30) ∗
          ((sp' + 64#64) ↦₆₄ w24) ∗ ((sp' + 72#64) ↦₆₄ w23) ∗
          ((sp' + 80#64) ↦₆₄ w22) ∗ ((sp' + 88#64) ↦₆₄ w21) ∗
          ((sp' + 96#64) ↦₆₄ w20) ∗ ((sp' + 104#64) ↦₆₄ w19)) ∗
        ((x.addr + 8#64) ↦₆₄ x.g.name.ptr) ∗
        ((x.addr + 16#64) ↦₆₄ BitVec.ofNat 64 x.g.name.bytes.length) ∗
        (x.g.name.ptr ↦ₛ x.g.name.bytes) ∗
        ((x.addr + 24#64) ↦₈ x.g.device) ∗
        stackAt sp' subStk ∗ A.pool lim st0 s ∗ Fr)
      Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ PanPost sf ∗ R)) := by
  obtain ⟨hx25, hx26, hx27, hx28, hvregs0⟩ := preservedTailRegs_elim hvregs
  have hshim := shim_lscro_of_cli (callerProg := lsProg_594 H) (stk := extHookStack) hC
  have halloc := allocNoOomExtern_lscro_of_cli (callerProg := lsProg_594 H) hC
  have hmemcpy := session_memcpy_region_lscro_of_cli (callerProg := lsProg_594 H)
    (stk := extHookStack) hC
  have h63 : (BitVec.ofNat 64 x.g.name.bytes.length)[63] = false :=
    ofNat_getElem_63_false (by omega)
  have h63' : (BitVec.ofNat 64 x.g.name.bytes.length).getLsbD 63 = false :=
    ofNat_getLsbD_63_false (by omega)
  by_cases hzero : x.g.name.bytes.length = 0
  · have hbs0 : x.g.name.bytes = [] := List.eq_nil_of_length_eq_zero hzero
    rw [hbs0]
    apply sepWPp_seq_lscro (mid := lsmpl.base 561) hcrl
    wp_steps_sync_594 (lsmpl.base 561)
    intro hcrl1
    have hv : vecU8At A.repAlloc sp' 0#64 1#64 [] =
        vecU8At A.repAlloc sp' (BitVec.ofNat 64 x.g.name.bytes.length) 1#64 x.g.name.bytes := by
      rw [hbs0]; rfl
    refine sepWPp_weaken_pre ?_ (hnext _ 1#64
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by rw [hbs0]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (preservedTailRegs_mk
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [calleeSavedVRegs, arm64_norm, *]))
      hcrl1)
    rw [← hv, hbs0]
    simp only [addrToOwnedEvents, List.length_nil, ↓reduceIte, AllocCostModel.stepEvents_nil]
    unfold addrCalleeSavedAt
    refine Entails.trans ?_
      (sepConj_mono_left (vecU8At_zero_init A.repAlloc sp'))
    simp (config := { failIfUnchanged := false }) only [arm64_norm, *]
    apply entails_of_eq
    sep_ac_rfl
  · have hpos : 0 < x.g.name.bytes.length := Nat.pos_of_ne_zero hzero
    have hevs_pos : addrToOwnedEvents x.g.name.bytes =
        rustAllocEvents x.g.name.bytes.length 1 := by
      simp only [addrToOwnedEvents, hzero, ↓reduceIte]
    have hfit_alloc : FitsEvents M lim st0 (rustAllocEvents x.g.name.bytes.length 1) := by
      rwa [← hevs_pos]
    have hne_beq : (BitVec.ofNat 64 x.g.name.bytes.length == 0#64) = false :=
      ofNat_beq_zero_false hpos (by omega)
    apply sepWPp_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl
    wp_steps_sync_594 (lsρ lsRustNoAllocShimSymCli)
    intro hcrl1
    rw [stackAt_sub_le sp' hext_le hsub64]
    refine call_lscro_addr (x := ()) hshim hcrl1
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, *])
      (ret_pc := (blkPl_594).base + shimRetOff)
      (by simp only [arm64_norm, *])
      (T := stackAt sp' extHookStack)
      (by dsimp [withStack, sessionShimBudgetSpec, sessionShimSpec];
          simp only [emp_sepConj, arm64_norm, *])
      ?_
    intro s2 hpc2 hrun2 hsp2 hcs2 hcrl2
    dsimp only [withStack, sessionShimBudgetSpec, sessionShimSpec]
    simp only [sepConj_assoc]
    refine SepWPp.pure_left fun hvm2 => ?_
    refine SepWPp.pure_left fun htr2 => ?_
    refine ProofLib.SepWPp.transport_budgetPool hvm2 (hnext := ?_)
    have hsp2' : s2.sp = sp' := by rw [hsp2]; simp only [arm64_norm, *]
    have htr2' : s2.trace = s0.trace := by rw [htr2]; simp only [arm64_norm, *]
    have hx19_2 : s2.readReg64 .x19 = x.ret := by rw [hcs2.1]; simp only [arm64_norm, *]
    have hx20_2 : s2.readReg64 .x20 = x.addr := by rw [hcs2.2.1]; simp only [arm64_norm, *]
    have hx21_2 : s2.readReg64 .x21 = BitVec.ofNat 64 x.g.name.bytes.length := by
      rw [hcs2.2.2.1]; simp only [arm64_norm, *]
    have hx23_2 : s2.readReg64 .x23 = x.g.name.ptr := by
      rw [hcs2.2.2.2.2.1]; simp only [arm64_norm, *]
    obtain ⟨hx25_2, hx26_2, hx27_2, hx28_2, hvregs_2⟩ :=
      preservedTailRegs_elim (preservedTailRegs_step (s0 := s0) hcs2
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [calleeSavedVRegs, arm64_norm, *]))
    apply sepWPp_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl2
    wp_steps_sync_594 (lsρ lsRustAllocSymCli)
    intro hcrl3
    have htoNat_len : (BitVec.ofNat 64 x.g.name.bytes.length).toNat = x.g.name.bytes.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have h1_toNat : (1#64).toNat = 1 := rfl
    have hlay_rust : RustLayoutOk x.g.name.bytes.length 1 :=
      ⟨layoutOk_align1 hpos (by omega), by decide⟩
    refine call_lscro_addr (x := (x.g.name.bytes.length, 1, st0)) halloc hcrl3
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, *])
      (ret_pc := (blkPl_594).base + allocRetOff)
      (by simp only [arm64_norm, *])
      (T := A.pool lim st0 _ ∗ stackAt sp' extHookStack)
      (by
        apply same_eq
        dsimp [rustAllocNoOomExternSpecWithStack,
          LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack,
          LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
          LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack]
        simp (config := { decide := true, failIfUnchanged := false }) only
          [arm64_norm, wp_norm, pure_true, emp_sepConj, *]
        unfold Same
        sep_ac_rfl)
      ?_
    intro s4 hpc4 hrun4 hsp4 hcs4 hcrl4
    have hsp4' : s4.sp = sp' := by rw [hsp4]; simp only [arm64_norm, *]
    have hx19_4 : s4.readReg64 .x19 = x.ret := by rw [hcs4.1]; simp only [arm64_norm, *]
    have hx20_4 : s4.readReg64 .x20 = x.addr := by rw [hcs4.2.1]; simp only [arm64_norm, *]
    have hx21_4 : s4.readReg64 .x21 = BitVec.ofNat 64 x.g.name.bytes.length := by
      rw [hcs4.2.2.1]; simp only [arm64_norm, *]
    have hx23_4 : s4.readReg64 .x23 = x.g.name.ptr := by
      rw [hcs4.2.2.2.2.1]; simp only [arm64_norm, *]
    obtain ⟨hx25_4, hx26_4, hx27_4, hx28_4, hvregs_4⟩ :=
      preservedTailRegs_elim (preservedTailRegs_step (s0 := s0) hcs4
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [calleeSavedVRegs, arm64_norm, *]))
    dsimp only [rustAllocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack]
    simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_left fun ⟨htr4', hnull, _⟩ => ?_
    have hnull' : s4.readReg64 .x0 ≠ 0 := hnull
    have hnull_beq : (s4.readReg64 .x0 == 0#64) = false := beq_false_of_ne hnull
    apply sepWPp_seq_lscro (mid := lsρ memcpyName) hcrl4
    wp_steps_sync_594 (lsρ memcpyName)
    intro hcrl5
    refine call_lscro_addr (x := (s4.readReg64 .x0, x.g.name.ptr, x.g.name.bytes))
      hmemcpy hcrl5
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, *])
      (ret_pc := (blkPl_594).base + memcpy0RetOff)
      (by simp only [arm64_norm, *])
      (T := memRegion (s4.readReg64 .x0) x.g.name.bytes.length ∗
        (x.g.name.ptr ↦ₛ x.g.name.bytes) ∗ stackAt sp' extHookStack)
      (by
        apply same_eq
        dsimp [withStack, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec]
        simp (config := { decide := true, failIfUnchanged := false }) only
          [arm64_norm, wp_norm, pure_true, emp_sepConj, *]
        unfold Same
        sep_ac_rfl)
      ?_
    intro s6 hpc6 hrun6 hsp6 hcs6 hcrl6
    dsimp only [withStack, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec]
    simp only [sepConj_assoc]
    refine SepWPp.pure_left fun hvm6 => ?_
    refine SepWPp.pure_left fun ⟨_, htr6⟩ => ?_
    refine ProofLib.SepWPp.transport_budgetPool hvm6 (hnext := ?_)
    have hsp6' : s6.sp = sp' := by rw [hsp6]; simp only [arm64_norm, *]
    have htr6' : s6.trace = s0.trace := by rw [htr6]; simp only [arm64_norm, *]
    have hx19_6 : s6.readReg64 .x19 = x.ret := by rw [hcs6.1]; simp only [arm64_norm, *]
    have hx20_6 : s6.readReg64 .x20 = x.addr := by rw [hcs6.2.1]; simp only [arm64_norm, *]
    have hx21_6 : s6.readReg64 .x21 = BitVec.ofNat 64 x.g.name.bytes.length := by
      rw [hcs6.2.2.1]; simp only [arm64_norm, *]
    have hx22_6 : s6.readReg64 .x22 = s4.readReg64 .x0 := by
      rw [hcs6.2.2.2.1]; simp only [arm64_norm, *]
    obtain ⟨hx25_6, hx26_6, hx27_6, hx28_6, hvregs_6⟩ :=
      preservedTailRegs_elim (preservedTailRegs_step (s0 := s0) hcs6
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [calleeSavedVRegs, arm64_norm, *]))
    apply sepWPp_seq_lscro (mid := lsmpl.base 561) hcrl6
    wp_steps_sync_594 (lsmpl.base 561)
    intro hcrl7
    refine sepWPp_weaken_pre ?_ (hnext _ (s4.readReg64 .x0)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (preservedTailRegs_mk
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [calleeSavedVRegs, arm64_norm, *]))
      hcrl7)
    rw [stackAt_sub_le sp' hext_le hsub64, hevs_pos]
    unfold addrCalleeSavedAt
    apply step_entails
      (vecU8At_pos_init A.repAlloc sp' (s4.readReg64 .x0) x.g.name.bytes hpos (by omega) hnull)
      (by
        (conv_lhs =>
          simp (config := { failIfUnchanged := false }) only [arm64_norm]
          simp (config := { failIfUnchanged := false }) only [← RustCliAllocBudget.repAlloc_live])
        sep_focus)
    simp (config := { failIfUnchanged := false }) only [arm64_norm, *]
    apply entails_of_eq
    sep_ac_rfl

/-! ## 4. Segment 2 (`140 .. 176`): `cliDoReserve` + `"."` + `decimal(device)` -/

theorem step_dot_and_decimal_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {H : LibsignalHooks} {resStack decStk subStk : Nat}
    (hdoRes : subroutine_ok (lsProg_594 H) (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (doReserveSpecOf resStack A lim)))
    (hdecCall : subroutine_ok (lsProg_594 H) (lsmpl.base 597)
      (withLsCodeRoLoaded lsmpl (decimalInnerSpec A lim DecEnv decStk)))
    (hres_le : resStack ≤ subStk) (hdec_le : decStk ≤ subStk) (hsub64 : subStk ≤ 2 ^ 64)
    {x : AddrTextGhost} {st0 : M.σ} {R Fr : SepProp} {s0 s : State} {sp' p0 : BitVec 64}
    {Q : State → SepProp → Prop} {PanPost : State → SepProp}
    (hfit : FitsEnv M lim st0 (AddrTextEnv DecEnv x.g))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 561)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp')
    (hsp_al : (sp' &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = (blkPl_594).base + res0RetOff)
    (hx0 : s.readReg64 .x0 = sp')
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 x.g.name.bytes.length)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = x.addr)
    (hvregs : preservedTailRegs s = preservedTailRegs s0)
    (hlen32 : x.g.name.bytes.length < 2 ^ 32)
    (hnext : ∀ (sm : State) (cap1 p1 : BitVec 64) (evsDec : List AllocEvent),
      sm.pc = (blkPl_594).base + decRetOff →
      sm.status = .Running →
      sm.sp = sp' →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = x.ret →
      preservedTailRegs sm = preservedTailRegs s0 →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      cap1 = BitVec.ofNat 64 (reserveCap x.g.name.bytes.length x.g.name.bytes.length 1) →
      cap1.toNat < 2 ^ 34 →
      DecEnv (x.g.device.zeroExtend 32) evsDec →
      SepWPp (lsProg_594 H) (s0.readReg64 .lr) sm
        (vecU8At A.repAlloc sp' cap1 p1 (x.g.name.bytes ++ [0x2e#8]) ∗
          vecU8 A.repAlloc (sp' + 24#64) (decimalText (x.g.device.zeroExtend 32).toNat) ∗
          ((x.addr + 24#64) ↦₈ x.g.device) ∗
          stackAt sp' subStk ∗
          A.pool lim
            (M.stepEvents evsDec
              (M.stepEvents (addrDotReserveEvents x.g.name.bytes)
                (M.stepEvents (addrToOwnedEvents x.g.name.bytes) st0))) sm ∗ Fr)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ PanPost sf ∗ R))) :
    SepWPp (lsProg_594 H) (s0.readReg64 .lr) s
      (vecU8At A.repAlloc sp' (BitVec.ofNat 64 x.g.name.bytes.length) p0 x.g.name.bytes ∗
        memRegion (sp' + 24#64) 24 ∗
        ((x.addr + 24#64) ↦₈ x.g.device) ∗
        stackAt sp' subStk ∗
        A.pool lim (M.stepEvents (addrToOwnedEvents x.g.name.bytes) st0) s ∗ Fr)
      Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ PanPost sf ∗ R)) := by
  have htoNat_len : (BitVec.ofNat 64 x.g.name.bytes.length).toNat = x.g.name.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨hcap1_lt34, hlen_lt_cap1, hres1_bound⟩ := reserveCap1_bounds hlen32
  have h1_toNat : (1#64).toNat = 1 := rfl
  have hres1_bound63 : reserveCap x.g.name.bytes.length x.g.name.bytes.length 1 + 1 ≤
      9223372036854775808 :=
    hres1_bound
  have hfit_dot := fits_dotReserve_of_addrTextEnv sp' p0 hfit
  have hfit_dec := fits_decimal_of_addrTextEnv hfit
  rw [stackAt_sub_le sp' hres_le hsub64]
  refine call_lscro_addr
    (x := (DoReserveCall.mk sp' (BitVec.ofNat 64 x.g.name.bytes.length)
      p0 x.g.name.bytes 1, M.stepEvents (addrToOwnedEvents x.g.name.bytes) st0))
    hdoRes hcrl hpc hrun
    (by simp only [State.spAligned, *])
    hlr
    (T := vecU8At A.repAlloc sp' (BitVec.ofNat 64 x.g.name.bytes.length) p0 x.g.name.bytes ∗
      A.pool lim (M.stepEvents (addrToOwnedEvents x.g.name.bytes) st0) s ∗ stackAt sp' resStack)
    (by
      apply same_eq
      dsimp [doReserveSpecOf]
      simp (config := { failIfUnchanged := false }) only [arm64_norm, pure_true, emp_sepConj, *]
      unfold Same
      sep_ac_rfl)
    ?_
  intro s1 hpc1 hrun1 hsp1 hcs1 hcrl1
  dsimp only [doReserveSpecOf]
  rw [doReserveEvents_dot_eq sp' p0 x.g.name.bytes, hsp, sepConj_assoc]
  refine SepWPp.pure_left fun htr1 => ?_
  have htr1' : s1.trace = s0.trace := htr1.trans htr
  have hsp1' : s1.sp = sp' := by rw [hsp1, hsp]
  have hx19_1 : s1.readReg64 .x19 = x.ret := hcs1.1.trans hx19
  have hx20_1 : s1.readReg64 .x20 = x.addr := hcs1.2.1.trans hx20
  obtain ⟨hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ :=
    preservedTailRegs_elim ((preservedTailRegs_of_cs hcs1).trans hvregs)
  simp only [sepExists_sepConj_left]
  refine sepWPp_exists_elim fun p1 => ?_
  set cap1 : BitVec 64 := BitVec.ofNat 64 (reserveCap x.g.name.bytes.length x.g.name.bytes.length 1)
  have hcap1_eq : (BitVec.ofNat 64
      (reserveCap (BitVec.ofNat 64 x.g.name.bytes.length).toNat x.g.name.bytes.length 1)) = cap1 := by
    rw [htoNat_len]
  rw [hcap1_eq]
  have hcap1_toNat : cap1.toNat = reserveCap x.g.name.bytes.length x.g.name.bytes.length 1 := by
    dsimp [cap1]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlt1 : x.g.name.bytes.length < cap1.toNat := by omega
  apply sepWPp_fold (vecU8At_open_one A.repAlloc sp' cap1 p1 x.g.name.bytes hlt1) (by sep_focus)
  rw [sepConj_assoc]
  refine SepWPp.pure_left fun ⟨h63_1, hp1⟩ => ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine sepWPp_exists_elim fun b0 => ?_
  have hadd1 : BitVec.ofNat 64 x.g.name.bytes.length + 1#64 =
      BitVec.ofNat 64 (x.g.name.bytes.length + 1) := by
    rw [← BitVec.ofNat_add]
  apply sepWPp_seq_lscro (mid := lsmpl.base 597) hcrl1
  wp_steps_sync_594 (lsmpl.base 597)
  intro hcrl2
  refine sepWPp_weaken_pre_state (P' := fun s_cur =>
      vecU8At A.repAlloc sp' cap1 p1 (x.g.name.bytes ++ [0x2e#8]) ∗
        memRegion (sp' + 24#64) 24 ∗
        ((x.addr + 24#64) ↦₈ x.g.device) ∗
        stackAt sp' subStk ∗
        A.pool lim
          (M.stepEvents (addrDotReserveEvents x.g.name.bytes)
            (M.stepEvents (addrToOwnedEvents x.g.name.bytes) st0)) s_cur ∗ Fr) ?_ ?_
  · rw [stackAt_sub_le sp' hres_le hsub64]
    apply step_entails
      (vecU8At_close_one A.repAlloc sp' cap1 p1 x.g.name.bytes 0x2e#8 hlt1 h63_1 hp1)
      (by
        (conv_lhs =>
          simp (config := { failIfUnchanged := false }) only [arm64_norm]
          simp (config := { failIfUnchanged := false }) only [← RustCliAllocBudget.repAlloc_live])
        sep_focus)
    simp (config := { failIfUnchanged := false }) only [arm64_norm, *]
    apply entails_of_eq
    sep_ac_rfl
  rw [stackAt_sub_le sp' hdec_le hsub64]
  refine call_lscro_addr
    (x := (DecimalGhost.mk (x.g.device.zeroExtend 32) (sp' + 24#64),
      M.stepEvents (addrDotReserveEvents x.g.name.bytes)
        (M.stepEvents (addrToOwnedEvents x.g.name.bytes) st0)))
    hdecCall hcrl2
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, *])
    (ret_pc := (blkPl_594).base + decRetOff)
    (by simp only [arm64_norm, *])
    (T := memRegion (sp' + 24#64) 24 ∗ stackAt sp' decStk ∗
      A.pool lim
        (M.stepEvents (addrDotReserveEvents x.g.name.bytes)
          (M.stepEvents (addrToOwnedEvents x.g.name.bytes) st0)) _)
    (by
      apply same_eq
      dsimp [decimalInnerSpec]
      simp (config := { failIfUnchanged := false }) only [arm64_norm, pure_true, emp_sepConj, *]
      unfold Same
      sep_ac_rfl)
    ?_
  intro s3 hpc3 hrun3 hsp3 hcs3 hcrl3
  dsimp only [decimalInnerSpec]
  simp only [sepExists_sepConj_left]
  refine sepWPp_exists_elim fun evsDec => ?_
  rw [sepConj_assoc]
  refine SepWPp.pure_left fun ⟨htr3, hDecEv⟩ => ?_
  have htr3' : s3.trace = s0.trace := by rw [htr3]; simp only [arm64_norm, *]
  have hsp3' : s3.sp = sp' := by rw [hsp3]; simp only [arm64_norm, *]
  have hx19_3 : s3.readReg64 .x19 = x.ret := by rw [hcs3.1]; simp only [arm64_norm, *]
  have hvregs_3 : preservedTailRegs s3 = preservedTailRegs s0 :=
    preservedTailRegs_step hcs3
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [calleeSavedVRegs, arm64_norm, *])
  refine sepWPp_weaken_pre ?_
    (hnext s3 cap1 p1 evsDec hpc3 hrun3 hsp3' htr3' hx19_3 hvregs_3 hcrl3 rfl (by omega) hDecEv)
  rw [stackAt_sub_le sp' hdec_le hsub64]
  simp (config := { failIfUnchanged := false }) only [arm64_norm, *]
  apply entails_of_eq
  sep_ac_rfl

/-! ## 5. Segment 3 (`176 .. 224` & `308 .. 336`): optional reserve + `memcpy` of `dec` -/

theorem step_append_dec_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {H : LibsignalHooks} {resStack subStk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hdoRes : subroutine_ok (lsProg_594 H) (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (doReserveSpecOf resStack A lim)))
    (hres_le : resStack ≤ subStk) (hext_le : extHookStack ≤ subStk) (hsub64 : subStk ≤ 2 ^ 64)
    {x : AddrTextGhost} {st0 : M.σ} {evsDec : List AllocEvent}
    {R Fr : SepProp} {s0 s : State} {sp' cap1 p1 : BitVec 64}
    {Q : State → SepProp → Prop} {PanPost : State → SepProp}
    (hfit : FitsEnv M lim st0 (AddrTextEnv DecEnv x.g))
    (hDecEv : DecEnv (x.g.device.zeroExtend 32) evsDec)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_594).base + decRetOff)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp')
    (hsp_al : (sp' &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hvregs : preservedTailRegs s = preservedTailRegs s0)
    (hlen32 : x.g.name.bytes.length < 2 ^ 32)
    (hcap1_eq : cap1 = BitVec.ofNat 64 (reserveCap x.g.name.bytes.length x.g.name.bytes.length 1))
    (hcap1_34 : cap1.toNat < 2 ^ 34)
    (hnext : ∀ (sm : State) (capF ptrF dCap dPtr : BitVec 64),
      sm.pc = (blkPl_594).base + memcpy1RetOff →
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
      LibsignalCodeRoLoaded lsmpl sm.mem →
      (decimalText (x.g.device.zeroExtend 32).toNat).length ≤ dCap.toNat →
      dCap.toNat < 2 ^ 63 →
      dPtr ≠ 0 →
      SepWPp (lsProg_594 H) (s0.readReg64 .lr) sm
        ((sp' ↦₆₄ capF) ∗ ((sp' + 8#64) ↦₆₄ ptrF) ∗
          ((sp' + 16#64) ↦₆₄ BitVec.ofNat 64 (x.g.name.bytes ++ [0x2e#8]).length) ∗
          vecU8Buf A.repAlloc capF ptrF ((x.g.name.bytes ++ [0x2e#8]) ++
            decimalText (x.g.device.zeroExtend 32).toNat) ∗
          ((sp' + 24#64) ↦₆₄ dCap) ∗ ((sp' + 32#64) ↦₆₄ dPtr) ∗
          ((sp' + 40#64) ↦₆₄
            BitVec.ofNat 64 (decimalText (x.g.device.zeroExtend 32).toNat).length) ∗
          (dPtr ↦ₛ decimalText (x.g.device.zeroExtend 32).toNat) ∗
          vecU8BufRest A.repAlloc dCap dPtr (decimalText (x.g.device.zeroExtend 32).toNat) ∗
          stackAt sp' subStk ∗
          A.pool lim
            (M.stepEvents (addrDecReserveEvents x.g.name.bytes x.g.device)
              (M.stepEvents evsDec
                (M.stepEvents (addrDotReserveEvents x.g.name.bytes)
                  (M.stepEvents (addrToOwnedEvents x.g.name.bytes) st0)))) sm ∗ Fr)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ PanPost sf ∗ R))) :
    SepWPp (lsProg_594 H) (s0.readReg64 .lr) s
      (vecU8At A.repAlloc sp' cap1 p1 (x.g.name.bytes ++ [0x2e#8]) ∗
        vecU8 A.repAlloc (sp' + 24#64) (decimalText (x.g.device.zeroExtend 32).toNat) ∗
        stackAt sp' subStk ∗
        A.pool lim
          (M.stepEvents evsDec
            (M.stepEvents (addrDotReserveEvents x.g.name.bytes)
              (M.stepEvents (addrToOwnedEvents x.g.name.bytes) st0))) s ∗ Fr)
      Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ PanPost sf ∗ R)) := by
  obtain ⟨hx25, hx26, hx27, hx28, hvregs0⟩ := preservedTailRegs_elim hvregs
  have hmemcpy := session_memcpy_region_lscro_of_cli (callerProg := lsProg_594 H)
    (stk := extHookStack) hC
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
  apply sepWPp_fold (vecU8_dec_unpack A.repAlloc (sp' + 24#64) dec) (by sep_focus)
  simp only [sepExists_sepConj_left]
  refine sepWPp_exists_elim fun dCap => ?_
  refine sepWPp_exists_elim fun dPtr => ?_
  rw [sepConj_assoc]
  refine SepWPp.pure_left fun ⟨hd_le, hd_63, hd_ptr⟩ => ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  by_cases hgrow : cap1.toNat < pfx.length + dec.length
  · have hgrow0 :
        (BitVec.ofNat 64 (reserveCap x.g.name.bytes.length x.g.name.bytes.length 1)).toNat <
          (x.g.name.bytes ++ [0x2e#8]).length +
            (decimalText (x.g.device.zeroExtend 32).toNat).length := by
      rwa [← hcap1_eq, hpfx_def, hdec_def]
    have hfit_res2 :
        FitsEnv M lim
          (M.stepEvents evsDec
            (M.stepEvents (addrDotReserveEvents x.g.name.bytes)
              (M.stepEvents (addrToOwnedEvents x.g.name.bytes) st0)))
          (DoReserveEnv (DoReserveCall.mk sp' cap1 p1 pfx dec.length)) := by
      have hf := fits_decReserve_of_addrTextEnv sp' p1 hfit hDecEv hgrow0
      rwa [← hcap1_eq, hpfx_def, hdec_def] at hf
    have hevs_res2 :
        doReserveEvents (DoReserveCall.mk sp' cap1 p1 pfx dec.length) =
          addrDecReserveEvents x.g.name.bytes x.g.device := by
      rw [hcap1_eq, ← hpfx_def, ← hdec_def]
      exact doReserveEvents_dec_grow_eq sp' p1 x.g.name.bytes x.g.device hgrow0
    clear hcap1_eq
    apply sepWPp_fold (vecU8At_header_unpack A.repAlloc sp' cap1 p1 pfx) (by sep_focus)
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨hpfx_le1, hcap1_63, _⟩ => ?_
    have hbhi_ult :
        (cap1 - BitVec.ofNat 64 pfx.length).ult (BitVec.ofNat 64 dec.length) = true :=
      cmp_hi_ult_true hpfx_le1 hcap1_63 hdec_le3 hgrow
    apply sepWPp_seq_lscro (mid := lsmpl.base 561) hcrl
    wp_steps_sync_594 (lsmpl.base 561)
    intro hcrl1
    obtain ⟨_, hfit2, hres2_bound⟩ :=
      reserveCap2_bounds (cap1 := cap1.toNat) (len := x.g.name.bytes.length) (decLen := dec.length)
        hcap1_34 hlen32 hdec_le3
    have hres2_bound' : reserveCap cap1.toNat pfx.length dec.length + 1 ≤ 9223372036854775808 := by
      subst hpfx_def; rw [List.length_append]; exact hres2_bound
    have hres2_le : reserveCap cap1.toNat pfx.length dec.length ≤ 9223372036854775807 := by
      omega
    refine sepWPp_weaken_pre_state (P' := fun s_cur =>
        vecU8At A.repAlloc sp' cap1 p1 pfx ∗
          ((sp' + 24#64) ↦₆₄ dCap) ∗
          ((sp' + 32#64) ↦₆₄ dPtr) ∗
          ((sp' + 40#64) ↦₆₄ BitVec.ofNat 64 dec.length) ∗
          (dPtr ↦ₛ dec) ∗ vecU8BufRest A.repAlloc dCap dPtr dec ∗
          stackAt sp' subStk ∗
          A.pool lim
            (M.stepEvents evsDec
              (M.stepEvents (addrDotReserveEvents x.g.name.bytes)
                (M.stepEvents (addrToOwnedEvents x.g.name.bytes) st0))) s_cur ∗ Fr)
      (by
        rw [vecU8At_eq_header_buf]
        unfold vecHeader
        simp (config := { failIfUnchanged := false }) only [arm64_norm, *]
        apply entails_of_eq
        sep_ac_rfl) ?_
    rw [stackAt_sub_le sp' hres_le hsub64]
    refine call_lscro_addr
      (x := (DoReserveCall.mk sp' cap1 p1 pfx dec.length,
        M.stepEvents evsDec
          (M.stepEvents (addrDotReserveEvents x.g.name.bytes)
            (M.stepEvents (addrToOwnedEvents x.g.name.bytes) st0))))
      hdoRes hcrl1
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, *])
      (ret_pc := (blkPl_594).base + res1RetOff)
      (by simp only [arm64_norm, *])
      (T := vecU8At A.repAlloc sp' cap1 p1 pfx ∗
        A.pool lim
          (M.stepEvents evsDec
            (M.stepEvents (addrDotReserveEvents x.g.name.bytes)
              (M.stepEvents (addrToOwnedEvents x.g.name.bytes) st0))) _ ∗ stackAt sp' resStack)
      (by
        apply same_eq
        dsimp [doReserveSpecOf]
        simp (config := { decide := true, failIfUnchanged := false }) only
          [arm64_norm, wp_norm, pure_true, emp_sepConj, *]
        unfold Same
        sep_ac_rfl)
      ?_
    intro s2 hpc2 hrun2 hsp2 hcs2 hcrl2
    dsimp only [doReserveSpecOf]
    rw [hevs_res2, sepConj_assoc]
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
    apply sepWPp_fold (vecU8At_open_slice A.repAlloc sp' cap2 p2 pfx dec.length hle2 hdec_pos)
      (by sep_focus)
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨hcap2_63, hp2_ne⟩ => ?_
    apply sepWPp_seq_lscro (mid := lsρ memcpyName) hcrl2
    wp_steps_sync_594 (lsρ memcpyName)
    intro hcrl3
    refine sepWPp_weaken_pre_state (P' := fun s_cur =>
        memRegion (p2 + BitVec.ofNat 64 pfx.length) dec.length ∗
          (dPtr ↦ₛ dec) ∗
          (sp' ↦₆₄ cap2) ∗
          ((sp' + 8#64) ↦₆₄ p2) ∗
          ((sp' + 16#64) ↦₆₄ BitVec.ofNat 64 pfx.length) ∗
          A.repAlloc.live p2 cap2.toNat 1 ∗ (p2 ↦ₛ pfx) ∗
          memRegion (p2 + BitVec.ofNat 64 (pfx.length + dec.length))
            (cap2.toNat - (pfx.length + dec.length)) ∗
          ((sp' + 24#64) ↦₆₄ dCap) ∗
          ((sp' + 32#64) ↦₆₄ dPtr) ∗
          ((sp' + 40#64) ↦₆₄ BitVec.ofNat 64 dec.length) ∗
          vecU8BufRest A.repAlloc dCap dPtr dec ∗
          stackAt sp' subStk ∗
          A.pool lim
            (M.stepEvents (addrDecReserveEvents x.g.name.bytes x.g.device)
              (M.stepEvents evsDec
                (M.stepEvents (addrDotReserveEvents x.g.name.bytes)
                  (M.stepEvents (addrToOwnedEvents x.g.name.bytes) st0)))) s_cur ∗ Fr)
      (by
        rw [stackAt_sub_le sp' hres_le hsub64]
        simp (config := { failIfUnchanged := false }) only [arm64_norm, *]
        apply entails_of_eq
        sep_ac_rfl) ?_
    rw [stackAt_sub_le sp' hext_le hsub64]
    refine call_lscro_addr (x := (p2 + BitVec.ofNat 64 pfx.length, dPtr, dec))
      hmemcpy hcrl3
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, *])
      (ret_pc := (blkPl_594).base + memcpy1RetOff)
      (by simp only [arm64_norm, *])
      (T := memRegion (p2 + BitVec.ofNat 64 pfx.length) dec.length ∗
        (dPtr ↦ₛ dec) ∗ stackAt sp' extHookStack)
      (by
        apply same_eq
        dsimp [withStack, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec]
        simp (config := { decide := true, failIfUnchanged := false }) only
          [arm64_norm, wp_norm, pure_true, emp_sepConj, *]
        unfold Same
        sep_ac_rfl)
      ?_
    intro s4 hpc4 hrun4 hsp4 hcs4 hcrl4
    dsimp only [withStack, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec]
    simp only [sepConj_assoc]
    refine SepWPp.pure_left fun hvm4 => ?_
    refine SepWPp.pure_left fun ⟨_, htr4⟩ => ?_
    refine ProofLib.SepWPp.transport_budgetPool hvm4 (hnext := ?_)
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
        hx19_4 hx20_4 hx21_4 hx22_4 hvregs_4 hcrl4 hd_le hd_63 hd_ptr)
    rw [stackAt_sub_le sp' hext_le hsub64, ← hcap2_toNat]
    apply step_entails (vecU8Buf_close_slice A.repAlloc cap2 p2 pfx dec hle2 (by omega) hcap2_63 hp2_ne)
      (by
        (conv_lhs =>
          simp (config := { failIfUnchanged := false }) only [arm64_norm]
          simp (config := { failIfUnchanged := false }) only [← RustCliAllocBudget.repAlloc_live])
        sep_focus)
    simp (config := { failIfUnchanged := false }) only [arm64_norm, *]
    apply entails_of_eq
    sep_ac_rfl
  · have hngrow0 :
        ¬ (BitVec.ofNat 64 (reserveCap x.g.name.bytes.length x.g.name.bytes.length 1)).toNat <
          (x.g.name.bytes ++ [0x2e#8]).length +
            (decimalText (x.g.device.zeroExtend 32).toNat).length := by
      rwa [← hcap1_eq, hpfx_def, hdec_def]
    have hevs_res2_nil : addrDecReserveEvents x.g.name.bytes x.g.device = [] :=
      addrDecReserveEvents_not_grow x.g.name.bytes x.g.device hngrow0
    clear hcap1_eq
    have hle1 : pfx.length + dec.length ≤ cap1.toNat := by omega
    apply sepWPp_fold (vecU8At_open_slice A.repAlloc sp' cap1 p1 pfx dec.length hle1 hdec_pos)
      (by sep_focus)
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨hcap1_63, hp1_ne⟩ => ?_
    have hbhi_ult :
        (cap1 - BitVec.ofNat 64 pfx.length).ult (BitVec.ofNat 64 dec.length) = false :=
      cmp_hi_ult_false hcap1_63 hdec_le3 hle1
    apply sepWPp_seq_lscro (mid := lsρ memcpyName) hcrl
    wp_steps_sync_594 (lsρ memcpyName)
    intro hcrl1
    rw [stackAt_sub_le sp' hext_le hsub64]
    refine call_lscro_addr (x := (p1 + BitVec.ofNat 64 pfx.length, dPtr, dec))
      hmemcpy hcrl1
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, *])
      (ret_pc := (blkPl_594).base + memcpy1RetOff)
      (by simp only [arm64_norm, *])
      (T := memRegion (p1 + BitVec.ofNat 64 pfx.length) dec.length ∗
        (dPtr ↦ₛ dec) ∗ stackAt sp' extHookStack)
      (by
        apply same_eq
        dsimp [withStack, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec]
        simp (config := { decide := true, failIfUnchanged := false }) only
          [arm64_norm, wp_norm, pure_true, emp_sepConj, *]
        unfold Same
        sep_ac_rfl)
      ?_
    intro s2 hpc2 hrun2 hsp2 hcs2 hcrl2
    dsimp only [withStack, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec]
    simp only [sepConj_assoc]
    refine SepWPp.pure_left fun hvm2 => ?_
    refine SepWPp.pure_left fun ⟨_, htr2⟩ => ?_
    refine ProofLib.SepWPp.transport_budgetPool hvm2 (hnext := ?_)
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
        hx19_2 hx20_2 hx21_2 hx22_2 hvregs_2 hcrl2 hd_le hd_63 hd_ptr)
    rw [stackAt_sub_le sp' hext_le hsub64, hevs_res2_nil, AllocCostModel.stepEvents_nil]
    apply step_entails (vecU8Buf_close_slice A.repAlloc cap1 p1 pfx dec hle1 (by omega) hcap1_63 hp1_ne)
      (by
        (conv_lhs =>
          simp (config := { failIfUnchanged := false }) only [arm64_norm]
          simp (config := { failIfUnchanged := false }) only [← RustCliAllocBudget.repAlloc_live])
        sep_focus)
    simp (config := { failIfUnchanged := false }) only [arm64_norm, *]
    apply entails_of_eq
    sep_ac_rfl

end LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.PlacedBudgetAux
