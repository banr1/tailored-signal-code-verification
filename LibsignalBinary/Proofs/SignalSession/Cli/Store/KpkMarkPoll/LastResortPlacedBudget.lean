/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CallsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortAfterGetPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortAfterGetPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Fs
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Fetches
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Pure
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `last_resort` Branch for `KpkMarkPoll`

Defines `KpkBaseKeysReserveEnv` and `KpkLastResortPreAfterGetEnv`, and proves budget-threaded
`kpk_last_resort_118_placed_of_after` and `kpk_last_resort_118_placed` (`+280 .. +372`) on
Block `578` (`lsProg_578 H`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortPlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall doReserveStackX reserveCap)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles FsInv LibsignalCodeRoLoaded TraceFsSound withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SignalSession.Cli
  (DirGhost KpkBaseKeysOk KpkMarkPollGhost KpkSeenOk ReadRule baseKeysName
   cliBcmpName cliBcmpSpec dirAt getResultAt keyName subroutine_ok_withFsInv utf8)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_578 blkPl_578 lsProg_578)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
  (CliPanicHooksPlaced ls_transfer_lscro)
open CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers
  (assemble_baseKeysName baseKeysName_eq_append bind_sepWPp_state_mark cs_vregs cs_x19 cs_x20
   cs_x24 cs_x26 cs_x28 cs_x29 dotBaseKeAddrPlaced epiloguePre fast_name_cap_ge
   files_eq_of_fsInv_trace_eq header3_entails_memRegion24 kpkMarkRoBundlePlaced kpkMinStk kpkSubMax
   memRegion_two_16 reserve_name_bound sepWPp_conseq sepWPp_of_sepWP_fs_placed
   setWidth_32_setWidth_64 slot_b0_24_24_merge spAligned_sub_f0 subStack_merge_pool_mid
   subStack_merge_rev_adj subStack_split utf8_dot_base_ke_length vecU8At_of_live_parts
   vecU8At_unpack_any vecU8At_unpack_pos_lr vecU8Tail vecU8_unpack_at)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserveSpecOf)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (DoReserveEnv doReserveEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced decimalSpecPlaced dirGetSpecPlaced dirPutSpecPlaced
   kpkMarkPollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CalleesPlacedBudget
  (kpkReserve_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CallsPlacedBudget
  (kpk_call_decimal_fs_placed kpk_call_dirGet_fs_placed kpk_call_reserve_fs_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget (optDeallocBufEvents)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.add_zero BitVec.zero_add
  BitVec.toNat_zero setWidth_32_setWidth_64

local macro_rules
  | `(tactic| kpk_norm) =>
    `(tactic|
      ((try with_reducible rfl)
       (try simp +zetaDelta only [wp_norm])
       (try simp +zetaDelta only [arm64_norm])
       (try simp +zetaDelta only [*])
       (try with_reducible rfl)
       try bv_omega))

/-! ## 1. Finite `.base-keys` Reserve Envelope -/

/-- Exact `.base-keys` `do_reserve_and_handle` event list when `decimal(id)` returned `spare`
unused capacity bytes (`0 ≤ spare ≤ 9`). -/
def kpkBaseKeysReserveEventsAt (id : BitVec 32) (spare : Nat) : List AllocEvent :=
  doReserveEvents ⟨0#64, BitVec.ofNat 64 ((keyName id).length + spare), 0#64, keyName id, 10⟩

/-- Finite 11-way disjunction of the `.base-keys` suffix reserve step:
either no reserve (`evs = []`), or `spare ∈ 0..9` (`decCap.toNat = (keyName id).length + spare`). -/
def KpkBaseKeysReserveEnv (id : BitVec 32) (evs : List AllocEvent) : Prop :=
  evs = [] ∨
  evs = kpkBaseKeysReserveEventsAt id 0 ∨
  evs = kpkBaseKeysReserveEventsAt id 1 ∨
  evs = kpkBaseKeysReserveEventsAt id 2 ∨
  evs = kpkBaseKeysReserveEventsAt id 3 ∨
  evs = kpkBaseKeysReserveEventsAt id 4 ∨
  evs = kpkBaseKeysReserveEventsAt id 5 ∨
  evs = kpkBaseKeysReserveEventsAt id 6 ∨
  evs = kpkBaseKeysReserveEventsAt id 7 ∨
  evs = kpkBaseKeysReserveEventsAt id 8 ∨
  evs = kpkBaseKeysReserveEventsAt id 9

/-- Composite pre-`after_lr_get` envelope on `+280 .. +372`:
`decimal(x.id)` → `KpkBaseKeysReserveEnv x.id` → `last_resort.get(.base-keys)`. -/
def KpkLastResortPreAfterGetEnv
    (DecEnv : BitVec 32 → List AllocEvent → Prop)
    (GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop)
    (F0 : FsFiles) (x : KpkMarkPollGhost) : List AllocEvent → Prop :=
  SeqEnv (DecEnv x.id)
    (SeqEnv (KpkBaseKeysReserveEnv x.id)
      (GetEnv F0 x.kg.lastResort (baseKeysName x.id)))

theorem kpkBaseKeysReserveEnv_of_ule9 {id : BitVec 32} {v decCap decPtr : BitVec 64}
    (hkn_lt32 : (keyName id).length < 2 ^ 32)
    (hd_len : (keyName id).length ≤ decCap.toNat)
    (_hd_lt : decCap.toNat < 2 ^ 63)
    (hule : (decCap - BitVec.ofNat 64 (keyName id).length).ule 9#64 = true) :
    KpkBaseKeysReserveEnv id (doReserveEvents ⟨v, decCap, decPtr, keyName id, 10⟩) := by
  have hlen_nat : (BitVec.ofNat 64 (keyName id).length).toNat = (keyName id).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub_nat : (decCap - BitVec.ofNat 64 (keyName id).length).toNat =
      decCap.toNat - (keyName id).length := by
    rw [BitVec.toNat_sub_of_le]
    · rw [hlen_nat]
    · rw [BitVec.le_def, hlen_nat]
      exact hd_len
  have hle9 : decCap.toNat - (keyName id).length ≤ 9 := by
    rw [BitVec.ule_iff_toNat_le] at hule
    change (decCap - BitVec.ofNat 64 (keyName id).length).toNat ≤ 9 at hule
    omega
  let spare := decCap.toNat - (keyName id).length
  have hcap_eq : decCap = BitVec.ofNat 64 ((keyName id).length + spare) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp [spare]; omega)]
    dsimp [spare]; omega
  have hev_eq :
      doReserveEvents ⟨v, decCap, decPtr, keyName id, 10⟩ =
        kpkBaseKeysReserveEventsAt id spare := by
    rw [hcap_eq]
    rfl
  rw [hev_eq]
  have hsp_le9 : spare ≤ 9 := hle9
  unfold KpkBaseKeysReserveEnv
  match spare, hsp_le9 with
  | 0, _ => exact Or.inr (Or.inl rfl)
  | 1, _ => exact Or.inr (Or.inr (Or.inl rfl))
  | 2, _ => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | 3, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | 4, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  | 5, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  | 6, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  | 7, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  | 8, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  | 9, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))))
  | _ + 10, h => omega

/-! ## 2. Continuation-Parameterized `+280 .. +372` Step (`kpk_last_resort_118_placed_of_after`) -/

set_option maxHeartbeats 1200000 in
/-- Verifies `+280 .. +372` (`decimal(id)` + optional `.base-keys` reserve + `.base-keys` suffix
write + `last_resort.get`) under `RustCliAllocBudget M`, handing off at `+372` to an arbitrary
continuation `hafter_lr`. -/
theorem kpk_last_resort_118_placed_of_after [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {decStk getStk putStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hP : CliPanicHooksPlaced H)
    (hDecimal : subroutine_ok (lsProg_578 H) (lsmpl.base 597)
      (decimalSpecPlaced A lim DecEnv decStk))
    (hGet : subroutine_ok (lsProg_578 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
    (hFs : TraceFsSound (lsProg_578 H))
    (x : KpkMarkPollGhost) (st : M.σ) (s0 s : State)
    (wDot wR0 wR7 wM0 wM6 : BitVec 64)
    (f0 f1 f2 f3 : BitVec 64) (tmp32 : BitVec 32)
    (P : SepProp) {Q Qp : State → SepProp → Prop}
    (hfit_pre : FitsEnv M lim st (KpkLastResortPreAfterGetEnv DecEnv GetEnv s0.fs.files x))
    (hstk : kpkMinStk decStk getStk putStk ≤ stk)
    (hhi_stk : stk ≤ 2 ^ 64)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hwDot : unpack64 wDot = utf8 ".base-ke")
    (hBkOk : KpkBaseKeysOk pathOk x.kg.lastResort x.id)
    (hpc : s.pc = (blkPl_578).base + bv% (280))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0xf0#64)
    (hfp : s.readReg64 .x29 = s0.sp - 0x60#64)
    (htr : s.trace = s0.trace)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hfs : FsInv s0.fs.files s0.trace s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx23 : s.readReg64 .x23 = x.id.setWidth 64)
    (hx26 : s.readReg64 .x26 = x.self)
    (hx28 : s.readReg64 .x28 = x.signedId.setWidth 64)
    (hfoc : P ⊢
      kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
      stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
      memRegion (s0.sp - 0xf0#64) 8 ∗
      ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
      ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
      memRegion (s0.sp - 0xc8#64) 24 ∗
      memRegion (s0.sp - 0xb0#64) 48 ∗
      memRegion (s0.sp - 0x80#64) 24 ∗
      memRegion (s0.sp - 0x68#64) 4 ∗
      ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
      dirAt A.repAlloc x.self x.kg.oneTime ∗
      dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
      (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
      epiloguePre s0 x ∗ A.pool lim st s)
    (hafter_lr : ∀ (s4 : State) (evsPre : List AllocEvent)
      (filePtr fileCap : BitVec 64) (gr : Except Unit (List (BitVec 8))),
      KpkLastResortPreAfterGetEnv DecEnv GetEnv s0.fs.files x evsPre →
      (gr = x.kg.lastResort.get rd s0.fs.files (baseKeysName x.id) ∧ s4.trace = s0.trace) →
      (baseKeysName x.id).length ≤ fileCap.toNat →
      fileCap.toNat < 2 ^ 63 →
      filePtr ≠ 0#64 →
      s4.pc = (blkPl_578).base + 372#64 →
      s4.status = .Running →
      s4.sp = s0.sp - 0xf0#64 →
      s4.readReg64 .x29 = s0.sp - 0x60#64 →
      LibsignalCodeRoLoaded lsmpl s4.mem →
      calleeSavedVRegs s4 = calleeSavedVRegs s0 →
      s4.readReg64 .x19 = x.fut →
      s4.readReg64 .x20 = x.out →
      s4.readReg64 .x24 = BitVec.ofNat 64 (baseKeysName x.id).length →
      s4.readReg64 .x26 = x.self →
      s4.readReg64 .x28 = x.signedId.setWidth 64 →
      SepWPp (lsProg_578 H) (s0.readReg64 .lr) s4
        (getResultAt A.repAlloc (s0.sp - 0xb0#64) gr ∗
          kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
          stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
          memRegion (s0.sp - 0xf0#64) 8 ∗
          ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
          ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗ ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
          memRegion (s0.sp - 0xc8#64) 24 ∗
          memRegion (s0.sp - 0x80#64) 24 ∗
          memRegion (s0.sp - 0x68#64) 4 ∗
          ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
          bytesAt false filePtr (baseKeysName x.id) ∗
          vecU8Tail A.repAlloc fileCap filePtr (baseKeysName x.id) ∗
          dirAt A.repAlloc x.self x.kg.oneTime ∗
          dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
          (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
          epiloguePre s0 x ∗ A.pool lim (M.stepEvents evsPre st) s4)
        Q Qp) :
    SepWPp (lsProg_578 H) (s0.readReg64 .lr) s P Q Qp := by
  have hhi : kpkMinStk decStk getStk putStk ≤ 2 ^ 64 := by omega
  have hdec_le : decStk ≤ kpkSubMax decStk getStk putStk := by unfold kpkSubMax; omega
  have hget_le : getStk ≤ kpkSubMax decStk getStk putStk := by unfold kpkSubMax; omega
  have hres_le : doReserveStackX ≤ kpkSubMax decStk getStk putStk := by unfold kpkSubMax; omega
  have hsp_al : s.spAligned = true := spAligned_sub_f0 hsp_align hsp
  have hdec_fs := subroutine_ok_withFsInv hFs hDecimal s0.fs.files s0.trace
  have hres : subroutine_ok (lsProg_578 H) (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (doReserveSpecOf doReserveStackX A lim)) :=
    ls_transfer_lscro (callerProg := lsProg_578 H) (j := 561)
      (kpkReserve_placed_ok hC hP (le_refl doReserveStackX))
  have hres_fs := subroutine_ok_withFsInv hFs hres s0.fs.files s0.trace
  have hget_fs := subroutine_ok_withFsInv hFs hGet s0.fs.files s0.trace
  have hfit_dec : FitsEnv M lim st (DecEnv x.id) := hfit_pre.seq_left
  clear hC hP hDecimal hGet hres
  dsimp only [lsProg_578] at hFs hdec_fs hres_fs hget_fs hafter_lr hpc ⊢
  refine sepWPp_conseq hfoc ?_
  rw [ProofLib.memRegion_split' (b := s0.sp - 0xb0#64) (n := 24) (k := 24)
        (b' := s0.sp - 0x98#64) rfl (by bv_omega) (by decide)]
  apply sepWPp_of_sepWP_fs_placed
    (mid := lsmpl.base 597)
    hFs hcrl hfs
  wp_steps_sync_pool (lsmpl.base 597)
  apply SepWP.done
    (by kpk_norm)
    (by wp_norm_lhs)
  intro hcrl_d1 hfs_d1
  apply bind_sepWPp_state_mark; intro st_d1
  have hsp_d1 : st_d1.sp = s0.sp - 0xf0#64 := by dsimp only [st_d1]; (try kpk_norm)
  dsimp only [st_d1] at *
  refine kpk_call_decimal_fs_placed hdec_fs { n := x.id, ret := s0.sp - 0xb0#64 } st
    (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
        (kpkSubMax decStk getStk putStk - decStk) ∗
      kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
      memRegion (s0.sp - 0xf0#64) 8 ∗
      ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
      ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
      memRegion (s0.sp - 0xc8#64) 24 ∗
      memRegion (s0.sp - 0x98#64) 24 ∗
      memRegion (s0.sp - 0x80#64) 24 ∗
      memRegion (s0.sp - 0x68#64) 4 ∗
      ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
      dirAt A.repAlloc x.self x.kg.oneTime ∗
      dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
      (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
      epiloguePre s0 x)
    (ret_pc := (blkPl_578).base + bv% (292))
    (by kpk_norm)
    (by kpk_norm)
    (spAligned_sub_f0 hsp_align hsp_d1)
    (by kpk_norm)
    hcrl_d1
    hfs_d1
    (by kpk_norm)
    (by kpk_norm)
    hfit_dec
    (by
      rw [hsp_d1, subStack_split s0.sp hdec_le hhi]
      unfold epiloguePre
      kpk_sep_norm
      sep_focus)
    fun s1 evsDec hpc1 hrun1 hsp1 hcs1 hcrl1 hfs1 htr1 hdecEv => ?_
  have hs1_sp : s1.sp = s0.sp - 0xf0#64 := hsp1.trans hsp_d1
  have hs1_al : s1.spAligned = true := spAligned_sub_f0 hsp_align hs1_sp
  have hs1_tr : s1.trace = s0.trace := by rw [htr1]; kpk_norm
  have hfit_after_dec :
      FitsEnv M lim (M.stepEvents evsDec st)
        (SeqEnv (KpkBaseKeysReserveEnv x.id)
          (GetEnv s0.fs.files x.kg.lastResort (baseKeysName x.id))) :=
    hfit_pre.seq_right hdecEv
  have hkn_lt32 : (keyName x.id).length < 2 ^ 32 := by
    have hb1 := hBkOk.1
    rw [← baseKeysName_eq_append, List.length_append, List.length_append] at hb1
    omega
  change SepWPp _ _ _ ((vecU8 A.repAlloc (s0.sp - 0xb0#64) (keyName x.id) ∗ _ ∗ _) ∗ _) _ _
  rw [hsp_d1, subStack_merge_pool_mid s0.sp hdec_le hhi,
      vecU8_unpack_at A.repAlloc (s0.sp - 0xb0#64) (keyName x.id)]
  kpk_sep_norm
  refine SepWPp.exists_elim fun decCap => SepWPp.exists_elim fun decPtr => ?_
  rw [vecU8At_unpack_any A.repAlloc (s0.sp - 0xb0#64) decCap decPtr (keyName x.id)]
  kpk_sep_norm
  refine SepWPp.pure_elim fun ⟨hd_len, hd_lt, hd_ptr⟩ => ?_
  have e_a8 : s0.sp - 0xb0#64 + 8#64 = s0.sp - 0xa8#64 := by bv_omega
  have e_a0 : s0.sp - 0xb0#64 + 16#64 = s0.sp - 0xa0#64 := by bv_omega
  rw [e_a8, e_a0]

  have hjoin_316 : ∀ (s2 : State) (evsDecRes : List AllocEvent)
      (fileCap filePtr : BitVec 64) (Q2 : SepProp),
      SeqEnv (DecEnv x.id) (KpkBaseKeysReserveEnv x.id) evsDecRes →
      FitsEnv M lim (M.stepEvents evsDecRes st)
        (GetEnv s0.fs.files x.kg.lastResort (baseKeysName x.id)) →
      (keyName x.id).length + 10 ≤ fileCap.toNat →
      fileCap.toNat < 2 ^ 63 →
      filePtr ≠ 0#64 →
      s2.pc = (blkPl_578).base + bv% (316) →
      s2.status = .Running →
      s2.sp = s0.sp - 0xf0#64 →
      s2.readReg64 .x29 = s0.sp - 0x60#64 →
      s2.trace = s0.trace →
      LibsignalCodeRoLoaded lsmpl s2.mem →
      FsInv s0.fs.files s0.trace s2 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      s2.readReg64 .x1 = BitVec.ofNat 64 (keyName x.id).length →
      s2.readReg64 .x19 = x.fut →
      s2.readReg64 .x20 = x.out →
      s2.readReg64 .x26 = x.self →
      s2.readReg64 .x28 = x.signedId.setWidth 64 →
      (Q2 ⊢
        kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
        stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
        memRegion (s0.sp - 0xf0#64) 8 ∗
        ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        memRegion (s0.sp - 0xc8#64) 24 ∗
        ((s0.sp - 0xb0#64) ↦₆₄ fileCap) ∗
        ((s0.sp - 0xa8#64) ↦₆₄ filePtr) ∗
        ((s0.sp - 0xa0#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
        memRegion (s0.sp - 0x98#64) 24 ∗
        memRegion (s0.sp - 0x80#64) 24 ∗
        memRegion (s0.sp - 0x68#64) 4 ∗
        ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
        A.repAlloc.live filePtr fileCap.toNat 1 ∗
        (filePtr ↦ₛ keyName x.id) ∗
        memRegion (filePtr + BitVec.ofNat 64 (keyName x.id).length)
          (fileCap.toNat - (keyName x.id).length) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
        epiloguePre s0 x ∗ A.pool lim (M.stepEvents evsDecRes st) s2) →
      SepWPp (blkPC_578.rebase (blkPl_578).base H) (s0.readReg64 .lr) s2 Q2 Q Qp := by
    intro s2 evsDecRes fileCap filePtr Q2 hevsDR hfitGet hf_ge10 hf_lt hf_ptr
      hpc2 hrun2 hsp2 hfp2 htr2 hcrl2 hfs2 hv2 s2_1 s2_19 s2_20 s2_26 s2_28 hQ2
    have hf_ne0 : fileCap ≠ 0#64 :=
      fun h0 => by have : fileCap.toNat = 0 := by subst h0; rfl
                   omega
    have hsp_al2 : s2.spAligned = true := spAligned_sub_f0 hsp_align hsp2
    refine sepWPp_conseq hQ2 ?_
    have hbkn_len : (baseKeysName x.id).length = (keyName x.id).length + 10 := by
      rw [← baseKeysName_eq_append, List.length_append, List.length_append,
          utf8_dot_base_ke_length]; rfl
    have hafter_dot : ∀ (s3 : State) (Q3 : SepProp),
        s3.pc = (blkPl_578).base + bv% (328) →
        s3.status = .Running →
        s3.sp = s0.sp - 0xf0#64 →
        s3.readReg64 .x29 = s0.sp - 0x60#64 →
        s3.trace = s0.trace →
        LibsignalCodeRoLoaded lsmpl s3.mem →
        FsInv s0.fs.files s0.trace s3 →
        calleeSavedVRegs s3 = calleeSavedVRegs s0 →
        s3.readReg64 .x1 = BitVec.ofNat 64 (keyName x.id).length →
        s3.readReg64 .x2 = filePtr →
        s3.readReg64 .x8 = dotBaseKeAddrPlaced →
        s3.readReg64 .x19 = x.fut →
        s3.readReg64 .x20 = x.out →
        s3.readReg64 .x26 = x.self →
        s3.readReg64 .x28 = x.signedId.setWidth 64 →
        (Q3 ⊢
          kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
          stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
          memRegion (s0.sp - 0xf0#64) 8 ∗
          ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
          ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
          memRegion (s0.sp - 0xc8#64) 24 ∗
          memRegion (s0.sp - 0xb0#64) 48 ∗
          memRegion (s0.sp - 0x80#64) 24 ∗
          memRegion (s0.sp - 0x68#64) 4 ∗
          ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
          A.repAlloc.live filePtr fileCap.toNat 1 ∗
          (filePtr ↦ₛ keyName x.id) ∗
          memRegion (filePtr + BitVec.ofNat 64 (keyName x.id).length)
            (fileCap.toNat - (keyName x.id).length) ∗
          dirAt A.repAlloc x.self x.kg.oneTime ∗
          dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
          (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
          epiloguePre s0 x ∗ A.pool lim (M.stepEvents evsDecRes st) s3) →
        SepWPp (blkPC_578.rebase (blkPl_578).base H) (s0.readReg64 .lr) s3 Q3 Q Qp := by
      intro s3 Q3 hpc3 hrun3 hsp3 hfp3 htr3 hcrl3 hfs3 hv3
        s3_1 s3_2 s3_8 s3_19 s3_20 s3_26 s3_28 hQ3
      have hsp_al3 : s3.spAligned = true := spAligned_sub_f0 hsp_align hsp3
      refine sepWPp_conseq hQ3 ?_
      have hsplit_10 :
          memRegion (filePtr + BitVec.ofNat 64 (keyName x.id).length)
            (fileCap.toNat - (keyName x.id).length) =
          memRegion (filePtr + BitVec.ofNat 64 (keyName x.id).length) 8 ∗
          memRegion (filePtr + BitVec.ofNat 64 (keyName x.id).length + 8#64) 2 ∗
          memRegion (filePtr + BitVec.ofNat 64 (baseKeysName x.id).length)
            (fileCap.toNat - (baseKeysName x.id).length) := by
        rw [ProofLib.memRegion_split'
              (b := filePtr + BitVec.ofNat 64 (keyName x.id).length)
              (n := 8) (k := fileCap.toNat - (keyName x.id).length - 8)
              (b' := filePtr + BitVec.ofNat 64 (keyName x.id).length + 8#64)
              (by omega) rfl (by omega),
            ProofLib.memRegion_split'
              (b := filePtr + BitVec.ofNat 64 (keyName x.id).length + 8#64)
              (n := 2) (k := fileCap.toNat - (baseKeysName x.id).length)
              (b' := filePtr + BitVec.ofNat 64 (baseKeysName x.id).length)
              (by omega)
              (by rw [hbkn_len, BitVec.ofNat_add]; bv_omega)
              (by omega)]
      rw [hsplit_10,
          ProofLib.memRegion_eight (filePtr + BitVec.ofNat 64 (keyName x.id).length),
          memRegion_two_16]
      unfold kpkMarkRoBundlePlaced
      kpk_sep_norm
      refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d8 => ?_

      apply sepWPp_of_sepWP_fs_placed
        (mid := lsmpl.base 589) hFs hcrl3 hfs3
      wp_steps_sync_pool (lsmpl.base 589)
      apply SepWP.done
        (by kpk_norm)
        (by wp_norm_lhs)
      intro hcrl_g2 hfs_g2
      apply bind_sepWPp_state_mark; intro st_g2
      have hsp_g2 : st_g2.sp = s0.sp - 0xf0#64 := by dsimp only [st_g2]; (try kpk_norm)
      have htr_g2 : st_g2.trace = s0.trace := by dsimp only [st_g2]; (try kpk_norm)
      have hfiles_g2 : st_g2.fs.files = s0.fs.files :=
        files_eq_of_fsInv_trace_eq hfs_g2 htr_g2
      dsimp only [st_g2] at *
      have hadd10 : BitVec.ofNat 64 (keyName x.id).length + 10#64 =
          BitVec.ofNat 64 (baseKeysName x.id).length := by
        rw [hbkn_len, BitVec.ofNat_add]
      have htoNat_bkn :
          (BitVec.ofNat 64 (baseKeysName x.id).length).toNat = (baseKeysName x.id).length := by
        have := hBkOk.1
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine kpk_call_dirGet_fs_placed hget_fs
        { ret := s0.sp - 0xb0#64, self := x.self + 0x28#64, dir := x.kg.lastResort,
          nameA := filePtr, name := baseKeysName x.id, nameRo := false }
        (M.stepEvents evsDecRes st)
        (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
            (kpkSubMax decStk getStk putStk - getStk) ∗
          kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
          memRegion (s0.sp - 0xf0#64) 8 ∗
          ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
          ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗ ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
          memRegion (s0.sp - 0xc8#64) 24 ∗
          memRegion (s0.sp - 0x80#64) 24 ∗
          memRegion (s0.sp - 0x68#64) 4 ∗
          ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
          vecU8Tail A.repAlloc fileCap filePtr (baseKeysName x.id) ∗
          dirAt A.repAlloc x.self x.kg.oneTime ∗
          (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
          epiloguePre s0 x)
        (ret_pc := (blkPl_578).base + bv% (372))
        (by kpk_norm)
        (by kpk_norm)
        (spAligned_sub_f0 hsp_align hsp_g2)
        (by kpk_norm)
        hcrl_g2
        hfs_g2
        (by kpk_norm)
        (by kpk_norm)
        (by kpk_norm)
        (by
          refine Eq.trans (congrArg BitVec.toNat
            (show _ = BitVec.ofNat 64 (keyName x.id).length + 10#64 by kpk_norm)) ?_
          rw [hadd10, htoNat_bkn])
        hBkOk.1
        hBkOk.2.1
        hBkOk.2.2
        (by rw [hfiles_g2]; exact hfitGet)
        (by
          rw [hsp_g2, subStack_split s0.sp hget_le hhi]
          have htail_file :
              A.repAlloc.live filePtr fileCap.toNat 1 ∗
                memRegion (filePtr + BitVec.ofNat 64 (baseKeysName x.id).length)
                  (fileCap.toNat - (baseKeysName x.id).length) =
              vecU8Tail A.repAlloc fileCap filePtr (baseKeysName x.id) := by
            unfold vecU8Tail; simp only [hf_ne0, ite_false]
          have hbytes_file := assemble_baseKeysName filePtr wDot x.id hwDot
          unfold kpkMarkRoBundlePlaced epiloguePre
          kpk_sep_norm
          refine Entails.trans ?_
            (sepConj_mono_right (sepConj_mono_left (Entails.of_eq hbytes_file)))
          rw [← htail_file]
          kpk_sep_norm
          sep_focus)
        fun s4 evsGet gr hpc4 hrun4 hsp4 hcs4 hcrl4 _hfs4 hgr4 => ?_
      have hs4_sp : s4.sp = s0.sp - 0xf0#64 := hsp4.trans hsp_g2
      rcases hgr4 with ⟨hgr_eq, htr4_eq, hevsGet⟩
      rw [hfiles_g2] at hgr_eq hevsGet
      have hgr4_s0 :
          gr = x.kg.lastResort.get rd s0.fs.files (baseKeysName x.id) ∧ s4.trace = s0.trace :=
        ⟨hgr_eq, htr4_eq.trans htr_g2⟩
      have hevsPre :
          KpkLastResortPreAfterGetEnv DecEnv GetEnv s0.fs.files x (evsDecRes ++ evsGet) := by
        unfold KpkLastResortPreAfterGetEnv
        rcases hevsDR with hevD | ⟨evs1, evs2, rfl, hevD, hevR⟩
        · exact SeqEnv.append hevD (SeqEnv.append (evs₁ := []) (Or.inl rfl) hevsGet)
        · rw [List.append_assoc]
          exact SeqEnv.append hevD (SeqEnv.append hevR hevsGet)
      have hpool_eq :
          M.stepEvents evsGet (M.stepEvents evsDecRes st) =
            M.stepEvents (evsDecRes ++ evsGet) st := by
        rw [M.stepEvents_append]
      rw [hpool_eq]
      refine sepWPp_conseq ?_
        (hafter_lr s4 (evsDecRes ++ evsGet) filePtr fileCap gr
          hevsPre hgr4_s0
          (by rw [hbkn_len]; exact hf_ge10) hf_lt hf_ptr
          (by kpk_norm) hrun4 hs4_sp
          (by rw [(cs_x29 hcs4)]; kpk_norm)
          hcrl4
          (by rw [(cs_vregs hcs4)]; kpk_norm)
          (by rw [(cs_x19 hcs4)]; kpk_norm)
          (by rw [(cs_x20 hcs4)]; kpk_norm)
          (by rw [(cs_x24 hcs4)]; rw [← hadd10]; kpk_norm)
          (by rw [(cs_x26 hcs4)]; kpk_norm)
          (by rw [(cs_x28 hcs4)]; kpk_norm))
      rw [hsp_g2, subStack_split s0.sp hget_le hhi]
      unfold epiloguePre
      kpk_sep_norm
      sep_focus
    apply sepWPp_of_sepWP_fs_placed
      (mid := (blkPl_578).base + bv% (328))
      hFs hcrl2 hfs2
    wp_steps_sync_pool ((blkPl_578).base + bv% (328))
    apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hcrl_dot hfs_dot
    refine hafter_dot _ _ (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm)
      hcrl_dot hfs_dot (by kpk_norm) (by kpk_norm) (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm) ?_

    have hm_hdr := header3_entails_memRegion24 (s0.sp - 0xb0#64) (s0.sp - 0xa8#64)
      (s0.sp - 0xa0#64) fileCap filePtr (BitVec.ofNat 64 (keyName x.id).length)
      (by bv_omega) (by bv_omega)
    have hm_b0 := Entails.trans (sepConj_mono_left hm_hdr) (slot_b0_24_24_merge s0.sp)
    unfold epiloguePre
    kpk_sep_norm
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left hm_b0))))))))))
    sep_focus
  by_cases hule : (decCap - BitVec.ofNat 64 (keyName x.id).length).ule 9#64 = true
  · have hbound10 := reserve_name_bound hkn_lt32 hd_len hd_lt hule
    have hresEv :
        KpkBaseKeysReserveEnv x.id
          (doReserveEvents ⟨s0.sp - 0xb0#64, decCap, decPtr, keyName x.id, 10⟩) :=
      kpkBaseKeysReserveEnv_of_ule9 hkn_lt32 hd_len hd_lt hule
    have hfit_res :
        FitsEnv M lim (M.stepEvents evsDec st)
          (DoReserveEnv ⟨s0.sp - 0xb0#64, decCap, decPtr, keyName x.id, 10⟩) := by
      intro evs hevs
      subst hevs
      exact hfit_after_dec.seq_left _ hresEv
    have hfit_get_res :
        FitsEnv M lim
          (M.stepEvents (evsDec ++ doReserveEvents ⟨s0.sp - 0xb0#64, decCap, decPtr, keyName x.id, 10⟩) st)
          (GetEnv s0.fs.files x.kg.lastResort (baseKeysName x.id)) := by
      rw [M.stepEvents_append]
      exact hfit_after_dec.seq_right hresEv
    apply sepWPp_of_sepWP_fs_placed
      (mid := lsmpl.base 561)
      hFs hcrl1 hfs1
    wp_steps_sync_pool (lsmpl.base 561)
    apply SepWP.done
      (by kpk_norm)
      (by wp_norm_lhs)
    intro hcrl_res hfs_res
    apply bind_sepWPp_state_mark; intro st_res
    have hsp_res : st_res.sp = s0.sp - 0xf0#64 := by (try dsimp only [st_res]); (try kpk_norm)
    (try dsimp only [st_res] at *)
    have hlen_kn_nat : (BitVec.ofNat 64 (keyName x.id).length).toNat = (keyName x.id).length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine kpk_call_reserve_fs_placed hres_fs ⟨s0.sp - 0xb0#64, decCap, decPtr, keyName x.id, 10⟩
      (M.stepEvents evsDec st)
      (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
          (kpkSubMax decStk getStk putStk - doReserveStackX) ∗
        kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
        memRegion (s0.sp - 0xf0#64) 8 ∗
        ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
        memRegion (s0.sp - 0xc8#64) 24 ∗
        memRegion (s0.sp - 0x98#64) 24 ∗
        memRegion (s0.sp - 0x80#64) 24 ∗
        memRegion (s0.sp - 0x68#64) 4 ∗
        ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
        epiloguePre s0 x)
      (ret_pc := (blkPl_578).base + bv% (1008))
      (by kpk_norm)
      (by kpk_norm)
      (spAligned_sub_f0 hsp_align hsp_res)
      (by kpk_norm)
      hcrl_res
      hfs_res
      (by kpk_norm)
      (by
        refine Eq.trans (congrArg BitVec.toNat
          (show _ = BitVec.ofNat 64 (keyName x.id).length by kpk_norm)) ?_
        exact hlen_kn_nat)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      hbound10
      hfit_res
      (by
        rw [hsp_res, subStack_split s0.sp hres_le hhi]
        have hv_at := vecU8At_of_live_parts A.repAlloc (s0.sp - 0xb0#64) (s0.sp - 0xa8#64)
          (s0.sp - 0xa0#64) decCap decPtr (keyName x.id) (by bv_omega) (by bv_omega)
          hd_len hd_lt hd_ptr
        refine Entails.trans ?_ (sepConj_mono_left (sepConj_mono_left hv_at))
        unfold epiloguePre
        kpk_sep_norm
        sep_focus)
      fun sm p' hpcm hrunm hspm hcsm hcrlm hfsm htrm hp'_ne => ?_
    let newCapN := reserveCap decCap.toNat (keyName x.id).length 10
    have hnew_lt : newCapN < 2 ^ 63 := by dsimp [newCapN] at *; omega
    have hnew_pos : 0 < newCapN := by dsimp [newCapN, reserveCap]; omega
    have hnew_ne0 : BitVec.ofNat 64 newCapN ≠ 0#64 := by
      intro h0
      have ht := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
      change newCapN = 0 at ht; omega
    have hnew_toNat : (BitVec.ofNat 64 newCapN).toNat = newCapN := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpool_res :
        M.stepEvents (doReserveEvents ⟨s0.sp - 0xb0#64, decCap, decPtr, keyName x.id, 10⟩)
          (M.stepEvents evsDec st) =
        M.stepEvents (evsDec ++ doReserveEvents ⟨s0.sp - 0xb0#64, decCap, decPtr, keyName x.id, 10⟩) st := by
      rw [M.stepEvents_append]
    rw [hpool_res]
    rw [vecU8At_unpack_pos_lr A.repAlloc (s0.sp - 0xb0#64) (BitVec.ofNat 64 newCapN) p'
          (keyName x.id) hnew_ne0, e_a8, e_a0]
    kpk_sep_norm
    refine SepWPp.pure_elim fun _ => ?_
    have hsm_sp : sm.sp = s0.sp - 0xf0#64 := hspm.trans hsp_res
    have hsm_al : sm.spAligned = true := spAligned_sub_f0 hsp_align hsm_sp
    have hsm_tr : sm.trace = s0.trace := by
      rw [htrm]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hs1_tr))
    rw [hsp_res, subStack_merge_rev_adj s0.sp hres_le hhi]
    apply sepWPp_of_sepWP_fs_placed
      (mid := (blkPl_578).base + bv% (316))
      hFs hcrlm hfsm
    wp_steps_sync_pool ((blkPl_578).base + bv% (316))
    apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hcrl_316 hfs_316
    refine hjoin_316 _
      (evsDec ++ doReserveEvents ⟨s0.sp - 0xb0#64, decCap, decPtr, keyName x.id, 10⟩)
      (BitVec.ofNat 64 newCapN) p' _
      (SeqEnv.append hdecEv hresEv)
      hfit_get_res
      (by rw [hnew_toNat]; dsimp [newCapN, reserveCap]; omega)
      (by rw [hnew_toNat]; exact hnew_lt)
      hp'_ne
      (by kpk_norm) (by kpk_norm)
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm_sp)))
      (by
        (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x29 hcsm)])
        (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x29 hcs1)]; kpk_norm))
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm_tr)))
      hcrl_316 hfs_316
      (by
        (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_vregs hcsm)])
        (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_vregs hcs1)]; kpk_norm))
      (by kpk_norm)
      (by
        (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x19 hcsm)])
        (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x19 hcs1)]; kpk_norm))
      (by
        (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x20 hcsm)])
        (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x20 hcs1)]; kpk_norm))
      (by
        (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x26 hcsm)])
        (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x26 hcs1)]; kpk_norm))
      (by
        (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x28 hcsm)])
        (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x28 hcs1)]; kpk_norm))
      (by unfold epiloguePre; kpk_sep_focus)
  · have hule_f : (decCap - BitVec.ofNat 64 (keyName x.id).length).ule 9#64 = false :=
      Bool.eq_false_iff.mpr hule
    have hfast_ge := fast_name_cap_ge hkn_lt32 hd_len hule_f
    have hd_ne0 : decCap ≠ 0#64 :=
      fun h0 => by have : decCap.toNat = 0 := by subst h0; rfl
                   omega
    have hfit_get_fast :
        FitsEnv M lim (M.stepEvents evsDec st)
          (GetEnv s0.fs.files x.kg.lastResort (baseKeysName x.id)) := by
      simpa only [M.stepEvents_nil] using hfit_after_dec.seq_right (Or.inl rfl)
    simp only [hd_ne0, ite_false]
    kpk_sep_norm
    apply sepWPp_of_sepWP_fs_placed
      (mid := (blkPl_578).base + bv% (316))
      hFs hcrl1 hfs1
    wp_steps_sync_pool ((blkPl_578).base + bv% (316))
    apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hcrl_316 hfs_316
    refine hjoin_316 _ evsDec decCap decPtr _
      (SeqEnv.inl hdecEv)
      hfit_get_fast
      hfast_ge hd_lt hd_ptr
      (by kpk_norm) (by kpk_norm)
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hs1_sp)))
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x29 hcs1)]; kpk_norm))
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hs1_tr)))
      hcrl_316 hfs_316
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_vregs hcs1)]; kpk_norm))
      (by kpk_norm)
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x19 hcs1)]; kpk_norm))
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x20 hcs1)]; kpk_norm))
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x26 hcs1)]; kpk_norm))
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x28 hcs1)]; kpk_norm))
      (by unfold epiloguePre; kpk_sep_focus)

/-! ## 3. Full `last_resort` Branch (`+280 ..`, `kpk_last_resort_118_placed`) -/

/-- Full `one_time = Ok([])` continuation from `+280` composed with
`LastResortAfterGetPlacedBudget.kpk_after_lr_get_174_placed`. -/
theorem kpk_last_resort_118_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {MarkEnv : FsFiles → KpkMarkPollGhost → List AllocEvent → Prop}
    {decStk getStk putStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hP : CliPanicHooksPlaced H)
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec))
    (hDecimal : subroutine_ok (lsProg_578 H) (lsmpl.base 597)
      (decimalSpecPlaced A lim DecEnv decStk))
    (hGet : subroutine_ok (lsProg_578 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
    (hPut : subroutine_ok (lsProg_578 H) (lsmpl.base 542)
      (dirPutSpecPlaced A lim PutEnv putStk))
    (hFs : TraceFsSound (lsProg_578 H))
    (x : KpkMarkPollGhost) (st0 st : M.σ) (evsOneTime : List AllocEvent)
    (s0 s : State)
    (wDot wR0 wR7 wM0 wM6 : BitVec 64)
    (f0 f1 f2 f3 : BitVec 64) (tmp32 : BitVec 32)
    (P : SepProp) {Q Qp : State → SepProp → Prop}
    (hst : st = M.stepEvents evsOneTime st0)
    (hfit_pre : FitsEnv M lim st (KpkLastResortPreAfterGetEnv DecEnv GetEnv s0.fs.files x))
    (hfit_ok : ∀ (evsPre : List AllocEvent) (fileCap : BitVec 64)
      (seenBs : List (BitVec 8)) (seenCap : BitVec 64),
      KpkLastResortPreAfterGetEnv DecEnv GetEnv s0.fs.files x evsPre →
      (baseKeysName x.id).length ≤ fileCap.toNat → fileCap.toNat < 2 ^ 63 →
      x.kg.lastResort.get rd s0.fs.files (baseKeysName x.id) = .ok seenBs →
      seenBs.length ≤ seenCap.toNat → seenCap.toNat < 2 ^ 63 →
      FitsEnv M lim (M.stepEvents evsPre st)
        (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortAfterGetPlacedBudgetAux.KpkAfterLrGetOkEnv
          PutEnv x seenCap fileCap seenBs))
    (hMarkErr : ∀ (evsPre : List AllocEvent) (fileCap : BitVec 64),
      KpkLastResortPreAfterGetEnv DecEnv GetEnv s0.fs.files x evsPre →
      (baseKeysName x.id).length ≤ fileCap.toNat → fileCap.toNat < 2 ^ 63 →
      x.kg.lastResort.get rd s0.fs.files (baseKeysName x.id) = .error () →
      MarkEnv s0.fs.files x (evsOneTime ++ evsPre ++ optDeallocBufEvents fileCap))
    (hMarkOk : ∀ (evsPre : List AllocEvent) (fileCap : BitVec 64)
      (seenBs : List (BitVec 8)) (seenCap : BitVec 64) (evs_after : List AllocEvent),
      KpkLastResortPreAfterGetEnv DecEnv GetEnv s0.fs.files x evsPre →
      (baseKeysName x.id).length ≤ fileCap.toNat → fileCap.toNat < 2 ^ 63 →
      x.kg.lastResort.get rd s0.fs.files (baseKeysName x.id) = .ok seenBs →
      seenBs.length ≤ seenCap.toNat → seenCap.toNat < 2 ^ 63 →
      LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortAfterGetPlacedBudgetAux.KpkAfterLrGetOkEnv
        PutEnv x seenCap fileCap seenBs evs_after →
      MarkEnv s0.fs.files x (evsOneTime ++ evsPre ++ evs_after))
    (hstk : kpkMinStk decStk getStk putStk ≤ stk)
    (hhi_stk : stk ≤ 2 ^ 64)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hwDot : unpack64 wDot = utf8 ".base-ke")
    (hBkOk : KpkBaseKeysOk pathOk x.kg.lastResort x.id)
    (hSeenOk : KpkSeenOk rd s0.fs.files x.kg.lastResort x.id x.signedId x.baseKey)
    (hlr_chg : x.kg.lastResort.changed.length < 2 ^ 32)
    (hget1 : x.kg.oneTime.get rd s0.fs.files (keyName x.id) = .ok [])
    (hpc : s.pc = (blkPl_578).base + bv% (280))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0xf0#64)
    (hfp : s.readReg64 .x29 = s0.sp - 0x60#64)
    (htr : s.trace = s0.trace)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hfs : FsInv s0.fs.files s0.trace s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx23 : s.readReg64 .x23 = x.id.setWidth 64)
    (hx26 : s.readReg64 .x26 = x.self)
    (hx28 : s.readReg64 .x28 = x.signedId.setWidth 64)
    (hfoc : P ⊢
      kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
      stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
      memRegion (s0.sp - 0xf0#64) 8 ∗
      ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
      ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
      memRegion (s0.sp - 0xc8#64) 24 ∗
      memRegion (s0.sp - 0xb0#64) 48 ∗
      memRegion (s0.sp - 0x80#64) 24 ∗
      memRegion (s0.sp - 0x68#64) 4 ∗
      ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
      dirAt A.repAlloc x.self x.kg.oneTime ∗
      dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
      (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
      epiloguePre s0 x ∗ A.pool lim st s)
    (hk_final : ∀ (sf : State) (P_f : SepProp),
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
        (kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv stk).post (x, st0) s0 sf) →
      Q sf P_f) :
    SepWPp (lsProg_578 H) (s0.readReg64 .lr) s P Q Qp :=
  kpk_last_resort_118_placed_of_after hC hP hDecimal hGet hFs
    x st s0 s wDot wR0 wR7 wM0 wM6 f0 f1 f2 f3 tmp32 P
    hfit_pre hstk hhi_stk hsp_align hwDot hBkOk
    hpc hrun hsp hfp htr hcrl hfs hvregs hx19 hx20 hx23 hx26 hx28 hfoc
    fun s4 evsPre filePtr fileCap gr hevsPre hgr4 hf_len hf_lt hf_ptr
      hpc4 hrun4 hs4_sp hfp4 hcrl4 hv4 hx19_4 hx20_4 hx24_4 hx26_4 hx28_4 => by
      have hpool_eq :
          M.stepEvents evsPre st = M.stepEvents (evsOneTime ++ evsPre) st0 := by
        rw [hst, M.stepEvents_append]
      rw [hpool_eq]
      exact
        LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortAfterGetPlacedBudget.kpk_after_lr_get_174_placed
          hC hBcmp hPut x st0 (evsOneTime ++ evsPre) s0 s4
          wDot wR0 wR7 wM0 wM6 f0 f1 filePtr fileCap tmp32 gr
          hstk hhi_stk hsp_align hSeenOk hlr_chg hget1 hgr4
          (fun seenBs seenCap hgr_ok hs_len hs_lt => by
            rw [← hpool_eq]
            exact hfit_ok evsPre fileCap seenBs seenCap hevsPre hf_len hf_lt
              (hgr4.1.symm.trans hgr_ok) hs_len hs_lt)
          (fun hgr_err =>
            hMarkErr evsPre fileCap hevsPre hf_len hf_lt (hgr4.1.symm.trans hgr_err))
          (fun seenBs seenCap evs_after hgr_ok hs_len hs_lt hevs_after =>
            hMarkOk evsPre fileCap seenBs seenCap evs_after hevsPre hf_len hf_lt
              (hgr4.1.symm.trans hgr_ok) hs_len hs_lt hevs_after)
          hf_len hf_lt hf_ptr hpc4 hrun4 hs4_sp hfp4 hcrl4 hv4
          hx19_4 hx20_4 hx24_4 hx26_4 hx28_4 hk_final

end LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortPlacedBudget
