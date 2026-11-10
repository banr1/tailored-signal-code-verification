/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `FdsGe3Closed`-Threaded Relocatable Callee Cell Wrappers & Outer Bridge for `KpkGetPoll`

Bridges `withFdsGe3Closed`-threaded relocatable callee contracts to cell-decomposed `KpkGetPoll`
specs on Block `576` (`lsProg_576 H`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutPlacedBudgetFd

open Arm64 Arm64.Obj ProofLib
open AsmConstants (boxSliceLenOff resultErrSpeOff spePayloadOff speSize)
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchet (extHookStack smallRootStack)
open CryptoVerification.LibsignalTripleRatchetRepr
  (errResultAt errTag okTagVec speAt speWord strRefAt utf8 vecResultAt)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles FsInv TraceFsSound extract_withLsCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.RecordCodecs (KyberPreKeyRecord SignedPreKeyRecordStructure)
open CryptoVerification.RecordCodecsBinary
  (DecodeGhost kyberPreKeyResultAt signedPreKeyStructAt)
open CryptoVerification.SpqrV1.Alloc (vecU8At_eq_header_sep_buf vecU8Buf)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli
  (DecimalGhost DirGetGhost DirGhost KpkPollGhost PkNameOk ReadRule dirAt
   getResultAt keyName kpkAnsAt pkAnsAt pkBoxAt subroutine_ok_withFsInv withFsInv
   withFsInv_entry withFsInv_post_elim withFsInv_pre_intro)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_576)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.Store.KpkGetPoll.Helpers
  (decodePostProp dirGetPostProp memRegion_16_cells memRegion_24_cells
   memRegion_32_cells memRegion_40_cells memRegion_48_words6 memRegion_88_words11
   memRegion_bound_of_pointsTo64 stackAt_kpkPoll_frame stackAt_sub_split vecU8BufRest
   words11At words4_entails_memRegion_32 words5_entails_memRegion_40 words6At)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget RustLayoutOk)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
  (KyberDecodeEnv SpkLoopEnv decodeKyberPreKeyPlacedSpec decodeKyberPreKeyRawSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (dealloc_keepsFs_lscro_of_fs subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed_of_keepsFs)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed extract_withFdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced decimalSpecPlaced dirGetSpecPlaced kpkGetPollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget
  (CliKpkGetPollEnv cliKpkGetPollInnerSpec deallocVecBufCellsSpec decimalFsCellsSpec
   decodeFsCellsSpec dirGetFsCellsSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudgetFd
  (cliKpkGetPollInnerSpec_fd deallocVecBufCellsSpec_fd decimalFsCellsSpec_fd
   decodeFsCellsSpec_fd dirGetFsCellsSpec_fd)

section Placed

private theorem entails_of_eq_p {P Q : SepProp} (h : P = Q) : P ⊢ Q :=
  h ▸ Entails.refl P

private theorem entails_pure_right_p {φ : Prop} {P Q : SepProp} (hφ : φ) (h : P ⊢ Q) :
    P ⊢ ⌜φ⌝ ∗ Q := by
  have htrue : φ = True := propext ⟨fun _ => trivial, fun _ => hφ⟩
  rw [htrue, ProofLib.pure_true, emp_sepConj]
  exact h

private theorem vecU8Buf_cap_lt_p {A : RustAlloc} {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    {Q : SepProp} {m : Memory} (h : m ⊨ vecU8Buf A cap ptr bs ∗ Q) :
    cap.toNat < 2 ^ 63 := by
  unfold vecU8Buf at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  exact h.1.2.1

private theorem vecU8Buf_split_raw_p (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢ (ptr ↦ₛ bs) ∗ vecU8BufRest A cap ptr bs := by
  unfold vecU8Buf vecU8BufRest
  refine (ProofLib.pure_extract_iff _ _ _).mpr fun hpure => ?_
  by_cases hcap : cap = 0
  · subst hcap
    have hbs0 : bs = [] := List.eq_nil_of_length_eq_zero
      (Nat.eq_zero_of_le_zero (by simpa using hpure.1))
    subst hbs0
    rw [pointsToBytes_nil]
    refine Entails.trans (entails_pure_right_p hpure (Entails.refl _)) ?_
    exact entails_of_eq_p (ProofLib.emp_sepConj _).symm
  · simp only [hcap, ite_false]
    refine Entails.trans ?_ (sepConj_mono_right (entails_pure_right_p hpure (Entails.refl _)))
    exact entails_of_eq_p (by sep_ac_rfl)

private theorem vecU8Buf_unsplit_raw_p (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    (ptr ↦ₛ bs) ∗ vecU8BufRest A cap ptr bs ⊢ vecU8Buf A cap ptr bs := by
  unfold vecU8Buf vecU8BufRest
  rw [← sepConj_assoc, sepConj_comm (ptr ↦ₛ bs), sepConj_assoc]
  refine (ProofLib.pure_extract_iff _ _ _).mpr fun hpure => entails_pure_right_p hpure ?_
  by_cases hcap : cap = 0
  · subst hcap
    have hbs0 : bs = [] := List.eq_nil_of_length_eq_zero
      (Nat.eq_zero_of_le_zero (by simpa using hpure.1))
    subst hbs0
    rw [pointsToBytes_nil, ProofLib.emp_sepConj]
    exact Entails.refl _
  · simp only [hcap, ite_false]
    exact entails_of_eq_p (by sep_ac_rfl)

private theorem bytesAt_false_eq_p (ptr : BitVec 64) (bs : List (BitVec 8)) :
    CryptoVerification.SpqrV1.ChainProofs.bytesAt false ptr bs = (ptr ↦ₛ bs) := rfl

private theorem kyberDeserialize_eq_p (bs : List (BitVec 8)) :
    KyberPreKeyRecord.deserialize bs =
      match SignedPreKeyRecordStructure.decode bs with
      | none => .error .invalidProtobufEncoding
      | some m => .ok ⟨m⟩ := by
  unfold KyberPreKeyRecord.deserialize
  cases SignedPreKeyRecordStructure.decode bs <;> rfl

theorem deallocVecBuf_cells_keepsFs_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    {calleeStk : Nat} {F0 : FsFiles} {T0 : List TraceEvent}
    (hC : AllocContractsFsPlaced A lim H)
    (hFs : TraceFsSound prog)
    (hle : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl (deallocVecBufCellsSpec A lim F0 T0 calleeStk)).keepsFs := by
  have hDealloc0 := subroutine_ok_withFsInv hFs
    (dealloc_keepsFs_lscro_of_fs (callerProg := prog) hC hi) F0 T0
  refine subroutine_ok.of_codeLoaded fun ⟨⟨cap, ptr, bs, fsp⟩, st⟩ R s0
    hpc hrun hpre hsp _ => ?_
  dsimp only [Spec.keepsFs] at hpre
  rcases extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  simp only [deallocVecBufCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfs0, hcap, hx0, hx1, hx2, hfsp, hlr⟩, hmem⟩
  subst hfsp
  unfold vecU8Buf at hmem
  have hcap0 : ¬(cap = 0) := hcap
  simp only [hcap0, ite_false] at hmem
  rw [sepConj_assoc, satisfies_pure_sepConj] at hmem
  rcases hmem with ⟨⟨hbs_le, hcap_lt, _⟩, hmem⟩
  have hcap_pos : 0 < cap.toNat := by
    by_cases hz : cap.toNat = 0
    · exact (hcap (BitVec.eq_of_toNat_eq hz)).elim
    · omega
  have hlay : RustLayoutOk cap.toNat 1 := ⟨⟨hcap_pos, ⟨0, rfl⟩, by omega⟩, by decide⟩
  have hreg : (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ⊢
      memRegion ptr cap.toNat := by
    have heq : cap.toNat = bs.length + (cap.toNat - bs.length) := by omega
    conv_rhs => rw [heq]
    rw [memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)]
    exact sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - extHookStack)
  have hmem_reg : s0.mem ⊨ memRegion ptr cap.toNat ∗
      (A.pool lim st s0 ∗ A.live ptr cap.toNat 1 ∗ stackAt s0.sp extHookStack ∗ stkRem ∗ R) := by
    refine Satisfies.mono (sepConj_mono_left hreg) ?_
    dsimp only [stkRem]
    convert hmem using 1; sep_ac_rfl
  let callG : BitVec 64 × Nat × Nat × M.σ := (ptr, cap.toNat, 1, st)
  have hpre0 : s0.mem ⊨
      (withFsInv (withLsCodeRoLoaded lsmpl
        (rustDeallocExternSpecWithStack M A lim extHookStack).keepsFs) F0 T0).pre
        callG s0 ∗ (stkRem ∗ R) := by
    refine withFsInv_pre_intro hfs0 ?_
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack, callG]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, by simp [hx1], by simp [hx2], hlay, hlr⟩, ?_⟩
    convert hmem_reg using 1; sep_ac_rfl
  refine hDealloc0.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    obtain ⟨hfsf, hq⟩ := withFsInv_post_elim hq
    dsimp only [Spec.keepsFs, withLsCodeRoLoaded, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
      deallocVecBufCellsSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hfs_eq, hq⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq⟩
    refine ⟨hfs_eq, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfsf, htr⟩, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; sep_ac_rfl
  · dsimp only [withFsInv, Spec.keepsFs, withLsCodeRoLoaded, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim
  · dsimp only [withFsInv, Spec.keepsFs, withLsCodeRoLoaded, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim
  · dsimp only [withFsInv, Spec.keepsFs, withLsCodeRoLoaded, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim

theorem deallocVecBuf_cells_placed_ok_fd [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    {calleeStk : Nat} {F0 : FsFiles} {T0 : List TraceEvent}
    (hC : AllocContractsFsPlaced A lim H)
    (hFs : TraceFsSound prog)
    (hle : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl (deallocVecBufCellsSpec_fd A lim F0 T0 calleeStk)) :=
  subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed_of_keepsFs
    (deallocVecBuf_cells_keepsFs_placed_ok hC hFs hle hhi hi)

theorem decimal_cells_placed_ok_fd [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {F0 : FsFiles} {T0 : List TraceEvent} {decStk calleeStk : Nat}
    (hDecimal : subroutine_ok prog (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)))
    (hFs : TraceFsSound prog)
    (hle : decStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 597)
      (withLsCodeRoLoaded lsmpl (decimalFsCellsSpec_fd A lim DecEnv F0 T0 calleeStk)) := by
  have hDec0 := subroutine_ok_withFsInv hFs hDecimal F0 T0
  refine subroutine_ok.of_codeLoaded fun ⟨⟨n, ret, o0, o1, o2, fsp⟩, st⟩ R s0
    hpc hrun hpre hsp _ => ?_
  rcases extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  dsimp only [decimalFsCellsSpec_fd] at hpre
  obtain ⟨hfds0, hpre⟩ := extract_withFdsGe3Closed hpre
  simp only [decimalFsCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfs0, hx0, hx1, hfsp, hfit⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - decStk)
  let callG : DecimalGhost × M.σ := (⟨n, ret⟩, st)
  have hpre0 : s0.mem ⊨
      (withFsInv (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)) F0 T0).pre
        callG s0 ∗ (stkRem ∗ R) := by
    refine withFsInv_pre_intro hfs0 ?_
    dsimp only [withFdsGe3Closed]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfds0, ?_⟩
    unfold decimalSpecPlaced
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [callG]
    simp only [memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hfit⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; sep_ac_rfl
  refine hDec0.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    obtain ⟨hfsf, hq⟩ := withFsInv_post_elim hq
    dsimp only [withFdsGe3Closed] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hfdsf, hq⟩
    dsimp only [decimalFsCellsSpec_fd, withFdsGe3Closed]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfdsf, ?_⟩
    dsimp only [withLsCodeRoLoaded, decimalSpecPlaced, decimalFsCellsSpec,
      callG, keyName] at hq ⊢
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨htr, hevs⟩, hq⟩
    dsimp only [vecU8] at hq
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨nCap, nPtr, hq⟩
    refine ⟨evs, nCap, nPtr, ?_⟩
    rw [vecU8At_eq_header_sep_buf] at hq
    dsimp only [vecHeader] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfsf, htr, hevs⟩, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; sep_ac_rfl
  · dsimp only [withFsInv, withFdsGe3Closed, withLsCodeRoLoaded, decimalSpecPlaced] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim
  · dsimp only [withFsInv, withFdsGe3Closed, withLsCodeRoLoaded, decimalSpecPlaced] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim
  · dsimp only [withFsInv, withFdsGe3Closed, withLsCodeRoLoaded, decimalSpecPlaced] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim

theorem dirGet_cells_placed_ok_fd [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {F0 : FsFiles} {T0 : List TraceEvent} {getStk calleeStk : Nat}
    (hGet : subroutine_ok prog (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hFs : TraceFsSound prog)
    (hle : getStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 589)
      (withLsCodeRoLoaded lsmpl
        (dirGetFsCellsSpec_fd rd pathOk A lim (fun dir id => GetEnv F0 dir (keyName id))
          F0 T0 calleeStk)) := by
  have hGet0 := subroutine_ok_withFsInv hFs hGet F0 T0
  refine subroutine_ok.of_codeLoaded
    fun ⟨⟨ret, self, dir, keyId, nCap, nPtr, o0, o1, o2, o3, o4, o5, fsp⟩, st⟩ R s0
      hpc hrun hpre hsp _ => ?_
  rcases extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  dsimp only [dirGetFsCellsSpec_fd] at hpre
  obtain ⟨hfds0, hpre⟩ := extract_withFdsGe3Closed hpre
  simp only [dirGetFsCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfs0, htr0, ⟨hnlen, hdlen, hpOk⟩, hx0, hx1, hx2, hx3, hfsp, hfit⟩, hmem⟩
  subst hfsp
  have hfiles : s0.fs.files = F0 :=
    hfs0.files_eq (evs := []) (by simp [htr0]) (by intro _ h; cases h)
  have hx3_nat : (s0.readReg64 .x3).toNat = (keyName keyId).length := by
    rw [hx3, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  let nRest := vecU8BufRest A.repAlloc nCap nPtr (keyName keyId)
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - getStk)
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  have hmem_sp : s0.mem ⊨ vecU8Buf A.repAlloc nCap nPtr (keyName keyId) ∗
      (dirAt A.repAlloc self dir ∗ words6At ret o0 o1 o2 o3 o4 o5 ∗
        stackAt s0.sp getStk ∗ A.pool lim st s0 ∗ stkRem ∗ R) := by
    dsimp only [stkRem]
    convert hmem using 1; sep_ac_rfl
  have hmem_bor : s0.mem ⊨ ((nPtr ↦ₛ keyName keyId) ∗ nRest) ∗
      (dirAt A.repAlloc self dir ∗ words6At ret o0 o1 o2 o3 o4 o5 ∗
        stackAt s0.sp getStk ∗ A.pool lim st s0 ∗ stkRem ∗ R) :=
    Satisfies.mono
      (sepConj_mono_left (vecU8Buf_split_raw_p A.repAlloc nCap nPtr (keyName keyId))) hmem_sp
  let callG : DirGetGhost × M.σ := (⟨ret, self, dir, nPtr, keyName keyId, false⟩, st)
  have hfit0 : FitsEnv M lim st (GetEnv s0.fs.files dir (keyName keyId)) := by
    rwa [hfiles]
  have hpre0 : s0.mem ⊨
      (withFsInv (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)) F0 T0).pre
        callG s0 ∗ (nRest ∗ stkRem ∗ R) := by
    refine withFsInv_pre_intro hfs0 ?_
    dsimp only [withFdsGe3Closed]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfds0, ?_⟩
    unfold dirGetSpecPlaced
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [callG]
    rw [memRegion_48_words6]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o5, o4, o3, o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3_nat, hnlen, hdlen, hpOk, hfit0⟩, ?_⟩
    rw [bytesAt_false_eq_p]
    convert hmem_bor using 1; sep_ac_rfl
  refine hGet0.mono_outcome callG (nRest ∗ stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    obtain ⟨hfsf, hq⟩ := withFsInv_post_elim hq
    dsimp only [withFdsGe3Closed] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hfdsf, hq⟩
    dsimp only [dirGetFsCellsSpec_fd, withFdsGe3Closed]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfdsf, ?_⟩
    dsimp only [withLsCodeRoLoaded, dirGetSpecPlaced, dirGetFsCellsSpec, callG] at hq ⊢
    rw [hfiles, bytesAt_false_eq_p] at hq
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, r, hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨hget_eq, htr_eq, hevs⟩, hq⟩
    have hq_unbor : sf.mem ⊨ ((nPtr ↦ₛ keyName keyId) ∗ nRest) ∗
        (getResultAt A.repAlloc ret r ∗ dirAt A.repAlloc self dir ∗ stackAt s0.sp getStk ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stkRem ∗ R) := by
      convert hq using 1; sep_ac_rfl
    have hq_rest : sf.mem ⊨ vecU8Buf A.repAlloc nCap nPtr (keyName keyId) ∗
        (getResultAt A.repAlloc ret r ∗ dirAt A.repAlloc self dir ∗ stackAt s0.sp getStk ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stkRem ∗ R) :=
      Satisfies.mono
        (sepConj_mono_left (vecU8Buf_unsplit_raw_p A.repAlloc nCap nPtr (keyName keyId))) hq_unbor
    clear hq hq_unbor
    rcases r with ⟨⟩ | bs
    · dsimp only [getResultAt, speAt, strRefAt, vecU8] at hq_rest
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq_rest
      rcases hq_rest with ⟨fPtr, msgBs, sCap, sPtr, hq⟩
      rw [vecU8At_eq_header_sep_buf] at hq
      dsimp only [vecHeader] at hq
      have hspe1 : speWord 1 = 0x8000000000000001#64 := by decide
      have herr_tag : (0xFFFFFFFFFFFFFFFF#64 : BitVec 64) = errTag := by decide
      let H := vecU8Buf A.repAlloc sCap sPtr msgBs ∗ (fPtr ↦ᵣ utf8 "read")
      refine ⟨evs, .error (), 0x8000000000000001#64, sCap, sPtr,
        BitVec.ofNat 64 msgBs.length, fPtr, BitVec.ofNat 64 (utf8 "read").length, H, ?_⟩
      have hprop : dirGetPostProp rd A.repAlloc F0 T0 dir keyId sf (.error ())
          0x8000000000000001#64 sCap sPtr (BitVec.ofNat 64 msgBs.length)
          fPtr (BitVec.ofNat 64 (utf8 "read").length) H := by
        refine ⟨rfl, ⟨hget_eq.symm, htr_eq.trans htr0⟩, fun out t7 t8 t9 t10 => ?_⟩
        dsimp only [words11At, kpkAnsAt, pkAnsAt, errResultAt, speAt, vecU8]
        have h8_eq : out + asm64% resultErrSpeOff = out + 8#64 := by bv_omega
        have h16_eq : out + 8#64 + asm64% spePayloadOff = out + 16#64 := by bv_omega
        have h40_eq : out + 8#64 + 32#64 = out + 40#64 := by bv_omega
        rw [herr_tag, ← hspe1, h8_eq, h16_eq, h40_eq]
        have h32 := words4_entails_memRegion_32 (out + 56#64) t7 t8 t9 t10
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at h32
        have hv : ((out + 16#64) ↦₆₄ sCap) ∗ ((out + 24#64) ↦₆₄ sPtr) ∗
            ((out + 32#64) ↦₆₄ BitVec.ofNat 64 msgBs.length) ∗
            vecU8Buf A.repAlloc sCap sPtr msgBs ⊢
            ∃∗ bs0 : List (BitVec 8), ∃∗ c0 : BitVec 64, ∃∗ p0 : BitVec 64,
              vecU8At A.repAlloc (out + 16#64) c0 p0 bs0 := by
          refine Entails.trans ?_
            (Entails.sepExists_right msgBs
              (Entails.sepExists_right sCap
                (Entails.sepExists_right sPtr (Entails.refl _))))
          rw [vecU8At_eq_header_sep_buf]
          dsimp only [vecHeader]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
          exact entails_of_eq_p (by sep_ac_rfl)
        have hf : ((out + 40#64) ↦₆₄ fPtr) ∗
            ((out + 48#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
            (fPtr ↦ᵣ utf8 "read") ⊢
            strRefAt (out + 40#64) (utf8 "read") := by
          unfold strRefAt
          refine Entails.sepExists_right fPtr ?_
          have h48_eq : out + 40#64 + asm64% boxSliceLenOff = out + 48#64 := by bv_omega
          rw [h48_eq]
          exact Entails.refl _
        dsimp only [H]
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono (sepConj_mono_right (sepConj_mono hv hf)) h32))
        exact entails_of_eq_p (by sep_ac_rfl)
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hprop, hevs⟩, ?_⟩
      rw [stackAt_sub_split s0.sp hle hhi]
      dsimp only [words6At, H, stkRem] at hq ⊢
      rw [hspe1] at hq
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq
      convert hq using 1; sep_ac_rfl
    · dsimp only [getResultAt, vecResultAt, vecU8] at hq_rest
      rw [memRegion_16_cells] at hq_rest
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq_rest
      rcases hq_rest with ⟨g5, g4, bCap, bPtr, hq⟩
      rw [vecU8At_eq_header_sep_buf] at hq
      dsimp only [vecHeader] at hq
      have hok_tag : okTagVec = 0xFFFFFFFFFFFFFFFE#64 := by decide
      refine ⟨evs, .ok bs, 0xFFFFFFFFFFFFFFFE#64, bCap, bPtr,
        BitVec.ofNat 64 bs.length, g4, g5, vecU8Buf A.repAlloc bCap bPtr bs, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨⟨hget_eq.symm, hfsf, htr_eq.trans htr0, rfl, rfl, rfl⟩, hevs⟩, ?_⟩
      rw [stackAt_sub_split s0.sp hle hhi]
      dsimp only [words6At, stkRem] at hq ⊢
      rw [hok_tag] at hq
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq
      convert hq using 1; sep_ac_rfl
  · dsimp only [withFsInv, withFdsGe3Closed, withLsCodeRoLoaded, dirGetSpecPlaced] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim
  · dsimp only [withFsInv, withFdsGe3Closed, withLsCodeRoLoaded, dirGetSpecPlaced] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim
  · dsimp only [withFsInv, withFdsGe3Closed, withLsCodeRoLoaded, dirGetSpecPlaced] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim

theorem decode_cells_placed_ok_fd [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {F0 : FsFiles} {T0 : List TraceEvent} {calleeStk : Nat}
    (hDec : subroutine_ok prog (lsmpl.base 595)
      (withFdsGe3Closed (decodeKyberPreKeyPlacedSpec A lim)))
    (hFs : TraceFsSound prog)
    (hle : smallRootStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64)
    (hSub : ∀ bs evs, SpkLoopEnv (2 * bs.length + 3) bs.length evs → DecodeEnv bs evs)
    (hSup : ∀ bs evs, KyberDecodeEnv bs.length evs → DecodeEnv bs evs) :
    subroutine_ok prog (lsmpl.base 595)
      (withLsCodeRoLoaded lsmpl (decodeFsCellsSpec_fd A lim DecodeEnv F0 T0 calleeStk)) := by
  have hDec0 := subroutine_ok_withFsInv hFs hDec F0 T0
  refine subroutine_ok.of_codeLoaded
    fun ⟨⟨ret, bCap, bPtr, bytes, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, fsp⟩, st⟩ R s0
      hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [decodeFsCellsSpec_fd] at hpre
  obtain ⟨hfds0, hpre⟩ := extract_withFdsGe3Closed hpre
  simp only [decodeFsCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfs0, htr0, hlen_pos, hlen_lt, hx0, hx1, hx2, hfsp, hfit⟩, hmem⟩
  subst hfsp
  have hx2_nat : (s0.readReg64 .x2).toNat = bytes.length := by
    rw [hx2, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hfit_loop : FitsEnv M lim st (SpkLoopEnv (2 * bytes.length + 3) bytes.length) :=
    hfit.mono (hSub bytes)
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let bRest := vecU8BufRest A.repAlloc bCap bPtr bytes
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - smallRootStack)
  have hmem_sp : s0.mem ⊨ vecU8Buf A.repAlloc bCap bPtr bytes ∗
      (words11At ret o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 ∗
        stackAt s0.sp smallRootStack ∗ A.pool lim st s0 ∗ stkRem ∗ R) := by
    dsimp only [stkRem]
    convert hmem using 1; sep_ac_rfl
  have hmem_bor : s0.mem ⊨ ((bPtr ↦ₛ bytes) ∗ bRest) ∗
      (words11At ret o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 ∗
        stackAt s0.sp smallRootStack ∗ A.pool lim st s0 ∗ stkRem ∗ R) :=
    Satisfies.mono (sepConj_mono_left (vecU8Buf_split_raw_p A.repAlloc bCap bPtr bytes)) hmem_sp
  let callG : DecodeGhost × M.σ := (⟨bPtr, bytes, ret⟩, st)
  have hpre0 : s0.mem ⊨
      (withFsInv (withFdsGe3Closed (decodeKyberPreKeyPlacedSpec A lim)) F0 T0).pre callG s0 ∗
        (bRest ∗ stkRem ∗ R) := by
    refine withFsInv_pre_intro hfs0 ?_
    dsimp only [withFdsGe3Closed]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfds0, ?_⟩
    refine satisfies_lscro_pre hcrl ?_
    unfold decodeKyberPreKeyRawSpec
    dsimp only [callG]
    rw [memRegion_88_words11]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o10, o9, o8, o7, o6, o5, o4, o3, o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2_nat, hlen_pos, hlen_lt, hfit_loop⟩, ?_⟩
    convert hmem_bor using 1; sep_ac_rfl
  refine hDec0.mono_outcome callG (bRest ∗ stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    obtain ⟨hfsf, hq⟩ := withFsInv_post_elim hq
    dsimp only [withFdsGe3Closed] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hfdsf, hq⟩
    dsimp only [decodeFsCellsSpec_fd, withFdsGe3Closed]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfdsf, ?_⟩
    dsimp only [withLsCodeRoLoaded, CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
      decodeKyberPreKeyPlacedSpec, decodeKyberPreKeyRawSpec, decodeFsCellsSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr_eq, hq⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    simp only [sepConj_assoc] at hq
    rw [satisfies_pure_sepConj] at hq
    rcases hq with ⟨hevs_k, hq⟩
    have hevs : DecodeEnv bytes evs := hSup bytes evs hevs_k
    have hq_unbor : sf.mem ⊨ ((bPtr ↦ₛ bytes) ∗ bRest) ∗
        (kyberPreKeyResultAt A.repAlloc ret (KyberPreKeyRecord.deserialize bytes) ∗
          stackAt s0.sp smallRootStack ∗ A.pool lim (M.stepEvents evs st) sf ∗ stkRem ∗ R) := by
      convert hq using 1; sep_ac_rfl
    have hq_rest : sf.mem ⊨ vecU8Buf A.repAlloc bCap bPtr bytes ∗
        (kyberPreKeyResultAt A.repAlloc ret (KyberPreKeyRecord.deserialize bytes) ∗
          stackAt s0.sp smallRootStack ∗ A.pool lim (M.stepEvents evs st) sf ∗ stkRem ∗ R) :=
      Satisfies.mono
        (sepConj_mono_left (vecU8Buf_unsplit_raw_p A.repAlloc bCap bPtr bytes)) hq_unbor
    clear hq hq_unbor
    have hdes := kyberDeserialize_eq_p bytes
    cases hsd : SignedPreKeyRecordStructure.decode bytes with
    | none =>
      rw [hsd] at hdes
      rw [hdes] at hq_rest
      dsimp only [kyberPreKeyResultAt, errResultAt, speAt] at hq_rest
      rw [show (asm% (speSize - spePayloadOff)) = 40 by rfl,
        show (88 - asm% (resultErrSpeOff + speSize)) = 32 by rfl,
        memRegion_40_cells, memRegion_32_cells] at hq_rest
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq_rest
      rcases hq_rest with ⟨w10, w9, w8, w7, w6, w5, w4, w3, w2, hq⟩
      have herr_tag : errTag = 0xFFFFFFFFFFFFFFFF#64 := by decide
      refine ⟨evs, 0xFFFFFFFFFFFFFFFF#64, speWord 2, w2, w3, w4, w5, w6, w7, w8, w9, w10, emp, ?_⟩
      have hprop : decodePostProp A.repAlloc F0 T0 bytes sf
          0xFFFFFFFFFFFFFFFF#64 (speWord 2) w2 w3 w4 w5 w6 w7 w8 w9 w10 emp := by
        unfold decodePostProp
        rw [hdes]
        refine ⟨hfsf, htr_eq.trans htr0, rfl, fun out t7 t8 t9 t10 => ?_⟩
        dsimp only [words11At, kpkAnsAt, pkAnsAt, kyberPreKeyResultAt, errResultAt, speAt]
        have h8_eq : out + asm64% resultErrSpeOff = out + 8#64 := by bv_omega
        have h16_eq : out + 8#64 + asm64% spePayloadOff = out + 16#64 := by bv_omega
        rw [h8_eq, h16_eq, ← herr_tag, sepConj_emp]
        have h40 := words5_entails_memRegion_40 (out + 16#64) w2 w3 w4 w5 w6
        have h32 := words4_entails_memRegion_32 (out + 56#64) t7 t8 t9 t10
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at h40 h32
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono (sepConj_mono_right h40) h32))
        exact entails_of_eq_p (by sep_ac_rfl)
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hprop, hevs⟩, ?_⟩
      rw [stackAt_sub_split s0.sp hle hhi]
      dsimp only [words11At, stkRem] at hq ⊢
      rw [herr_tag] at hq
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq ⊢
      convert hq using 1; sep_ac_rfl
    | some m =>
      rw [hsd] at hdes
      rw [hdes] at hq_rest
      dsimp only [kyberPreKeyResultAt, signedPreKeyStructAt, vecU8] at hq_rest
      rw [memRegion_eq_exists_bytes (ret + 0x54#64) 4 (by decide)] at hq_rest
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq_rest
      rcases hq_rest with ⟨pad4, sigCap, sigPtr, skCap, skPtr, pkCap, pkPtr, hq⟩
      rw [vecU8At_eq_header_sep_buf, vecU8At_eq_header_sep_buf, vecU8At_eq_header_sep_buf] at hq
      dsimp only [vecHeader] at hq
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq
      have hpk_ex : sf.mem ⊨ vecU8Buf A.repAlloc pkCap pkPtr m.publicKey ∗
          (((ret ↦₆₄ pkCap) ∗ ((ret + 8#64) ↦₆₄ pkPtr) ∗
            ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length)) ∗
           (((ret + 24#64) ↦₆₄ skCap) ∗ ((ret + 32#64) ↦₆₄ skPtr) ∗
            ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
            vecU8Buf A.repAlloc skCap skPtr m.privateKey) ∗
           (((ret + 48#64) ↦₆₄ sigCap) ∗ ((ret + 56#64) ↦₆₄ sigPtr) ∗
            ((ret + 64#64) ↦₆₄ BitVec.ofNat 64 m.signature.length) ∗
            vecU8Buf A.repAlloc sigCap sigPtr m.signature) ∗
           ((ret + 72#64) ↦₆₄ m.timestamp) ∗ ((ret + 80#64) ↦₃₂ m.id) ∗
           (⌜pad4.length = 4⌝ ∗ ((ret + 84#64) ↦ₛ pad4)) ∗
           vecU8Buf A.repAlloc bCap bPtr bytes ∗ stackAt s0.sp smallRootStack ∗
           A.pool lim (M.stepEvents evs st) sf ∗
           (stkRem ∗ R)) := by
        convert hq using 1; sep_ac_rfl
      have hpk_lt : pkCap.toNat < 2 ^ 63 := vecU8Buf_cap_lt_p hpk_ex
      clear hpk_ex
      have hpad_ex : sf.mem ⊨ ⌜pad4.length = 4⌝ ∗
          (((ret ↦₆₄ pkCap) ∗ ((ret + 8#64) ↦₆₄ pkPtr) ∗
            ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
            vecU8Buf A.repAlloc pkCap pkPtr m.publicKey) ∗
           (((ret + 24#64) ↦₆₄ skCap) ∗ ((ret + 32#64) ↦₆₄ skPtr) ∗
            ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
            vecU8Buf A.repAlloc skCap skPtr m.privateKey) ∗
           (((ret + 48#64) ↦₆₄ sigCap) ∗ ((ret + 56#64) ↦₆₄ sigPtr) ∗
            ((ret + 64#64) ↦₆₄ BitVec.ofNat 64 m.signature.length) ∗
            vecU8Buf A.repAlloc sigCap sigPtr m.signature) ∗
           ((ret + 72#64) ↦₆₄ m.timestamp) ∗ ((ret + 80#64) ↦₃₂ m.id) ∗
           ((ret + 84#64) ↦ₛ pad4) ∗
           vecU8Buf A.repAlloc bCap bPtr bytes ∗ stackAt s0.sp smallRootStack ∗
           A.pool lim (M.stepEvents evs st) sf ∗
           (stkRem ∗ R)) := by
        convert hq using 1; sep_ac_rfl
      rw [satisfies_pure_sepConj] at hpad_ex
      rcases hpad_ex with ⟨hpad_len, hq_nopad⟩
      have hlen8 : (unpack32 m.id ++ pad4).length = 8 := by simp [hpad_len]
      obtain ⟨w10, hw10⟩ := exists_unpack64_of_length_8 hlen8
      have htail_word : ∀ a : BitVec 64,
          ((a + 0x50#64) ↦₃₂ m.id) ∗ ((a + 0x54#64) ↦ₛ pad4) =
            ((a + 0x50#64) ↦₆₄ w10) := fun a => by
        rw [pointsTo32_eq_pointsToBytes, pointsTo64_eq_pointsToBytes, ← hw10,
          pointsToBytes_append, unpack32_length]
        have ha : a + 0x50#64 + BitVec.ofNat 64 4 = a + 0x54#64 := by bv_omega
        rw [ha]
      let H := vecU8Buf A.repAlloc pkCap pkPtr m.publicKey ∗
        vecU8Buf A.repAlloc skCap skPtr m.privateKey ∗
        vecU8Buf A.repAlloc sigCap sigPtr m.signature
      refine ⟨evs, pkCap, pkPtr, BitVec.ofNat 64 m.publicKey.length,
        skCap, skPtr, BitVec.ofNat 64 m.privateKey.length,
        sigCap, sigPtr, BitVec.ofNat 64 m.signature.length,
        m.timestamp, w10, H, ?_⟩
      have hprop : decodePostProp A.repAlloc F0 T0 bytes sf
          pkCap pkPtr (BitVec.ofNat 64 m.publicKey.length)
          skCap skPtr (BitVec.ofNat 64 m.privateKey.length)
          sigCap sigPtr (BitVec.ofNat 64 m.signature.length)
          m.timestamp w10 H := by
        unfold decodePostProp
        rw [hdes]
        refine ⟨hfsf, htr_eq.trans htr0, hpk_lt, fun out => ?_⟩
        unfold words11At kpkAnsAt pkAnsAt kyberPreKeyResultAt signedPreKeyStructAt vecU8
        have h80 : out + 80#64 = out + 0x50#64 := rfl
        rw [h80, ← htail_word out]
        have hv1 : (out ↦₆₄ pkCap) ∗ ((out + 8#64) ↦₆₄ pkPtr) ∗
            ((out + 16#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
            vecU8Buf A.repAlloc pkCap pkPtr m.publicKey ⊢
            ∃∗ c0 : BitVec 64, ∃∗ p0 : BitVec 64, vecU8At A.repAlloc out c0 p0 m.publicKey := by
          refine Entails.trans ?_
            (Entails.sepExists_right pkCap (Entails.sepExists_right pkPtr (Entails.refl _)))
          rw [vecU8At_eq_header_sep_buf]
          dsimp only [vecHeader]
          exact entails_of_eq_p (by sep_ac_rfl)
        have hv2 : ((out + 24#64) ↦₆₄ skCap) ∗ ((out + 32#64) ↦₆₄ skPtr) ∗
            ((out + 40#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
            vecU8Buf A.repAlloc skCap skPtr m.privateKey ⊢
            ∃∗ c0 : BitVec 64, ∃∗ p0 : BitVec 64,
              vecU8At A.repAlloc (out + 0x18#64) c0 p0 m.privateKey := by
          refine Entails.trans ?_
            (Entails.sepExists_right skCap (Entails.sepExists_right skPtr (Entails.refl _)))
          rw [vecU8At_eq_header_sep_buf]
          dsimp only [vecHeader]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
          exact entails_of_eq_p (by sep_ac_rfl)
        have hv3 : ((out + 48#64) ↦₆₄ sigCap) ∗ ((out + 56#64) ↦₆₄ sigPtr) ∗
            ((out + 64#64) ↦₆₄ BitVec.ofNat 64 m.signature.length) ∗
            vecU8Buf A.repAlloc sigCap sigPtr m.signature ⊢
            ∃∗ c0 : BitVec 64, ∃∗ p0 : BitVec 64,
              vecU8At A.repAlloc (out + 0x30#64) c0 p0 m.signature := by
          refine Entails.trans ?_
            (Entails.sepExists_right sigCap (Entails.sepExists_right sigPtr (Entails.refl _)))
          rw [vecU8At_eq_header_sep_buf]
          dsimp only [vecHeader]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
          exact entails_of_eq_p (by sep_ac_rfl)
        have hpad_ent : ((out + 0x54#64) ↦ₛ pad4) ⊢ memRegion (out + 0x54#64) 4 := by
          rw [← hpad_len]
          exact pointsToBytes_entails_memRegion (out + 0x54#64) pad4
        dsimp only [H]
        refine Entails.trans ?_
          (sepConj_mono hv1
            (sepConj_mono hv2
              (sepConj_mono hv3
                (sepConj_mono_right (sepConj_mono_right hpad_ent)))))
        exact entails_of_eq_p (by sep_ac_rfl)
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hprop, hevs⟩, ?_⟩
      rw [stackAt_sub_split s0.sp hle hhi]
      have hre_pad : ((ret + 80#64) ↦₃₂ m.id) ∗
          (((ret ↦₆₄ pkCap) ∗ ((ret + 8#64) ↦₆₄ pkPtr) ∗
            ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
            vecU8Buf A.repAlloc pkCap pkPtr m.publicKey) ∗
           (((ret + 24#64) ↦₆₄ skCap) ∗ ((ret + 32#64) ↦₆₄ skPtr) ∗
            ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
            vecU8Buf A.repAlloc skCap skPtr m.privateKey) ∗
           (((ret + 48#64) ↦₆₄ sigCap) ∗ ((ret + 56#64) ↦₆₄ sigPtr) ∗
            ((ret + 64#64) ↦₆₄ BitVec.ofNat 64 m.signature.length) ∗
            vecU8Buf A.repAlloc sigCap sigPtr m.signature) ∗
           ((ret + 72#64) ↦₆₄ m.timestamp) ∗
           ((ret + 84#64) ↦ₛ pad4) ∗
           vecU8Buf A.repAlloc bCap bPtr bytes ∗ stackAt s0.sp smallRootStack ∗
           A.pool lim (M.stepEvents evs st) sf ∗
           (stkRem ∗ R)) =
          (((ret + 80#64) ↦₃₂ m.id) ∗ ((ret + 84#64) ↦ₛ pad4)) ∗
          (((ret ↦₆₄ pkCap) ∗ ((ret + 8#64) ↦₆₄ pkPtr) ∗
            ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
            vecU8Buf A.repAlloc pkCap pkPtr m.publicKey) ∗
           (((ret + 24#64) ↦₆₄ skCap) ∗ ((ret + 32#64) ↦₆₄ skPtr) ∗
            ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
            vecU8Buf A.repAlloc skCap skPtr m.privateKey) ∗
           (((ret + 48#64) ↦₆₄ sigCap) ∗ ((ret + 56#64) ↦₆₄ sigPtr) ∗
            ((ret + 64#64) ↦₆₄ BitVec.ofNat 64 m.signature.length) ∗
            vecU8Buf A.repAlloc sigCap sigPtr m.signature) ∗
           ((ret + 72#64) ↦₆₄ m.timestamp) ∗
           vecU8Buf A.repAlloc bCap bPtr bytes ∗ stackAt s0.sp smallRootStack ∗
           A.pool lim (M.stepEvents evs st) sf ∗
           (stkRem ∗ R)) := by sep_ac_rfl
      have hq_w10 : sf.mem ⊨ ((ret + 80#64) ↦₆₄ w10) ∗
          (((ret ↦₆₄ pkCap) ∗ ((ret + 8#64) ↦₆₄ pkPtr) ∗
            ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
            vecU8Buf A.repAlloc pkCap pkPtr m.publicKey) ∗
           (((ret + 24#64) ↦₆₄ skCap) ∗ ((ret + 32#64) ↦₆₄ skPtr) ∗
            ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
            vecU8Buf A.repAlloc skCap skPtr m.privateKey) ∗
           (((ret + 48#64) ↦₆₄ sigCap) ∗ ((ret + 56#64) ↦₆₄ sigPtr) ∗
            ((ret + 64#64) ↦₆₄ BitVec.ofNat 64 m.signature.length) ∗
            vecU8Buf A.repAlloc sigCap sigPtr m.signature) ∗
           ((ret + 72#64) ↦₆₄ m.timestamp) ∗
           vecU8Buf A.repAlloc bCap bPtr bytes ∗ stackAt s0.sp smallRootStack ∗
           A.pool lim (M.stepEvents evs st) sf ∗
           (stkRem ∗ R)) := by
        rw [show ret + 80#64 = ret + 0x50#64 from rfl, ← htail_word ret, ← hre_pad]
        convert hq_nopad using 1; sep_ac_rfl
      dsimp only [words11At, H, stkRem] at hq_w10 ⊢
      convert hq_w10 using 1; sep_ac_rfl
  · dsimp only [withFsInv, withFdsGe3Closed,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
      decodeKyberPreKeyPlacedSpec, decodeKyberPreKeyRawSpec] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim
  · dsimp only [withFsInv, withFdsGe3Closed,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
      decodeKyberPreKeyPlacedSpec, decodeKyberPreKeyRawSpec] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim
  · dsimp only [withFsInv, withFdsGe3Closed,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
      decodeKyberPreKeyPlacedSpec, decodeKyberPreKeyRawSpec] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim

theorem kpkGetPoll_placed_of_inner_fd [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → BitVec 32 → List AllocEvent → Prop}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {calleeStk stk : Nat}
    (hInner : calleeStk ≤ 2 ^ 64 →
      subroutine_ok prog ((blkPl_576).base)
        (withLsCodeRoLoaded lsmpl
          (cliKpkGetPollInnerSpec_fd rd pathOk A lim DecEnv GetEnv DecodeEnv calleeStk)))
    (hstk : 0x1b0 + calleeStk ≤ stk) :
    subroutine_ok prog ((blkPl_576).base)
      (withFdsGe3Closed
        (kpkGetPollSpecPlaced rd pathOk A lim
          (CliKpkGetPollEnv DecEnv GetEnv DecodeEnv rd) stk)) := by
  refine subroutine_ok.of_codeLoaded fun ⟨x, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hfds0, hpre⟩ := extract_withFdsGe3Closed hpre
  unfold kpkGetPollSpecPlaced at hpre
  obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hn1, hn2, hs1, hs2, hfit⟩, hmem⟩
  dsimp only [pkBoxAt] at hmem
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine memRegion_bound_of_pointsTo64 (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk)
      (a := x.fut) (v := x.self)
      (R := ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
        memRegion (x.fut + 0xd#64) 3 ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        memRegion x.out 88 ∗ A.pool lim st s0 ∗ R) ?_
    dsimp only [stackAt] at hmem
    convert hmem using 1; sep_ac_rfl
  have hcal_hi : calleeStk ≤ 2 ^ 64 := by omega
  have hframe_hi : calleeStk + 432 ≤ 2 ^ 64 := by omega
  rw [stackAt_sub_split s0.sp (subStk := calleeStk + 432) (by omega) hstk_hi,
    stackAt_kpkPoll_frame s0.sp hframe_hi] at hmem
  let F_extra := memRegion (x.fut + 0xd#64) 3 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 432))
  have hpre_in : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (cliKpkGetPollInnerSpec_fd rd pathOk A lim DecEnv GetEnv DecodeEnv calleeStk)).pre
          (x, st) s0 ∗
        (F_extra ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [cliKpkGetPollInnerSpec_fd, withFdsGe3Closed]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfds0, ?_⟩
    dsimp only [cliKpkGetPollInnerSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨withFsInv_entry s0, hx0, hx8, hn1, hn2, hs1, hs2, hfit⟩, ?_⟩
    dsimp only [F_extra]
    convert hmem using 1; sep_ac_rfl
  refine (hInner hcal_hi).mono_outcome (x, st) (F_extra ∗ R) s0 hpc hrun hpre_in hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, cliKpkGetPollInnerSpec_fd, withFdsGe3Closed] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hfdsf, hq⟩
    dsimp only [withFdsGe3Closed]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfdsf, ?_⟩
    dsimp only [cliKpkGetPollInnerSpec, kpkGetPollSpecPlaced, pkBoxAt] at hq ⊢
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    refine ⟨evs, ?_⟩
    rw [stackAt_sub_split s0.sp (subStk := calleeStk + 432) (by omega) hstk_hi,
      stackAt_kpkPoll_frame s0.sp hframe_hi]
    dsimp only [F_extra] at hq
    convert hq using 1; sep_ac_rfl
  · dsimp only [withLsCodeRoLoaded, cliKpkGetPollInnerSpec_fd, withFdsGe3Closed,
      cliKpkGetPollInnerSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, cliKpkGetPollInnerSpec_fd, withFdsGe3Closed,
      cliKpkGetPollInnerSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, cliKpkGetPollInnerSpec_fd, withFdsGe3Closed,
      cliKpkGetPollInnerSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutPlacedBudgetFd
