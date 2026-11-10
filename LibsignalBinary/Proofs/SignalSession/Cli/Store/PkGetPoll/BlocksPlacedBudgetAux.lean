/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.BlocksPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable Callee Wrappers for `get_pre_key::{closure#0}`

Budget-threaded callee cell wrappers, `vecU8Buf` helpers, and outer specification bridge for
Block `573` (`lsProg_573 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.BlocksPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (SignalProtocolError)
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8)
open CryptoVerification.LibsignalTripleRatchet (extHookStack smallRootStack)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropSpeStackX)
open CryptoVerification.LibsignalTripleRatchetRepr
  (errResultAt errTag okTagVec speAt speWord strRefAt vecResultAt)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles LibsignalCodeRoLoaded NoFsEv TraceFsSound extract_withLsCodeRoLoaded
   sepWP_seq_lscro sepWPp_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.RecordCodecs (PreKeyRecord)
open CryptoVerification.RecordCodecsBinary (DecodeGhost preKeyRecordAt preKeyResultAt)
open CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers (pkDeserialize_eq_of_decodeLoop)
open CryptoVerification.SpqrV1.Alloc (vecU8At_eq_header_sep_buf vecU8Buf)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli
  (DecimalGhost DirGetGhost DirGhost DropSpeWordGhost PkPollGhost ReadRule dirAt
   files_eq_at_callback getResultAt keyName pkAnsAt pkBoxAt pkGetAnsAt subroutine_ok_withFsInv
   utf8 withFsInv withFsInv_entry withFsInv_post_elim withFsInv_pre_intro)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.Store.PkGetPoll.Helpers
  (DropSpeCellsGhost PkDecCellsGhost bytes_sep_vecU8BufRest_zero cells_32_split cells_sub_12_96_eq
   cells_sub_2_176_eq cells_sub_3_200_eq cells_sub_6_256_eq cells_sub_7_152_eq dirGetPayload
   memRegion_16_cells memRegion_24_cells memRegion_40_cells memRegion_48_cells memRegion_56_cells
   memRegion_bound_of_pointsTo64 pkDecPayload pkPollSlack pkSavedRegs readErrHeap
   stackAt_pkPoll_frame stackAt_sub_split vecU8BufRest vecU8Buf_eq_bytes_sep_rest)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget RustLayoutOk)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget
  (PreKeyDeserializeEnv RecordCodecLoopEnv preKeyDeserializePlacedSpec preKeyDeserializeRawSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced decimalSpecPlaced dirGetSpecPlaced dropSpeWordSpecPlaced
   pkGetPollSpecOfPlaced pkGetPollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget (dealloc_lscro_of_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget
  (CliPkGetPollEnv deallocBufCellsSpec decimalCellsSpec dirGetCellsSpec dropSpeWordCellsSpec
   pkDecCellsSpec pkGetPollInnerSpec)

section Placed

/-- Budget-threaded epilogue postcondition predicate for `get_pre_key::{closure#0}` (Block `573`). -/
def pkEpiloguePost {M : AllocCostModel} (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecEnv : BitVec 32 → List AllocEvent → Prop)
    (GetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop)
    (PkDecEnv : List (BitVec 8) → List AllocEvent → Prop)
    (calleeStk : Nat) (x : PkPollGhost) (st0 : M.σ) (s0 sf : State) (P_f : SepProp) : Prop :=
  sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
    (P_f ⊢ (pkGetPollInnerSpec rd pathOk A lim DecEnv GetEnv PkDecEnv calleeStk).post
      (x, st0) s0 sf)

/-- Call a total (`onPanic = ⌜False⌝`, `onExit = ⌜False⌝`, `onOom = ⌜False⌝`) spec wrapped in
`withLsCodeRoLoaded lsmpl`, preserving `LibsignalCodeRoLoaded lsmpl` in a `SepWP` continuation. -/
theorem pk_call_total_sepWP_lscro [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    {α : Type} {callee_pc ret_pc : BitVec 64} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog callee_pc (withLsCodeRoLoaded lsmpl spec))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = callee_pc)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hP : P ⊢ spec.pre x s ∗ F)
    (hexit : ∀ sf code R', ¬ (sf.mem ⊨ spec.onExit x code s sf ∗ R') := by
      intro _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', ¬ (sf.mem ⊨ spec.onOom x s sf ∗ R') := by
      intro _ _ ho; exact not_satisfies_false_sepConj ho)
    (hpanic : ∀ sf R', ¬ (sf.mem ⊨ spec.onPanic x s sf ∗ R') := by
      intro _ _ hp; exact not_satisfies_false_sepConj hp)
    (hnext : ∀ sf : State,
      LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      SepWP prog ret sf (spec.post x s sf ∗ F) Q) :
    SepWP prog ret s P Q := by
  refine sepWP_seq_lscro (mid := ret_pc) hcrl ?_
  refine ProofLib.SepWP.call_subroutine_frame (x := x) (F := F) hcall hpc hrun hsp hlr
    (fun R hm => ?_)
    (fun R' sm _ hp => ?_)
    (fun R' code sm _ he => ?_)
    (fun sm hpcm hrunm hspm hcsm =>
      ProofLib.SepWP.done hpcm hrunm (fun hcrlm => ?_))
    (fun R' sm _ ho => ?_)
  · have hm_pre : s.mem ⊨ (spec.pre x s ∗ F) ∗ R :=
      Satisfies.mono (sepConj_mono_left hP) hm
    exact satisfies_lscro_pre hcrl (by simpa only [sepConj_assoc] using hm_pre)
  · dsimp only [withLsCodeRoLoaded] at hp
    exact hpanic sm R' hp
  · dsimp only [withLsCodeRoLoaded] at he
    exact hexit sm code R' he
  · dsimp only [withLsCodeRoLoaded]
    exact hnext sm hcrlm hpcm hrunm hspm hcsm
  · dsimp only [withLsCodeRoLoaded] at ho
    exact (hoom sm (F ∗ R') ho).elim

/-- Panic-aware (`SepWPp`) counterpart of `pk_call_total_sepWP_lscro` for any `Qp`. -/
theorem pk_call_total_sepWPp_lscro [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    {α : Type} {callee_pc ret_pc : BitVec 64} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog callee_pc (withLsCodeRoLoaded lsmpl spec))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = callee_pc)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hP : P ⊢ spec.pre x s ∗ F)
    (hexit : ∀ sf code R', ¬ (sf.mem ⊨ spec.onExit x code s sf ∗ R') := by
      intro _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', ¬ (sf.mem ⊨ spec.onOom x s sf ∗ R') := by
      intro _ _ ho; exact not_satisfies_false_sepConj ho)
    (hpanic : ∀ sf R', ¬ (sf.mem ⊨ spec.onPanic x s sf ∗ R') := by
      intro _ _ hp; exact not_satisfies_false_sepConj hp)
    (hnext : ∀ sf : State,
      LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine sepWPp_seq_lscro (mid := ret_pc) hcrl ?_
  refine ProofLib.SepWP.call_subroutine_frame (x := x) (F := F) hcall hpc hrun hsp hlr
    (fun R hm => ?_)
    (fun R' sm _ hp => ?_)
    (fun R' code sm _ he => ?_)
    (fun sm hpcm hrunm hspm hcsm =>
      ProofLib.SepWP.done hpcm hrunm (fun hcrlm => ?_))
    (fun R' sm _ ho => ?_)
  · have hm_pre : s.mem ⊨ (spec.pre x s ∗ F) ∗ R :=
      Satisfies.mono (sepConj_mono_left hP) hm
    exact satisfies_lscro_pre hcrl (by simpa only [sepConj_assoc] using hm_pre)
  · dsimp only [withLsCodeRoLoaded] at hp
    exact hpanic sm R' hp
  · dsimp only [withLsCodeRoLoaded] at he
    exact hexit sm code R' he
  · dsimp only [withLsCodeRoLoaded]
    exact hnext sm hcrlm hpcm hrunm hspm hcsm
  · dsimp only [withLsCodeRoLoaded] at ho
    exact (hoom sm (F ∗ R') ho).elim

/-! ## 1. Frame & `vecU8Buf` Helpers -/

theorem bytes_zero_elim_p {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {ptr : BitVec 64} {bs : List (BitVec 8)} {Rest : SepProp}
    {Q : State → SepProp → Prop} {P : SepProp}
    (heq : P = ((ptr ↦ₛ bs) ∗ vecU8BufRest A 0#64 ptr bs) ∗ Rest)
    (h : SepWP prog ret s Rest Q) :
    SepWP prog ret s P Q := by
  rw [heq, bytes_sep_vecU8BufRest_zero]
  exact SepWP.pure_elim fun _ => h

theorem pkFrame_pack_p (sp : BitVec 64) (s0 : State)
    (u0 u1 u2 u3 u4 u5 n0 n1 n2 k0 k1 g0 g1 g2 g3 g4 g5 g6 : BitVec 64) :
    (pkPollSlack sp ∗ pkSavedRegs sp s0 ∗
      ((sp - 256#64) ↦₆₄ u0) ∗ ((sp - 248#64) ↦₆₄ u1) ∗
      ((sp - 240#64) ↦₆₄ u2) ∗ ((sp - 232#64) ↦₆₄ u3) ∗
      ((sp - 224#64) ↦₆₄ u4) ∗ ((sp - 216#64) ↦₆₄ u5) ∗
      ((sp - 200#64) ↦₆₄ n0) ∗ ((sp - 192#64) ↦₆₄ n1) ∗ ((sp - 184#64) ↦₆₄ n2) ∗
      ((sp - 176#64) ↦₆₄ k0) ∗ ((sp - 168#64) ↦₆₄ k1) ∗
      ((sp - 152#64) ↦₆₄ g0) ∗ ((sp - 144#64) ↦₆₄ g1) ∗
      ((sp - 136#64) ↦₆₄ g2) ∗ ((sp - 128#64) ↦₆₄ g3) ∗
      ((sp - 120#64) ↦₆₄ g4) ∗ ((sp - 112#64) ↦₆₄ g5) ∗ ((sp - 104#64) ↦₆₄ g6)) ⊢
      cells (sp - 256#64) 32 := by
  rw [cells_32_split]
  have h6 : (((sp - 256#64) ↦₆₄ u0) ∗ ((sp - 248#64) ↦₆₄ u1) ∗ ((sp - 240#64) ↦₆₄ u2) ∗
      ((sp - 232#64) ↦₆₄ u3) ∗ ((sp - 224#64) ↦₆₄ u4) ∗ ((sp - 216#64) ↦₆₄ u5)) ⊢
      cells (sp - 256#64) 6 := by
    rw [cells_sub_6_256_eq]
    exact Entails.sepExists_right u0 (Entails.sepExists_right u1 (Entails.sepExists_right u2
      (Entails.sepExists_right u3 (Entails.sepExists_right u4
        (Entails.sepExists_right u5 (Entails.refl _))))))
  have h3 : (((sp - 200#64) ↦₆₄ n0) ∗ ((sp - 192#64) ↦₆₄ n1) ∗ ((sp - 184#64) ↦₆₄ n2)) ⊢
      cells (sp - 200#64) 3 := by
    rw [cells_sub_3_200_eq]
    exact Entails.sepExists_right n0 (Entails.sepExists_right n1
      (Entails.sepExists_right n2 (Entails.refl _)))
  have h2 : (((sp - 176#64) ↦₆₄ k0) ∗ ((sp - 168#64) ↦₆₄ k1)) ⊢ cells (sp - 176#64) 2 := by
    rw [cells_sub_2_176_eq]
    exact Entails.sepExists_right k0 (Entails.sepExists_right k1 (Entails.refl _))
  have h7 : (((sp - 152#64) ↦₆₄ g0) ∗ ((sp - 144#64) ↦₆₄ g1) ∗ ((sp - 136#64) ↦₆₄ g2) ∗
      ((sp - 128#64) ↦₆₄ g3) ∗ ((sp - 120#64) ↦₆₄ g4) ∗ ((sp - 112#64) ↦₆₄ g5) ∗
      ((sp - 104#64) ↦₆₄ g6)) ⊢ cells (sp - 152#64) 7 := by
    rw [cells_sub_7_152_eq]
    exact Entails.sepExists_right g0 (Entails.sepExists_right g1 (Entails.sepExists_right g2
      (Entails.sepExists_right g3 (Entails.sepExists_right g4 (Entails.sepExists_right g5
        (Entails.sepExists_right g6 (Entails.refl _)))))))
  have h12 : pkSavedRegs sp s0 ⊢ cells (sp - 96#64) 12 := by
    unfold pkSavedRegs
    rw [cells_sub_12_96_eq]
    exact Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
      (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
        (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
          (Entails.sepExists_right _ (Entails.sepExists_right _
            (Entails.sepExists_right _ (Entails.refl _))))))))))))
  refine Entails.trans (Q :=
    pkPollSlack sp ∗
      (((sp - 256#64) ↦₆₄ u0) ∗ ((sp - 248#64) ↦₆₄ u1) ∗ ((sp - 240#64) ↦₆₄ u2) ∗
        ((sp - 232#64) ↦₆₄ u3) ∗ ((sp - 224#64) ↦₆₄ u4) ∗ ((sp - 216#64) ↦₆₄ u5)) ∗
      (((sp - 200#64) ↦₆₄ n0) ∗ ((sp - 192#64) ↦₆₄ n1) ∗ ((sp - 184#64) ↦₆₄ n2)) ∗
      (((sp - 176#64) ↦₆₄ k0) ∗ ((sp - 168#64) ↦₆₄ k1)) ∗
      (((sp - 152#64) ↦₆₄ g0) ∗ ((sp - 144#64) ↦₆₄ g1) ∗ ((sp - 136#64) ↦₆₄ g2) ∗
        ((sp - 128#64) ↦₆₄ g3) ∗ ((sp - 120#64) ↦₆₄ g4) ∗ ((sp - 112#64) ↦₆₄ g5) ∗
        ((sp - 104#64) ↦₆₄ g6)) ∗
      pkSavedRegs sp s0) (Entails.of_eq (by sep_ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono h6
    (sepConj_mono h3 (sepConj_mono h2 (sepConj_mono h7 h12))))

private theorem sepExists_congr_p {α : Type} {f g : α → SepProp} (h : ∀ x, f x = g x) :
    (∃∗ x, f x) = (∃∗ x, g x) :=
  congrArg sepExists (funext h)

private theorem pure_true_eq_emp_p {P : Prop} (h : P) : (⌜P⌝ : SepProp) = emp := by
  rw [eq_true h]
  exact pure_true

private theorem pointsTo32_memRegion4_eq_p (a : BitVec 64) (lo : BitVec 32) :
    ((a ↦₃₂ lo) ∗ memRegion (a + 4#64) 4) =
      ∃∗ hi : BitVec 32, (a ↦₆₄ (hi ++ lo)) := by
  rw [ProofLib.memRegion_four (a + 4#64)]
  simp only [sepExists_sepConj_right]
  apply sepExists_congr_p; intro hi
  have hlo : BitVec.extractLsb' 0 32 (hi ++ lo) = lo := by bv_bits
  have hhi : BitVec.extractLsb' 32 32 (hi ++ lo) = hi := by bv_bits
  rw [ProofLib.pointsTo64_split32 a (hi ++ lo), hlo, hhi]

private theorem vecU8_eq_words_sep_bytes_rest_p (A : RustAlloc) (v : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8 A v bs =
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ vecU8BufRest A cap ptr bs := by
  unfold vecU8
  apply sepExists_congr_p; intro cap
  apply sepExists_congr_p; intro ptr
  rw [vecU8At_eq_header_sep_buf, vecU8Buf_eq_bytes_sep_rest]
  dsimp only [vecHeader]
  sep_ac_rfl

private theorem bytes_sep_memRegion_entails_memRegion_p (ptr : BitVec 64) (bs : List (BitVec 8))
    {cap : Nat} (hlen : bs.length ≤ cap) (hcap : cap ≤ 2 ^ 64) :
    ((ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap - bs.length)) ⊢
      memRegion ptr cap := by
  have heq : cap = bs.length + (cap - bs.length) := by omega
  conv_rhs => rw [heq]
  rw [memRegion_split ptr bs.length (cap - bs.length) (by omega),
    memRegion_eq_exists_bytes ptr bs.length (by omega)]
  apply sepConj_mono_left
  exact Entails.sepExists_right bs (Entails.pure_right rfl (Entails.refl _))

private theorem vecU8Buf_cap_add_one_ne_zero_p {m : Memory} {A : RustAlloc}
    {cap ptr : BitVec 64} {bs : List (BitVec 8)} {R : SepProp}
    (h : m ⊨ vecU8Buf A cap ptr bs ∗ R) : cap + 1#64 ≠ 0#64 := by
  unfold vecU8Buf at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  have hlt := h.1.2.1
  bv_omega

/-! ## 2. Placed Budget Callee Cell Wrappers & Outer Bridge -/

theorem dealloc_buf_cells_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg prog i H] {calleeStk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hle : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl (deallocBufCellsSpec A lim calleeStk)) := by
  have hDealloc := dealloc_lscro_of_cli (callerProg := prog) hC hi
  refine subroutine_ok.of_codeLoaded fun ⟨⟨ptr, cap, bs, fsp⟩, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  rcases extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  simp only [deallocBufCellsSpec, vecU8BufRest, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hfsp, hcap0, hlr_ls⟩, hmem⟩
  subst hfsp
  have hmem1 : s0.mem ⊨ ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((ptr ↦ₛ bs) ∗ (if cap = 0 then emp
        else A.repAlloc.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
        A.pool lim st s0 ∗ stackAt s0.sp calleeStk ∗ R) := by
    convert hmem using 1; sep_ac_rfl
  rw [satisfies_pure_sepConj] at hmem1
  rcases hmem1 with ⟨⟨hlen, hlt, _hptr⟩, hmem2⟩
  have hcap0' : cap ≠ 0 := hcap0
  simp only [hcap0', ↓reduceIte] at hmem2
  rw [stackAt_sub_split s0.sp hle hhi] at hmem2
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - extHookStack)
  have hcap_pos : 0 < cap.toNat := by
    by_cases hz : cap.toNat = 0
    · exact (hcap0 (BitVec.eq_of_toNat_eq hz)).elim
    · omega
  have hlay : RustLayoutOk cap.toNat 1 := ⟨⟨hcap_pos, ⟨0, rfl⟩, by omega⟩, by decide⟩
  have hmem_reg : s0.mem ⊨ ((ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
      (A.pool lim st s0 ∗ A.live ptr cap.toNat 1 ∗ stackAt s0.sp extHookStack ∗ stkRem ∗ R) := by
    dsimp only [RustCliAllocBudget.repAlloc, stkRem] at hmem2 ⊢
    convert hmem2 using 1; sep_ac_rfl
  have hmem_reg' : s0.mem ⊨ memRegion ptr cap.toNat ∗
      (A.pool lim st s0 ∗ A.live ptr cap.toNat 1 ∗ stackAt s0.sp extHookStack ∗ stkRem ∗ R) :=
    Satisfies.mono
      (sepConj_mono_left (bytes_sep_memRegion_entails_memRegion_p ptr bs hlen (by omega))) hmem_reg
  have hx1_nat : (s0.readReg64 .x1).toNat = cap.toNat := congrArg BitVec.toNat hx1
  have hx2_nat : (s0.readReg64 .x2).toNat = 1 := by rw [hx2]; rfl
  let callG : BitVec 64 × Nat × Nat × M.σ := (ptr, cap.toNat, 1, st)
  have hpre0 : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack M A lim extHookStack)).pre
        callG s0 ∗ (stkRem ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack, callG]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1_nat, hx2_nat, hlay, hlr_ls⟩, ?_⟩
    convert hmem_reg' using 1; sep_ac_rfl
  refine hDealloc.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
      deallocBufCellsSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨htr, hq⟩
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; sep_ac_rfl
  · dsimp only [withLsCodeRoLoaded, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem decimal_cells_placed_ok [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {decStk calleeStk : Nat}
    (hDecimal : subroutine_ok prog (lsmpl.base 597) (decimalSpecPlaced A lim DecEnv decStk))
    (hFs : TraceFsSound prog)
    (hle : decStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 597)
      (withLsCodeRoLoaded lsmpl (decimalCellsSpec A lim DecEnv calleeStk)) := by
  refine subroutine_ok.of_codeLoaded fun ⟨⟨n, ret, o0, o1, o2, fsp⟩, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  rcases extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  simp only [decimalCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hfsp, hfit⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - decStk)
  let callG : DecimalGhost × M.σ := (⟨n, ret⟩, st)
  have hDecFs := subroutine_ok_withFsInv hFs hDecimal s0.fs.files s0.trace
  have hpre0 : s0.mem ⊨
      (withFsInv (decimalSpecPlaced A lim DecEnv decStk) s0.fs.files s0.trace).pre callG s0 ∗
      (stkRem ∗ R) := by
    refine withFsInv_pre_intro (withFsInv_entry s0) ?_
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
  refine hDecFs.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    obtain ⟨hfs', hq⟩ := withFsInv_post_elim hq
    dsimp only [withLsCodeRoLoaded, decimalSpecPlaced, decimalCellsSpec, callG, keyName] at hq ⊢
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨htr, hevs⟩, hq⟩
    have hfiles : sf.fs.files = s0.fs.files :=
      files_eq_at_callback hfs' (evs := []) (by simp [htr]) NoFsEv.nil
    change sf.mem ⊨
      (vecU8 A.repAlloc ret (keyName n) ∗ stackAt s0.sp decStk ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      (stkRem ∗ R) at hq
    rw [vecU8_eq_words_sep_bytes_rest_p] at hq
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨nCap, nPtr, hq⟩
    refine ⟨evs, nCap, nPtr, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr, hfiles, hevs⟩, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; sep_ac_rfl
  · dsimp only [withFsInv, withLsCodeRoLoaded, decimalSpecPlaced] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim
  · dsimp only [withFsInv, withLsCodeRoLoaded, decimalSpecPlaced] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim
  · dsimp only [withFsInv, withLsCodeRoLoaded, decimalSpecPlaced] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim

theorem dirGet_cells_placed_ok [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {GetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk calleeStk : Nat}
    (hGet : subroutine_ok prog (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim (fun _ => GetEnv) getStk))
    (hle : getStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 589)
      (withLsCodeRoLoaded lsmpl (dirGetCellsSpec rd pathOk A lim GetEnv calleeStk)) := by
  refine subroutine_ok.of_codeLoaded
    fun ⟨⟨ret, self, dir, nameA, name, o0, o1, o2, o3, o4, o5, fsp⟩, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  rcases extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  simp only [dirGetCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hfsp, hnlen, hplen, hpok, hfit⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - getStk)
  let callG : DirGetGhost × M.σ := (⟨ret, self, dir, nameA, name, false⟩, st)
  have hpre0 : s0.mem ⊨
      (dirGetSpecPlaced rd pathOk A lim (fun _ => GetEnv) getStk).pre callG s0 ∗ (stkRem ∗ R) := by
    unfold dirGetSpecPlaced
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [callG, CryptoVerification.SpqrV1.ChainProofs.bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte, memRegion_48_cells, sepExists_sepConj_left,
      sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o5, o4, o3, o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hnlen, hplen, hpok, hfit⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; sep_ac_rfl
  refine hGet.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, dirGetSpecPlaced, dirGetCellsSpec, callG,
      CryptoVerification.SpqrV1.ChainProofs.bytesAt] at hq ⊢
    simp only [Bool.false_eq_true, ↓reduceIte, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, r, hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hdisj, hq⟩
    rcases r with ⟨⟩ | bs
    · dsimp only [getResultAt, speAt, strRefAt] at hq
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
        BitVec.add_assoc, BitVec.reduceAdd] at hq
      rcases hq with ⟨w4, ebs, hq⟩
      have hq' : sf.mem ⊨ vecU8 A.repAlloc (ret + 8#64) ebs ∗
          ((ret ↦₆₄ speWord 1) ∗ ((ret + 32#64) ↦₆₄ w4) ∗
            ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
            (w4 ↦ᵣ utf8 "read") ∗ dirAt A.repAlloc self dir ∗ (nameA ↦ₛ name) ∗
            stackAt s0.sp getStk ∗ A.pool lim (M.stepEvents evs st) sf ∗ (stkRem ∗ R)) := by
        convert hq using 1; sep_ac_rfl
      dsimp only [vecU8] at hq'
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hq'
      rcases hq' with ⟨w1, w2, hq'⟩
      rw [vecU8At_eq_header_sep_buf] at hq'
      dsimp only [vecHeader] at hq'
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq'
      refine ⟨evs, .error (), speWord 1, w1, w2, BitVec.ofNat 64 ebs.length, w4,
        BitVec.ofNat 64 (utf8 "read").length, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hdisj, ?_⟩
      dsimp only [dirGetPayload, readErrHeap]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
      refine ⟨ebs, ?_⟩
      rw [stackAt_sub_split s0.sp hle hhi]
      simp only [eq_self, and_self, pure_true_eq_emp_p trivial, emp_sepConj]
      dsimp only [stkRem] at hq'
      convert hq' using 1; sep_ac_rfl
    · dsimp only [getResultAt, vecResultAt] at hq
      rw [vecU8_eq_words_sep_bytes_rest_p A.repAlloc (ret + 8#64) bs] at hq
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
        BitVec.add_assoc, BitVec.reduceAdd] at hq
      rcases hq with ⟨w1, w2, hq⟩
      rw [memRegion_16_cells (ret + 32#64)] at hq
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
        BitVec.add_assoc, BitVec.reduceAdd] at hq
      rcases hq with ⟨w5, w4, hq⟩
      refine ⟨evs, .ok bs, okTagVec, w1, w2, BitVec.ofNat 64 bs.length, w4, w5, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hdisj, ?_⟩
      dsimp only [dirGetPayload]
      rw [stackAt_sub_split s0.sp hle hhi]
      simp only [eq_self, and_self, pure_true_eq_emp_p trivial, emp_sepConj]
      dsimp only [stkRem] at hq
      convert hq using 1; sep_ac_rfl
  · dsimp only [dirGetSpecPlaced, withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [dirGetSpecPlaced, withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [dirGetSpecPlaced, withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem pkDec_cells_placed_ok [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PkDecEnv : List (BitVec 8) → List AllocEvent → Prop}
    {calleeStk : Nat}
    (hDec : subroutine_ok prog (lsmpl.base 65) (preKeyDeserializePlacedSpec A lim))
    (hle : smallRootStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64)
    (hSub : ∀ bs evs, RecordCodecLoopEnv (2 * bs.length + 3) bs.length evs → PkDecEnv bs evs)
    (hSup : ∀ bs evs, PreKeyDeserializeEnv bs.length evs → PkDecEnv bs evs) :
    subroutine_ok prog (lsmpl.base 65)
      (withLsCodeRoLoaded lsmpl (pkDecCellsSpec A lim PkDecEnv calleeStk)) := by
  refine subroutine_ok.of_codeLoaded
    fun ⟨⟨bytesA, bytes, ret, o0, o1, o2, o3, o4, o5, o6, fsp⟩, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  rcases extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  simp only [pkDecCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hblen, hx8, hfsp, hfit⟩, hmem⟩
  subst hfsp
  have hfit_loop : FitsEnv M lim st (RecordCodecLoopEnv (2 * bytes.length + 3) bytes.length) :=
    hfit.mono (hSub bytes)
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - smallRootStack)
  let callG : DecodeGhost × M.σ := (⟨bytesA, bytes, ret⟩, st)
  have hpre0 : s0.mem ⊨ (preKeyDeserializePlacedSpec A lim).pre callG s0 ∗ (stkRem ∗ R) := by
    change s0.mem ⊨ (withLsCodeRoLoaded lsmpl (preKeyDeserializeRawSpec A lim)).pre callG s0 ∗
      (stkRem ∗ R)
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [preKeyDeserializeRawSpec, callG]
    simp only [memRegion_56_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o6, o5, o4, o3, o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hblen, hx8, hfit_loop⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; sep_ac_rfl
  refine hDec.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, preKeyDeserializePlacedSpec, preKeyDeserializeRawSpec,
      pkDecCellsSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq⟩
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hevs0, hq⟩
    have hevs : PkDecEnv bytes evs := hSup bytes evs hevs0
    rcases hres : PreKeyRecord.deserialize bytes with e | rec
    · have he : e = .invalidProtobufEncoding := by
        have hloop := pkDeserialize_eq_of_decodeLoop bytes
        rw [hres] at hloop
        split at hloop
        · nomatch hloop
        · injection hloop
      subst he
      rw [hres] at hq
      dsimp only [preKeyResultAt, errResultAt, speAt] at hq
      simp only [Nat.sub_self, memRegion_zero, sepConj_emp, BitVec.add_assoc,
        BitVec.reduceAdd] at hq
      have hq' : sf.mem ⊨ memRegion (ret + 16#64) 40 ∗
          ((ret ↦₆₄ errTag) ∗ ((ret + 8#64) ↦₆₄ speWord 2) ∗
            (bytesA ↦ₛ bytes) ∗ stackAt s0.sp smallRootStack ∗
            A.pool lim (M.stepEvents evs st) sf ∗ (stkRem ∗ R)) := by
        convert hq using 1; sep_ac_rfl
      rw [memRegion_40_cells] at hq'
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
        BitVec.add_assoc, BitVec.reduceAdd] at hq'
      rcases hq' with ⟨d6, d5, d4, d3, d2, hq'⟩
      refine ⟨evs, errTag, speWord 2, d2, d3, d4, d5, d6, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨htr, hevs⟩, ?_⟩
      dsimp only [pkDecPayload]
      rw [stackAt_sub_split s0.sp hle hhi]
      simp only [eq_self, and_self, pure_true_eq_emp_p trivial, emp_sepConj]
      dsimp only [stkRem] at hq'
      convert hq' using 1; sep_ac_rfl
    · rw [hres] at hq
      dsimp only [preKeyResultAt, preKeyRecordAt] at hq
      have hq1 : sf.mem ⊨
          vecU8 A.repAlloc ret rec.preKey.publicKey ∗
          vecU8 A.repAlloc (ret + 24#64) rec.preKey.privateKey ∗
          (((ret + 48#64) ↦₃₂ rec.preKey.id) ∗ memRegion (ret + 52#64) 4) ∗
          ((bytesA ↦ₛ bytes) ∗ stackAt s0.sp smallRootStack ∗
            A.pool lim (M.stepEvents evs st) sf ∗ (stkRem ∗ R)) := by
        convert hq using 1; sep_ac_rfl
      have h52 : ret + 48#64 + 4#64 = ret + 52#64 := by bv_omega
      rw [← h52, pointsTo32_memRegion4_eq_p (ret + 48#64) rec.preKey.id] at hq1
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq1
      rcases hq1 with ⟨hi32, hq1⟩
      dsimp only [vecU8] at hq1
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq1
      rcases hq1 with ⟨d3, d4, d0, d1, hq1⟩
      rw [vecU8At_eq_header_sep_buf, vecU8At_eq_header_sep_buf] at hq1
      dsimp only [vecHeader] at hq1
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq1
      have hd0_ne : d0 + 1#64 ≠ 0#64 := by
        refine vecU8Buf_cap_add_one_ne_zero_p (m := sf.mem) (A := A.repAlloc) (cap := d0) (ptr := d1)
          (bs := rec.preKey.publicKey)
          (R := (ret ↦₆₄ d0) ∗ ((ret + 8#64) ↦₆₄ d1) ∗
            ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 rec.preKey.publicKey.length) ∗
            ((ret + 24#64) ↦₆₄ d3) ∗ ((ret + 32#64) ↦₆₄ d4) ∗
            ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 rec.preKey.privateKey.length) ∗
            vecU8Buf A.repAlloc d3 d4 rec.preKey.privateKey ∗
            ((ret + 48#64) ↦₆₄ (hi32 ++ rec.preKey.id)) ∗
            (bytesA ↦ₛ bytes) ∗ stackAt s0.sp smallRootStack ∗
            A.pool lim (M.stepEvents evs st) sf ∗ (stkRem ∗ R)) ?_
        convert hq1 using 1; sep_ac_rfl
      refine ⟨evs, d0, d1, BitVec.ofNat 64 rec.preKey.publicKey.length,
        d3, d4, BitVec.ofNat 64 rec.preKey.privateKey.length, hi32 ++ rec.preKey.id, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨htr, hevs⟩, ?_⟩
      dsimp only [pkDecPayload]
      rw [stackAt_sub_split s0.sp hle hhi]
      have hid_lo : (hi32 ++ rec.preKey.id).extractLsb' 0 32 = rec.preKey.id := by bv_bits
      rw [pure_true_eq_emp_p (⟨hd0_ne, rfl, rfl, hid_lo⟩ :
        d0 + 1#64 ≠ 0#64 ∧
          BitVec.ofNat 64 rec.preKey.publicKey.length =
            BitVec.ofNat 64 rec.preKey.publicKey.length ∧
          BitVec.ofNat 64 rec.preKey.privateKey.length =
            BitVec.ofNat 64 rec.preKey.privateKey.length ∧
          (hi32 ++ rec.preKey.id).extractLsb' 0 32 = rec.preKey.id), emp_sepConj]
      dsimp only [stkRem] at hq1
      convert hq1 using 1; sep_ac_rfl
  · dsimp only [withLsCodeRoLoaded, preKeyDeserializePlacedSpec, preKeyDeserializeRawSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, preKeyDeserializePlacedSpec, preKeyDeserializeRawSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, preKeyDeserializePlacedSpec, preKeyDeserializeRawSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem dropSpeWord_cells_placed_ok [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {calleeStk : Nat}
    (hDrop : subroutine_ok prog (lsmpl.base 553) (dropSpeWordSpecPlaced A lim))
    (hle : dropSpeStackX ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 553)
      (withLsCodeRoLoaded lsmpl (dropSpeWordCellsSpec A lim calleeStk)) := by
  refine subroutine_ok.of_codeLoaded
    fun ⟨⟨a, c1, c2, c3, c4, c5, fsp⟩, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  rcases extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  simp only [dropSpeWordCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hfsp⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - dropSpeStackX)
  let callG : DropSpeWordGhost × M.σ := (⟨a, 13⟩, st)
  have hpre0 : s0.mem ⊨ (dropSpeWordSpecPlaced A lim).pre callG s0 ∗ (stkRem ∗ R) := by
    unfold dropSpeWordSpecPlaced
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [callG]
    simp only [memRegion_40_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, BitVec.add_assoc, BitVec.reduceAdd]
    refine ⟨c5, c4, c3, c2, c1, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, Or.inl trivial⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; sep_ac_rfl
  refine hDrop.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, dropSpeWordSpecPlaced, dropSpeWordCellsSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq⟩
    have hq' : sf.mem ⊨ memRegion a 48 ∗
        (A.pool lim st sf ∗ stackAt s0.sp dropSpeStackX ∗ (stkRem ∗ R)) := by
      convert hq using 1; sep_ac_rfl
    rw [memRegion_48_cells] at hq'
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq' ⊢
    rcases hq' with ⟨m5, m4, m3, m2, m1, m0, hq'⟩
    refine ⟨m0, m1, m2, m3, m4, m5, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq'
    convert hq' using 1; sep_ac_rfl
  · dsimp only [withLsCodeRoLoaded, dropSpeWordSpecPlaced] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, dropSpeWordSpecPlaced] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, dropSpeWordSpecPlaced] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem pkGetPoll_placed_of_inner [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PkDecEnv : List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {calleeStk stk : Nat}
    (hInner : calleeStk ≤ 2 ^ 64 →
      subroutine_ok prog entry
        (withLsCodeRoLoaded lsmpl
          (pkGetPollInnerSpec rd pathOk A lim DecEnv GetEnv PkDecEnv calleeStk)))
    (hstk : 256 + calleeStk ≤ stk) :
    subroutine_ok prog entry
      (pkGetPollSpecPlaced rd pathOk A lim
        (CliPkGetPollEnv DecEnv GetEnv PkDecEnv rd) stk) := by
  refine subroutine_ok.of_codeLoaded fun ⟨x, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  unfold pkGetPollSpecPlaced pkGetPollSpecOfPlaced at hpre
  rcases extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  dsimp only [] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hname, hsize, hfit⟩, hmem⟩
  dsimp only [pkBoxAt] at hmem
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine memRegion_bound_of_pointsTo64 (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk)
      (a := x.fut) (v := x.self)
      (R := ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 0#8) ∗
        memRegion (x.fut + 13#64) 3 ∗
        dirAt A.repAlloc x.self x.dir ∗ memRegion x.out 56 ∗ A.pool lim st s0 ∗ R) ?_
    dsimp only [stackAt] at hmem
    convert hmem using 1; sep_ac_rfl
  have hcal_hi : calleeStk ≤ 2 ^ 64 := by omega
  have hframe_hi : calleeStk + 256 ≤ 2 ^ 64 := by omega
  rw [stackAt_sub_split s0.sp (subStk := calleeStk + 256) (by omega) hstk_hi,
    stackAt_pkPoll_frame s0.sp hframe_hi] at hmem
  let F_extra := memRegion (x.fut + 13#64) 3 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 256))
  have hpre_in : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (pkGetPollInnerSpec rd pathOk A lim DecEnv GetEnv PkDecEnv calleeStk)).pre (x, st) s0 ∗
      (F_extra ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [pkGetPollInnerSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hname, hsize, hfit⟩, ?_⟩
    dsimp only [F_extra]
    convert hmem using 1; sep_ac_rfl
  refine (hInner hcal_hi).mono_outcome (x, st) (F_extra ∗ R) s0 hpc hrun hpre_in hsp
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, pkGetPollInnerSpec, pkGetPollSpecPlaced,
      pkGetPollSpecOfPlaced, pkGetAnsAt, pkBoxAt] at hq ⊢
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, ans, hq⟩
    refine ⟨evs, ans, ?_⟩
    rw [stackAt_sub_split s0.sp (subStk := calleeStk + 256) (by omega) hstk_hi,
      stackAt_pkPoll_frame s0.sp hframe_hi]
    dsimp only [F_extra] at hq
    convert hq using 1; sep_ac_rfl
  · dsimp only [withLsCodeRoLoaded, pkGetPollInnerSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, pkGetPollInnerSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, pkGetPollInnerSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.BlocksPlacedBudgetAux
