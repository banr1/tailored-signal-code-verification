/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymB
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.DropSpeWordPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.Sym
public meta import ProofLib
public meta import LibsignalBinary.Proofs.Common.InImageKit
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public meta import Lean
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.Blocks
public import LibsignalBinary.Proofs.RecordCodecs.Deps
public import LibsignalBinary.Proofs.SignalSession.Cli.Fs
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Relocatable Callee Wrappers and Error/Epilogue Blocks for `get_pre_key::{closure#0}`

Placed callee cell wrappers, outer specification bridge, shared epilogue (`+348 .. +404`), and
error-branch lemmas (`step_err_200`, `step_dec_err_152`) on `lsProg_573 H` under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.PkGetPoll.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary
open CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.CodeLayout CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
open CliPkGetPollNorm

section Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_sub_496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_add_neg496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.esp_add_496_sub_496

/-! ## 1. Unified `wp_call_spec_lscro` for `SepWP` and `SepWPp` -/

open Lean Elab Tactic Meta in
meta def wpCallSpecLsCro (hcall specStx hinv arg : Term) : TacticM Unit := do
  let g0 ← getMainGoal
  let gty := (← g0.withContext do instantiateMVars (← g0.getType)).consumeMData
  let isWPp ← if gty.isAppOfArity ``SepWPp 7 then pure true
    else if gty.isAppOfArity ``SepWP 6 then pure false
    else throwError "wp_call_spec_lscro: goal is not `SepWP …` / `SepWPp …`"
  let sGoal := gty.getArg! 2
  let hinvId ← freshIdent `hcrl_call
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hinvSfId ← freshIdent `hcrl_sf
  let sStx ← g0.withContext (Term.exprToSyntax sGoal)
  let haveStx ← `(tactic|
    have $hinvId:ident :
        CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl ($sStx).mem := by
      first
        | with_reducible exact $hinv
        | exact ⟨($hinv).1, ($hinv).2⟩
        | exact lscro_of_mem_eq $hinv (by simp only [arm64_norm, wp_norm]; done)
        | exact lscro_of_mem_eq ⟨($hinv).1, ($hinv).2⟩ (by simp only [arm64_norm, wp_norm]; done))
  if !(← tryTacticCatchRuntimeBool (evalTactic haveStx)) then
    throwError "wp_call_spec_lscro: could not establish `LibsignalCodeRoLoaded lsmpl s.mem`"
  if isWPp then
    evalTactic (← `(tactic|
      apply (SepWPp.call_lscro (pl := lsmpl) (spec := $specStx) $hcall $hinvId (x := $arg))))
  else
    evalTactic (← `(tactic|
      apply (SepWP.call_lscro (pl := lsmpl) (spec := $specStx) $hcall $hinvId (x := $arg))))
  inImageKitCloseSetup "wp_call_spec_lscro"
  let gs ← getGoals
  let gPre :: gA :: gB :: gCont :: rest := gs
    | throwError "wp_call_spec_lscro: unexpected subgoals"
  setGoals [gPre]
  lsCroKitClearInvHyps
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR' ⊢
  )))
  inImageKitDestructureSat
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  let preLeft ← getGoals
  let mut side : List MVarId := []
  if isWPp then
    setGoals [gA]
    inImageKitClearByName hinvId.getId
    let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic|
      wp_focus_close (wp_unfold_specs; intro _ _ _ _ _he; exact not_satisfies_false_sepConj _he))))
    side := side ++ (← getGoals)
    setGoals [gB]
    inImageKitClearByName hinvId.getId
    let gB' ← getMainGoal
    gB'.setTag `panic
    side := side ++ [gB']
  else
    setGoals [gA]
    inImageKitClearByName hinvId.getId
    let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic|
      wp_focus_close (wp_unfold_specs; intro _ _ _ _hp; exact not_satisfies_false_sepConj _hp))))
    side := side ++ (← getGoals)
    setGoals [gB]
    inImageKitClearByName hinvId.getId
    let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic|
      wp_focus_close (wp_unfold_specs; intro _ _ _ _ _he; exact not_satisfies_false_sepConj _he))))
    side := side ++ (← getGoals)
  setGoals [gCont]
  inImageKitClearByName hinvId.getId
  evalTactic (← `(tactic|
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hinvSfId:ident))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  if isWPp then inImageKitElimSpatialWPp hspId else wpElimSpatialContext hspId
  let contGoals ← getGoals
  let mut restOpen : List MVarId := []
  for m in rest do
    if ← m.isAssigned then continue
    let ty ← instantiateMVars (← m.getType)
    if ty.consumeMData.isAppOfArity ``autoParam 2 then
      let m' ← m.replaceTargetDefEq (ty.consumeMData.getArg! 0)
      let saved ← saveState
      setGoals [m']
      if ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_close_oom_default))) then
        if (← getGoals).isEmpty then continue
      saved.restore
      restOpen := restOpen ++ [m']
    else
      restOpen := restOpen ++ [m]
  let preOpen ← preLeft.filterM fun m => not <$> m.isAssigned
  let sideOpen ← side.filterM fun m => not <$> m.isAssigned
  setGoals (contGoals ++ preOpen ++ sideOpen ++ restOpen)

syntax (name := wpCallSpecLsCroPkTac) "wp_call_spec_lscro" ppSpace colGt term:max
  ppSpace colGt term:max ppSpace colGt term:max ppSpace colGt term:max : tactic

elab_rules : tactic
  | `(tactic| wp_call_spec_lscro $hcall $spec $hinv $arg) =>
    wpCallSpecLsCro hcall spec hinv arg

/-! ## 2. Placed Callee Cell Wrappers & Outer Bridge -/

theorem bytes_zero_elim_p {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {ptr : BitVec 64} {bs : List (BitVec 8)} {Rest : SepProp}
    {Q : State → SepProp → Prop} {P : SepProp}
    (heq : P = ((ptr ↦ₛ bs) ∗ vecU8BufRest A 0#64 ptr bs) ∗ Rest)
    (h : SepWP prog ret s Rest Q) :
    SepWP prog ret s P Q := by
  rw [heq, bytes_sep_vecU8BufRest_zero]
  exact SepWP.pure_elim fun _ => h

private theorem pkFrame_pack_p (sp : BitVec 64) (s0 : State)
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
      pkSavedRegs sp s0) (Entails.of_eq (by ac_rfl)) ?_
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
  rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf, vecU8Buf_eq_bytes_sep_rest]
  dsimp only [vecHeader]
  ac_rfl

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
    (h : m ⊨ SpqrV1.Alloc.vecU8Buf A cap ptr bs ∗ R) : cap + 1#64 ≠ 0#64 := by
  unfold SpqrV1.Alloc.vecU8Buf at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  have hlt := h.1.2.1
  bv_omega

theorem dealloc_buf_cells_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {A : RustAlloc} {H : LibsignalHooks} [IsLsBlockProg prog i H] {calleeStk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hle : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustDeallocSymCli)
      (StoreKit.withLsCodeRoLoaded lsmpl (deallocBufCellsSpec A calleeStk)) := by
  have hDealloc := dealloc_lscro_of_cli (callerProg := prog) hC hi
  intro ⟨ptr, cap, bs, fsp⟩ R s0 hpc hrun hpre hsp hcl
  rcases StoreKit.extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  simp only [deallocBufCellsSpec, vecU8BufRest, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hfsp, hcap0⟩, hmem⟩
  subst hfsp
  have hmem1 : s0.mem ⊨ ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((ptr ↦ₛ bs) ∗ (if cap = 0 then emp
        else A.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
        A.pool ∗ stackAt s0.sp calleeStk ∗ R) := by
    convert hmem using 1; ac_rfl
  rw [satisfies_pure_sepConj] at hmem1
  rcases hmem1 with ⟨⟨hlen, hlt, _hptr⟩, hmem2⟩
  have hcap0' : cap ≠ 0 := hcap0
  simp only [hcap0', ↓reduceIte] at hmem2
  rw [stackAt_sub_split s0.sp hle hhi] at hmem2
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - extHookStack)
  have hcap_pos : 0 < cap.toNat := by
    have : cap ≠ 0#64 := hcap0
    bv_omega
  have hlay : LayoutOk cap.toNat 1 := ⟨hcap_pos, ⟨0, rfl⟩, by omega⟩
  have hmem_reg : s0.mem ⊨ ((ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
      (A.pool ∗ A.live ptr cap.toNat 1 ∗ stackAt s0.sp extHookStack ∗ stkRem ∗ R) := by
    dsimp only [stkRem]
    convert hmem2 using 1; ac_rfl
  have hmem_reg' : s0.mem ⊨ memRegion ptr cap.toNat ∗
      (A.pool ∗ A.live ptr cap.toNat 1 ∗ stackAt s0.sp extHookStack ∗ stkRem ∗ R) :=
    Satisfies.mono
      (sepConj_mono_left (bytes_sep_memRegion_entails_memRegion_p ptr bs hlen (by omega))) hmem_reg
  have hpre0 : s0.mem ⊨
      (StoreKit.withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack A extHookStack)).pre
        (ptr, cap.toNat, 1) s0 ∗ (stkRem ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, by simp [hx1], by simp [hx2], hlay⟩, ?_⟩
    convert hmem_reg' using 1; ac_rfl
  rcases hDealloc (ptr, cap.toNat, 1) (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨_hpan, hq⟩ | ⟨_code, _hex, hq⟩ | ⟨_hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, rustDeallocExternSpecWithStack,
      deallocBufCellsSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨htr, hq⟩
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · dsimp only [StoreKit.withLsCodeRoLoaded, rustDeallocExternSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [StoreKit.withLsCodeRoLoaded, rustDeallocExternSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [StoreKit.withLsCodeRoLoaded, rustDeallocExternSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem decimal_cells_placed_ok [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {decStk calleeStk : Nat}
    (hDecimal : subroutine_ok prog (lsmpl.base 597) (decimalSpecPlaced A decStk))
    (hFs : TraceFsSound prog)
    (hle : decStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 597)
      (StoreKit.withLsCodeRoLoaded lsmpl (decimalCellsSpec A calleeStk)) := by
  intro ⟨n, ret, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp hcl
  rcases StoreKit.extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  simp only [decimalCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hfsp⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - decStk)
  let callG : DecimalGhost := ⟨n, ret⟩
  have hDecFs := subroutine_ok_withFsInv hFs hDecimal s0.fs.files s0.trace
  have hpre0 : s0.mem ⊨ (withFsInv (decimalSpecPlaced A decStk) s0.fs.files s0.trace).pre
      callG s0 ∗ (stkRem ∗ R) := by
    refine withFsInv_pre_intro (withFsInv_entry s0) ?_
    unfold decimalSpecPlaced
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [callG]
    simp only [memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  rcases hDecFs callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, _hex, hq⟩ | ⟨_hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    obtain ⟨hfs', hq⟩ := withFsInv_post_elim hq
    dsimp only [StoreKit.withLsCodeRoLoaded, decimalSpecPlaced, decimalCellsSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq⟩
    have hfiles : sf.fs.files = s0.fs.files :=
      files_eq_at_callback hfs' (evs := []) (by simp [htr]) NoFsEv.nil
    change sf.mem ⊨ (vecU8 A ret (keyName n) ∗ stackAt s0.sp decStk ∗ A.pool) ∗ (stkRem ∗ R) at hq
    rw [vecU8_eq_words_sep_bytes_rest_p] at hq
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨nCap, nPtr, hq⟩
    refine ⟨nCap, nPtr, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr, hfiles⟩, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    change sf.mem ⊨ (⌜FsInv s0.fs.files s0.trace sf⌝ ∗
      (decimalSpecPlaced A decStk).onPanic callG s0 sf) ∗ (stkRem ∗ R) at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨_, hq⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, decimalSpecPlaced, decimalCellsSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · change sf.mem ⊨ (⌜FsInv s0.fs.files s0.trace sf⌝ ∗
      (decimalSpecPlaced A decStk).onExit callG code s0 sf) ∗ (stkRem ∗ R) at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (allowPanic_not_exited hq.2).elim
  · change sf.mem ⊨ (⌜FsInv s0.fs.files s0.trace sf⌝ ∗
      (decimalSpecPlaced A decStk).onOom callG s0 sf) ∗ (stkRem ∗ R) at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    dsimp only [decimalSpecPlaced, StoreKit.withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq.2).elim

theorem dirGet_cells_placed_ok [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk calleeStk : Nat}
    (hGet : subroutine_ok prog (lsmpl.base 589) (dirGetSpecPlaced rd pathOk A getStk))
    (hle : getStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 589)
      (StoreKit.withLsCodeRoLoaded lsmpl (dirGetCellsSpec rd pathOk A calleeStk)) := by
  intro ⟨ret, self, dir, nameA, name, o0, o1, o2, o3, o4, o5, fsp⟩ R s0 hpc hrun hpre hsp hcl
  rcases StoreKit.extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  simp only [dirGetCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hfsp, hnlen, hplen, hpok⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - getStk)
  let callG : DirGetGhost := ⟨ret, self, dir, nameA, name, false⟩
  have hpre0 : s0.mem ⊨ (dirGetSpecPlaced rd pathOk A getStk).pre callG s0 ∗ (stkRem ∗ R) := by
    unfold dirGetSpecPlaced
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [callG, SpqrV1.ChainProofs.bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte, memRegion_48_cells, sepExists_sepConj_left,
      sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o5, o4, o3, o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hnlen, hplen, hpok⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  rcases hGet callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨_code, _hex, hq⟩ | ⟨_hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, dirGetSpecPlaced, dirGetCellsSpec, callG,
      SpqrV1.ChainProofs.bytesAt] at hq ⊢
    simp only [Bool.false_eq_true, ↓reduceIte, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨r, hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hdisj, hq⟩
    rcases r with ⟨⟩ | bs
    · dsimp only [getResultAt, speAt, strRefAt] at hq
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
        BitVec.add_assoc, BitVec.reduceAdd] at hq
      rcases hq with ⟨w4, ebs, hq⟩
      have hq' : sf.mem ⊨ vecU8 A (ret + 8#64) ebs ∗
          ((ret ↦₆₄ speWord 1) ∗ ((ret + 32#64) ↦₆₄ w4) ∗
            ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
            (w4 ↦ᵣ utf8 "read") ∗ dirAt A self dir ∗ (nameA ↦ₛ name) ∗
            stackAt s0.sp getStk ∗ A.pool ∗ (stkRem ∗ R)) := by
        convert hq using 1; ac_rfl
      dsimp only [vecU8] at hq'
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hq'
      rcases hq' with ⟨w1, w2, hq'⟩
      rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf] at hq'
      dsimp only [vecHeader] at hq'
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq'
      refine ⟨.error (), speWord 1, w1, w2, BitVec.ofNat 64 ebs.length, w4,
        BitVec.ofNat 64 (utf8 "read").length, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hdisj, ?_⟩
      dsimp only [dirGetPayload, readErrHeap]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
      refine ⟨ebs, ?_⟩
      rw [stackAt_sub_split s0.sp hle hhi]
      simp only [eq_self, and_self, pure_true_eq_emp_p trivial, emp_sepConj]
      dsimp only [stkRem] at hq'
      convert hq' using 1; ac_rfl
    · dsimp only [getResultAt, vecResultAt] at hq
      rw [vecU8_eq_words_sep_bytes_rest_p A (ret + 8#64) bs] at hq
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
        BitVec.add_assoc, BitVec.reduceAdd] at hq
      rcases hq with ⟨w1, w2, hq⟩
      rw [memRegion_16_cells (ret + 32#64)] at hq
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
        BitVec.add_assoc, BitVec.reduceAdd] at hq
      rcases hq with ⟨w5, w4, hq⟩
      refine ⟨.ok bs, okTagVec, w1, w2, BitVec.ofNat 64 bs.length, w4, w5, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hdisj, ?_⟩
      dsimp only [dirGetPayload]
      rw [stackAt_sub_split s0.sp hle hhi]
      simp only [eq_self, and_self, pure_true_eq_emp_p trivial, emp_sepConj]
      dsimp only [stkRem] at hq
      convert hq using 1; ac_rfl
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, dirGetSpecPlaced, dirGetCellsSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [dirGetSpecPlaced, StoreKit.withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem pkDec_cells_placed_ok [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {calleeStk : Nat}
    (hDec : subroutine_ok prog (lsmpl.base 65) (preKeyDeserializePlacedSpec A))
    (hle : smallRootStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 65)
      (StoreKit.withLsCodeRoLoaded lsmpl (pkDecCellsSpec A calleeStk)) := by
  intro ⟨bytesA, bytes, ret, o0, o1, o2, o3, o4, o5, o6, fsp⟩ R s0 hpc hrun hpre hsp hcl
  rcases StoreKit.extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  simp only [pkDecCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hblen, hx8, hfsp⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - smallRootStack)
  let callG : DecodeGhost := ⟨bytesA, bytes, ret⟩
  have hpre0 : s0.mem ⊨ (preKeyDeserializePlacedSpec A).pre callG s0 ∗ (stkRem ∗ R) := by
    change s0.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl (preKeyDeserializeRawSpec A)).pre callG s0 ∗
      (stkRem ∗ R)
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [preKeyDeserializeRawSpec, callG]
    simp only [memRegion_56_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o6, o5, o4, o3, o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hblen, hx8⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  rcases hDec callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨_code, _hex, hq⟩ | ⟨_hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, LibsignalTripleRatchet.withLsCodeRoLoaded,
      preKeyDeserializePlacedSpec, preKeyDeserializeRawSpec, pkDecCellsSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
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
      rw [memRegion_40_cells] at hq
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
        BitVec.add_assoc, BitVec.reduceAdd] at hq
      rcases hq with ⟨d6, d5, d4, d3, d2, hq⟩
      refine ⟨errTag, speWord 2, d2, d3, d4, d5, d6, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨htr, ?_⟩
      dsimp only [pkDecPayload]
      rw [stackAt_sub_split s0.sp hle hhi]
      simp only [eq_self, and_self, pure_true_eq_emp_p trivial, emp_sepConj]
      dsimp only [stkRem] at hq
      convert hq using 1; ac_rfl
    · rw [hres] at hq
      dsimp only [preKeyResultAt, preKeyRecordAt] at hq
      have hq1 : sf.mem ⊨
          vecU8 A ret rec.preKey.publicKey ∗
          vecU8 A (ret + 24#64) rec.preKey.privateKey ∗
          (((ret + 48#64) ↦₃₂ rec.preKey.id) ∗ memRegion (ret + 52#64) 4) ∗
          ((bytesA ↦ₛ bytes) ∗ stackAt s0.sp smallRootStack ∗ A.pool ∗ (stkRem ∗ R)) := by
        convert hq using 1; ac_rfl
      have h52 : ret + 48#64 + 4#64 = ret + 52#64 := by bv_omega
      rw [← h52, pointsTo32_memRegion4_eq_p (ret + 48#64) rec.preKey.id] at hq1
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq1
      rcases hq1 with ⟨hi32, hq1⟩
      dsimp only [vecU8] at hq1
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq1
      rcases hq1 with ⟨d3, d4, d0, d1, hq1⟩
      rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf, SpqrV1.Alloc.vecU8At_eq_header_sep_buf] at hq1
      dsimp only [vecHeader] at hq1
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq1
      have hd0_ne : d0 + 1#64 ≠ 0#64 := by
        refine vecU8Buf_cap_add_one_ne_zero_p (m := sf.mem) (A := A) (cap := d0) (ptr := d1)
          (bs := rec.preKey.publicKey)
          (R := (ret ↦₆₄ d0) ∗ ((ret + 8#64) ↦₆₄ d1) ∗
            ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 rec.preKey.publicKey.length) ∗
            ((ret + 24#64) ↦₆₄ d3) ∗ ((ret + 32#64) ↦₆₄ d4) ∗
            ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 rec.preKey.privateKey.length) ∗
            SpqrV1.Alloc.vecU8Buf A d3 d4 rec.preKey.privateKey ∗
            ((ret + 48#64) ↦₆₄ (hi32 ++ rec.preKey.id)) ∗
            (bytesA ↦ₛ bytes) ∗ stackAt s0.sp smallRootStack ∗ A.pool ∗ (stkRem ∗ R)) ?_
        convert hq1 using 1; ac_rfl
      refine ⟨d0, d1, BitVec.ofNat 64 rec.preKey.publicKey.length,
        d3, d4, BitVec.ofNat 64 rec.preKey.privateKey.length, hi32 ++ rec.preKey.id, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨htr, ?_⟩
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
      convert hq1 using 1; ac_rfl
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, LibsignalTripleRatchet.withLsCodeRoLoaded,
      preKeyDeserializePlacedSpec, preKeyDeserializeRawSpec, pkDecCellsSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [preKeyDeserializePlacedSpec, preKeyDeserializeRawSpec,
      LibsignalTripleRatchet.withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem dropSpeWord_cells_placed_ok [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {calleeStk : Nat}
    (hDrop : subroutine_ok prog (lsmpl.base 553) (dropSpeWordSpecPlaced A))
    (hle : dropSpeStackX ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 553)
      (StoreKit.withLsCodeRoLoaded lsmpl (dropSpeWordCellsSpec A calleeStk)) := by
  intro ⟨a, c1, c2, c3, c4, c5, fsp⟩ R s0 hpc hrun hpre hsp hcl
  rcases StoreKit.extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  simp only [dropSpeWordCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hfsp⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - dropSpeStackX)
  let callG : DropSpeWordGhost := ⟨a, 13⟩
  have hpre0 : s0.mem ⊨ (dropSpeWordSpecPlaced A).pre callG s0 ∗ (stkRem ∗ R) := by
    unfold dropSpeWordSpecPlaced
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [callG]
    simp only [memRegion_40_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, BitVec.add_assoc, BitVec.reduceAdd]
    refine ⟨c5, c4, c3, c2, c1, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, Or.inl trivial⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  rcases hDrop callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨_hpan, hq⟩ | ⟨_code, _hex, hq⟩ | ⟨_hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, dropSpeWordSpecPlaced, dropSpeWordCellsSpec,
      callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq⟩
    rw [memRegion_48_cells] at hq
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨m5, m4, m3, m2, m1, m0, hq⟩
    refine ⟨m0, m1, m2, m3, m4, m5, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · dsimp only [StoreKit.withLsCodeRoLoaded, dropSpeWordSpecPlaced] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [StoreKit.withLsCodeRoLoaded, dropSpeWordSpecPlaced] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [StoreKit.withLsCodeRoLoaded, dropSpeWordSpecPlaced] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem pkGetPoll_placed_of_inner [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {A : RustAlloc} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {calleeStk stk : Nat}
    (hInner : calleeStk ≤ 2 ^ 64 →
      subroutine_ok prog entry
        (StoreKit.withLsCodeRoLoaded lsmpl (pkGetPollInnerSpec rd pathOk A calleeStk)))
    (hstk : 256 + calleeStk ≤ stk) :
    subroutine_ok prog entry (pkGetPollSpecPlaced rd pathOk A stk) := by
  intro x R s0 hpc hrun hpre hsp hcl
  unfold pkGetPollSpecPlaced pkGetPollSpecOfPlaced at hpre
  rcases StoreKit.extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  dsimp only [] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hname, hsize⟩, hmem⟩
  dsimp only [pkBoxAt] at hmem
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine memRegion_bound_of_pointsTo64 (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk)
      (a := x.fut) (v := x.self)
      (R := ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 0#8) ∗
        memRegion (x.fut + 13#64) 3 ∗
        dirAt A x.self x.dir ∗ memRegion x.out 56 ∗
        A.pool ∗ R) ?_
    dsimp only [stackAt] at hmem
    convert hmem using 1; ac_rfl
  have hcal_hi : calleeStk ≤ 2 ^ 64 := by omega
  have hframe_hi : calleeStk + 256 ≤ 2 ^ 64 := by omega
  rw [stackAt_sub_split s0.sp (subStk := calleeStk + 256) (by omega) hstk_hi,
    stackAt_pkPoll_frame s0.sp hframe_hi] at hmem
  let F_extra := memRegion (x.fut + 13#64) 3 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 256))
  have hpre_in : s0.mem ⊨
      (StoreKit.withLsCodeRoLoaded lsmpl (pkGetPollInnerSpec rd pathOk A calleeStk)).pre x s0 ∗
      (F_extra ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [pkGetPollInnerSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hname, hsize⟩, ?_⟩
    dsimp only [F_extra]
    convert hmem using 1; ac_rfl
  rcases hInner hcal_hi x (F_extra ∗ R) s0 hpc hrun hpre_in hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨_code, _hex, hq⟩ | ⟨_hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, pkGetPollInnerSpec, pkGetPollSpecPlaced,
      pkGetPollSpecOfPlaced, pkBoxAt] at hq ⊢
    rw [stackAt_sub_split s0.sp (subStk := calleeStk + 256) (by omega) hstk_hi,
      stackAt_pkPoll_frame s0.sp hframe_hi]
    dsimp only [F_extra] at hq
    convert hq using 1; ac_rfl
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, pkGetPollInnerSpec, pkGetPollSpecPlaced,
      pkGetPollSpecOfPlaced] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [StoreKit.withLsCodeRoLoaded, pkGetPollSpecPlaced, pkGetPollSpecOfPlaced] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-! ## 3. Shared Epilogue (`+348` .. `+404` `ret`) on `lsProg_573 H` -/

theorem step_epilogue_348_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {calleeStk : Nat} {x : PkPollGhost} {s0 s : State} {P : SepProp}
    (ans : PkAns PreKeyRecord)
    (o0 o1 o2 o3 o4 o5 o6 u2 u3 u4 u5 n0 n1 n2 k0 k1 g0 g1 g2 g3 g4 g5 g6 : BitVec 64)
    (payload : SepProp)
    (hpc : s.pc = (blkPl_573).base + bv% (348))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 256#64)
    (hal0 : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx26 : s.readReg64 .x26 = o0)
    (hx25 : s.readReg64 .x25 = o1)
    (hx23 : s.readReg64 .x23 = o2)
    (hx24 : s.readReg64 .x24 = o3)
    (hx21 : s.readReg64 .x21 = o4)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hAns :
      ans = pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
        s.trace = s0.trace)
    (hReasm :
      ((x.out ↦₆₄ o0) ∗ ((x.out + 8#64) ↦₆₄ o1) ∗
        ((x.out + 16#64) ↦₆₄ o2) ∗ ((x.out + 24#64) ↦₆₄ o3) ∗
        ((x.out + 32#64) ↦₆₄ o4) ∗ ((x.out + 40#64) ↦₆₄ o5) ∗
        ((x.out + 48#64) ↦₆₄ o6)) ∗ payload ⊢
      pkGetAnsAt A x.out ans)
    (hP : P ⊢
      pkBoxKeep x s0 ∗ payload ∗ dirAt A x.self x.dir ∗ A.pool ∗
        stackAt (s0.sp - 256#64) calleeStk ∗
        ((s0.sp - 256#64) ↦₆₄ o5) ∗ ((s0.sp - 248#64) ↦₆₄ o6) ∗
        ((s0.sp - 240#64) ↦₆₄ u2) ∗ ((s0.sp - 232#64) ↦₆₄ u3) ∗
        ((s0.sp - 224#64) ↦₆₄ u4) ∗ ((s0.sp - 216#64) ↦₆₄ u5) ∗
        ((s0.sp - 200#64) ↦₆₄ n0) ∗ ((s0.sp - 192#64) ↦₆₄ n1) ∗ ((s0.sp - 184#64) ↦₆₄ n2) ∗
        ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
        ((s0.sp - 152#64) ↦₆₄ g0) ∗ ((s0.sp - 144#64) ↦₆₄ g1) ∗
        ((s0.sp - 136#64) ↦₆₄ g2) ∗ ((s0.sp - 128#64) ↦₆₄ g3) ∗
        ((s0.sp - 120#64) ↦₆₄ g4) ∗ ((s0.sp - 112#64) ↦₆₄ g5) ∗ ((s0.sp - 104#64) ↦₆₄ g6)) :
    SepWP (lsProg_573 H) (s0.readReg64 Reg.lr) s P
      (pkEpiloguePost rd pathOk A calleeStk x s0) := by
  refine SepWP.weaken_pre hP ?_
  have hal : s.spAligned = true := sp_sub_256_spAligned hal0 hsp
  unfold pkBoxKeep
  rw [memRegion_56_cells x.out]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => ?_
  unfold pkSavedRegs
  wp_steps
  apply bind_sepWP_state; intro sf
  apply SepWP.done (by simp only [sf, wp_norm, arm64_norm, *])
    (by simp only [sf, wp_norm, arm64_norm, *])
  refine ⟨by simp only [sf, wp_norm, arm64_norm, *], ?_, ?_⟩
  · refine ⟨by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *]⟩
  · have htr_sf : sf.trace = s.trace := by simp only [sf, wp_norm, arm64_norm]
    have hAns' :
        ans = pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
          sf.trace = s0.trace :=
      ⟨hAns.1, htr_sf.trans hAns.2⟩
    dsimp only [pkGetPollInnerSpec]
    have hpack := pkFrame_pack_p s0.sp s0 o5 o6 u2 u3 u4 u5 n0 n1 n2 k0 k1 g0 g1 g2 g3 g4 g5 g6
    refine Entails.trans (Q :=
      (((x.out ↦₆₄ o0) ∗ ((x.out + 8#64) ↦₆₄ o1) ∗
          ((x.out + 16#64) ↦₆₄ o2) ∗ ((x.out + 24#64) ↦₆₄ o3) ∗
          ((x.out + 32#64) ↦₆₄ o4) ∗ ((x.out + 40#64) ↦₆₄ o5) ∗
          ((x.out + 48#64) ↦₆₄ o6)) ∗ payload) ∗
      (pkPollSlack s0.sp ∗ pkSavedRegs s0.sp s0 ∗
        ((s0.sp - 256#64) ↦₆₄ o5) ∗ ((s0.sp - 248#64) ↦₆₄ o6) ∗
        ((s0.sp - 240#64) ↦₆₄ u2) ∗ ((s0.sp - 232#64) ↦₆₄ u3) ∗
        ((s0.sp - 224#64) ↦₆₄ u4) ∗ ((s0.sp - 216#64) ↦₆₄ u5) ∗
        ((s0.sp - 200#64) ↦₆₄ n0) ∗ ((s0.sp - 192#64) ↦₆₄ n1) ∗ ((s0.sp - 184#64) ↦₆₄ n2) ∗
        ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
        ((s0.sp - 152#64) ↦₆₄ g0) ∗ ((s0.sp - 144#64) ↦₆₄ g1) ∗
        ((s0.sp - 136#64) ↦₆₄ g2) ∗ ((s0.sp - 128#64) ↦₆₄ g3) ∗
        ((s0.sp - 120#64) ↦₆₄ g4) ∗ ((s0.sp - 112#64) ↦₆₄ g5) ∗ ((s0.sp - 104#64) ↦₆₄ g6)) ∗
      ((x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 1#8) ∗
        dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk)) ?_ ?_
    · unfold pkSavedRegs
      exact Entails.of_eq (by ac_rfl)
    · refine Entails.trans (sepConj_mono hReasm (sepConj_mono_left hpack)) ?_
      refine Entails.trans (Q :=
        pkGetAnsAt A x.out ans ∗
          ((x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 1#8) ∗
            dirAt A x.self x.dir ∗ A.pool ∗
            stackAt (s0.sp - 256#64) calleeStk ∗ cells (s0.sp - 256#64) 32))
        (Entails.of_eq (by ac_rfl)) ?_
      exact sepConj_mono_left (Entails.sepExists_right ans (Entails.pure_right hAns' (Entails.refl _)))

/-! ## 4. Branch 1 (`Dir::get` returned `Err`, `+200` .. `+232` -> `+348`) -/

theorem step_err_200_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {calleeStk : Nat} {x : PkPollGhost} {s0 s : State} {P : SepProp}
    (hDeallocCells : subroutine_ok (lsProg_573 H) (lsρ lsRustDeallocSymCli)
      (StoreKit.withLsCodeRoLoaded lsmpl (deallocBufCellsSpec A calleeStk)))
    (w1 w2 w3 w4 w5 nCap nPtr nLen u0 u1 u2 u3 u4 u5 k0 k1 g6 : BitVec 64)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_573).base + bv% (200))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 256#64)
    (hal0 : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx21 : s.readReg64 .x21 = w3)
    (hx22 : s.readReg64 .x22 = nPtr)
    (hx23 : s.readReg64 .x23 = w1)
    (hx24 : s.readReg64 .x24 = w2)
    (hx25 : s.readReg64 .x25 = speWord 1)
    (hx27 : s.readReg64 .x27 = s0.sp - 152#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hAns :
      (PkAns.readErr : PkAns PreKeyRecord) =
          pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
        s.trace = s0.trace)
    (hP : P ⊢
      pkBoxKeep x s0 ∗ readErrHeap A w1 w2 w3 w4 w5 ∗
        (nPtr ↦ₛ keyName x.id) ∗ vecU8BufRest A nCap nPtr (keyName x.id) ∗
        dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
        ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
        ((s0.sp - 240#64) ↦₆₄ u2) ∗ ((s0.sp - 232#64) ↦₆₄ u3) ∗
        ((s0.sp - 224#64) ↦₆₄ u4) ∗ ((s0.sp - 216#64) ↦₆₄ u5) ∗
        ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
        ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
        ((s0.sp - 152#64) ↦₆₄ speWord 1) ∗ ((s0.sp - 144#64) ↦₆₄ w1) ∗
        ((s0.sp - 136#64) ↦₆₄ w2) ∗ ((s0.sp - 128#64) ↦₆₄ w3) ∗
        ((s0.sp - 120#64) ↦₆₄ w4) ∗ ((s0.sp - 112#64) ↦₆₄ w5) ∗ ((s0.sp - 104#64) ↦₆₄ g6)) :
    SepWP (lsProg_573 H) (s0.readReg64 Reg.lr) s P
      (pkEpiloguePost rd pathOk A calleeStk x s0) := by
  refine SepWP.weaken_pre hP ?_; clear hP
  have hal : s.spAligned = true := sp_sub_256_spAligned hal0 hsp
  by_cases hnCap : nCap = 0#64
  · subst hnCap
    refine bytes_zero_elim_p (ptr := nPtr) (bs := keyName x.id)
      (Rest := pkBoxKeep x s0 ∗ readErrHeap A w1 w2 w3 w4 w5 ∗
        dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
        ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
        ((s0.sp - 240#64) ↦₆₄ u2) ∗ ((s0.sp - 232#64) ↦₆₄ u3) ∗
        ((s0.sp - 224#64) ↦₆₄ u4) ∗ ((s0.sp - 216#64) ↦₆₄ u5) ∗
        ((s0.sp - 200#64) ↦₆₄ 0#64) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
        ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
        ((s0.sp - 152#64) ↦₆₄ speWord 1) ∗ ((s0.sp - 144#64) ↦₆₄ w1) ∗
        ((s0.sp - 136#64) ↦₆₄ w2) ∗ ((s0.sp - 128#64) ↦₆₄ w3) ∗
        ((s0.sp - 120#64) ↦₆₄ w4) ∗ ((s0.sp - 112#64) ↦₆₄ w5) ∗ ((s0.sp - 104#64) ↦₆₄ g6))
      (by ac_rfl) ?_
    apply StoreKit.sepWP_seq_lscro (mid := (blkPl_573).base + bv% (348)) hcrl
    wp_steps
    try
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
    intro _hcrl_ep
    apply bind_sepWP_state; intro s_ep
    have htr_ep : s_ep.trace = s.trace := by simp only [s_ep, wp_norm, arm64_norm]
    have hpc_ep : s_ep.pc = (blkPl_573).base + bv% (348) := by
      simp only [s_ep, wp_norm, arm64_norm, *]; try bv_omega
    exact step_epilogue_348_placed .readErr errTag (speWord 1) w1 w2 w3 w4 w5
      u2 u3 u4 u5 0#64 nPtr nLen k0 k1 (speWord 1) w1 w2 w3 w4 w5 g6
      (readErrHeap A w1 w2 w3 w4 w5)
      hpc_ep
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      hal0
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *]; rfl)
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      ⟨hAns.1, htr_ep.trans hAns.2⟩
      (readErr_reassemble A x.out w1 w2 w3 w4 w5)
      (Entails.of_eq (by ac_rfl))
  · have hnCap_eq : (nCap == 0#64) = false := beq_eq_false_iff_ne.mpr hnCap
    have hnCap_ne : (nCap != 0#64) = true := bne_iff_ne.mpr hnCap
    apply StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
    wp_steps
    try
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
    intro hcrl1
    wp_call_spec_lscro hDeallocCells (deallocBufCellsSpec A calleeStk) hcrl1
      (nPtr, nCap, keyName x.id, s0.sp - 256#64)
    apply StoreKit.sepWP_seq_lscro (mid := (blkPl_573).base + bv% (348)) hcrl_sf
    wp_steps
    try
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
    intro _hcrl_ep
    apply bind_sepWP_state; intro s_ep
    have htr_ep : s_ep.trace = s.trace := by simp only [s_ep, wp_norm, arm64_norm, *]
    have hpc_ep : s_ep.pc = (blkPl_573).base + bv% (348) := by
      simp only [s_ep, wp_norm, arm64_norm, *]; try bv_omega
    exact step_epilogue_348_placed .readErr errTag (speWord 1) w1 w2 w3 w4 w5
      u2 u3 u4 u5 nCap nPtr nLen k0 k1 (speWord 1) w1 w2 w3 w4 w5 g6
      (readErrHeap A w1 w2 w3 w4 w5)
      hpc_ep
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      hal0
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *]; rfl)
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      ⟨hAns.1, htr_ep.trans hAns.2⟩
      (readErr_reassemble A x.out w1 w2 w3 w4 w5)
      (Entails.of_eq (by ac_rfl))

/-! ## 5. Branch 2 (`PreKeyRecord::deserialize` returned `Err`, `+152` .. `+232` -> `+348`) -/

theorem step_dec_err_152_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {calleeStk : Nat} {x : PkPollGhost} {s0 s : State} {P : SepProp}
    (hDeallocCells : subroutine_ok (lsProg_573 H) (lsρ lsRustDeallocSymCli)
      (StoreKit.withLsCodeRoLoaded lsmpl (deallocBufCellsSpec A calleeStk)))
    (e : SignalProtocolError) (bytes : List (BitVec 8))
    (w1 w2 nCap nPtr nLen d0 d1 d2 d3 d4 d5 d6 u0 u1 u2 u3 k0 k1 : BitVec 64)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_573).base + bv% (152))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 256#64)
    (hal0 : s0.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx21 : s.readReg64 .x21 = d4)
    (hx22 : s.readReg64 .x22 = nPtr)
    (hx23 : s.readReg64 .x23 = w1)
    (hx24 : s.readReg64 .x24 = w2)
    (hx25 : s.readReg64 .x25 = d1)
    (hx27 : s.readReg64 .x27 = d3)
    (hx28 : s.readReg64 .x28 = d2)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hd0_tag : d0 = errTag)
    (hAns : PkAns.decodeErr e =
      pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)))
    (hP : P ⊢
      pkBoxKeep x s0 ∗ pkDecPayload A (.error e) d0 d1 d2 d3 d4 d5 d6 ∗
        (w2 ↦ₛ bytes) ∗ vecU8BufRest A w1 w2 bytes ∗
        (nPtr ↦ₛ keyName x.id) ∗ vecU8BufRest A nCap nPtr (keyName x.id) ∗
        dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
        ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
        ((s0.sp - 240#64) ↦₆₄ u2) ∗ ((s0.sp - 232#64) ↦₆₄ u3) ∗
        ((s0.sp - 224#64) ↦₆₄ d5) ∗ ((s0.sp - 216#64) ↦₆₄ d6) ∗
        ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
        ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
        ((s0.sp - 152#64) ↦₆₄ d0) ∗ ((s0.sp - 144#64) ↦₆₄ d1) ∗
        ((s0.sp - 136#64) ↦₆₄ d2) ∗ ((s0.sp - 128#64) ↦₆₄ d3) ∗
        ((s0.sp - 120#64) ↦₆₄ d4) ∗ ((s0.sp - 112#64) ↦₆₄ d5) ∗ ((s0.sp - 104#64) ↦₆₄ d6)) :
    SepWP (lsProg_573 H) (s0.readReg64 Reg.lr) s P
      (pkEpiloguePost rd pathOk A calleeStk x s0) := by
  refine SepWP.weaken_pre hP ?_; clear hP
  have hal : s.spAligned = true := sp_sub_256_spAligned hal0 hsp
  suffices hjoin180 : ∀ (s1 : State) (P1 : SepProp),
      StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.pc = (blkPl_573).base + bv% (180) →
      s1.status = .Running →
      s1.sp = s0.sp - 256#64 →
      s1.trace = s0.trace →
      s1.readReg64 .x19 = x.fut →
      s1.readReg64 .x20 = x.out →
      s1.readReg64 .x21 = d4 →
      s1.readReg64 .x22 = nPtr →
      s1.readReg64 .x25 = d1 →
      s1.readReg64 .x27 = d3 →
      s1.readReg64 .x28 = d2 →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      (P1 ⊢ pkBoxKeep x s0 ∗ pkDecPayload A (.error e) d0 d1 d2 d3 d4 d5 d6 ∗
        (nPtr ↦ₛ keyName x.id) ∗ vecU8BufRest A nCap nPtr (keyName x.id) ∗
        dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
        ((s0.sp - 256#64) ↦₆₄ d5) ∗ ((s0.sp - 248#64) ↦₆₄ d6) ∗
        ((s0.sp - 240#64) ↦₆₄ d5) ∗ ((s0.sp - 232#64) ↦₆₄ d6) ∗
        ((s0.sp - 224#64) ↦₆₄ d5) ∗ ((s0.sp - 216#64) ↦₆₄ d6) ∗
        ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
        ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
        ((s0.sp - 152#64) ↦₆₄ d0) ∗ ((s0.sp - 144#64) ↦₆₄ d1) ∗
        ((s0.sp - 136#64) ↦₆₄ d2) ∗ ((s0.sp - 128#64) ↦₆₄ d3) ∗
        ((s0.sp - 120#64) ↦₆₄ d4) ∗ ((s0.sp - 112#64) ↦₆₄ d5) ∗ ((s0.sp - 104#64) ↦₆₄ d6)) →
      SepWP (lsProg_573 H) (s0.readReg64 Reg.lr) s1 P1
        (pkEpiloguePost rd pathOk A calleeStk x s0) by
    by_cases hw1 : w1 = 0#64
    · subst hw1
      refine bytes_zero_elim_p (ptr := w2) (bs := bytes)
        (Rest := pkBoxKeep x s0 ∗ pkDecPayload A (.error e) d0 d1 d2 d3 d4 d5 d6 ∗
          (nPtr ↦ₛ keyName x.id) ∗ vecU8BufRest A nCap nPtr (keyName x.id) ∗
          dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
          ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
          ((s0.sp - 240#64) ↦₆₄ u2) ∗ ((s0.sp - 232#64) ↦₆₄ u3) ∗
          ((s0.sp - 224#64) ↦₆₄ d5) ∗ ((s0.sp - 216#64) ↦₆₄ d6) ∗
          ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
          ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
          ((s0.sp - 152#64) ↦₆₄ d0) ∗ ((s0.sp - 144#64) ↦₆₄ d1) ∗
          ((s0.sp - 136#64) ↦₆₄ d2) ∗ ((s0.sp - 128#64) ↦₆₄ d3) ∗
          ((s0.sp - 120#64) ↦₆₄ d4) ∗ ((s0.sp - 112#64) ↦₆₄ d5) ∗ ((s0.sp - 104#64) ↦₆₄ d6))
        (by ac_rfl) ?_
      apply StoreKit.sepWP_seq_lscro (mid := (blkPl_573).base + bv% (180)) hcrl
      wp_steps
      try
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *])
      intro hcrl1
      apply bind_sepWP_state; intro s1
      exact hjoin180 s1 _ hcrl1
        (by simp only [s1, wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (Entails.of_eq (by ac_rfl))
    · have hw1_eq : (w1 == 0#64) = false := beq_eq_false_iff_ne.mpr hw1
      have hw1_ne : (w1 != 0#64) = true := bne_iff_ne.mpr hw1
      apply StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
      wp_steps
      try
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *])
      intro hcrl1
      wp_call_spec_lscro hDeallocCells (deallocBufCellsSpec A calleeStk) hcrl1
        (w2, w1, bytes, s0.sp - 256#64)
      exact hjoin180 sf _ hcrl_sf
        (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (Entails.of_eq (by ac_rfl))
  clear hcrl hpc hrun hsp hal htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx28 hvregs s
  intro s1 P1 hcrl1 hpc1 hrun1 hsp1 htr1 h19_1 h20_1 h21_1 h22_1 h25_1 h27_1 h28_1 hv1 hP1
  refine SepWP.weaken_pre hP1 ?_; clear hP1
  have hal1 : s1.spAligned = true := sp_sub_256_spAligned hal0 hsp1
  by_cases hnCap : nCap = 0#64
  · subst hnCap
    refine bytes_zero_elim_p (ptr := nPtr) (bs := keyName x.id)
      (Rest := pkBoxKeep x s0 ∗ pkDecPayload A (.error e) d0 d1 d2 d3 d4 d5 d6 ∗
        dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 256#64) calleeStk ∗
        ((s0.sp - 256#64) ↦₆₄ d5) ∗ ((s0.sp - 248#64) ↦₆₄ d6) ∗
        ((s0.sp - 240#64) ↦₆₄ d5) ∗ ((s0.sp - 232#64) ↦₆₄ d6) ∗
        ((s0.sp - 224#64) ↦₆₄ d5) ∗ ((s0.sp - 216#64) ↦₆₄ d6) ∗
        ((s0.sp - 200#64) ↦₆₄ 0#64) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
        ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
        ((s0.sp - 152#64) ↦₆₄ d0) ∗ ((s0.sp - 144#64) ↦₆₄ d1) ∗
        ((s0.sp - 136#64) ↦₆₄ d2) ∗ ((s0.sp - 128#64) ↦₆₄ d3) ∗
        ((s0.sp - 120#64) ↦₆₄ d4) ∗ ((s0.sp - 112#64) ↦₆₄ d5) ∗ ((s0.sp - 104#64) ↦₆₄ d6))
      (by ac_rfl) ?_
    apply StoreKit.sepWP_seq_lscro (mid := (blkPl_573).base + bv% (348)) hcrl1
    wp_steps
    try
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
    intro _hcrl_ep
    apply bind_sepWP_state; intro s_ep
    have hpc_ep : s_ep.pc = (blkPl_573).base + bv% (348) := by
      simp only [s_ep, wp_norm, arm64_norm, *]; try bv_omega
    have hx26_ep : s_ep.readReg64 .x26 = d0 := by
      rw [hd0_tag]; simp only [s_ep, wp_norm, arm64_norm, *]; rfl
    exact step_epilogue_348_placed (.decodeErr e) d0 d1 d2 d3 d4 d5 d6
      d5 d6 d5 d6 0#64 nPtr nLen k0 k1 d0 d1 d2 d3 d4 d5 d6
      (pkDecPayload A (.error e) d0 d1 d2 d3 d4 d5 d6)
      hpc_ep
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      hal0
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      hx26_ep
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      ⟨hAns, by simp only [s_ep, wp_norm, arm64_norm, *]⟩
      (decodeErr_reassemble A x.out e d0 d1 d2 d3 d4 d5 d6)
      (Entails.of_eq (by ac_rfl))
  · have hnCap_eq : (nCap == 0#64) = false := beq_eq_false_iff_ne.mpr hnCap
    have hnCap_ne : (nCap != 0#64) = true := bne_iff_ne.mpr hnCap
    apply StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl1
    wp_steps
    try
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hcrl2
    wp_call_spec_lscro hDeallocCells (deallocBufCellsSpec A calleeStk) hcrl2
      (nPtr, nCap, keyName x.id, s0.sp - 256#64)
    apply StoreKit.sepWP_seq_lscro (mid := (blkPl_573).base + bv% (348)) hcrl_sf
    wp_steps
    try
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
    intro _hcrl_ep
    apply bind_sepWP_state; intro s_ep
    have hpc_ep : s_ep.pc = (blkPl_573).base + bv% (348) := by
      simp only [s_ep, wp_norm, arm64_norm, *]; try bv_omega
    have hx26_ep : s_ep.readReg64 .x26 = d0 := by
      rw [hd0_tag]; simp only [s_ep, wp_norm, arm64_norm, *]; rfl
    exact step_epilogue_348_placed (.decodeErr e) d0 d1 d2 d3 d4 d5 d6
      d5 d6 d5 d6 nCap nPtr nLen k0 k1 d0 d1 d2 d3 d4 d5 d6
      (pkDecPayload A (.error e) d0 d1 d2 d3 d4 d5 d6)
      hpc_ep
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      hal0
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      hx26_ep
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      ⟨hAns, by simp only [s_ep, wp_norm, arm64_norm, *]⟩
      (decodeErr_reassemble A x.out e d0 d1 d2 d3 d4 d5 d6)
      (Entails.of_eq (by ac_rfl))

end Placed

end CryptoVerification.SignalSession.Cli.Store.PkGetPoll.Helpers
