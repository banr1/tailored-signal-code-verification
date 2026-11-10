/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll
public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymB
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyDecode
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEq
public meta import ProofLib
public meta import LibsignalBinary.Proofs.Common.InImageKit
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public meta import Lean
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.RecordCodecs.RoundTrip
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import all Init.Data.String.Defs

/-!
# Relocatable Symbolic Execution of `is_trusted_identity::{closure#0}`

Proves `cliIdTrustPollInnerSpecPlaced` and outer `idTrustPoll_placed_of_inner` on Block `566`
under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.IdTrustPoll.Helpers

open Arm64 Arm64.Obj ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoGames.LibsignalSessionApi CryptoVerification.RecordCodecs
open CryptoVerification.LibsignalSession CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon

section Placed

attribute [local irreducible] Program.fetch Program.externAt?
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
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  CliIdTrustPollNorm.sp_setPC_pre
  CliIdTrustPollNorm.sp_setMem_setPC_pre
  CliIdTrustPollNorm.sp_writeVReg128_pre
  CliIdTrustPollNorm.fs_setPC_pre
  CliIdTrustPollNorm.fs_setMem_pre
  CliIdTrustPollNorm.fs_setPState_pre
  CliIdTrustPollNorm.fs_writeReg64_pre
  CliIdTrustPollNorm.fs_writeReg32_pre
  CliIdTrustPollNorm.fs_writeReg_pre
  CliIdTrustPollNorm.fs_writeVReg128_pre
  CliIdTrustPollNorm.trace_writeVReg128_pre
  CliIdTrustPollNorm.readReg64_setPC_pre
  CliIdTrustPollNorm.readReg64_setMem_setPC_pre
  CliIdTrustPollNorm.readReg64_writeVReg128_pre
  CliIdTrustPollNorm.readReg32_setPC_pre
  CliIdTrustPollNorm.readReg32_setMem_setPC_pre
  CliIdTrustPollNorm.readReg32_writeVReg128_pre
  CliIdTrustPollNorm.readReg_setPC_pre
  CliIdTrustPollNorm.readReg_setMem_setPC_pre
  CliIdTrustPollNorm.readReg_writeVReg128_pre
  CliIdTrustPollNorm.readVReg128_setPC_pre
  CliIdTrustPollNorm.readVReg128_setMem_setPC_pre
  CliIdTrustPollNorm.readVReg128_setMem_pre
  CliIdTrustPollNorm.readVReg128_setPState_pre
  CliIdTrustPollNorm.readVReg128_writeReg64_pre
  CliIdTrustPollNorm.readVReg128_writeReg32_pre
  CliIdTrustPollNorm.readVReg128_writeReg_pre
  CliIdTrustPollNorm.extractLsb_append_lo
  CliIdTrustPollNorm.extractLsb_append_hi
  CliIdTrustPollNorm.extractLsb_pack32_0
  CliIdTrustPollNorm.extractLsb_pack32_8
  CliIdTrustPollNorm.extractLsb_pack32_16
  CliIdTrustPollNorm.extractLsb_pack32_24
  CliIdTrustPollNorm.extractLsb_pack32_0_16
  CliIdTrustPollNorm.extractLsb_pack32_16_16
  CliIdTrustPollNorm.speWord_one_eq
  CliIdTrustPollNorm.okTagVec_eq_neg2
  CliIdTrustPollNorm.trace_writeReg32_pre
  CliIdTrustPollNorm.trace_writeReg_pre

/-! ## 1. Placed Callee Cell Wrappers -/

open Lean Elab Tactic Meta in
meta def wpCallSpecLsCro (hcall specStx hinv arg : Term) : TacticM Unit := do
  let g0 ← getMainGoal
  let gty := (← g0.withContext do instantiateMVars (← g0.getType)).consumeMData
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
  evalTactic (← `(tactic|
    apply (SepWPp.call_lscro (pl := lsmpl) (spec := $specStx) $hcall $hinvId (x := $arg))))
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
  setGoals [gA]
  inImageKitClearByName hinvId.getId
  let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic|
    wp_focus_close (wp_unfold_specs; intro _ _ _ _ _he; exact not_satisfies_false_sepConj _he))))
  let mut side : List MVarId := (← getGoals)
  setGoals [gB]
  inImageKitClearByName hinvId.getId
  let gB' ← getMainGoal
  gB'.setTag `panic
  side := side ++ [gB']
  setGoals [gCont]
  inImageKitClearByName hinvId.getId
  evalTactic (← `(tactic|
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hinvSfId:ident))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  inImageKitElimSpatialWPp hspId
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

syntax (name := wpCallSpecLsCroTac) "wp_call_spec_lscro" ppSpace colGt term:max
  ppSpace colGt term:max ppSpace colGt term:max ppSpace colGt term:max : tactic

elab_rules : tactic
  | `(tactic| wp_call_spec_lscro $hcall $spec $hinv $arg) =>
    wpCallSpecLsCro hcall spec hinv arg

theorem dirGet_cells_placed_ok [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk calleeStk : Nat}
    (hGet : subroutine_ok prog (lsmpl.base 589) (dirGetSpecPlaced rd pathOk A getStk))
    (hle : getStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 589)
      (StoreKit.withLsCodeRoLoaded lsmpl (dirGetCellsSpec rd pathOk A calleeStk)) := by
  intro ⟨ret, self, dir, nameA, name, fsp⟩ R s0 hpc hrun hpre hsp hcl
  rcases StoreKit.extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  simp only [dirGetCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hfsp, hnl, hpl, hpok⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - getStk)
  let callG : DirGetGhost := ⟨ret, self, dir, nameA, name, false⟩
  have hpre0 : s0.mem ⊨ (dirGetSpecPlaced rd pathOk A getStk).pre callG s0 ∗ (stkRem ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [ callG]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hnl, hpl, hpok⟩, ?_⟩
    have hif : (if false = true then (nameA ↦ᵣ name) else (nameA ↦ₛ name)) = (nameA ↦ₛ name) := rfl
    dsimp only [SpqrV1.ChainProofs.bytesAt, stkRem]
    rw [hif]
    convert hmem using 1; ac_rfl
  rcases hGet callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, _hex, hq⟩ | ⟨_hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    have hif : (if false = true then (nameA ↦ᵣ name) else (nameA ↦ₛ name)) = (nameA ↦ₛ name) := rfl
    dsimp only [StoreKit.withLsCodeRoLoaded, dirGetSpecPlaced, dirGetCellsSpec,
      SpqrV1.ChainProofs.bytesAt, callG] at hq ⊢
    rw [hif] at hq
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, dirGetSpecPlaced, dirGetCellsSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [dirGetSpecPlaced, StoreKit.withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

def ikDecodeCellsSpecPlaced [LibsignalPlacement] (calleeStk : Nat) :
    Spec IkDecodeCellsGhost where
  pre := fun (bytesA, bytes, ret, ik, fsp) s =>
    ⌜s.readReg64 .x0 = bytesA ∧ (s.readReg64 .x1).toNat = bytes.length ∧
      s.readReg64 .x8 = ret ∧ s.sp = fsp ∧ decodeIdentityKey bytes = .ok ik⌝ ∗
      (bytesA ↦ₛ bytes) ∗ memRegion ret 48 ∗ FromRecordCallees.lsLogOff ∗ stackAt fsp calleeStk
  post := fun (bytesA, bytes, ret, ik, fsp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (ret ↦₆₄ okTagVec) ∗ ((ret + 8#64) ↦ₛ ik.publicKey.bytes.toList) ∗
      memRegion (ret + 40#64) 8 ∗
      (bytesA ↦ₛ bytes) ∗ FromRecordCallees.lsLogOff ∗ stackAt fsp calleeStk
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem ikDecode_cells_placed_ok [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {calleeStk : Nat}
    (hDec : subroutine_ok prog (lsmpl.base 18)
      (StoreKit.withLsCodeRoLoaded lsmpl (RecordCodecsBinary.identityKeyDecodeRawSpec A)))
    (hle : 0x60 ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 18)
      (StoreKit.withLsCodeRoLoaded lsmpl (ikDecodeCellsSpecPlaced calleeStk)) := by
  intro ⟨bytesA, bytes, ret, ik, fsp⟩ R s0 hpc hrun hpre hsp hcl
  rcases StoreKit.extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  simp only [ikDecodeCellsSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hfsp, hdec⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - 0x60)
  let callG : RecordCodecsBinary.DecodeGhost := ⟨bytesA, bytes, ret⟩
  have hlog : FromRecordCallees.lsLogOff = lsLogOff := rfl
  have hpre0 : s0.mem ⊨
      (StoreKit.withLsCodeRoLoaded lsmpl (RecordCodecsBinary.identityKeyDecodeRawSpec A)).pre
        callG s0 ∗ (stkRem ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [RecordCodecsBinary.identityKeyDecodeRawSpec, callG]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx8⟩, ?_⟩
    rw [hlog] at hmem
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  rcases hDec callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨_hpan, hq⟩ | ⟨_code, _hex, hq⟩ | ⟨_hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, RecordCodecsBinary.identityKeyDecodeRawSpec,
      ikDecodeCellsSpecPlaced, callG] at hq ⊢
    rw [hdec, ← hlog] at hq
    dsimp only [RecordCodecsBinary.identityKeyResultAt] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨htr, hq⟩
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · dsimp only [StoreKit.withLsCodeRoLoaded, RecordCodecsBinary.identityKeyDecodeRawSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [RecordCodecsBinary.identityKeyDecodeRawSpec, StoreKit.withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem deallocVecBuf_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {A : RustAlloc} {H : LibsignalHooks} [IsLsBlockProg prog i H] {calleeStk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hle : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustDeallocSymCli)
      (StoreKit.withLsCodeRoLoaded lsmpl (deallocVecBufSpec A calleeStk)) := by
  have hDealloc := dealloc_lscro_of_cli (callerProg := prog) hC hi
  intro ⟨bPtr, bCap, bs, fsp⟩ R s0 hpc hrun hpre hsp hcl
  rcases StoreKit.extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  simp only [deallocVecBufSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hfsp, hlen, hlt, hnz⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  dsimp only [vecU8BufRest] at hmem
  simp only [hnz, ↓reduceIte] at hmem
  have hreg : (bPtr ↦ₛ bs) ∗ memRegion (bPtr + BitVec.ofNat 64 bs.length) (bCap.toNat - bs.length) ⊢
      memRegion bPtr bCap.toNat := by
    have hsplit : memRegion bPtr bCap.toNat =
        memRegion bPtr bs.length ∗
        memRegion (bPtr + BitVec.ofNat 64 bs.length) (bCap.toNat - bs.length) := by
      have heq : bCap.toNat = bs.length + (bCap.toNat - bs.length) := by omega
      conv_lhs => rw [heq]
      rw [memRegion_split bPtr bs.length (bCap.toNat - bs.length) (by omega)]
    rw [hsplit]
    exact sepConj_mono_left (IsBlock.entails_memRegion (IsBlock.pointsToBytes bPtr bs))
  have hlay : LayoutOk bCap.toNat 1 := ⟨by bv_omega, ⟨0, rfl⟩, by omega⟩
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - extHookStack)
  have hmem_reg : s0.mem ⊨
      memRegion bPtr bCap.toNat ∗
      (A.live bPtr bCap.toNat 1 ∗ A.pool ∗ stackAt s0.sp extHookStack ∗ stkRem ∗ R) := by
    refine Satisfies.mono (sepConj_mono_left hreg) ?_
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  have hpre0 : s0.mem ⊨
      (StoreKit.withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack A extHookStack)).pre
        (bPtr, bCap.toNat, 1) s0 ∗ (stkRem ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, by rw [hx1], by rw [hx2]; rfl, hlay⟩, ?_⟩
    convert hmem_reg using 1; ac_rfl
  rcases hDealloc (bPtr, bCap.toNat, 1) (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨_hpan, hq⟩ | ⟨_code, _hex, hq⟩ | ⟨_hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, rustDeallocExternSpecWithStack,
      deallocVecBufSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨htr, hq⟩
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · dsimp only [StoreKit.withLsCodeRoLoaded, rustDeallocExternSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [rustDeallocExternSpecWithStack, StoreKit.withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem pkEq_cells_placed_ok [LibsignalPlacement] {prog : Program} {calleeStk : Nat}
    (hEq : subroutine_ok prog (lsmpl.base 212)
      (StoreKit.withLsCodeRoLoaded lsmpl Getters.publicKeyEqSpec))
    (hle : 64 ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 212)
      (StoreKit.withLsCodeRoLoaded lsmpl (pkEqCellsSpec calleeStk)) := by
  intro ⟨p1, ik1, p2, ik2, fsp⟩ R s0 hpc hrun hpre hsp hcl
  rcases StoreKit.extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  simp only [pkEqCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hfsp⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - 64)
  have hpre0 : s0.mem ⊨
      (StoreKit.withLsCodeRoLoaded lsmpl Getters.publicKeyEqSpec).pre
        (p1, ik1.publicKey, p2, ik2.publicKey, s0.sp) s0 ∗ (stkRem ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [Getters.publicKeyEqSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, rfl⟩, ?_⟩
    rw [← stackAt_64_eq_pkEq_frames s0.sp]
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  rcases hEq (p1, ik1.publicKey, p2, ik2.publicKey, s0.sp) (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl
      with ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨_hpan, hq⟩ | ⟨_code, _hex, hq⟩ | ⟨_hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, Getters.publicKeyEqSpec, pkEqCellsSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨⟨hr0, htr⟩, hq⟩
    rw [publicKey_beq_eq_decide] at hr0
    refine ⟨⟨hr0, htr⟩, ?_⟩
    rw [← stackAt_64_eq_pkEq_frames s0.sp] at hq
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · dsimp only [StoreKit.withLsCodeRoLoaded, Getters.publicKeyEqSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [StoreKit.withLsCodeRoLoaded, Getters.publicKeyEqSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [StoreKit.withLsCodeRoLoaded, Getters.publicKeyEqSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-! ## 2. Inner Spec & Outer Wrapper (`idTrustPoll_placed_of_inner`) -/

def cliIdTrustPollInnerSpecPlaced [LibsignalPlacement] (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (A : RustAlloc) (calleeStk : Nat) : Spec IdPollGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.call.fut ∧ s.readReg64 .x8 = x.call.out ∧
      x.call.call.addr.name.bytes.length < 2 ^ 32 ∧ x.peers.path.length < 2 ^ 32 ∧
      pathOk (pathOf x.peers.path x.call.call.addr.name.bytes) ∧
      (∀ bs, x.peers.get rd s.fs.files x.call.call.addr.name.bytes = .ok bs → IdFileWf bs) ∧
      x.call.call.addr.name.bytes.length ≤ x.call.call.addr.name.cap.toNat ∧
      x.call.call.addr.name.cap.toNat < 2 ^ 63 ∧ x.call.call.addr.name.ptr ≠ 0#64⌝ ∗
      (x.call.fut ↦₆₄ x.self) ∗ ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
      ((x.call.fut + 16#64) ↦₆₄ x.call.call.keyA) ∗ ((x.call.fut + 24#64) ↦₈ 0#8) ∗
      dirAt A (x.self + 40#64) x.peers ∗ memRegion x.call.out 48 ∗
      (x.call.call.addrA ↦₆₄ x.call.call.addr.name.cap) ∗
      ((x.call.call.addrA + 8#64) ↦₆₄ x.call.call.addr.name.ptr) ∗
      ((x.call.call.addrA + 16#64) ↦₆₄ BitVec.ofNat 64 x.call.call.addr.name.bytes.length) ∗
      (x.call.call.addr.name.ptr ↦ₛ x.call.call.addr.name.bytes) ∗
      (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗ FromRecordCallees.lsLogOff ∗
      A.pool ∗ stackAt (s.sp - 192#64) calleeStk ∗ cells (s.sp - 192#64) 24
  post := fun x s0 sf =>
    (∃∗ gr : Except Unit (List (BitVec 8)),
      ∃∗ p : Except Unit (Option IdentityKey),
      ⌜(gr = x.peers.get rd s0.fs.files x.call.call.addr.name.bytes ∧ sf.trace = s0.trace) ∧
        IdPeerAns gr p⌝ ∗
      idTrustOutAt A x.call.out (idTrustOf p x.call.call.key)) ∗
      (x.call.fut ↦₆₄ x.self) ∗ ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
      ((x.call.fut + 16#64) ↦₆₄ x.call.call.keyA) ∗ ((x.call.fut + 24#64) ↦₈ 1#8) ∗
      dirAt A (x.self + 40#64) x.peers ∗
      (x.call.call.addrA ↦₆₄ x.call.call.addr.name.cap) ∗
      ((x.call.call.addrA + 8#64) ↦₆₄ x.call.call.addr.name.ptr) ∗
      ((x.call.call.addrA + 16#64) ↦₆₄ BitVec.ofNat 64 x.call.call.addr.name.bytes.length) ∗
      (x.call.call.addr.name.ptr ↦ₛ x.call.call.addr.name.bytes) ∗
      (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗ FromRecordCallees.lsLogOff ∗
      A.pool ∗ stackAt (s0.sp - 192#64) calleeStk ∗ cells (s0.sp - 192#64) 24
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem idTrustPoll_placed_of_inner [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {A : RustAlloc} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {calleeStk stk : Nat}
    (hInner : calleeStk ≤ 2 ^ 64 →
      subroutine_ok prog entry
        (StoreKit.withLsCodeRoLoaded lsmpl (cliIdTrustPollInnerSpecPlaced rd pathOk A calleeStk)))
    (hstk : 0xc0 + calleeStk ≤ stk) :
    subroutine_ok prog entry (idTrustPollSpecPlaced rd pathOk A stk) := by
  intro ⟨x, d⟩ R s0 hpc hrun hpre hsp hcl
  dsimp only [idTrustPollSpecPlaced, StoreKit.withLsCodeRoLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcrl, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hname, hpath, hpok, hwf⟩, hmem⟩
  dsimp only [idTrustBoxAt, AddrGhost.val] at hpok hwf hmem
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine memRegion_bound_of_pointsTo64 (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk)
      (a := x.call.fut) (v := x.self)
      (R := ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
        ((x.call.fut + 0x10#64) ↦₆₄ x.call.call.keyA) ∗ ((x.call.fut + 0x18#64) ↦₈ 0#8) ∗
        ((x.call.fut + 0x19#64) ↦₈ d) ∗ memRegion (x.call.fut + 0x1a#64) 6 ∗
        dirAt A (x.self + 0x28#64) x.peers ∗ memRegion x.call.out 48 ∗
        protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
        (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗ FromRecordCallees.lsLogOff ∗
        A.pool ∗ R) ?_
    dsimp only [stackAt] at hmem
    convert hmem using 1; ac_rfl
  have hcal_hi : calleeStk ≤ 2 ^ 64 := by omega
  have hframe_hi : calleeStk + 192 ≤ 2 ^ 64 := by omega
  rw [protocolAddressAt_eq_expose A x.call.call.addr x.call.call.addrA] at hmem
  have hmem' : s0.mem ⊨
      ⌜x.call.call.addr.name.bytes.length ≤ x.call.call.addr.name.cap.toNat ∧
        x.call.call.addr.name.cap.toNat < 2 ^ 63 ∧ x.call.call.addr.name.ptr ≠ 0#64⌝ ∗
      ((x.call.fut ↦₆₄ x.self) ∗ ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
        ((x.call.fut + 16#64) ↦₆₄ x.call.call.keyA) ∗ ((x.call.fut + 24#64) ↦₈ 0#8) ∗
        ((x.call.fut + 25#64) ↦₈ d) ∗ memRegion (x.call.fut + 26#64) 6 ∗
        dirAt A (x.self + 40#64) x.peers ∗ memRegion x.call.out 48 ∗
        (x.call.call.addrA ↦₆₄ x.call.call.addr.name.cap) ∗
        ((x.call.call.addrA + 8#64) ↦₆₄ x.call.call.addr.name.ptr) ∗
        ((x.call.call.addrA + 16#64) ↦₆₄ BitVec.ofNat 64 x.call.call.addr.name.bytes.length) ∗
        (x.call.call.addr.name.ptr ↦ₛ x.call.call.addr.name.bytes) ∗
        vecU8BufRest A x.call.call.addr.name.cap x.call.call.addr.name.ptr
          x.call.call.addr.name.bytes.length ∗
        ((x.call.call.addrA + 24#64) ↦₈ x.call.call.addr.device) ∗
        memRegion (x.call.call.addrA + 25#64) 7 ∗
        (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗ FromRecordCallees.lsLogOff ∗
        A.pool ∗ stackAt s0.sp stk ∗ R) := by
    convert hmem using 1; ac_rfl
  rw [satisfies_pure_sepConj] at hmem'
  rcases hmem' with ⟨⟨hncap, hnlt, hnptr⟩, hmem⟩
  rw [stackAt_sub_split s0.sp (subStk := calleeStk + 192) (by omega) hstk_hi,
    stackAt_idTrustPoll_frame s0.sp hframe_hi] at hmem
  let F_extra :=
    ((x.call.fut + 25#64) ↦₈ d) ∗ memRegion (x.call.fut + 26#64) 6 ∗
      vecU8BufRest A x.call.call.addr.name.cap x.call.call.addr.name.ptr
        x.call.call.addr.name.bytes.length ∗
      ((x.call.call.addrA + 24#64) ↦₈ x.call.call.addr.device) ∗
      memRegion (x.call.call.addrA + 25#64) 7 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 192))
  have hpre_in : s0.mem ⊨
      (StoreKit.withLsCodeRoLoaded lsmpl (cliIdTrustPollInnerSpecPlaced rd pathOk A calleeStk)).pre
        x s0 ∗ (F_extra ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [cliIdTrustPollInnerSpecPlaced]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hname, hpath, hpok, hwf, hncap, hnlt, hnptr⟩, ?_⟩
    dsimp only [F_extra]
    convert hmem using 1; ac_rfl
  rcases hInner hcal_hi x (F_extra ∗ R) s0 hpc hrun hpre_in hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨_code, _hex, hq⟩ | ⟨_hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, cliIdTrustPollInnerSpecPlaced,
      idTrustPollSpecPlaced, idTrustBoxAt, AddrGhost.val] at hq ⊢
    rw [protocolAddressAt_eq_expose A x.call.call.addr x.call.call.addrA,
        stackAt_sub_split s0.sp (subStk := calleeStk + 192) (by omega) hstk_hi,
        stackAt_idTrustPoll_frame s0.sp hframe_hi]
    have hq_pure : sf.mem ⊨
        ⌜x.call.call.addr.name.bytes.length ≤ x.call.call.addr.name.cap.toNat ∧
          x.call.call.addr.name.cap.toNat < 2 ^ 63 ∧ x.call.call.addr.name.ptr ≠ 0#64⌝ ∗
        (((∃∗ gr : Except Unit (List (BitVec 8)), ∃∗ p : Except Unit (Option IdentityKey),
            ⌜(gr = x.peers.get rd s0.fs.files x.call.call.addr.name.bytes ∧ sf.trace = s0.trace) ∧
              IdPeerAns gr p⌝ ∗
            idTrustOutAt A x.call.out (idTrustOf p x.call.call.key)) ∗
          (x.call.fut ↦₆₄ x.self) ∗ ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
          ((x.call.fut + 16#64) ↦₆₄ x.call.call.keyA) ∗ ((x.call.fut + 24#64) ↦₈ 1#8) ∗
          dirAt A (x.self + 40#64) x.peers ∗
          (x.call.call.addrA ↦₆₄ x.call.call.addr.name.cap) ∗
          ((x.call.call.addrA + 8#64) ↦₆₄ x.call.call.addr.name.ptr) ∗
          ((x.call.call.addrA + 16#64) ↦₆₄ BitVec.ofNat 64 x.call.call.addr.name.bytes.length) ∗
          (x.call.call.addr.name.ptr ↦ₛ x.call.call.addr.name.bytes) ∗
          (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗ FromRecordCallees.lsLogOff ∗
          A.pool ∗ stackAt (s0.sp - 192#64) calleeStk ∗ cells (s0.sp - 192#64) 24) ∗
        (F_extra ∗ R)) := by
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hncap, hnlt, hnptr⟩, hq⟩
    dsimp only [F_extra] at hq_pure
    convert hq_pure using 1; ac_rfl
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, cliIdTrustPollInnerSpecPlaced,
      idTrustPollSpecPlaced] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [StoreKit.withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-! ## 3. Local Focus & Unpack Helpers for Block `566` -/

private theorem utf8_read_len_eq_p : BitVec.ofNat 64 (utf8 "read").length = 4#64 := by
  decide +kernel

private theorem close_panic_subgoal_p {s0 s_call sf : State} {F R : SepProp}
    (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
  refine allowPanic_frame ?_ (by rwa [sepConj_assoc] at hm)
  rintro ⟨hfail, hpref⟩
  unfold allocFailedIn at hfail ⊢
  rw [htr] at hfail hpref
  exact ⟨hfail, hpref⟩

private def idTrustPostAns_p (A : RustAlloc) (out : BitVec 64)
    (dget : Except Unit (List (BitVec 8))) (key : IdentityKey)
    (s0 sf : State) : SepProp :=
  ∃∗ gr : Except Unit (List (BitVec 8)),
  ∃∗ p : Except Unit (Option IdentityKey),
    ⌜(gr = dget ∧ sf.trace = s0.trace) ∧ IdPeerAns gr p⌝ ∗
    idTrustOutAt A out (idTrustOf p key)

private theorem idTrustPostAns_intro_p (A : RustAlloc) (out : BitVec 64)
    (dget gr : Except Unit (List (BitVec 8))) (p : Except Unit (Option IdentityKey))
    (key : IdentityKey) (s0 sf : State)
    (hpure : (gr = dget ∧ sf.trace = s0.trace) ∧ IdPeerAns gr p) :
    idTrustOutAt A out (idTrustOf p key) ⊢
      idTrustPostAns_p A out dget key s0 sf := by
  have htrue : (((gr = dget ∧ sf.trace = s0.trace) ∧ IdPeerAns gr p) : Prop) = True :=
    propext ⟨fun _ => trivial, fun _ => hpure⟩
  unfold idTrustPostAns_p
  refine Entails.sepExists_right gr (Entails.sepExists_right p ?_)
  rw [htrue]
  exact Entails.of_eq (by simp)

private theorem focus_postAns_p (A : RustAlloc) (out : BitVec 64)
    (dget gr : Except Unit (List (BitVec 8))) (p : Except Unit (Option IdentityKey))
    (key : IdentityKey) (s0 : State)
    {prog : Program} {ret_pc : BitVec 64} {s_ret : State}
    {P R : SepProp} {post : State → SepProp → Prop}
    (hf : P = idTrustOutAt A out (idTrustOf p key) ∗ R)
    (hpure : (gr = dget ∧ s_ret.trace = s0.trace) ∧ IdPeerAns gr p)
    (hnext : SepWP prog ret_pc s_ret (idTrustPostAns_p A out dget key s0 s_ret ∗ R) post) :
    SepWP prog ret_pc s_ret P post :=
  SepWP.focus_weaken (idTrustPostAns_intro_p A out dget gr p key s0 s_ret hpure) (hf := hf) hnext

private theorem focus_out_err_fold_p (A : RustAlloc) (out : BitVec 64)
    (sCap sPtr : BitVec 64) (sBs : List (BitVec 8)) (fnPtr : BitVec 64)
    {prog : Program} {ret_pc : BitVec 64} {s_ret : State}
    {P R : SepProp} {post : State → SepProp → Prop}
    {b8 : BitVec 8} {w9 : BitVec 32} {h13 : BitVec 16} {b15 : BitVec 8}
    {b40 b41 b42 b43 : BitVec 8} {w44 : BitVec 32}
    (hf : P = ((out ↦₆₄ speWord 1) ∗
        (((out + 8#64) ↦₈ b8) ∗ ((out + 9#64) ↦₃₂ w9) ∗
          ((out + 13#64) ↦₁₆ h13) ∗ ((out + 15#64) ↦₈ b15)) ∗
        ((out + 16#64) ↦₆₄ sPtr) ∗ ((out + 24#64) ↦₆₄ BitVec.ofNat 64 sBs.length) ∗
        SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs ∗
        ((out + 32#64) ↦₆₄ fnPtr) ∗
        (((out + 40#64) ↦₈ b40) ∗ ((out + 41#64) ↦₈ b41) ∗
          ((out + 42#64) ↦₈ b42) ∗ ((out + 43#64) ↦₈ b43) ∗ ((out + 44#64) ↦₃₂ w44)) ∗
        (fnPtr ↦ᵣ utf8 "read")) ∗ R)
    (hsCap : b15 ++ h13 ++ w9 ++ b8 = sCap)
    (hfnLen : w44 ++ b43 ++ b42 ++ b41 ++ b40 = 4#64)
    (hnext : SepWP prog ret_pc s_ret (idTrustOutAt A out (.error ()) ∗ R) post) :
    SepWP prog ret_pc s_ret P post :=
  SepWP.focus_weaken
    (out_err_fold A out sCap sPtr sBs fnPtr b8 w9 h13 b15 b40 b41 b42 b43 w44
      hsCap (hfnLen.trans utf8_read_len_eq_p.symm))
    (hf := hf) hnext

private theorem focus_pollKeyChunks_sp_144_p (sp : BitVec 64) {bs : List (BitVec 8)}
    {kw0 : BitVec 32} {kw4 : BitVec 16} {kb6 : BitVec 8}
    {kv7 kv15 kv23 : BitVec 64} {kb31 : BitVec 8}
    (hchunks : ∀ a : BitVec 64, (a ↦ₛ bs) = pollKeyChunks a kw0 kw4 kb6 kv7 kv15 kv23 kb31)
    {prog : Program} {target : BitVec 64} {s : State}
    {P R : SepProp} {post : State → SepProp → Prop}
    {w0' : BitVec 32} {w4' : BitVec 16} {b6' : BitVec 8}
    (hf : P = (((sp - 144#64) ↦₃₂ w0') ∗ ((sp - 140#64) ↦₁₆ w4') ∗
        ((sp - 138#64) ↦₈ b6') ∗ ((sp - 137#64) ↦₆₄ kv7) ∗
        ((sp - 129#64) ↦₆₄ kv15) ∗ ((sp - 121#64) ↦₆₄ kv23) ∗
        ((sp - 113#64) ↦₈ kb31)) ∗ R)
    (hw0 : w0' = kw0) (hw4 : w4' = kw4) (hb6 : b6' = kb6)
    (hnext : SepWP prog target s (((sp - 144#64) ↦ₛ bs) ∗ R) post) :
    SepWP prog target s P post := by
  rw [hf, pollKeyChunks_sp_144_of_eq sp hchunks hw0 hw4 hb6]
  exact hnext

private theorem unpack_getResultAt_err_p {prog : Program} {ret : BitVec 64} {sf : State}
    {A : RustAlloc} {sp : BitVec 64} {rest : SepProp}
    {Q Qp : State → SepProp → Prop}
    (h : ∀ (fnPtr : BitVec 64) (sBs : List (BitVec 8)) (sCap sPtr : BitVec 64),
      SepWPp prog ret sf
        (((sp - 144#64) ↦₆₄ speWord 1) ∗
          ((sp - 136#64) ↦₆₄ sCap) ∗ ((sp - 128#64) ↦₆₄ sPtr) ∗
          ((sp - 120#64) ↦₆₄ BitVec.ofNat 64 sBs.length) ∗
          SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs ∗
          ((sp - 112#64) ↦₆₄ fnPtr) ∗
          ((sp - 104#64) ↦₆₄ 4#64) ∗
          (fnPtr ↦ᵣ utf8 "read") ∗ rest) Q Qp) :
    SepWPp prog ret sf (getResultAt A (sp - 144#64) (.error ()) ∗ rest) Q Qp := by
  rw [getResultAt_err_sp_144 A sp, utf8_read_len_eq_p]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply ProofLib.SepWPp.exists_elim; intro fnPtr
  apply ProofLib.SepWPp.exists_elim; intro sBs
  apply ProofLib.SepWPp.exists_elim; intro sCap
  apply ProofLib.SepWPp.exists_elim; intro sPtr
  exact h fnPtr sBs sCap sPtr

private theorem unpack_getResultAt_ok_p {prog : Program} {ret : BitVec 64} {sf : State}
    {A : RustAlloc} {sp : BitVec 64} {bs : List (BitVec 8)} {rest : SepProp}
    {Q Qp : State → SepProp → Prop}
    (h : ∀ (bCap bPtr : BitVec 64),
      bs.length ≤ bCap.toNat → bCap.toNat < 2 ^ 63 → bPtr ≠ 0#64 →
      SepWPp prog ret sf
        (((sp - 144#64) ↦₆₄ okTagVec) ∗ ((sp - 136#64) ↦₆₄ bCap) ∗
          ((sp - 128#64) ↦₆₄ bPtr) ∗ ((sp - 120#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (bPtr ↦ₛ bs) ∗ vecU8BufRest A bCap bPtr bs.length ∗
          memRegion (sp - 112#64) 16 ∗ rest) Q Qp) :
    SepWPp prog ret sf (getResultAt A (sp - 144#64) (.ok bs) ∗ rest) Q Qp := by
  rw [getResultAt_ok_sp_144 A sp bs]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply ProofLib.SepWPp.exists_elim; intro bCap
  apply ProofLib.SepWPp.exists_elim; intro bPtr
  apply ProofLib.SepWPp.pure_elim; rintro ⟨h1, h2, h3⟩
  exact h bCap bPtr h1 h2 h3

private theorem cells_24_lo_p (sp : BitVec 64) :
    cells (sp - 192#64) 24 =
      (∃∗ v0 : BitVec 64, (sp - 192#64) ↦₆₄ v0) ∗
      ((∃∗ b1 : BitVec 8, (sp - 184#64) ↦₈ b1) ∗ memRegion (sp - 183#64) 7) ∗
      (∃∗ v2 : BitVec 64, (sp - 176#64) ↦₆₄ v2) ∗
      ((∃∗ b3 : BitVec 8, (sp - 168#64) ↦₈ b3) ∗ memRegion (sp - 167#64) 7) ∗
      (∃∗ v4 : BitVec 64, (sp - 160#64) ↦₆₄ v4) ∗
      ((∃∗ b5 : BitVec 8, (sp - 152#64) ↦₈ b5) ∗ memRegion (sp - 151#64) 7) ∗
      memRegion (sp - 144#64) 48 ∗
      (∃∗ s29 : BitVec 64, (sp - 96#64) ↦₆₄ s29) ∗
      (∃∗ s30 : BitVec 64, (sp - 88#64) ↦₆₄ s30) ∗
      (∃∗ s27 : BitVec 64, (sp - 80#64) ↦₆₄ s27) ∗
      ((∃∗ w0 : BitVec 32, (sp - 72#64) ↦₃₂ w0) ∗
        (∃∗ b4 : BitVec 8, (sp - 68#64) ↦₈ b4) ∗
        (∃∗ b5 : BitVec 8, (sp - 67#64) ↦₈ b5) ∗
        (∃∗ b6 : BitVec 8, (sp - 66#64) ↦₈ b6) ∗
        (∃∗ b7 : BitVec 8, (sp - 65#64) ↦₈ b7)) ∗
      (∃∗ s26 : BitVec 64, (sp - 64#64) ↦₆₄ s26) ∗
      (∃∗ s25 : BitVec 64, (sp - 56#64) ↦₆₄ s25) ∗
      (∃∗ s24 : BitVec 64, (sp - 48#64) ↦₆₄ s24) ∗
      (∃∗ s23 : BitVec 64, (sp - 40#64) ↦₆₄ s23) ∗
      (∃∗ s22 : BitVec 64, (sp - 32#64) ↦₆₄ s22) ∗
      (∃∗ s21 : BitVec 64, (sp - 24#64) ↦₆₄ s21) ∗
      (∃∗ s20 : BitVec 64, (sp - 16#64) ↦₆₄ s20) ∗
      (∃∗ s19 : BitVec 64, (sp - 8#64) ↦₆₄ s19) := by
  rw [cells_24_split sp, memRegion_8_sp_72_lo sp]

private theorem cells_24_hi_p (sp : BitVec 64) :
    cells (sp - 192#64) 24 =
      (∃∗ v0 : BitVec 64, (sp - 192#64) ↦₆₄ v0) ∗
      ((∃∗ b1 : BitVec 8, (sp - 184#64) ↦₈ b1) ∗ memRegion (sp - 183#64) 7) ∗
      (∃∗ v2 : BitVec 64, (sp - 176#64) ↦₆₄ v2) ∗
      ((∃∗ b3 : BitVec 8, (sp - 168#64) ↦₈ b3) ∗ memRegion (sp - 167#64) 7) ∗
      (∃∗ v4 : BitVec 64, (sp - 160#64) ↦₆₄ v4) ∗
      ((∃∗ b5 : BitVec 8, (sp - 152#64) ↦₈ b5) ∗ memRegion (sp - 151#64) 7) ∗
      memRegion (sp - 144#64) 48 ∗
      (∃∗ s29 : BitVec 64, (sp - 96#64) ↦₆₄ s29) ∗
      (∃∗ s30 : BitVec 64, (sp - 88#64) ↦₆₄ s30) ∗
      (∃∗ s27 : BitVec 64, (sp - 80#64) ↦₆₄ s27) ∗
      ((∃∗ b0 : BitVec 8, (sp - 72#64) ↦₈ b0) ∗
        (∃∗ b1 : BitVec 8, (sp - 71#64) ↦₈ b1) ∗
        (∃∗ b2 : BitVec 8, (sp - 70#64) ↦₈ b2) ∗
        (∃∗ w3 : BitVec 32, (sp - 69#64) ↦₃₂ w3) ∗
        (∃∗ b7 : BitVec 8, (sp - 65#64) ↦₈ b7)) ∗
      (∃∗ s26 : BitVec 64, (sp - 64#64) ↦₆₄ s26) ∗
      (∃∗ s25 : BitVec 64, (sp - 56#64) ↦₆₄ s25) ∗
      (∃∗ s24 : BitVec 64, (sp - 48#64) ↦₆₄ s24) ∗
      (∃∗ s23 : BitVec 64, (sp - 40#64) ↦₆₄ s23) ∗
      (∃∗ s22 : BitVec 64, (sp - 32#64) ↦₆₄ s22) ∗
      (∃∗ s21 : BitVec 64, (sp - 24#64) ↦₆₄ s21) ∗
      (∃∗ s20 : BitVec 64, (sp - 16#64) ↦₆₄ s20) ∗
      (∃∗ s19 : BitVec 64, (sp - 8#64) ↦₆₄ s19) := by
  rw [cells_24_split sp, memRegion_8_sp_72_hi sp]

private def cliIdTrustPollExpandedSpecPlaced [LibsignalPlacement] (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (A : RustAlloc) (calleeStk : Nat) : Spec IdPollGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.call.fut ∧ s.readReg64 .x8 = x.call.out ∧
      x.call.call.addr.name.bytes.length < 2 ^ 32 ∧ x.peers.path.length < 2 ^ 32 ∧
      pathOk (pathOf x.peers.path x.call.call.addr.name.bytes) ∧
      (∀ bs, x.peers.get rd s.fs.files x.call.call.addr.name.bytes = .ok bs → IdFileWf bs) ∧
      x.call.call.addr.name.bytes.length ≤ x.call.call.addr.name.cap.toNat ∧
      x.call.call.addr.name.cap.toNat < 2 ^ 63 ∧ x.call.call.addr.name.ptr ≠ 0#64⌝ ∗
      (x.call.fut ↦₆₄ x.self) ∗ ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
      ((x.call.fut + 16#64) ↦₆₄ x.call.call.keyA) ∗ ((x.call.fut + 24#64) ↦₈ 0#8) ∗
      dirAt A (x.self + 40#64) x.peers ∗
      memRegion x.call.out 48 ∗
      (x.call.call.addrA ↦₆₄ x.call.call.addr.name.cap) ∗
      ((x.call.call.addrA + 8#64) ↦₆₄ x.call.call.addr.name.ptr) ∗
      ((x.call.call.addrA + 16#64) ↦₆₄ BitVec.ofNat 64 x.call.call.addr.name.bytes.length) ∗
      (x.call.call.addr.name.ptr ↦ₛ x.call.call.addr.name.bytes) ∗
      (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗ FromRecordCallees.lsLogOff ∗
      A.pool ∗ stackAt (s.sp - 192#64) calleeStk ∗
      ((∃∗ v0 : BitVec 64, (s.sp - 192#64) ↦₆₄ v0) ∗
        ((∃∗ b1 : BitVec 8, (s.sp - 184#64) ↦₈ b1) ∗ memRegion (s.sp - 183#64) 7) ∗
        (∃∗ v2 : BitVec 64, (s.sp - 176#64) ↦₆₄ v2) ∗
        ((∃∗ b3 : BitVec 8, (s.sp - 168#64) ↦₈ b3) ∗ memRegion (s.sp - 167#64) 7) ∗
        (∃∗ v4 : BitVec 64, (s.sp - 160#64) ↦₆₄ v4) ∗
        ((∃∗ b5 : BitVec 8, (s.sp - 152#64) ↦₈ b5) ∗ memRegion (s.sp - 151#64) 7) ∗
        memRegion (s.sp - 144#64) 48 ∗
        (∃∗ s29 : BitVec 64, (s.sp - 96#64) ↦₆₄ s29) ∗
        (∃∗ s30 : BitVec 64, (s.sp - 88#64) ↦₆₄ s30) ∗
        (∃∗ s27 : BitVec 64, (s.sp - 80#64) ↦₆₄ s27) ∗
        ((∃∗ w0 : BitVec 32, (s.sp - 72#64) ↦₃₂ w0) ∗
          (∃∗ b4 : BitVec 8, (s.sp - 68#64) ↦₈ b4) ∗
          (∃∗ b5 : BitVec 8, (s.sp - 67#64) ↦₈ b5) ∗
          (∃∗ b6 : BitVec 8, (s.sp - 66#64) ↦₈ b6) ∗
          (∃∗ b7 : BitVec 8, (s.sp - 65#64) ↦₈ b7)) ∗
        (∃∗ s26 : BitVec 64, (s.sp - 64#64) ↦₆₄ s26) ∗
        (∃∗ s25 : BitVec 64, (s.sp - 56#64) ↦₆₄ s25) ∗
        (∃∗ s24 : BitVec 64, (s.sp - 48#64) ↦₆₄ s24) ∗
        (∃∗ s23 : BitVec 64, (s.sp - 40#64) ↦₆₄ s23) ∗
        (∃∗ s22 : BitVec 64, (s.sp - 32#64) ↦₆₄ s22) ∗
        (∃∗ s21 : BitVec 64, (s.sp - 24#64) ↦₆₄ s21) ∗
        (∃∗ s20 : BitVec 64, (s.sp - 16#64) ↦₆₄ s20) ∗
        (∃∗ s19 : BitVec 64, (s.sp - 8#64) ↦₆₄ s19))
  post := fun x s0 sf =>
    idTrustPostAns_p A x.call.out
      (x.peers.get rd s0.fs.files x.call.call.addr.name.bytes) x.call.call.key s0 sf ∗
      (x.call.fut ↦₆₄ x.self) ∗ ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
      ((x.call.fut + 16#64) ↦₆₄ x.call.call.keyA) ∗ ((x.call.fut + 24#64) ↦₈ 1#8) ∗
      dirAt A (x.self + 40#64) x.peers ∗
      (x.call.call.addrA ↦₆₄ x.call.call.addr.name.cap) ∗
      ((x.call.call.addrA + 8#64) ↦₆₄ x.call.call.addr.name.ptr) ∗
      ((x.call.call.addrA + 16#64) ↦₆₄ BitVec.ofNat 64 x.call.call.addr.name.bytes.length) ∗
      (x.call.call.addr.name.ptr ↦ₛ x.call.call.addr.name.bytes) ∗
      (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗ FromRecordCallees.lsLogOff ∗
      A.pool ∗ stackAt (s0.sp - 192#64) calleeStk ∗
      ((∃∗ v0 : BitVec 64, (s0.sp - 192#64) ↦₆₄ v0) ∗
        ((∃∗ b1 : BitVec 8, (s0.sp - 184#64) ↦₈ b1) ∗ memRegion (s0.sp - 183#64) 7) ∗
        (∃∗ v2 : BitVec 64, (s0.sp - 176#64) ↦₆₄ v2) ∗
        ((∃∗ b3 : BitVec 8, (s0.sp - 168#64) ↦₈ b3) ∗ memRegion (s0.sp - 167#64) 7) ∗
        (∃∗ v4 : BitVec 64, (s0.sp - 160#64) ↦₆₄ v4) ∗
        ((∃∗ b5 : BitVec 8, (s0.sp - 152#64) ↦₈ b5) ∗ memRegion (s0.sp - 151#64) 7) ∗
        memRegion (s0.sp - 144#64) 48 ∗
        (∃∗ s29 : BitVec 64, (s0.sp - 96#64) ↦₆₄ s29) ∗
        (∃∗ s30 : BitVec 64, (s0.sp - 88#64) ↦₆₄ s30) ∗
        (∃∗ s27 : BitVec 64, (s0.sp - 80#64) ↦₆₄ s27) ∗
        ((∃∗ b0 : BitVec 8, (s0.sp - 72#64) ↦₈ b0) ∗
          (∃∗ b1 : BitVec 8, (s0.sp - 71#64) ↦₈ b1) ∗
          (∃∗ b2 : BitVec 8, (s0.sp - 70#64) ↦₈ b2) ∗
          (∃∗ w3 : BitVec 32, (s0.sp - 69#64) ↦₃₂ w3) ∗
          (∃∗ b7 : BitVec 8, (s0.sp - 65#64) ↦₈ b7)) ∗
        (∃∗ s26 : BitVec 64, (s0.sp - 64#64) ↦₆₄ s26) ∗
        (∃∗ s25 : BitVec 64, (s0.sp - 56#64) ↦₆₄ s25) ∗
        (∃∗ s24 : BitVec 64, (s0.sp - 48#64) ↦₆₄ s24) ∗
        (∃∗ s23 : BitVec 64, (s0.sp - 40#64) ↦₆₄ s23) ∗
        (∃∗ s22 : BitVec 64, (s0.sp - 32#64) ↦₆₄ s22) ∗
        (∃∗ s21 : BitVec 64, (s0.sp - 24#64) ↦₆₄ s21) ∗
        (∃∗ s20 : BitVec 64, (s0.sp - 16#64) ↦₆₄ s20) ∗
        (∃∗ s19 : BitVec 64, (s0.sp - 8#64) ↦₆₄ s19))
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private theorem cliIdTrustPollExpandedSpecPlaced_eq [LibsignalPlacement] (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (A : RustAlloc) (calleeStk : Nat) :
    cliIdTrustPollExpandedSpecPlaced rd pathOk A calleeStk =
      cliIdTrustPollInnerSpecPlaced rd pathOk A calleeStk := by
  unfold cliIdTrustPollExpandedSpecPlaced cliIdTrustPollInnerSpecPlaced idTrustPostAns_p
  congr 1
  · funext x s
    rw [cells_24_lo_p s.sp]
  · funext x s0 sf
    rw [cells_24_hi_p s0.sp]

/-! ## 4. Main Symbolic Execution of Block `566` -/

set_option pp.deepTerms false in
set_option pp.maxSteps 1000000 in
set_option maxHeartbeats 3200000 in
theorem idTrustPollInner_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hGet : subroutine_ok ((blkPC_566).rebase (blkPl_566).base H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A getStk))
    (hDec : subroutine_ok ((blkPC_566).rebase (blkPl_566).base H) (lsmpl.base 18)
      (StoreKit.withLsCodeRoLoaded lsmpl (RecordCodecsBinary.identityKeyDecodeRawSpec A)))
    (hEq : subroutine_ok ((blkPC_566).rebase (blkPl_566).base H) (lsmpl.base 212)
      (StoreKit.withLsCodeRoLoaded lsmpl Getters.publicKeyEqSpec))
    (hhi : max (max getStk 0x60) (max 64 extHookStack) ≤ 2 ^ 64) :
    subroutine_ok ((blkPC_566).rebase (blkPl_566).base H) (blkPl_566).base
      (StoreKit.withLsCodeRoLoaded lsmpl
        (cliIdTrustPollInnerSpecPlaced rd pathOk A
          (max (max getStk 0x60) (max 64 extHookStack)))) := by
  let calleeStk := max (max getStk 0x60) (max 64 extHookStack)
  rw [← cliIdTrustPollExpandedSpecPlaced_eq]
  unfold StoreKit.withLsCodeRoLoaded
  simp (config := { maxSteps := 2000000 }) only [cliIdTrustPollExpandedSpecPlaced,
    sepExists_sepConj_left, sepExists_sepConj_right]
  have hGetCells := dirGet_cells_placed_ok (calleeStk := calleeStk) hGet (by omega) hhi
  have hDecCells := ikDecode_cells_placed_ok (calleeStk := calleeStk) hDec (by omega) hhi
  have hDeallocCells := deallocVecBuf_placed_ok (prog := (blkPC_566).rebase (blkPl_566).base H)
    (i := 566) (calleeStk := calleeStk) hC (by omega) hhi
  have hEqCells := pkEq_cells_placed_ok (calleeStk := calleeStk) hEq (by omega) hhi
  clear hGet hDec hEq hC
  wpp_init x s0
  have hcrl0 : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by
    assumption
  -- Prologue (`+0x0 .. +0x40`) -> `Dir::get`
  apply StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 589) hcrl0
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl1
  wp_call_spec_lscro hGetCells (dirGetCellsSpec rd pathOk A calleeStk) hcrl1
    (s0.sp - 144#64, x.self + 40#64, x.peers,
      x.call.call.addr.name.ptr, x.call.call.addr.name.bytes, s0.sp - 192#64)
  case panic =>
    intro sf _ hm
    exact close_panic_subgoal_p (by simp only [wp_norm, arm64_norm, *]) hm
  -- Split on `Dir::get` result `w : Except Unit (List (BitVec 8))`
  cases w with
  | error u =>
    cases u
    apply unpack_getResultAt_err_p
    intro fnPtr sBs sCap sPtr
    apply SepWPp.of_sepWP_ret
    apply SepWP.focus_rw (out_48_pre_split x.call.out)
    wp_pull_exists
    apply SepWP.focus_weaken (sp_152_fold_64 s0.sp _)
    wp_pull_exists
    wp_steps
    apply SepWP.focus_rw (pointsTo64_sp_152_split s0.sp _)
    wp_steps
    apply SepWP.focus_rw (sevenLo_sp_151' s0.sp _ _ _ _)
    wp_steps
    apply SepWP.focus_rw (sevenLo_sp_72' s0.sp _ _ _ _)
    wp_steps
    apply SepWP.focus_rw (sevenHi_sp_72' s0.sp _ _ _ _)
    wp_steps
    apply SepWP.focus_rw (sevenLo_sp_72' s0.sp _ _ _ _)
    wp_steps
    apply SepWP.focus_rw (sevenLo_out_41' x.call.out _ _ _ _)
    wp_steps
    apply SepWP.focus_weaken (sp_151_sevenHi_fold_7 s0.sp _ _ _ _)
    apply SepWP.focus_weaken (sp_144_cells6_fold_48 s0.sp _ _ _ _ _ _)
    refine focus_out_err_fold_p A x.call.out sCap sPtr sBs fnPtr (by sep_focus) ?_ ?_ ?_
    · bv_bits
    · bv_bits
    refine focus_postAns_p A x.call.out
      (x.peers.get rd s0.fs.files x.call.call.addr.name.bytes)
      (.error ()) (.error ()) x.call.call.key s0 (by sep_focus) ?_ ?_
    · exact post_err_disj (sf1 := sf) ⟨by assumption, by assumption⟩
        (by simp only [wp_norm, arm64_norm])
    wp_done
  | ok bs =>
    have ⟨hget, _htr_get⟩ :=
      post_ok_disj (bs := bs)
        (dget := x.peers.get rd s0.fs.files x.call.call.addr.name.bytes)
        (s0 := s0) (sf1 := sf) ⟨by assumption, by assumption⟩
    have hfile : IdFileWf bs := by
      have hwf : ∀ bs, x.peers.get rd s0.fs.files x.call.call.addr.name.bytes = .ok bs →
          IdFileWf bs := by assumption
      exact hwf bs hget.symm
    cases bs with
    | nil =>
      apply unpack_getResultAt_ok_p
      intro bCap bPtr hbCap_le hbCap_lt _hbPtr_ne
      by_cases hc0 : bCap = 0#64
      · subst hc0
        apply SepWPp.of_sepWP_ret
        apply SepWP.focus_rw (out_48_pre_split x.call.out)
        wp_pull_exists
        have hemp : ((bPtr ↦ₛ ([] : List (BitVec 8))) ∗ vecU8BufRest A 0#64 bPtr 0) = emp := by
          simp [vecU8BufRest]
        apply SepWP.focus_rw hemp
        wp_steps
        apply SepWP.focus_rw (sevenLo_sp_72' s0.sp _ _ _ _)
        wp_steps
        apply SepWP.focus_rw (sevenLo_out_41' x.call.out _ _ _ _)
        wp_steps
        apply SepWP.focus_weaken (sp_144_cells4_fold_48 s0.sp _ _ _ _)
        apply SepWP.focus_weaken
          (out_ok_fold A x.call.out true _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl)
        refine focus_postAns_p A x.call.out
          (x.peers.get rd s0.fs.files x.call.call.addr.name.bytes)
          (.ok []) (.ok none) x.call.call.key s0 (by sep_focus) ?_ ?_
        · exact ⟨⟨hget, by simp only [wp_norm, arm64_norm, *]⟩, rfl⟩
        wp_done
      · have hc0_beq : (bCap == 0#64) = false := beq_false_of_ne hc0
        apply StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli)
          (by assumption)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hcrl_d0
        wp_call_spec_lscro hDeallocCells (deallocVecBufSpec A calleeStk) hcrl_d0
          (bPtr, bCap, [], s0.sp - 192#64)
        case panic =>
          intro sf_p _ hm
          exact close_panic_subgoal_p (by simp only [wp_norm, arm64_norm, *]) hm
        apply SepWPp.of_sepWP_ret
        apply SepWP.focus_rw (out_48_pre_split x.call.out)
        wp_pull_exists
        wp_steps
        apply SepWP.focus_rw (sevenLo_sp_72' s0.sp _ _ _ _)
        wp_steps
        apply SepWP.focus_rw (sevenLo_out_41' x.call.out _ _ _ _)
        wp_steps
        apply SepWP.focus_weaken (sp_144_cells4_fold_48 s0.sp _ _ _ _)
        apply SepWP.focus_weaken
          (out_ok_fold A x.call.out true _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl)
        refine focus_postAns_p A x.call.out
          (x.peers.get rd s0.fs.files x.call.call.addr.name.bytes)
          (.ok []) (.ok none) x.call.call.key s0 (by sep_focus) ?_ ?_
        · exact ⟨⟨hget, by simp only [wp_norm, arm64_norm, *]⟩, rfl⟩
        wp_done
    | cons b bs' =>
      rcases hfile with hnil | ⟨ik, hser⟩
      · nomatch hnil
      · have hdec : decodeIdentityKey (b :: bs') = .ok ik :=
          hser ▸ decodeIdentityKey_serialize ik
        apply unpack_getResultAt_ok_p
        intro bCap bPtr hbCap_le hbCap_lt _hbPtr_ne
        have hlen_lt : (b :: bs').length < 2 ^ 63 := Nat.lt_of_le_of_lt hbCap_le hbCap_lt
        have hlen_ne : BitVec.ofNat 64 (b :: bs').length ≠ 0#64 := cons_len_bv_ne_zero hlen_lt
        have hlen_beq : (BitVec.ofNat 64 (b :: bs').length == 0#64) = false :=
          beq_false_of_ne hlen_ne
        have hbCap_ne : bCap ≠ 0#64 := cap_ne_zero_of_cons hbCap_le
        have hbCap_beq : (bCap == 0#64) = false := beq_false_of_ne hbCap_ne
        -- Step `+0x44 .. +0x60` -> `IdentityKey::decode`
        apply StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 18)
          (by assumption)
        wp_steps
        apply SepWP.focus_weaken (sp_144_cells4_fold_48 s0.sp _ _ _ _)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hcrl_dec
        wp_call_spec_lscro hDecCells (ikDecodeCellsSpecPlaced calleeStk) hcrl_dec
          (bPtr, b :: bs', s0.sp - 144#64, ik, s0.sp - 192#64)
        case panic =>
          intro sf_p _ hm
          exact close_panic_subgoal_p (by simp only [wp_norm, arm64_norm, *]) hm
        -- Unpack 32-byte decoded public key at `s0.sp - 136#64`, load into regs, call `dealloc`
        rcases exists_pollKeyChunks_of_length_32 ik.publicKey.bytes.toList_length with
          ⟨kw0, kw4, kb6, kv7, kv15, kv23, kb31, hchunks⟩
        have hkey_sp136 :
            ((s0.sp - 144#64 + 8#64) ↦ₛ ik.publicKey.bytes.toList) =
              ((s0.sp - 136#64) ↦₃₂ kw0) ∗ ((s0.sp - 132#64) ↦₁₆ kw4) ∗
              ((s0.sp - 130#64) ↦₈ kb6) ∗ ((s0.sp - 129#64) ↦₆₄ kv7) ∗
              ((s0.sp - 121#64) ↦₆₄ kv15) ∗ ((s0.sp - 113#64) ↦₆₄ kv23) ∗
              ((s0.sp - 105#64) ↦₈ kb31) := by
          have ha : s0.sp - 144#64 + 8#64 = s0.sp - 136#64 := by bv_omega
          rw [ha, hchunks (s0.sp - 136#64), pollKeyChunks_sp_136]
        have hm8 : memRegion (s0.sp - 144#64 + 40#64) 8 = memRegion (s0.sp - 104#64) 8 := by
          congr 1; bv_omega
        apply StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli)
          (by assumption)
        apply SepWP.focus_rw hkey_sp136
        apply SepWP.focus_rw hm8
        wp_steps
        apply SepWP.focus_weaken (sp_144_ikDec_fold_48 s0.sp _ _ _ _ _ _ _ _)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hcrl_d1
        wp_call_spec_lscro hDeallocCells (deallocVecBufSpec A calleeStk) hcrl_d1
          (bPtr, bCap, b :: bs', s0.sp - 192#64)
        case panic =>
          intro sf_p _ hm
          exact close_panic_subgoal_p (by simp only [wp_norm, arm64_norm, *]) hm
        -- Reassemble 32-byte key at `s0.sp - 144#64`, call `PublicKey::eq`
        apply StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 212)
          (by assumption)
        apply SepWP.focus_rw (sret_48_sp_144_rebuild_split s0.sp)
        wp_pull_exists
        wp_steps
        refine focus_pollKeyChunks_sp_144_p s0.sp hchunks (by sep_focus) ?_ ?_ ?_ ?_
        · bv_bits
        · bv_bits
        · bv_bits
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hcrl_eq
        wp_call_spec_lscro hEqCells (pkEqCellsSpec calleeStk) hcrl_eq
          (s0.sp - 144#64, ik, x.call.call.keyA, x.call.call.key, s0.sp - 192#64)
        case panic =>
          intro sf_p _ hm
          rw [← sepConj_assoc]
          refine close_panic_subgoal_p ?_ hm
          simp only [wp_norm, arm64_norm, *]
        -- Write `Ok(ik == key)` into `x.call.out` and return
        apply SepWPp.of_sepWP_ret
        apply SepWP.focus_rw (out_48_pre_split x.call.out)
        wp_pull_exists
        wp_steps
        apply SepWP.focus_rw (sevenLo_sp_72' s0.sp _ _ _ _)
        wp_steps
        apply SepWP.focus_rw (sevenLo_out_41' x.call.out _ _ _ _)
        wp_steps
        apply SepWP.focus_weaken (sp_144_key_fold_48 s0.sp ik.publicKey.bytes.toList_length)
        apply SepWP.focus_weaken
          (out_ok_fold A x.call.out (decide (ik = x.call.call.key))
            _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl)
        refine focus_postAns_p A x.call.out
          (x.peers.get rd s0.fs.files x.call.call.addr.name.bytes)
          (.ok (b :: bs')) (.ok (some ik)) x.call.call.key s0 (by sep_focus) ?_ ?_
        · exact ⟨⟨hget, by simp only [wp_norm, arm64_norm, *]⟩, ⟨ik, rfl, hser⟩⟩
        wp_done

end Placed

end CryptoVerification.SignalSession.Cli.Store.IdTrustPoll.Helpers
