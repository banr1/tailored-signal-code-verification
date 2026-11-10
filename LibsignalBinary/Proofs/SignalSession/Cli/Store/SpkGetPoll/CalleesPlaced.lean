/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymPost
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymB
public import LibsignalBinary.Proofs.RecordCodecs.SignedDeps
public import LibsignalBinary.Proofs.SignalSession.Cli.Fs
public meta import ProofLib
public meta import LibsignalBinary.Proofs.Common.InImageKit
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public meta import Lean
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Relocatable Callee Wrappers, Cut Combinators, and Epilogue for `get_signed_pre_key::{closure#0}`

Placed callee cell wrappers, sret unpack/pack helpers, framed cut combinators, and shared epilogue
(`+344 .. ret`) on Block `571` (`lsProg_571 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.SpkGetPoll.Helpers

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession.Cli CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
open CliSpkPollNorm

section Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm] words6At words11At
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

syntax (name := wpCallSpecLsCroSpkTac) "wp_call_spec_lscro" ppSpace colGt term:max
  ppSpace colGt term:max ppSpace colGt term:max ppSpace colGt term:max : tactic

elab_rules : tactic
  | `(tactic| wp_call_spec_lscro $hcall $spec $hinv $arg) =>
    wpCallSpecLsCro hcall spec hinv arg

/-! ## 2. Private Sret Unpack & Epilogue Pack Helpers -/

private theorem getResultAt_unpack_p (A : RustAlloc) (ret : BitVec 64)
    (gr : Except Unit (List (BitVec 8))) :
    getResultAt A ret gr ⊢
      ∃∗ g0 : BitVec 64, ∃∗ g1 : BitVec 64, ∃∗ g2 : BitVec 64,
      ∃∗ g3 : BitVec 64, ∃∗ g4 : BitVec 64, ∃∗ g5 : BitVec 64,
        words6At ret g0 g1 g2 g3 g4 g5 ∗ dirGetDetached A gr g0 g1 g2 g3 g4 g5 := by
  cases gr with
  | error u =>
    cases u
    dsimp only [getResultAt, dirGetDetached]
    refine Entails.trans (speAt_unpack A (utf8 "read") ret .invalidState) ?_
    refine Entails.sepExists_elim fun g0 => Entails.sepExists_elim fun g1 =>
      Entails.sepExists_elim fun g2 => Entails.sepExists_elim fun g3 =>
      Entails.sepExists_elim fun g4 => Entails.sepExists_elim fun g5 => ?_
    refine Entails.sepExists_right g0 (Entails.sepExists_right g1
      (Entails.sepExists_right g2 (Entails.sepExists_right g3
      (Entails.sepExists_right g4 (Entails.sepExists_right g5 ?_)))))
    dsimp only [speDetached]
    rw [sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bs => Entails.sepExists_right bs ?_
    have hpull :
        (words6At ret g0 g1 g2 g3 g4 g5 ∗
          ⌜g0 = speWord 1 ∧ g3 = BitVec.ofNat 64 bs.length ∧
            g5 = BitVec.ofNat 64 (utf8 "read").length⌝ ∗
          SpqrV1.Alloc.vecU8Buf A g1 g2 bs ∗ (g4 ↦ᵣ utf8 "read")) =
        (⌜g0 = speWord 1 ∧ g3 = BitVec.ofNat 64 bs.length ∧
            g5 = BitVec.ofNat 64 (utf8 "read").length⌝ ∗
          words6At ret g0 g1 g2 g3 g4 g5 ∗
          SpqrV1.Alloc.vecU8Buf A g1 g2 bs ∗ (g4 ↦ᵣ utf8 "read")) := by ac_rfl
    rw [hpull]
    refine Entails.pure_left fun ⟨hg0, hg3, hg5⟩ => ?_
    have hgoal :
        words6At ret g0 g1 g2 g3 g4 g5 ∗
          SpqrV1.Alloc.vecU8Buf A g1 g2 bs ∗ (g4 ↦ᵣ utf8 "read") ⊢
        ⌜g0 = speWord 1⌝ ∗
          ⌜g0 = speWord 1 ∧ g3 = BitVec.ofNat 64 bs.length ∧
            g5 = BitVec.ofNat 64 (utf8 "read").length⌝ ∗
          words6At ret g0 g1 g2 g3 g4 g5 ∗
          SpqrV1.Alloc.vecU8Buf A g1 g2 bs ∗ (g4 ↦ᵣ utf8 "read") :=
      Entails.pure_right hg0 (Entails.pure_right ⟨hg0, hg3, hg5⟩ (Entails.refl _))
    exact Entails.trans hgoal (Entails.of_eq (by ac_rfl))
  | ok bs =>
    dsimp only [getResultAt, vecResultAt, dirGetDetached, words6At]
    have h8 : asm64% decResultVecOff = 8#64 := rfl
    have h32 : asm64% (decResultVecOff + vecSize) = 32#64 := rfl
    have hs : asm% (speSize - (decResultVecOff + vecSize)) = 16 := rfl
    rw [h8, h32, hs, memRegion_16_cells (ret + 32#64)]
    dsimp only [vecU8]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun g5 => Entails.sepExists_elim fun g4 =>
      Entails.sepExists_elim fun g1 => Entails.sepExists_elim fun g2 => ?_
    rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf]
    dsimp only [vecHeader]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.sepExists_right okTagVec (Entails.sepExists_right g1
      (Entails.sepExists_right g2 (Entails.sepExists_right (BitVec.ofNat 64 bs.length)
      (Entails.sepExists_right g4 (Entails.sepExists_right g5 ?_)))))
    rw [show (okTagVec = okTagVec ∧ BitVec.ofNat 64 bs.length = BitVec.ofNat 64 bs.length) = True from
      eq_true ⟨rfl, rfl⟩, pure_true, emp_sepConj]
    exact Entails.of_eq (by ac_rfl)

private theorem signedPreKeyResultAt_unpack_p (A : RustAlloc) (ret : BitVec 64)
    (res : Except SignalProtocolError SignedPreKeyRecord) :
    signedPreKeyResultAt A ret res ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
      ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64,
        words11At ret w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
        decodeSpkDetached A res w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 := by
  cases res with
  | error e =>
    dsimp only [signedPreKeyResultAt, errResultAt, decodeSpkDetached]
    have htag : errTag = 0xFFFFFFFFFFFFFFFF#64 := rfl
    have hoff8 : asm64% resultErrSpeOff = 8#64 := rfl
    have hoff56 : asm64% (resultErrSpeOff + speSize) = 56#64 := rfl
    have hsz : 88 - asm% (resultErrSpeOff + speSize) = 32 := rfl
    rw [htag, hoff8, hoff56, hsz, memRegion_32_cells (ret + 56#64)]
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_left (speAt_unpack A [] (ret + 8#64) e))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w10 => Entails.sepExists_elim fun w9 =>
      Entails.sepExists_elim fun w8 => Entails.sepExists_elim fun w7 =>
      Entails.sepExists_elim fun u0 => Entails.sepExists_elim fun u1 =>
      Entails.sepExists_elim fun u2 => Entails.sepExists_elim fun u3 =>
      Entails.sepExists_elim fun u4 => Entails.sepExists_elim fun u5 => ?_
    refine Entails.sepExists_right 0xFFFFFFFFFFFFFFFF#64 (Entails.sepExists_right u0
      (Entails.sepExists_right u1 (Entails.sepExists_right u2
      (Entails.sepExists_right u3 (Entails.sepExists_right u4
      (Entails.sepExists_right u5 (Entails.sepExists_right w7
      (Entails.sepExists_right w8 (Entails.sepExists_right w9
      (Entails.sepExists_right w10 ?_))))))))))
    dsimp only [words6At, words11At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [pure_true, emp_sepConj]
    exact Entails.of_eq (by ac_rfl)
  | ok r =>
    dsimp only [signedPreKeyResultAt, decodeSpkDetached]
    refine Entails.trans (spkStruct_unpack A ret r.signedPreKey) ?_
    refine Entails.sepExists_elim fun w0 => Entails.sepExists_elim fun w1 =>
      Entails.sepExists_elim fun w2 => Entails.sepExists_elim fun w3 =>
      Entails.sepExists_elim fun w4 => Entails.sepExists_elim fun w5 =>
      Entails.sepExists_elim fun w6 => Entails.sepExists_elim fun w7 =>
      Entails.sepExists_elim fun w8 => Entails.sepExists_elim fun w9 =>
      Entails.sepExists_elim fun w10 => ?_
    refine Entails.sepExists_right w0 (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right w3
      (Entails.sepExists_right w4 (Entails.sepExists_right w5
      (Entails.sepExists_right w6 (Entails.sepExists_right w7
      (Entails.sepExists_right w8 (Entails.sepExists_right w9
      (Entails.sepExists_right w10 ?_))))))))))
    dsimp only [spkStructDetached]
    have hpull :
        (words11At ret w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
          ⌜w2 = BitVec.ofNat 64 r.signedPreKey.publicKey.length ∧
            w5 = BitVec.ofNat 64 r.signedPreKey.privateKey.length ∧
            w8 = BitVec.ofNat 64 r.signedPreKey.signature.length ∧
            w9 = r.signedPreKey.timestamp ∧
            w10.extractLsb' 0 32 = r.signedPreKey.id ∧
            w0 ≠ 0xFFFFFFFFFFFFFFFF#64⌝ ∗
          SpqrV1.Alloc.vecU8Buf A w0 w1 r.signedPreKey.publicKey ∗
          SpqrV1.Alloc.vecU8Buf A w3 w4 r.signedPreKey.privateKey ∗
          SpqrV1.Alloc.vecU8Buf A w6 w7 r.signedPreKey.signature) =
        (⌜w2 = BitVec.ofNat 64 r.signedPreKey.publicKey.length ∧
            w5 = BitVec.ofNat 64 r.signedPreKey.privateKey.length ∧
            w8 = BitVec.ofNat 64 r.signedPreKey.signature.length ∧
            w9 = r.signedPreKey.timestamp ∧
            w10.extractLsb' 0 32 = r.signedPreKey.id ∧
            w0 ≠ 0xFFFFFFFFFFFFFFFF#64⌝ ∗
          words11At ret w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
          SpqrV1.Alloc.vecU8Buf A w0 w1 r.signedPreKey.publicKey ∗
          SpqrV1.Alloc.vecU8Buf A w3 w4 r.signedPreKey.privateKey ∗
          SpqrV1.Alloc.vecU8Buf A w6 w7 r.signedPreKey.signature) := by ac_rfl
    rw [hpull]
    refine Entails.pure_left fun hprops => ?_
    have hgoal :
        words11At ret w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
          SpqrV1.Alloc.vecU8Buf A w0 w1 r.signedPreKey.publicKey ∗
          SpqrV1.Alloc.vecU8Buf A w3 w4 r.signedPreKey.privateKey ∗
          SpqrV1.Alloc.vecU8Buf A w6 w7 r.signedPreKey.signature ⊢
        ⌜w0 ≠ 0xFFFFFFFFFFFFFFFF#64⌝ ∗
          ⌜w2 = BitVec.ofNat 64 r.signedPreKey.publicKey.length ∧
            w5 = BitVec.ofNat 64 r.signedPreKey.privateKey.length ∧
            w8 = BitVec.ofNat 64 r.signedPreKey.signature.length ∧
            w9 = r.signedPreKey.timestamp ∧
            w10.extractLsb' 0 32 = r.signedPreKey.id ∧
            w0 ≠ 0xFFFFFFFFFFFFFFFF#64⌝ ∗
          words11At ret w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
          SpqrV1.Alloc.vecU8Buf A w0 w1 r.signedPreKey.publicKey ∗
          SpqrV1.Alloc.vecU8Buf A w3 w4 r.signedPreKey.privateKey ∗
          SpqrV1.Alloc.vecU8Buf A w6 w7 r.signedPreKey.signature :=
      Entails.pure_right hprops.2.2.2.2.2 (Entails.pure_right hprops (Entails.refl _))
    exact Entails.trans hgoal (Entails.of_eq (by ac_rfl))

private theorem cells_pack_5_376_p (sp a0 a1 a2 a3 a4 : BitVec 64) :
    ((sp - 376#64) ↦₆₄ a0) ∗ ((sp - 368#64) ↦₆₄ a1) ∗ ((sp - 360#64) ↦₆₄ a2) ∗
      ((sp - 352#64) ↦₆₄ a3) ∗ ((sp - 344#64) ↦₆₄ a4) ⊢ cells (sp - 376#64) 5 := by
  rw [cells_sub_5_376_eq]
  exact Entails.sepExists_right a0 (Entails.sepExists_right a1 (Entails.sepExists_right a2
    (Entails.sepExists_right a3 (Entails.sepExists_right a4 (Entails.refl _)))))

private theorem cells_pack_5_336_p (sp a0 a1 a2 a3 a4 : BitVec 64) :
    ((sp - 336#64) ↦₆₄ a0) ∗ ((sp - 328#64) ↦₆₄ a1) ∗ ((sp - 320#64) ↦₆₄ a2) ∗
      ((sp - 312#64) ↦₆₄ a3) ∗ ((sp - 304#64) ↦₆₄ a4) ⊢ cells (sp - 336#64) 5 := by
  rw [cells_sub_5_336_eq]
  exact Entails.sepExists_right a0 (Entails.sepExists_right a1 (Entails.sepExists_right a2
    (Entails.sepExists_right a3 (Entails.sepExists_right a4 (Entails.refl _)))))

private theorem cells_pack_5_296_p (sp a0 a1 a2 a3 a4 : BitVec 64) :
    ((sp - 296#64) ↦₆₄ a0) ∗ ((sp - 288#64) ↦₆₄ a1) ∗ ((sp - 280#64) ↦₆₄ a2) ∗
      ((sp - 272#64) ↦₆₄ a3) ∗ ((sp - 264#64) ↦₆₄ a4) ⊢ cells (sp - 296#64) 5 := by
  rw [cells_sub_5_296_eq]
  exact Entails.sepExists_right a0 (Entails.sepExists_right a1 (Entails.sepExists_right a2
    (Entails.sepExists_right a3 (Entails.sepExists_right a4 (Entails.refl _)))))

private theorem cells_pack_5_248_p (sp a0 a1 a2 a3 a4 : BitVec 64) :
    ((sp - 248#64) ↦₆₄ a0) ∗ ((sp - 240#64) ↦₆₄ a1) ∗ ((sp - 232#64) ↦₆₄ a2) ∗
      ((sp - 224#64) ↦₆₄ a3) ∗ ((sp - 216#64) ↦₆₄ a4) ⊢ cells (sp - 248#64) 5 := by
  rw [cells_sub_5_248_eq]
  exact Entails.sepExists_right a0 (Entails.sepExists_right a1 (Entails.sepExists_right a2
    (Entails.sepExists_right a3 (Entails.sepExists_right a4 (Entails.refl _)))))

private theorem cells_pack_6_200_p (sp a0 a1 a2 a3 a4 a5 : BitVec 64) :
    ((sp - 200#64) ↦₆₄ a0) ∗ ((sp - 192#64) ↦₆₄ a1) ∗ ((sp - 184#64) ↦₆₄ a2) ∗
      ((sp - 176#64) ↦₆₄ a3) ∗ ((sp - 168#64) ↦₆₄ a4) ∗ ((sp - 160#64) ↦₆₄ a5) ⊢
      cells (sp - 200#64) 6 := by
  rw [cells_sub_6_200_eq]
  exact Entails.sepExists_right a0 (Entails.sepExists_right a1 (Entails.sepExists_right a2
    (Entails.sepExists_right a3 (Entails.sepExists_right a4
      (Entails.sepExists_right a5 (Entails.refl _))))))

private theorem cells_pack_5_152_p (sp a0 a1 a2 a3 a4 : BitVec 64) :
    ((sp - 152#64) ↦₆₄ a0) ∗ ((sp - 144#64) ↦₆₄ a1) ∗ ((sp - 136#64) ↦₆₄ a2) ∗
      ((sp - 128#64) ↦₆₄ a3) ∗ ((sp - 120#64) ↦₆₄ a4) ⊢ cells (sp - 152#64) 5 := by
  rw [cells_sub_5_152_eq]
  exact Entails.sepExists_right a0 (Entails.sepExists_right a1 (Entails.sepExists_right a2
    (Entails.sepExists_right a3 (Entails.sepExists_right a4 (Entails.refl _)))))

private theorem cells_pack_6_96_p (sp a0 a1 a2 a3 a4 a5 : BitVec 64) :
    ((sp - 96#64) ↦₆₄ a0) ∗ ((sp - 88#64) ↦₆₄ a1) ∗ ((sp - 80#64) ↦₆₄ a2) ∗
      ((sp - 72#64) ↦₆₄ a3) ∗ ((sp - 64#64) ↦₆₄ a4) ∗ ((sp - 56#64) ↦₆₄ a5) ⊢
      cells (sp - 96#64) 6 := by
  rw [cells_sub_6_96_eq]
  exact Entails.sepExists_right a0 (Entails.sepExists_right a1 (Entails.sepExists_right a2
    (Entails.sepExists_right a3 (Entails.sepExists_right a4
      (Entails.sepExists_right a5 (Entails.refl _))))))

private theorem cells_pack_6_48_p (sp a0 a1 a2 a3 a4 a5 : BitVec 64) :
    ((sp - 48#64) ↦₆₄ a0) ∗ ((sp - 40#64) ↦₆₄ a1) ∗ ((sp - 32#64) ↦₆₄ a2) ∗
      ((sp - 24#64) ↦₆₄ a3) ∗ ((sp - 16#64) ↦₆₄ a4) ∗ ((sp - 8#64) ↦₆₄ a5) ⊢
      cells (sp - 48#64) 6 := by
  rw [cells_sub_6_48_eq]
  exact Entails.sepExists_right a0 (Entails.sepExists_right a1 (Entails.sepExists_right a2
    (Entails.sepExists_right a3 (Entails.sepExists_right a4
      (Entails.sepExists_right a5 (Entails.refl _))))))

private theorem frame48_pack_groups_p (sp : BitVec 64) :
    spkPollSlack sp ∗
      (cells (sp - 376#64) 5 ∗ cells (sp - 336#64) 5 ∗ cells (sp - 296#64) 5) ∗
      cells (sp - 248#64) 5 ∗
      cells (sp - 200#64) 6 ∗ cells (sp - 152#64) 5 ∗
      cells (sp - 96#64) 6 ∗ cells (sp - 48#64) 6 ⊢
      cells (sp - 384#64) 48 := by
  rw [cells_48_split sp]
  dsimp only [spkScratch15]
  exact Entails.of_eq (by ac_rfl)

private theorem spkEpiPost_pack_p (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustAlloc) (calleeStk : Nat) (x : PkPollGhost) (s0 sf : State)
    (ans : PkAns SignedPreKeyRecord) (D : SepProp)
    (o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 : BitVec 64)
    (a0 b2 b3 b4 c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 e5 f0 f1 f2 f3 f4 : BitVec 64)
    (hpack : words11At x.out o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 ∗ D ⊢ spkAnsAt A x.out ans)
    (hans : ans = pkAnsOf SignedPreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
          sf.trace = s0.trace) :
    ((x.out ↦₆₄ o0) ∗ ((x.out + 8#64) ↦₆₄ o1) ∗ ((x.out + 16#64) ↦₆₄ o2) ∗
      ((x.out + 24#64) ↦₆₄ o3) ∗ ((x.out + 32#64) ↦₆₄ o4) ∗ ((x.out + 40#64) ↦₆₄ o5) ∗
      ((x.out + 48#64) ↦₆₄ o6) ∗ ((x.out + 56#64) ↦₆₄ o7) ∗ ((x.out + 64#64) ↦₆₄ o8) ∗
      ((x.out + 72#64) ↦₆₄ o9) ∗ ((x.out + 80#64) ↦₆₄ o10)) ∗ D ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 1#8) ∗
      dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 384#64) calleeStk ∗
      (spkPollSlack s0.sp ∗
        ((((s0.sp - 376#64) ↦₆₄ a0) ∗ ((s0.sp - 368#64) ↦₆₄ o7) ∗ ((s0.sp - 360#64) ↦₆₄ o8) ∗
          ((s0.sp - 352#64) ↦₆₄ o9) ∗ ((s0.sp - 344#64) ↦₆₄ o10)) ∗
         (((s0.sp - 336#64) ↦₆₄ o5) ∗ ((s0.sp - 328#64) ↦₆₄ o6) ∗ ((s0.sp - 320#64) ↦₆₄ b2) ∗
          ((s0.sp - 312#64) ↦₆₄ b3) ∗ ((s0.sp - 304#64) ↦₆₄ b4)) ∗
         (((s0.sp - 296#64) ↦₆₄ c0) ∗ ((s0.sp - 288#64) ↦₆₄ c1) ∗ ((s0.sp - 280#64) ↦₆₄ c2) ∗
          ((s0.sp - 272#64) ↦₆₄ c3) ∗ ((s0.sp - 264#64) ↦₆₄ c4))) ∗
        (((s0.sp - 248#64) ↦₆₄ d0) ∗ ((s0.sp - 240#64) ↦₆₄ d1) ∗ ((s0.sp - 232#64) ↦₆₄ d2) ∗
          ((s0.sp - 224#64) ↦₆₄ d3) ∗ ((s0.sp - 216#64) ↦₆₄ d4)) ∗
        (((s0.sp - 200#64) ↦₆₄ e0) ∗ ((s0.sp - 192#64) ↦₆₄ e1) ∗ ((s0.sp - 184#64) ↦₆₄ e2) ∗
          ((s0.sp - 176#64) ↦₆₄ e3) ∗ ((s0.sp - 168#64) ↦₆₄ e4) ∗ ((s0.sp - 160#64) ↦₆₄ e5)) ∗
        (((s0.sp - 152#64) ↦₆₄ f0) ∗ ((s0.sp - 144#64) ↦₆₄ f1) ∗ ((s0.sp - 136#64) ↦₆₄ f2) ∗
          ((s0.sp - 128#64) ↦₆₄ f3) ∗ ((s0.sp - 120#64) ↦₆₄ f4)) ∗
        (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ⊢
      (spkGetPollInnerSpec rd pathOk A calleeStk).post x s0 sf := by
  have hans' : words11At x.out o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 ∗ D ⊢
      ∃∗ a : PkAns SignedPreKeyRecord,
        ⌜a = pkAnsOf SignedPreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
            sf.trace = s0.trace⌝ ∗
        spkAnsAt A x.out a :=
    Entails.trans hpack (spkAns_intro rd A x s0 sf ans hans)
  dsimp only [words11At] at hans'
  have hsaved :
      (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ⊢
      cells (s0.sp - 96#64) 6 ∗ cells (s0.sp - 48#64) 6 := by
    have hsplit :
        (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
         ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
         ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) =
        ((((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25)) ∗
         (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) := by
      ac_rfl
    rw [hsplit]
    exact sepConj_mono
      (cells_pack_6_96_p s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28)
        (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25))
      (cells_pack_6_48_p s0.sp (s0.readReg64 .x24) (s0.readReg64 .x23)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
  have hcells := Entails.trans
    (sepConj_mono_right
      (sepConj_mono
        (sepConj_mono (cells_pack_5_376_p s0.sp a0 o7 o8 o9 o10)
          (sepConj_mono (cells_pack_5_336_p s0.sp o5 o6 b2 b3 b4)
            (cells_pack_5_296_p s0.sp c0 c1 c2 c3 c4)))
        (sepConj_mono (cells_pack_5_248_p s0.sp d0 d1 d2 d3 d4)
          (sepConj_mono (cells_pack_6_200_p s0.sp e0 e1 e2 e3 e4 e5)
            (sepConj_mono (cells_pack_5_152_p s0.sp f0 f1 f2 f3 f4) hsaved)))))
    (frame48_pack_groups_p s0.sp)
  dsimp only [spkGetPollInnerSpec]
  have hassoc :
      (((x.out ↦₆₄ o0) ∗ ((x.out + 8#64) ↦₆₄ o1) ∗ ((x.out + 16#64) ↦₆₄ o2) ∗
        ((x.out + 24#64) ↦₆₄ o3) ∗ ((x.out + 32#64) ↦₆₄ o4) ∗ ((x.out + 40#64) ↦₆₄ o5) ∗
        ((x.out + 48#64) ↦₆₄ o6) ∗ ((x.out + 56#64) ↦₆₄ o7) ∗ ((x.out + 64#64) ↦₆₄ o8) ∗
        ((x.out + 72#64) ↦₆₄ o9) ∗ ((x.out + 80#64) ↦₆₄ o10)) ∗ D ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 1#8) ∗
        dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 384#64) calleeStk ∗
        (spkPollSlack s0.sp ∗
          ((((s0.sp - 376#64) ↦₆₄ a0) ∗ ((s0.sp - 368#64) ↦₆₄ o7) ∗ ((s0.sp - 360#64) ↦₆₄ o8) ∗
            ((s0.sp - 352#64) ↦₆₄ o9) ∗ ((s0.sp - 344#64) ↦₆₄ o10)) ∗
           (((s0.sp - 336#64) ↦₆₄ o5) ∗ ((s0.sp - 328#64) ↦₆₄ o6) ∗ ((s0.sp - 320#64) ↦₆₄ b2) ∗
            ((s0.sp - 312#64) ↦₆₄ b3) ∗ ((s0.sp - 304#64) ↦₆₄ b4)) ∗
           (((s0.sp - 296#64) ↦₆₄ c0) ∗ ((s0.sp - 288#64) ↦₆₄ c1) ∗ ((s0.sp - 280#64) ↦₆₄ c2) ∗
            ((s0.sp - 272#64) ↦₆₄ c3) ∗ ((s0.sp - 264#64) ↦₆₄ c4))) ∗
          (((s0.sp - 248#64) ↦₆₄ d0) ∗ ((s0.sp - 240#64) ↦₆₄ d1) ∗ ((s0.sp - 232#64) ↦₆₄ d2) ∗
            ((s0.sp - 224#64) ↦₆₄ d3) ∗ ((s0.sp - 216#64) ↦₆₄ d4)) ∗
          (((s0.sp - 200#64) ↦₆₄ e0) ∗ ((s0.sp - 192#64) ↦₆₄ e1) ∗ ((s0.sp - 184#64) ↦₆₄ e2) ∗
            ((s0.sp - 176#64) ↦₆₄ e3) ∗ ((s0.sp - 168#64) ↦₆₄ e4) ∗ ((s0.sp - 160#64) ↦₆₄ e5)) ∗
          (((s0.sp - 152#64) ↦₆₄ f0) ∗ ((s0.sp - 144#64) ↦₆₄ f1) ∗ ((s0.sp - 136#64) ↦₆₄ f2) ∗
            ((s0.sp - 128#64) ↦₆₄ f3) ∗ ((s0.sp - 120#64) ↦₆₄ f4)) ∗
          (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
            ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
            ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))) =
      ((((x.out ↦₆₄ o0) ∗ ((x.out + 8#64) ↦₆₄ o1) ∗ ((x.out + 16#64) ↦₆₄ o2) ∗
        ((x.out + 24#64) ↦₆₄ o3) ∗ ((x.out + 32#64) ↦₆₄ o4) ∗ ((x.out + 40#64) ↦₆₄ o5) ∗
        ((x.out + 48#64) ↦₆₄ o6) ∗ ((x.out + 56#64) ↦₆₄ o7) ∗ ((x.out + 64#64) ↦₆₄ o8) ∗
        ((x.out + 72#64) ↦₆₄ o9) ∗ ((x.out + 80#64) ↦₆₄ o10)) ∗ D) ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 1#8) ∗
        dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 384#64) calleeStk ∗
        (spkPollSlack s0.sp ∗
          ((((s0.sp - 376#64) ↦₆₄ a0) ∗ ((s0.sp - 368#64) ↦₆₄ o7) ∗ ((s0.sp - 360#64) ↦₆₄ o8) ∗
            ((s0.sp - 352#64) ↦₆₄ o9) ∗ ((s0.sp - 344#64) ↦₆₄ o10)) ∗
           (((s0.sp - 336#64) ↦₆₄ o5) ∗ ((s0.sp - 328#64) ↦₆₄ o6) ∗ ((s0.sp - 320#64) ↦₆₄ b2) ∗
            ((s0.sp - 312#64) ↦₆₄ b3) ∗ ((s0.sp - 304#64) ↦₆₄ b4)) ∗
           (((s0.sp - 296#64) ↦₆₄ c0) ∗ ((s0.sp - 288#64) ↦₆₄ c1) ∗ ((s0.sp - 280#64) ↦₆₄ c2) ∗
            ((s0.sp - 272#64) ↦₆₄ c3) ∗ ((s0.sp - 264#64) ↦₆₄ c4))) ∗
          (((s0.sp - 248#64) ↦₆₄ d0) ∗ ((s0.sp - 240#64) ↦₆₄ d1) ∗ ((s0.sp - 232#64) ↦₆₄ d2) ∗
            ((s0.sp - 224#64) ↦₆₄ d3) ∗ ((s0.sp - 216#64) ↦₆₄ d4)) ∗
          (((s0.sp - 200#64) ↦₆₄ e0) ∗ ((s0.sp - 192#64) ↦₆₄ e1) ∗ ((s0.sp - 184#64) ↦₆₄ e2) ∗
            ((s0.sp - 176#64) ↦₆₄ e3) ∗ ((s0.sp - 168#64) ↦₆₄ e4) ∗ ((s0.sp - 160#64) ↦₆₄ e5)) ∗
          (((s0.sp - 152#64) ↦₆₄ f0) ∗ ((s0.sp - 144#64) ↦₆₄ f1) ∗ ((s0.sp - 136#64) ↦₆₄ f2) ∗
            ((s0.sp - 128#64) ↦₆₄ f3) ∗ ((s0.sp - 120#64) ↦₆₄ f4)) ∗
          (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
            ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
            ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))) := by
    ac_rfl
  rw [hassoc]
  exact sepConj_mono hans'
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hcells))))))

/-! ## 3. Placed Callee Cell Wrappers & Outer Bridge -/

theorem decimal_cells_placed_ok [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {decStk calleeStk : Nat}
    (hDecimal : subroutine_ok prog (lsmpl.base 597) (decimalSpecPlaced A decStk))
    (hFs : TraceFsSound prog)
    (hle : decStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 597)
      (StoreKit.withLsCodeRoLoaded lsmpl (decimalCellsSpec A calleeStk)) := by
  intro ⟨id, ret, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp hcl
  rcases StoreKit.extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  simp only [decimalCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hfsp⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - decStk)
  let callG : DecimalGhost := ⟨id, ret⟩
  have hpre_base : s0.mem ⊨ (decimalSpecPlaced A decStk).pre callG s0 ∗ (stkRem ∗ R) := by
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
  have hpre_fs := withFsInv_pre_intro (withFsInv_entry s0) hpre_base
  have hDecFs := subroutine_ok_withFsInv hFs hDecimal s0.fs.files s0.trace
  rcases hDecFs callG (stkRem ∗ R) s0 hpc hrun hpre_fs hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨_code, _hex, hq⟩ | ⟨_hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    obtain ⟨hfs_sf, hq⟩ := withFsInv_post_elim hq
    dsimp only [StoreKit.withLsCodeRoLoaded, decimalSpecPlaced, decimalCellsSpec, callG,
      keyName] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq⟩
    have hfiles : sf.fs.files = s0.fs.files :=
      files_eq_at_callback hfs_sf (evs := []) (by rw [htr, List.append_nil]) (by simp [NoFsEv])
    dsimp only [vecU8] at hq
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨nCap, nPtr, hq⟩
    refine ⟨nCap, nPtr, ?_⟩
    rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf] at hq
    dsimp only [vecHeader] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr, hfiles⟩, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [withFsInv, StoreKit.withLsCodeRoLoaded, decimalSpecPlaced,
      decimalCellsSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact allowPanic_frame (F := stkRem) (fun h => h) (by simpa only [sepConj_assoc] using hq.2)
  · dsimp only [withFsInv] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact False.elim (allowPanic_not_exited hq.2)
  · dsimp only [withFsInv, decimalSpecPlaced, StoreKit.withLsCodeRoLoaded] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact False.elim (not_satisfies_false_sepConj hq.2)

theorem dirGet_cells_placed_ok [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk calleeStk : Nat} {F0 : FsFiles}
    (hGet : subroutine_ok prog (lsmpl.base 589) (dirGetSpecPlaced rd pathOk A getStk))
    (hle : getStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 589)
      (StoreKit.withLsCodeRoLoaded lsmpl (dirGetCellsSpec rd pathOk A F0 calleeStk)) := by
  intro ⟨ret, self, dir, nCap, nPtr, id, o0, o1, o2, o3, o4, o5, fsp⟩ R s0 hpc hrun hpre hsp hcl
  rcases StoreKit.extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  simp only [dirGetCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hfsp, hfiles, hnameOk⟩, hmem⟩
  subst hfsp
  rcases hnameOk with ⟨hnlen, hdlen, hpOk⟩
  have hx3_nat : (s0.readReg64 .x3).toNat = (keyName id).length := by
    rw [hx3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [stackAt_sub_split s0.sp hle hhi, vecU8Buf_eq_bytes_sep_rest A nCap nPtr (keyName id)] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - getStk)
  let nameRem := vecU8BufRest A nCap nPtr (keyName id)
  let callG : DirGetGhost := ⟨ret, self, dir, nPtr, keyName id, false⟩
  have hpre0 : s0.mem ⊨ (dirGetSpecPlaced rd pathOk A getStk).pre callG s0 ∗
      (nameRem ∗ stkRem ∗ R) := by
    unfold dirGetSpecPlaced
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [callG, SpqrV1.ChainProofs.bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte, memRegion_48_cells, sepExists_sepConj_left,
      sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o5, o4, o3, o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3_nat, hnlen, hdlen, hpOk⟩, ?_⟩
    dsimp only [stkRem, nameRem]
    dsimp only [SpqrV1.ChainProofs.bytesAt] at hmem
    simp only [Bool.false_eq_true, ↓reduceIte] at hmem
    convert hmem using 1; ac_rfl
  rcases hGet callG (nameRem ∗ stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨_code, _hex, hq⟩ | ⟨_hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, dirGetSpecPlaced, dirGetCellsSpec, callG,
      SpqrV1.ChainProofs.bytesAt] at hq ⊢
    simp only [Bool.false_eq_true, ↓reduceIte] at hq
    rw [hfiles] at hq
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨gr, hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hdisj, hq⟩
    have hq' := Satisfies.mono (sepConj_mono_left (getResultAt_unpack_p A ret gr)) hq
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq' ⊢
    rcases hq' with ⟨g0, g1, g2, g3, g4, g5, hq'⟩
    refine ⟨gr, g0, g1, g2, g3, g4, g5, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hdisj, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi, vecU8Buf_eq_bytes_sep_rest A nCap nPtr (keyName id)]
    dsimp only [SpqrV1.ChainProofs.bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [stkRem, nameRem] at hq'
    convert hq' using 1; ac_rfl
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, dirGetSpecPlaced, dirGetCellsSpec] at hq ⊢
    exact allowPanic_frame (F := nameRem ∗ stkRem) (fun h => h) (by simpa only [sepConj_assoc] using hq)
  · exact False.elim (allowPanic_not_exited hq)
  · dsimp only [dirGetSpecPlaced, StoreKit.withLsCodeRoLoaded] at hq
    exact False.elim (not_satisfies_false_sepConj hq)

theorem decodeSpk_cells_placed_ok [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {calleeStk : Nat}
    (hDec : subroutine_ok prog (lsmpl.base 595) (decodeSignedPreKeyPlacedSpec A))
    (hle : smallRootStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 595)
      (StoreKit.withLsCodeRoLoaded lsmpl (decodeSpkCellsSpec A calleeStk)) := by
  intro ⟨ret, bCap, bPtr, bytes, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, fsp⟩
    R s0 hpc hrun hpre hsp hcl
  rcases StoreKit.extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  simp only [decodeSpkCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hfsp, hlen_pos, hlen_lt⟩, hmem⟩
  subst hfsp
  have hx2_nat : (s0.readReg64 .x2).toNat = bytes.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [stackAt_sub_split s0.sp hle hhi, vecU8Buf_eq_bytes_sep_rest A bCap bPtr bytes] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - smallRootStack)
  let bytesRem := vecU8BufRest A bCap bPtr bytes
  let callG : DecodeGhost := ⟨bPtr, bytes, ret⟩
  have hpre0 : s0.mem ⊨ (decodeSignedPreKeyPlacedSpec A).pre callG s0 ∗
      (bytesRem ∗ stkRem ∗ R) := by
    change s0.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl (decodeSignedPreKeyRawSpec A)).pre callG s0 ∗
      (bytesRem ∗ stkRem ∗ R)
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [decodeSignedPreKeyRawSpec, callG]
    simp only [memRegion_88_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, c0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2_nat, hlen_pos, hlen_lt⟩, ?_⟩
    dsimp only [stkRem, bytesRem]
    dsimp only [SpqrV1.ChainProofs.bytesAt] at hmem
    simp only [Bool.false_eq_true, ↓reduceIte] at hmem
    convert hmem using 1; ac_rfl
  rcases hDec callG (bytesRem ∗ stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨_code, _hex, hq⟩ | ⟨_hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, LibsignalTripleRatchet.withLsCodeRoLoaded,
      decodeSignedPreKeyPlacedSpec, decodeSignedPreKeyRawSpec, decodeSpkCellsSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq⟩
    rw [sepConj_assoc] at hq
    have hq' := Satisfies.mono
      (sepConj_mono_left
        (signedPreKeyResultAt_unpack_p A ret (SignedPreKeyRecord.deserialize bytes)))
      hq
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq' ⊢
    rcases hq' with ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, hq'⟩
    refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi, vecU8Buf_eq_bytes_sep_rest A bCap bPtr bytes]
    dsimp only [SpqrV1.ChainProofs.bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [stkRem, bytesRem] at hq'
    convert hq' using 1; ac_rfl
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, LibsignalTripleRatchet.withLsCodeRoLoaded,
      decodeSignedPreKeyPlacedSpec, decodeSignedPreKeyRawSpec, decodeSpkCellsSpec] at hq ⊢
    exact allowPanic_frame (F := bytesRem ∗ stkRem) (fun h => h) (by simpa only [sepConj_assoc] using hq)
  · exact False.elim (allowPanic_not_exited hq)
  · dsimp only [decodeSignedPreKeyPlacedSpec, decodeSignedPreKeyRawSpec,
      LibsignalTripleRatchet.withLsCodeRoLoaded] at hq
    exact False.elim (not_satisfies_false_sepConj hq)

theorem deallocBuf_cells_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {A : RustAlloc} {H : LibsignalHooks} [IsLsBlockProg prog i H] {calleeStk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hle : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustDeallocSymCli)
      (StoreKit.withLsCodeRoLoaded lsmpl (deallocBufCellsSpec A calleeStk)) := by
  have hDealloc := dealloc_lscro_of_cli (callerProg := prog) hC hi
  intro ⟨cap, ptr, bytes, fsp⟩ R s0 hpc hrun hpre hsp hcl
  rcases StoreKit.extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  simp only [deallocBufCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hfsp, hcap⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  have hmem' := Satisfies.mono (sepConj_mono_left (vecU8Buf_ne_zero_dealloc A bytes hcap)) hmem
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hmem'
  rcases hmem' with ⟨hlay, hmem'⟩
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - extHookStack)
  have hx1_nat : (s0.readReg64 .x1).toNat = cap.toNat := congrArg BitVec.toNat hx1
  have hx2_nat : (s0.readReg64 .x2).toNat = 1 := by rw [hx2]; rfl
  have hpre0 : s0.mem ⊨
      (StoreKit.withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack A extHookStack)).pre
        (ptr, cap.toNat, 1) s0 ∗ (stkRem ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1_nat, hx2_nat, hlay⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem' using 1; ac_rfl
  rcases hDealloc (ptr, cap.toNat, 1) (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩⟩
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
    exact False.elim (not_satisfies_false_sepConj hq)
  · dsimp only [StoreKit.withLsCodeRoLoaded, rustDeallocExternSpecWithStack] at hq
    exact False.elim (not_satisfies_false_sepConj hq)
  · dsimp only [StoreKit.withLsCodeRoLoaded, rustDeallocExternSpecWithStack] at hq
    exact False.elim (not_satisfies_false_sepConj hq)

theorem dropSpeWord_cells_placed_ok [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {calleeStk : Nat}
    (hDrop : subroutine_ok prog (lsmpl.base 553) (dropSpeWordSpecPlaced A))
    (hle : dropSpeStackX ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 553)
      (StoreKit.withLsCodeRoLoaded lsmpl (dropSpeWordCellsSpec A calleeStk)) := by
  intro ⟨a, d1, d2, d3, d4, d5, fsp⟩ R s0 hpc hrun hpre hsp hcl
  rcases StoreKit.extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  simp only [dropSpeWordCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hfsp⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - dropSpeStackX)
  let callG : DropSpeWordGhost := ⟨a, 14⟩
  have hpre0 : s0.mem ⊨ (dropSpeWordSpecPlaced A).pre callG s0 ∗ (stkRem ∗ R) := by
    unfold dropSpeWordSpecPlaced
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [callG]
    simp only [memRegion_40_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨d5, d4, d3, d2, d1, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, Or.inr trivial⟩, ?_⟩
    dsimp only [words6At, stkRem] at hmem ⊢
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    convert hmem using 1; ac_rfl
  rcases hDrop callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, dropSpeWordSpecPlaced, dropSpeWordCellsSpec,
      callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq⟩
    simp only [memRegion_48_cells, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨c5, c4, c3, c2, c1, c0, hq⟩
    refine ⟨c0, c1, c2, c3, c4, c5, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · dsimp only [dropSpeWordSpecPlaced, StoreKit.withLsCodeRoLoaded] at hq
    exact False.elim (not_satisfies_false_sepConj hq)
  · dsimp only [dropSpeWordSpecPlaced, StoreKit.withLsCodeRoLoaded] at hq
    exact False.elim (not_satisfies_false_sepConj hq)
  · dsimp only [dropSpeWordSpecPlaced, StoreKit.withLsCodeRoLoaded] at hq
    exact False.elim (not_satisfies_false_sepConj hq)

theorem spkGetPoll_placed_of_inner [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {A : RustAlloc} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {calleeStk stk : Nat}
    (hInner : calleeStk ≤ 2 ^ 64 →
      subroutine_ok prog entry
        (StoreKit.withLsCodeRoLoaded lsmpl (spkGetPollInnerSpec rd pathOk A calleeStk)))
    (hstk : 0x180 + calleeStk ≤ stk) :
    subroutine_ok prog entry (spkGetPollSpecPlaced rd pathOk A stk) := by
  intro x R s0 hpc hrun hpre hsp hcl
  unfold spkGetPollSpecPlaced pkGetPollSpecOfPlaced at hpre
  rcases StoreKit.extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  dsimp only [] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hname, hsize⟩, hmem⟩
  dsimp only [pkBoxAt] at hmem
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine memRegion_bound_of_pointsTo64 (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk)
      (a := x.fut) (v := x.self)
      (R := ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
        memRegion (x.fut + 0xd#64) 3 ∗
        dirAt A x.self x.dir ∗ memRegion x.out 88 ∗ A.pool ∗ R) ?_
    dsimp only [stackAt] at hmem
    convert hmem using 1; ac_rfl
  have hcal_hi : calleeStk ≤ 2 ^ 64 := by omega
  have hframe_hi : calleeStk + 384 ≤ 2 ^ 64 := by omega
  rw [stackAt_sub_split s0.sp (subStk := calleeStk + 384) (by omega) hstk_hi,
    stackAt_spkPoll_frame s0.sp hframe_hi] at hmem
  let F_extra := memRegion (x.fut + 0xd#64) 3 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 384))
  have hpre_in : s0.mem ⊨
      (StoreKit.withLsCodeRoLoaded lsmpl (spkGetPollInnerSpec rd pathOk A calleeStk)).pre x s0 ∗
      (F_extra ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [spkGetPollInnerSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hname, hsize⟩, ?_⟩
    dsimp only [F_extra]
    convert hmem using 1; ac_rfl
  rcases hInner hcal_hi x (F_extra ∗ R) s0 hpc hrun hpre_in hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨_code, _hex, hq⟩ | ⟨_hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, spkGetPollInnerSpec, spkGetPollSpecPlaced,
      pkGetPollSpecOfPlaced, pkBoxAt] at hq ⊢
    rw [stackAt_sub_split s0.sp (subStk := calleeStk + 384) (by omega) hstk_hi,
      stackAt_spkPoll_frame s0.sp hframe_hi]
    dsimp only [F_extra] at hq
    convert hq using 1; ac_rfl
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, spkGetPollInnerSpec, spkGetPollSpecPlaced,
      pkGetPollSpecOfPlaced] at hq ⊢
    exact allowPanic_frame (F := F_extra) (fun h => h) (by simpa only [sepConj_assoc] using hq)
  · exact False.elim (allowPanic_not_exited hq)
  · dsimp only [StoreKit.withLsCodeRoLoaded, spkGetPollSpecPlaced, pkGetPollSpecOfPlaced] at hq
    exact False.elim (not_satisfies_false_sepConj hq)

/-! ## 4. Placed Cut Combinators & Shared Epilogue (`+344` .. `ret`) on `lsProg_571 H` -/

theorem sepWP_frame_cut_placed [LibsignalPlacement] {prog : Program} {mid target_pc : BitVec 64}
    {s : State} {P P_sub Q_sub F : SepProp} {post : State → SepProp → Prop}
    {Φ : State → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P_sub (fun sm Pm => sm.spAligned = true ∧ Φ sm ∧ (Pm ⊢ Q_sub)))
    (hP : P ⊢ P_sub ∗ F := by
      try simp only [words11At, words6At, spkSavedAt,
        sp248_8, sp248_16, sp200_8, sp200_16, sp200_24, sp200_32, sp200_40,
        sp200_48, sp200_56, sp200_64, sp200_72, sp200_80]
      sep_frame)
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → sm.spAligned = true →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → Φ sm → SepWP prog target_pc sm (Q_sub ∗ F) post) :
    SepWP prog target_pc s P post := by
  refine SepWP.weaken_pre hP ?_
  refine StoreKit.sepWP_seq_lscro (mid := mid) hcrl ?_
  exact sepWP_frame_right (SepWP.mono h1 fun sm Pm hpcm hrunm ⟨hspm, hΦm, hent⟩ hcrlm =>
    SepWP.weaken_pre (sepConj_mono_left hent) (h2 sm hpcm hrunm hspm hcrlm hΦm))

theorem sepWPp_frame_cut_placed [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P_sub Q_sub F : SepProp} {post Qp : State → SepProp → Prop}
    {Φ : State → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P_sub (fun sm Pm => sm.spAligned = true ∧ Φ sm ∧ (Pm ⊢ Q_sub)))
    (hP : P ⊢ P_sub ∗ F := by
      try simp only [words11At, words6At, spkSavedAt,
        sp248_8, sp248_16, sp200_8, sp200_16, sp200_24, sp200_32, sp200_40,
        sp200_48, sp200_56, sp200_64, sp200_72, sp200_80]
      sep_frame)
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → sm.spAligned = true →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → Φ sm → SepWPp prog ret sm (Q_sub ∗ F) post Qp) :
    SepWPp prog ret s P post Qp := by
  refine SepWPp.weaken_pre hP ?_
  refine StoreKit.sepWPp_seq_lscro (mid := mid) hcrl ?_
  exact sepWP_frame_right (SepWP.mono h1 fun sm Pm hpcm hrunm ⟨hspm, hΦm, hent⟩ hcrlm =>
    SepWPp.weaken_pre (sepConj_mono_left hent) (h2 sm hpcm hrunm hspm hcrlm hΦm))

theorem epilogue_placed_ok [LibsignalPlacement] {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {A : RustAlloc} {calleeStk : Nat} {x : PkPollGhost} {R : SepProp}
    {s0 s : State} {ans : PkAns SignedPreKeyRecord} {D P : SepProp}
    {o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 : BitVec 64}
    {u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 : BitVec 64}
    {a0 b2 b3 b4 c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 e5 f0 f1 f2 f3 f4 : BitVec 64}
    (hpc : s.pc = (blkPl_571).base + bv% 344)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 384#64)
    (hvr : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx26 : s.readReg64 .x26 = o0)
    (hx25 : s.readReg64 .x25 = o1)
    (hx23 : s.readReg64 .x23 = o2)
    (hx24 : s.readReg64 .x24 = o3)
    (hx21 : s.readReg64 .x21 = o4)
    (hpack : words11At x.out o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 ∗ D ⊢ spkAnsAt A x.out ans)
    (hans : ans = pkAnsOf SignedPreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
          s.trace = s0.trace)
    (hP : P ⊢ spkEpiPre A calleeStk x s0 D
      u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10
      a0 o7 o8 o9 o10 o5 o6 b2 b3 b4 c0 c1 c2 c3 c4 d0 d1 d2 d3 d4
      e0 e1 e2 e3 e4 e5 f0 f1 f2 f3 f4 := by
        try simp only [spkEpiPre, words11At, words6At, spkSavedAt,
          sp248_8, sp248_16, sp200_8, sp200_16, sp200_24, sp200_32, sp200_32, sp200_40,
          sp200_48, sp200_56, sp200_64, sp200_72, sp200_80]
        sep_frame) :
    SepWP (lsProg_571 H) (s0.readReg64 .x30) s P
      (spkPostQ rd pathOk A calleeStk x R s0) := by
  refine SepWP.weaken_pre hP ?_
  dsimp only [lsProg_571, spkEpiPre, spkSavedAt, words11At, spkPostQ] at hpc ⊢
  clear hP
  wp_steps
  try
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨fun hm => Satisfies.mono (sepConj_mono_left ?_) hm, ?_, ?_⟩
  · refine Entails.trans (Entails.of_eq (by ac_rfl))
      (spkEpiPost_pack_p rd pathOk A calleeStk x s0 _ ans D
        o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10
        a0 b2 b3 b4 c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 e5 f0 f1 f2 f3 f4
        hpack (trace_ans_congr (s := s) rfl hans))
  · simp only [wp_norm, arm64_norm]
  · rw [CalleeSavedPreserved.iff_regs]
    simp only [wp_norm, arm64_norm, hvr]

end Placed

end CryptoVerification.SignalSession.Cli.Store.SpkGetPoll.Helpers
