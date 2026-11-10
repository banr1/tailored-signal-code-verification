/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4StoreSession -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1PlacedBudgetSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Steps
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# `HookSat`-Backed Budget-Threaded Stage P2 Entry Bridge (`Matched/M2BridgePlacedBudgetSat`)

Additive `HookSat (Rust.withPanics ext) lsBlackBoxU8Sym blackBoxSpecSat` sibling of
`LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudget`.
Carves `promoteMatchingSessionMatchStack16` (`1200` B) directly out of `stackAt sp rootStack`
(`262144` B), keeping all outer theorem conclusions token-identical to `M2BridgePlacedBudget`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudgetSat

noncomputable section

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (PublicKey)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (
  LibsignalPlacement lsBlackBoxU8Sym lsLogFilterAddr lsmpl lsρ withLsCodeLoaded
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (rootStack)
open CryptoVerification.LibsignalTripleRatchet.Getters (remoteIdentityOkAt)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost sessionStateAt)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost sessionRecordAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (processPrekeyActive10At)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (SepWPp.weaken_frame)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkPl_518 lsProg_518)
open scoped CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  SessionExtraRel stackAt_split_of_le
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  prevSessionsEmptyAt processPrekeyActive10At_eq_placed
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
  rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat (blackBoxSpecSat)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  PublicKeySerializeEnv publicKeySerializeEvents publicKeySerializeSpec
  publicKeySerializeSpecWithStack
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1PlacedBudgetSat (
  promoteMatchingSessionMatchBudgetSpec16 promoteMatchingSessionMatchSpec16
  promoteMatchingSessionMatchStack16 promote_matching_session_match_placed_ok_at_sat
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudget (
  stageP2_matched_08c0_to_094c_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudgetAux (
  StageP2MatchedBridgeEnv boxU8Buf_pk_serialize_entails_placed
  fitsEnv_publicKeySerialize_of_bridge memRegion_3e0_34_split_16_18_placed
  p2_seg1a_placed_wp p2_seg1b_placed_wp stack_root_to_pkSerialize_m2_placed
  stageP2Matched0868PrePlaced stageP2Matched094cPostPlaced stageP2MatchedBridgeEvents
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2OkPlacedBudgetAux (
  bind_sepWPp_nopanic_state sepWPp_lift_qp
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2PlacedBudget (
  bind_sepWP_lscro_steps_m2_placed call_lscro_nopanic_m2_placed
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

theorem hookSat_blackBox_withPanics_placed {ext : String → Option (State → State)}
    (h_bb : HookSat ext lsBlackBoxU8Sym blackBoxSpecSat) :
    HookSat (Rust.withPanics ext) lsBlackBoxU8Sym blackBoxSpecSat := by
  have hnp : Rust.isPanicSymbol lsBlackBoxU8Sym = false := by
    simp [Rust.isPanicSymbol, lsBlackBoxU8Sym]
  rcases h_bb with ⟨f, hf, hok⟩
  refine ⟨f, ?_, hok⟩
  simpa [Rust.withPanics, hnp] using hf

theorem stack_root_to_promoteMatch16 (sp : BitVec 64) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - promoteMatchingSessionMatchStack16) ∗
        stackAt sp promoteMatchingSessionMatchStack16 :=
  stackAt_split_of_le sp rootStack promoteMatchingSessionMatchStack16 (by decide) hn

/-! ## Stage P2 Matched Prefix Part A (`+0x0868 → +0x08c0`) and Composition under `HookSat` -/

set_option maxHeartbeats 800000 in
/-- `HookSat`-backed sibling of `M2BridgePlacedBudget.stageP2_matched_0868_to_08c0_placed`. -/
theorem stageP2_matched_0868_to_08c0_placed_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hser : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim)))
    (h_bb : HookSat (Rust.withPanics ext) lsBlackBoxU8Sym blackBoxSpecSat)
    (st : M.σ) (s : State)
    (sp coroPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt : BitVec 64)
    (msgVerByte b_4f1 : BitVec 8)
    (baseKey : PublicKey)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (hcur : r.currentSession = some sess)
    (hver : sess.state.version = msgVerByte.zeroExtend 32)
    (halice : sess.aliceBaseKey = baseKey.serialize)
    (hfits : FitsEnv M lim st PublicKeySerializeEnv)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + 0x868#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = kyberStorePtr)
    (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kyberStoreVt)
    (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr)
    (hx13 : s.readReg64 .x13 = preKeyStoreVt)
    (hx14 : s.readReg64 .x14 = localAddrPtr)
    (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = idStoreVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkStoreVt)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hx29 : s.readReg64 .x29 = sp + 0xc70#64) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) ((blkPl_518).base + 0x8c0#64) s
      (cells (coroPtr + 0x3f8#64) 6 ∗
       cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
       ((msgPtr + 0xf0#64) ↦₈ msgVerByte) ∗
       sessionRecordAt A.repAlloc (coroPtr + 0xe0#64) g r ∗
       memRegion (sp + 0x3e0#64) 34 ∗
       A.pool lim st s ∗
       stackAt sp rootStack)
      (fun sf P_f =>
        (P_f ⊢
          processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            kyberStorePtr kyberStoreVt ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
          ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
          ((msgPtr + 0xf0#64) ↦₈ msgVerByte) ∗
          sessionRecordAt A.repAlloc (coroPtr + 0xe0#64) g r ∗
          A.live (sf.readReg64 .x21) 33 1 ∗
          ((sf.readReg64 .x21) ↦ₛ baseKey.serialize) ∗
          ((sp + 0x3e0#64) ↦₆₄ 0#64) ∗
          ((sp + 0x3e8#64) ↦₈ 1#8) ∗
          memRegion (sp + 0x3e9#64) 7 ∗
          memRegion (sp + 0x3f0#64) 18 ∗
          A.pool lim (M.stepEvents publicKeySerializeEvents st) sf ∗
          stackAt sp rootStack) ∧
        sf.sp = sp ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x19 = coroPtr ∧
        sf.readReg64 .x26 = 33#64 ∧
        sf.readReg64 .x28 = sp + 0xa90#64 ∧
        sf.readReg64 .x29 = sp + 0xc70#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  have hroot_le : rootStack ≤ 2 ^ 64 := Nat.le_trans hsp_root (Nat.le_of_lt sp.isLt)
  have h1a := p2_seg1a_placed_wp (A := A) (lim := lim) ext st s coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt msgVerByte b_4f1
    hpc hrun hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24
  refine bind_sepWP_lscro_steps_m2_placed hcro h1a (by sep_focus)
    fun s1 _ hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hx0_1, hx19_1, _, hx22_1, hx23_1, hx24_1, hx25_1,
    _, _, hx28_1, hx29_1, hx30_1, hvregs1⟩
  have hsp1 : s1.sp = sp := hsp1_s.trans hsp_eq
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_pkSerialize_m2_placed sp hsp_root)) (by sep_focus) ?_
  have hφ_ser : s1.readReg64 .x0 = msgPtr + 0xa8#64 ∧ FitsEnv M lim st PublicKeySerializeEnv :=
    ⟨hx0_1, hfits⟩
  refine call_lscro_nopanic_m2_placed
    (spec := publicKeySerializeSpec M A lim)
    (x := (⟨msgPtr + 0xa8#64, baseKey⟩, st))
    (φ := s1.readReg64 .x0 = msgPtr + 0xa8#64 ∧ FitsEnv M lim st PublicKeySerializeEnv)
    (T := ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗ A.pool lim st s1 ∗
      stackAt sp (allocHookStack + 32))
    hcro1 (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hser)
    hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [publicKeySerializeSpec, publicKeySerializeSpecWithStack]; rw [hsp1])
    hφ_ser
    (by sep_focus)
    (hpan_false := fun _ => rfl)
    (hexit_false := fun _ _ => rfl)
    (hoom_false := fun _ => rfl)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 hsp2_al hcs2 hcro2 => ?_)
  dsimp only [publicKeySerializeSpec, publicKeySerializeSpecWithStack]
  rw [hsp1]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx1_2, htr2_1⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_pkSerialize_m2_placed sp hsp_root).symm) (by sep_focus) ?_
  let serPtr := s2.readReg64 .x0
  let st1 := M.stepEvents publicKeySerializeEvents st
  refine SepWPp.weaken_frame (boxU8Buf_pk_serialize_entails_placed A.repAlloc serPtr baseKey) (by sep_focus) ?_
  rcases hcs2 with ⟨hx19_cs2, _, _, hx22_cs2, hx23_cs2, hx24_cs2, hx25_cs2,
    _, _, hx28_cs2, hx29_cs2, hvregs_cs2⟩
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx22_2 : s2.readReg64 .x22 = spkStorePtr := hx22_cs2.trans hx22_1
  have hx23_2 : s2.readReg64 .x23 = coroPtr + 0xe0#64 := hx23_cs2.trans hx23_1
  have hx24_2 : s2.readReg64 .x24 = spkStoreVt := hx24_cs2.trans hx24_1
  have hx25_2 : s2.readReg64 .x25 = msgVerByte.zeroExtend 64 := hx25_cs2.trans hx25_1
  have h1b := p2_seg1b_placed_wp (A := A) (lim := lim) ext st1 s2 coroPtr serPtr spkStorePtr spkStoreVt msgVerByte
    hpc2 hrun2 rfl hx1_2 hx19_2 hx22_2 hx23_2 hx24_2 hx25_2
  refine bind_sepWP_lscro_steps_m2_placed hcro2 h1b (by sep_focus)
    fun s3 _ hpc3 hrun3 hcro3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hx0_3, hx1_3, hx2_3, hx3_3, hx8_3, hx19_3, hx21_3,
    _, _, _, _, hx26_3, _, hx28_3, hx29_3, hx30_3, hvregs3⟩
  have hsp3 : s3.sp = sp := hsp3_2.trans hsp2
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3_2] using hsp2_al
  rw [hsp2] at hx8_3
  conv => arg 4; rw [memRegion_3e0_34_split_16_18_placed sp]
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_promoteMatch16 sp hroot_le)) (by sep_focus) ?_
  have hlen33 : baseKey.serialize.length = 33 := by simp [PublicKey.serialize]
  have hprom := subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (promote_matching_session_match_placed_ok_at_sat (A := A.repAlloc)
      (callerProg := lsProg_518 (Rust.withPanics ext)) h_bb)
  have hφ_prom :
      s3.readReg64 .x0 = coroPtr + 0xe0#64 ∧
      s3.readReg64 .x1 = msgVerByte.zeroExtend 64 ∧
      s3.readReg64 .x2 = serPtr ∧
      s3.readReg64 .x3 = 33#64 ∧
      s3.readReg64 .x8 = sp + 0x3e0#64 ∧
      r.currentSession = some sess ∧
      sess.state.version = msgVerByte.zeroExtend 32 ∧
      sess.aliceBaseKey = baseKey.serialize ∧
      baseKey.serialize.length = 33 :=
    ⟨hx0_3, hx1_3, hx2_3, hx3_3, hx8_3, hcur, hver, halice, hlen33⟩
  refine call_lscro_nopanic_m2_placed
    (spec := promoteMatchingSessionMatchBudgetSpec16 A.repAlloc)
    (x := ⟨coroPtr + 0xe0#64, msgVerByte, serPtr, baseKey.serialize, sp + 0x3e0#64, g, r, sess⟩)
    (φ := s3.readReg64 .x0 = coroPtr + 0xe0#64 ∧
      s3.readReg64 .x1 = msgVerByte.zeroExtend 64 ∧
      s3.readReg64 .x2 = serPtr ∧
      s3.readReg64 .x3 = 33#64 ∧
      s3.readReg64 .x8 = sp + 0x3e0#64 ∧
      r.currentSession = some sess ∧
      sess.state.version = msgVerByte.zeroExtend 32 ∧
      sess.aliceBaseKey = baseKey.serialize ∧
      baseKey.serialize.length = 33)
    (T := sessionRecordAt A.repAlloc (coroPtr + 0xe0#64) g r ∗
      (serPtr ↦ₛ baseKey.serialize) ∗
      memRegion (sp + 0x3e0#64) 16 ∗
      stackAt sp promoteMatchingSessionMatchStack16)
    hcro3 hprom hpc3 hrun3 hsp3_al hx30_3
    (by
      dsimp only [promoteMatchingSessionMatchBudgetSpec16, withVmPreserved,
        promoteMatchingSessionMatchSpec16]
      rw [hsp3])
    hφ_prom
    (by sep_focus)
    (hpan_false := fun _ => rfl)
    (hexit_false := fun _ _ => rfl)
    (hoom_false := fun _ => rfl)
    (hnext := fun s4 _ hpc4 hrun4 hsp4_3 _ hcs4 hcro4 => ?_)
  dsimp only [promoteMatchingSessionMatchBudgetSpec16, withVmPreserved,
    promoteMatchingSessionMatchSpec16]
  rw [hsp3]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.pure_elim fun hvm4 => SepWPp.pure_elim fun htr4_3 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (A.pool_of_vmPreserved hvm4).symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_promoteMatch16 sp hroot_le).symm) (by sep_focus) ?_
  rcases hcs4 with ⟨hx19_cs4, _, hx21_cs4, _, _, _, _, hx26_cs4, _, hx28_cs4, hx29_cs4, hvregs_cs4⟩
  have hx21_4 : s4.readReg64 .x21 = serPtr := hx21_cs4.trans hx21_3
  refine SepWPp.done hpc4 hrun4 ⟨?_, hsp4_3.trans hsp3,
    htr4_3.trans (htr3_2.trans (htr2_1.trans htr1_s)),
    hx19_cs4.trans hx19_3,
    hx26_cs4.trans hx26_3,
    hx28_cs4.trans (hx28_3.trans (hx28_cs2.trans (hx28_1.trans hx28))),
    hx29_cs4.trans (hx29_3.trans (hx29_cs2.trans (hx29_1.trans hx29))),
    hvregs_cs4.trans (hvregs3.trans (hvregs_cs2.trans hvregs1)),
    hcro4⟩
  rw [hx21_4]
  dsimp +zetaDelta only [serPtr, st1, RustCliAllocBudget.repAlloc]
  change _ ⊢ _
  exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 600000 in
/-- `HookSat`-backed sibling of `M2BridgePlacedBudget.stageP2_matched_0868_to_094c_placed`. -/
theorem stageP2_matched_0868_to_094c_placed_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hser : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim)))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (h_bb : HookSat (Rust.withPanics ext) lsBlackBoxU8Sym blackBoxSpecSat)
    (st : M.σ) (s : State)
    (sp coroPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt : BitVec 64)
    (msgVerByte b_4f1 : BitVec 8)
    (baseKey : PublicKey)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (hcur : r.currentSession = some sess)
    (hver : sess.state.version = msgVerByte.zeroExtend 32)
    (halice : sess.aliceBaseKey = baseKey.serialize)
    (hfits : FitsEnv M lim st PublicKeySerializeEnv)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + 0x868#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = kyberStorePtr)
    (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kyberStoreVt)
    (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr)
    (hx13 : s.readReg64 .x13 = preKeyStoreVt)
    (hx14 : s.readReg64 .x14 = localAddrPtr)
    (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = idStoreVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkStoreVt)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hx29 : s.readReg64 .x29 = sp + 0xc70#64) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) ((blkPl_518).base + 0x94c#64) s
      (cells (coroPtr + 0x3f8#64) 6 ∗
       cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
       ((msgPtr + 0xf0#64) ↦₈ msgVerByte) ∗
       sessionRecordAt A.repAlloc (coroPtr + 0xe0#64) g r ∗
       memRegion (sp + 0x3e0#64) 34 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       A.pool lim st s ∗
       stackAt sp rootStack)
      (fun sf P_f =>
        (P_f ⊢
          ∃∗ recG : SessionGhost,
            ⌜g.cur = some recG ∧ SessionExtraRel recG sess⌝ ∗
            processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
              idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
              kyberStorePtr kyberStoreVt ∗
            ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
            ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
            ((msgPtr + 0xf0#64) ↦₈ msgVerByte) ∗
            prevSessionsEmptyAt A.repAlloc coroPtr g ∗
            sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG sess.state ∗
            remoteIdentityOkAt (sp + 0x3e0#64) sess.state.remoteIdentity ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            A.pool lim (M.stepEvents stageP2MatchedBridgeEvents st) sf ∗
            stackAt sp rootStack) ∧
        sf.sp = sp ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x19 = coroPtr ∧
        sf.readReg64 .x21 = sp + 0x370#64 ∧
        sf.readReg64 .x25 = sp + 0x210#64 ∧
        sf.readReg64 .x28 = sp + 0xa90#64 ∧
        sf.readReg64 .x29 = sp + 0xc70#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  have hpartA := stageP2_matched_0868_to_08c0_placed_sat (Qp := fun _ _ => False)
    hser h_bb st s sp coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt msgVerByte b_4f1 baseKey g r sess
    hcur hver halice hfits hcro hsp_eq hsp_root hpc hrun hsp_align
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hx28 hx29
  refine bind_sepWPp_nopanic_state hpartA (by sep_focus)
    fun sm _ hpcm hrunm hregsm => ?_
  rcases hregsm with ⟨hspm, htrm, hx19m, hx26m, hx28m, hx29m, hvregsm, hcrom⟩
  have hspm_align : (sm.sp &&& 15#64 == 0#64) = true := by rw [hspm, ← hsp_eq]; exact hsp_align
  have hlen33 : baseKey.serialize.length = 33 := by simp [PublicKey.serialize]
  conv => arg 4; rw [processPrekeyActive10At_eq_placed]
  simp only [sepConj_assoc]
  have hpartB := stageP2_matched_08c0_to_094c_placed
    (Qp := fun _ _ => False)
    hdealloc (M.stepEvents publicKeySerializeEvents st) sm sp coroPtr
    (sm.readReg64 .x21) baseKey.serialize g r sess
    hcur hlen33 hcrom hspm hsp_root hpcm hrunm hspm_align
    hx19m rfl hx26m hx28m hx29m
  refine sepWPp_lift_qp ?_
  refine bind_sepWPp_nopanic_state hpartB (by sep_focus)
    fun sf _ hpcf hrunf hregsf => ?_
  rcases hregsf with ⟨hspf, htrf, hx19f, hx21f, hx25f, hx28f, hx29f, hvregsf, hcrof⟩
  sep_norm
  refine SepWPp.exists_elim fun recG => SepWPp.pure_elim fun ⟨hgc, hextra⟩ => ?_
  refine SepWPp.done hpcf hrunf ⟨?_, hspf, htrf.trans htrm,
    hx19f, hx21f, hx25f, hx28f, hx29f, hvregsf.trans hvregsm, hcrof⟩
  refine Entails.sepExists_right recG (Entails.pure_right ⟨hgc, hextra⟩ ?_)
  have hstep_eq :
      M.stepEvents (rustDeallocEvents 33 1) (M.stepEvents publicKeySerializeEvents st) =
      M.stepEvents stageP2MatchedBridgeEvents st := by
    unfold stageP2MatchedBridgeEvents
    exact (M.stepEvents_append publicKeySerializeEvents (rustDeallocEvents 33 1) st).symm
  rw [hstep_eq, processPrekeyActive10At_eq_placed]
  exact Entails.of_eq (by sep_ac_rfl)

/-- `HookSat`-backed sibling of `M2BridgePlacedBudget.stageP2_matched_0868_to_094c_of_bridgeEnv_placed`. -/
theorem stageP2_matched_0868_to_094c_of_bridgeEnv_placed_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hser : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim)))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (h_bb : HookSat (Rust.withPanics ext) lsBlackBoxU8Sym blackBoxSpecSat)
    (st : M.σ) (s : State)
    (sp coroPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt : BitVec 64)
    (msgVerByte b_4f1 : BitVec 8)
    (baseKey : PublicKey)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (hcur : r.currentSession = some sess)
    (hver : sess.state.version = msgVerByte.zeroExtend 32)
    (halice : sess.aliceBaseKey = baseKey.serialize)
    (hfits : FitsEnv M lim st StageP2MatchedBridgeEnv)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + 0x868#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = kyberStorePtr)
    (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kyberStoreVt)
    (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr)
    (hx13 : s.readReg64 .x13 = preKeyStoreVt)
    (hx14 : s.readReg64 .x14 = localAddrPtr)
    (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = idStoreVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkStoreVt)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hx29 : s.readReg64 .x29 = sp + 0xc70#64) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) ((blkPl_518).base + 0x94c#64) s
      (stageP2Matched0868PrePlaced A lim st s sp coroPtr msgPtr msgVerByte b_4f1 baseKey g r)
      (fun sf P_f =>
        (∃ evs : List AllocEvent, StageP2MatchedBridgeEnv evs ∧
          (P_f ⊢ stageP2Matched094cPostPlaced A lim (M.stepEvents evs st) sf sp coroPtr msgPtr
            remoteAddrPtr localAddrPtr idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            kyberStorePtr kyberStoreVt msgVerByte baseKey g sess)) ∧
        sf.sp = sp ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x19 = coroPtr ∧
        sf.readReg64 .x21 = sp + 0x370#64 ∧
        sf.readReg64 .x25 = sp + 0x210#64 ∧
        sf.readReg64 .x28 = sp + 0xa90#64 ∧
        sf.readReg64 .x29 = sp + 0xc70#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  have hmain := stageP2_matched_0868_to_094c_placed_sat (Qp := fun _ _ => False)
    hser hdealloc h_bb st s sp coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt msgVerByte b_4f1 baseKey g r sess
    hcur hver halice (fitsEnv_publicKeySerialize_of_bridge hfits)
    hcro hsp_eq hsp_root hpc hrun hsp_align
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hx28 hx29
  refine sepWPp_lift_qp ?_
  intro R hm hL
  dsimp only [stageP2Matched0868PrePlaced] at hm
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hent, hregs⟩ | ⟨_, _, _, hpan⟩ | ⟨_, hoom⟩⟩ :=
    hmain R hm hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf,
      ⟨stageP2MatchedBridgeEvents, rfl, hent⟩, hregs⟩⟩
  · exact False.elim hpan
  · exact (not_satisfies_false_sepConj hoom).elim

end

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudgetSat
