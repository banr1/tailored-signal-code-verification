/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ParseServiceId
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ParseServiceIdBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# `HookSat`-Parameterized Budget-Compatible Relocatable Contracts for Block `17`

Additive `*Sat` sibling of
`LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountPlacedBudget` proving
`RecvWireSameAccountBudget.isSameAccountDistinctRawSpec` and
`RecvWireSameAccountBudget.isSameAccountDistinctSpec` under `[LibsignalPlacement]` from
`HookSat H lsBlackBoxU8Sym blackBoxSpecSat` instead of `H lsBlackBoxU8Sym = some blackBoxHook`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountPlacedBudgetSat

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps
  (sepWP_rebase_vmPreserved trapHooks
   vmPreserved_refl_iff vmPreserved_setPC vmPreserved_advancePC vmPreserved_setPState
   vmPreserved_writeReg64 vmPreserved_writeReg32 vmPreserved_writeReg
   vmPreserved_writeVReg128 vmPreserved_writeVReg64 vmPreserved_writeVReg32
   vmPreserved_applyWriteback vmPreserved_setStatus vmPreserved_appendTrace
   vmPreserved_setFs vmPreserved_stepExclLoop tpidrEl0_applyWriteback)
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
   lsBlackBoxU8Sym ls_subroutine_ok_cl_of_block ls_subroutine_ok_of_block
   lsmpl sepWP_seq_lscl withLsCl withLsCodeLoaded
   blkPC_206 blkPl_206 blkPC_212 blkPl_212 blkPC_252 blkPl_252)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr
  (UuidParser uuidTryParse kindByte serviceIdParse)
open CryptoVerification.LibsignalTripleRatchet
  (parseSidResultAt parseSidStack parseSidSpec parseSidCodeSpec
   uuidTryParseStack uuidTryParseSpec uuidTryParseCodeSpec)
open CryptoVerification.LibsignalTripleRatchet.ParseServiceId
  (uuidWord0 uuidWord1 parseSidResultAt_some_eq)
open CryptoVerification.LibsignalTripleRatchet.Getters
  (blkPC_17 blkPl_17)
open CryptoVerification.E2E.Pqxdh.WireEntries
  (SidCellsRel DistinctSid isSameAccountDistinctStack)
open LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountBudget
  (isSameAccountDistinctRawSpec isSameAccountDistinctSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountPlacedBudget
  (isSameAccountEqDistinct_of_raw_placed)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat
  (blackBoxSpecSat publicKeyEqMemSpec16 publicKey_eq_mem_placed_vm_ok_16_sat)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ParseServiceIdBudget
  (parseSid_placed_ok_of_code parseSid_placed_ok_of_contract)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem sepWP_vm_step {P : Program} {b mid target : BitVec 64}
    {Hk : String → Option (State → State)} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop}
    (hwp : SepWP (P.rebase b Hk) mid s Pre
      (fun sm Pm => VmPreserved s sm ∧
        (VmPreserved s sm → SepWP (P.rebase b Hk) target sm Pm post))) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq hwp fun _ _ _ _ ⟨hvm, hk⟩ => hk hvm

private theorem sepWP_lscl_vm_step [LibsignalPlacement] {P : Program} {b mid target : BitVec 64}
    {Hk : String → Option (State → State)} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hwp : SepWP (P.rebase b Hk) mid s Pre
      (fun sm Pm => VmPreserved s sm ∧
        (LibsignalCodeLoaded lsmpl sm.mem → VmPreserved s sm →
          SepWP (P.rebase b Hk) target sm Pm post))) :
    SepWP (P.rebase b Hk) target s Pre post :=
  sepWP_seq_lscl hcl (mid := mid) (SepWP.mono hwp fun _ _ _ _ ⟨hvm, hk⟩ hcl' => hk hcl' hvm)

private theorem vmPreserved_of_eq {s1 s2 : State}
    (hbs : s2.brkStart = s1.brkStart) (hbrk : s2.brk = s1.brk)
    (htp : s2.tpidrEl0 = s1.tpidrEl0) (hphys : s2.physMemAvail = s1.physMemAvail)
    (hmem : s2.mem = s1.mem) (hfs : s2.fs = s1.fs) :
    VmPreserved s1 s2 :=
  ⟨⟨hbs, hbrk, htp⟩, hphys, fun _ => by rw [hmem], LibsignalBinary.Heap.FdsHiFrame.of_fs_eq hfs⟩

attribute [local irreducible] VmPreserved

private theorem vm_chain {s0 s1 s2 s3 : State}
    (h01 : VmPreserved s0 s1) (h23 : VmPreserved s2 s3)
    (hbs : s2.brkStart = s1.brkStart := by simp)
    (hbrk : s2.brk = s1.brk := by simp)
    (htp : s2.tpidrEl0 = s1.tpidrEl0 := by simp)
    (hphys : s2.physMemAvail = s1.physMemAvail := by simp)
    (hmem : s2.mem = s1.mem := by simp)
    (hfs : s2.fs = s1.fs := by simp) :
    VmPreserved s0 s3 :=
  h01.trans ((vmPreserved_of_eq hbs hbrk htp hphys hmem hfs).trans h23)

/-! ## 1. Stack & Callee Spec Adapters (`Block 212` and `Block 206`) -/

private theorem stackAt_parseSidStack_eq_publicKeyEq16_placed (sp : BitVec 64) :
    stackAt sp parseSidStack =
      memRegion (sp - 80#64) 80 ∗
      memRegion (sp - 272#64) 192 := by
  simp only [stackAt, parseSidStack, uuidTryParseStack]
  rw [show (80 + 192 : Nat) = 272 from rfl,
      show BitVec.ofNat 64 272 = 272#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 272#64) (b' := sp - 80#64) (N := 272) (n := 192) (k := 80)
        (by decide) (by bv_omega) (by decide)]
  sep_ac_rfl

private def publicKeyEqMem80PlacedSpec :
    Spec (BitVec 64 × PublicKey × BitVec 64 × PublicKey × BitVec 64) where
  pre := fun (p1, pk1, p2, pk2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp⌝ ∗
    (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
    stackAt sp parseSidStack
  post := fun (p1, pk1, p2, pk2, sp) s0 sf =>
    ⌜VmPreserved s0 sf⌝ ∗
    ⌜sf.readReg64 .x0 = (if pk1 == pk2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
    (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
    stackAt sp parseSidStack

private theorem publicKeyEqMem80_placed_ok_sat [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hEq : subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
      (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqMemSpec16))) :
    subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
      (withLsCodeLoaded lsmpl publicKeyEqMem80PlacedSpec) := by
  refine subroutine_ok_map hEq ?_
  rintro ⟨p1, pk1, p2, pk2, sp⟩ R s0 hpre
  refine ⟨(p1, pk1, p2, pk2, sp), memRegion (sp - 272#64) 192 ∗ R, ?_, ?_⟩
  · simp only [withLsCodeLoaded, withVmPreserved, publicKeyEqMemSpec16, publicKeyEqMem80PlacedSpec,
      stackAt_parseSidStack_eq_publicKeyEq16_placed sp] at hpre ⊢
    exact Satisfies.of_eq hpre (by sep_ac_rfl)
  · intro sf hpost
    simp only [withVmPreserved, publicKeyEqMemSpec16, publicKeyEqMem80PlacedSpec,
      stackAt_parseSidStack_eq_publicKeyEq16_placed sp] at hpost ⊢
    exact Satisfies.of_eq hpost (by sep_ac_rfl)

private theorem memRegion_17_eq_cells_placed (a : BitVec 64) :
    memRegion a 17 =
      ∃∗ b0 : BitVec 8, ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        (a ↦₈ b0) ∗ ((a + 1#64) ↦₆₄ w0) ∗ ((a + 9#64) ↦₆₄ w1) := by
  rw [show (17 : Nat) = 1 + (8 + 8) by decide,
    memRegion_split a 1 (8 + 8) (by decide),
    memRegion_split (a + 1#64) 8 8 (by decide),
    memRegion_one a, ProofLib.memRegion_eight (a + 1#64),
    ProofLib.memRegion_eight (a + 1#64 + 8#64)]
  have h9 : a + 1#64 + 8#64 = a + 9#64 := by bv_arith
  rw [h9, sepExists_sepConj_left]
  refine congrArg sepExists (funext fun b0 => ?_)
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine congrArg sepExists (funext fun w0 => ?_)
  rw [sepExists_sepConj_right, sepExists_sepConj_right]

private theorem pointsTo_17_entails_memRegion_placed (a : BitVec 64)
    (b0 : BitVec 8) (w0 w1 : BitVec 64) :
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₆₄ w0) ∗ ((a + 9#64) ↦₆₄ w1)) ⊢ memRegion a 17 := by
  rw [memRegion_17_eq_cells_placed a]
  exact Entails.sepExists_right b0 (Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.refl _)))

private theorem memRegion_16_out_split_placed (a : BitVec 64) :
    memRegion (a + 1#64) 16 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ((a + 1#64) ↦₆₄ w0) ∗ ((a + 9#64) ↦₆₄ w1) := by
  rw [show (16 : Nat) = 8 + 8 by decide, memRegion_split (a + 1#64) 8 8 (by decide)]
  have h9 : a + 1#64 + BitVec.ofNat 64 8 = a + 9#64 := by bv_arith
  rw [h9, ProofLib.memRegion_eight (a + 1#64), ProofLib.memRegion_eight (a + 9#64),
    sepExists_sepConj_left]
  refine congrArg sepExists (funext fun w0 => ?_)
  rw [sepExists_sepConj_right]

private theorem parseSidResultAt_entails_rel_cells_placed (out : BitVec 64)
    (res : Option (Bool × List.Vector (BitVec 8) 16)) :
    parseSidResultAt out res ⊢
      ∃∗ b0 : BitVec 8, ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        ⌜SidCellsRel res b0 w0 w1⌝ ∗
        (out ↦₈ b0) ∗ ((out + 1#64) ↦₆₄ w0) ∗ ((out + 9#64) ↦₆₄ w1) := by
  cases res with
  | none =>
    simp only [parseSidResultAt, SidCellsRel, memRegion_16_out_split_placed,
      sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro w0
    apply Entails.sepExists_elim; intro w1
    refine Entails.sepExists_right 2#8 (Entails.sepExists_right w0 (Entails.sepExists_right w1 ?_))
    exact Entails.pure_right rfl (Entails.of_eq (by sep_ac_rfl))
  | some val =>
    rcases val with ⟨pni, uuid⟩
    rw [parseSidResultAt_some_eq out pni uuid]
    exact Entails.sepExists_right (kindByte pni)
      (Entails.sepExists_right (uuidWord0 uuid)
        (Entails.sepExists_right (uuidWord1 uuid)
          (Entails.pure_right ⟨rfl, rfl, rfl⟩ (Entails.refl _))))

private abbrev ParseSidRelPlacedGhost :=
  BitVec 64 × List (BitVec 8) × BitVec 64 × BitVec 8 × BitVec 64 × BitVec 64

private def parseSidRelPlacedSpec (parse : UuidParser) : Spec ParseSidRelPlacedGhost where
  pre := fun (p, bs, out, b0, w0, w1) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ s.readReg64 .x8 = out⌝ ∗
      (p ↦ₛ bs) ∗ (out ↦₈ b0) ∗ ((out + 1#64) ↦₆₄ w0) ∗ ((out + 9#64) ↦₆₄ w1) ∗
      stackAt s.sp parseSidStack
  post := fun (p, bs, out, _, _, _) s0 sf =>
    ⌜VmPreserved s0 sf⌝ ∗
      ⌜sf.trace = s0.trace⌝ ∗
      (p ↦ₛ bs) ∗
      (∃∗ b0' : BitVec 8, ∃∗ w0' : BitVec 64, ∃∗ w1' : BitVec 64,
        ⌜SidCellsRel (serviceIdParse parse bs) b0' w0' w1'⌝ ∗
        (out ↦₈ b0') ∗ ((out + 1#64) ↦₆₄ w0') ∗ ((out + 9#64) ↦₆₄ w1')) ∗
      stackAt s0.sp parseSidStack

private theorem parseSidRel_placed_ok [LibsignalPlacement] {parse : UuidParser}
    {H : String → Option (State → State)}
    (hParse : subroutine_ok ((blkPC_206).rebase (blkPl_206).base H) (blkPl_206).base
      (withLsCodeLoaded lsmpl (withVmPreserved (parseSidCodeSpec parse)))) :
    subroutine_ok ((blkPC_206).rebase (blkPl_206).base H) (blkPl_206).base
      (withLsCodeLoaded lsmpl (parseSidRelPlacedSpec parse)) := by
  refine subroutine_ok_map hParse ?_
  rintro ⟨p, bs, out, b0, w0, w1⟩ R s0 hpre
  refine ⟨(p, bs, out), R, ?_, fun sf hpost => ?_⟩
  · simp only [withLsCodeLoaded, withVmPreserved, parseSidRelPlacedSpec, parseSidCodeSpec,
      parseSidSpec] at hpre ⊢
    have hm : s0.mem ⊨ ((out ↦₈ b0) ∗ ((out + 1#64) ↦₆₄ w0) ∗ ((out + 9#64) ↦₆₄ w1)) ∗
        (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧ s0.readReg64 .x8 = out⌝ ∗
          ⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗
          (p ↦ₛ bs) ∗ stackAt s0.sp parseSidStack ∗ R) :=
      Satisfies.of_eq hpre (by sep_ac_rfl)
    have hm' :=
      Arm64.Satisfies.mono (sepConj_mono_left (pointsTo_17_entails_memRegion_placed out b0 w0 w1)) hm
    exact Satisfies.of_eq hm' (by sep_ac_rfl)
  · simp only [withLsCodeLoaded, withVmPreserved, parseSidCodeSpec, parseSidSpec,
      parseSidRelPlacedSpec] at hpost ⊢
    have hm : sf.mem ⊨ parseSidResultAt out (serviceIdParse parse bs) ∗
        (⌜VmPreserved s0 sf⌝ ∗ ⌜sf.trace = s0.trace⌝ ∗ (p ↦ₛ bs) ∗
          stackAt s0.sp parseSidStack ∗ R) :=
      Satisfies.of_eq hpost (by sep_ac_rfl)
    have hm' :=
      Arm64.Satisfies.mono (sepConj_mono_left (parseSidResultAt_entails_rel_cells_placed out _)) hm
    exact Satisfies.of_eq hm' (by sep_ac_rfl)

private theorem stackAt_isSameAccountDistinct_split_placed (sp : BitVec 64) :
    stackAt sp isSameAccountDistinctStack =
      stackAt (sp - 80#64) parseSidStack ∗
      memRegion (sp - 80#64) 12 ∗
      (∃∗ b0 : BitVec 8, ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        ((sp - 68#64) ↦₈ b0) ∗ ((sp - 67#64) ↦₆₄ w0) ∗ ((sp - 59#64) ↦₆₄ w1)) ∗
      memRegion (sp - 51#64) 3 ∗
      ProofLib.cells (sp - 48#64) 6 := by
  simp only [stackAt, isSameAccountDistinctStack, parseSidStack, uuidTryParseStack]
  rw [show (80 + (80 + 192) : Nat) = 352 from rfl,
      show (80 + 192 : Nat) = 272 from rfl,
      show BitVec.ofNat 64 352 = 352#64 from rfl,
      show BitVec.ofNat 64 272 = 272#64 from rfl,
      show sp - 80#64 - 272#64 = sp - 352#64 by bv_arith,
      show (352 : Nat) = 272 + (12 + (17 + (3 + 8 * 6))) by decide,
      memRegion_split (sp - 352#64) 272 (12 + (17 + (3 + 8 * 6))) (by decide),
      memRegion_split (sp - 352#64 + 272#64) 12 (17 + (3 + 8 * 6)) (by decide),
      memRegion_split (sp - 352#64 + 272#64 + 12#64) 17 (3 + 8 * 6) (by decide),
      memRegion_split (sp - 352#64 + 272#64 + 12#64 + 17#64) 3 (8 * 6) (by decide),
      ProofLib.memRegion_cells _ 6 (by decide),
      memRegion_17_eq_cells_placed]
  have h1 : sp - 352#64 + 272#64 = sp - 80#64 := by bv_arith
  have h2 : sp - 80#64 + 12#64 = sp - 68#64 := by bv_arith
  have h3 : sp - 68#64 + 1#64 = sp - 67#64 := by bv_arith
  have h4 : sp - 68#64 + 9#64 = sp - 59#64 := by bv_arith
  have h5 : sp - 68#64 + 17#64 = sp - 51#64 := by bv_arith
  have h6 : sp - 51#64 + 3#64 = sp - 48#64 := by bv_arith
  rw [h1, h2, h3, h4, h5, h6]

private theorem pack64_inj_placed (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (h : pack64 a0 a1 a2 a3 a4 a5 a6 a7 = pack64 b0 b1 b2 b3 b4 b5 b6 b7) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 ∧ a5 = b5 ∧ a6 = b6 ∧ a7 = b7 := by
  unfold pack64 at h
  exact ⟨
    calc a0 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 0 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 0 8 := congrArg _ h
      _ = b0 := by unfold pack64; bv_bits,
    calc a1 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 8 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 8 8 := congrArg _ h
      _ = b1 := by unfold pack64; bv_bits,
    calc a2 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 16 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 16 8 := congrArg _ h
      _ = b2 := by unfold pack64; bv_bits,
    calc a3 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 24 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 24 8 := congrArg _ h
      _ = b3 := by unfold pack64; bv_bits,
    calc a4 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 32 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 32 8 := congrArg _ h
      _ = b4 := by unfold pack64; bv_bits,
    calc a5 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 40 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 40 8 := congrArg _ h
      _ = b5 := by unfold pack64; bv_bits,
    calc a6 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 48 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 48 8 := congrArg _ h
      _ = b6 := by unfold pack64; bv_bits,
    calc a7 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 56 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 56 8 := congrArg _ h
      _ = b7 := by unfold pack64; bv_bits⟩

private theorem uuid_eq_of_uuidWords_eq_placed {u1 u2 : List.Vector (BitVec 8) 16}
    (hw0 : uuidWord0 u1 = uuidWord0 u2)
    (hw1 : uuidWord1 u1 = uuidWord1 u2) :
    u1 = u2 := by
  rcases u1 with ⟨l1, hl1⟩
  rcases u2 with ⟨l2, hl2⟩
  rcases l1 with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7,
    _ | ⟨a8, _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, _ | ⟨a12, _ | ⟨a13, _ | ⟨a14, _ | ⟨a15,
      _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try cases hl1
  rcases l2 with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
      _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try cases hl2
  simp only [uuidWord0, uuidWord1, List.Vector.toList, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hw0 hw1
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ :=
    pack64_inj_placed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw0
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ :=
    pack64_inj_placed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw1
  rfl

private theorem kindByte_inj_placed {p1 p2 : Bool} (h : kindByte p1 = kindByte p2) : p1 = p2 := by
  cases p1 <;> cases p2 <;> revert h <;> decide

private theorem sidCellsRel_ne_of_distinct_placed {parse : UuidParser} {bs1 bs2 : List (BitVec 8)}
    {b0_1 b0_2 : BitVec 8} {w0_1 w1_1 w0_2 w1_2 : BitVec 64}
    (hDist : DistinctSid parse bs1 bs2)
    (hrel1 : SidCellsRel (serviceIdParse parse bs1) b0_1 w0_1 w1_1)
    (hrel2 : SidCellsRel (serviceIdParse parse bs2) b0_2 w0_2 w1_2)
    (hb1 : b0_1 ≠ 2#8) (hb2 : b0_2 ≠ 2#8) (hkind : b0_1 = b0_2) :
    w0_1 = w0_2 ∧ w1_1 = w1_2 → False := by
  rintro ⟨hw0, hw1⟩
  cases hs1 : serviceIdParse parse bs1 with
  | none => rw [hs1, SidCellsRel] at hrel1; exact hb1 hrel1
  | some v1 =>
    rcases v1 with ⟨p1, u1⟩
    rw [hs1, SidCellsRel] at hrel1
    rcases hrel1 with ⟨hb0_1, hw0_1, hw1_1⟩
    cases hs2 : serviceIdParse parse bs2 with
    | none => rw [hs2, SidCellsRel] at hrel2; exact hb2 hrel2
    | some v2 =>
      rcases v2 with ⟨p2, u2⟩
      rw [hs2, SidCellsRel] at hrel2
      rcases hrel2 with ⟨hb0_2, hw0_2, hw1_2⟩
      have hp : p1 = p2 := kindByte_inj_placed (hb0_1.symm.trans (hkind.trans hb0_2))
      have hu : u1 = u2 := uuid_eq_of_uuidWords_eq_placed
        (hw0_1.symm.trans (hw0.trans hw0_2))
        (hw1_1.symm.trans (hw1.trans hw1_2))
      subst hp hu
      exact hDist (p1, u1) hs1 hs2

private theorem cond_uuid_words_ne_placed {w0_1 w1_1 w0_2 w1_2 : BitVec 64}
    (hne : w0_1 = w0_2 ∧ w1_1 = w1_2 → False) :
    (if (w0_1 == w0_2) = true then w1_1 != w1_2 else true) = true := by
  by_cases h0 : (w0_1 == w0_2) = true
  · simp only [h0, ↓reduceIte, bne_iff_ne]
    intro h1
    exact hne ⟨of_decide_eq_true h0, h1⟩
  · simp only [h0, Bool.false_eq_true, ↓reduceIte]

private theorem sidCellsRel_b0_cases_placed {o : Option (Bool × List.Vector (BitVec 8) 16)}
    {b0 : BitVec 8} {w0 w1 : BitVec 64} (h : SidCellsRel o b0 w0 w1) :
    b0 = 0#8 ∨ b0 = 1#8 ∨ b0 = 2#8 := by
  cases o with
  | none => right; right; exact h
  | some v => rcases v with ⟨p, _⟩; rcases h with ⟨rfl, _, _⟩; cases p <;> simp [kindByte]

/-! ## 2. `isSameAccountDistinctRaw_placed_ok_sat` on Block `17` -/

/-- Block `17` (`<IdentityKey>::is_same_account`) meets `RecvWireSameAccountBudget.isSameAccountDistinctRawSpec parse`
under `[LibsignalPlacement]`, given `VmPreserved`-carrying `subroutine_ok` for Block `212` (`publicKeyEqMemSpec16`)
and Block `206` (`parseSidCodeSpec parse`). -/
theorem isSameAccountDistinctRaw_placed_ok_of_callees_sat [LibsignalPlacement] {parse : UuidParser}
    {H : String → Option (State → State)}
    (hEq : subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
      (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqMemSpec16)))
    (hParse : subroutine_ok ((blkPC_206).rebase (blkPl_206).base H) (blkPl_206).base
      (withLsCodeLoaded lsmpl (withVmPreserved (parseSidCodeSpec parse)))) :
    subroutine_ok ((blkPC_17).rebase (blkPl_17).base H) (blkPl_17).base
      (withLsCodeLoaded lsmpl (isSameAccountDistinctRawSpec parse)) := by
  simp only [withLsCodeLoaded, isSameAccountDistinctRawSpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.WireEntries.isSameAccountDistinctRawSpec]
  have hEq0 : subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (lsmpl.base 212)
      (withLsCodeLoaded lsmpl publicKeyEqMem80PlacedSpec) :=
    publicKeyEqMem80_placed_ok_sat hEq
  have hEq' := ls_subroutine_ok_cl_of_block (callerProg := (blkPC_17).rebase (blkPl_17).base H) hEq0
  simp only [withLsCl, publicKeyEqMem80PlacedSpec] at hEq'
  have hParse0 : subroutine_ok ((blkPC_206).rebase (blkPl_206).base H) (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidRelPlacedSpec parse)) :=
    parseSidRel_placed_ok hParse
  have hParse' := ls_subroutine_ok_cl_of_block (callerProg := (blkPC_17).rebase (blkPl_17).base H) hParse0
  simp only [withLsCl, parseSidRelPlacedSpec] at hParse'
  wp_init x s0
  obtain ⟨localIkA, localIk, localAddr, localNamePtr, localNameBytes,
    remoteIkA, remoteIk, remoteAddr, remoteNamePtr, remoteNameBytes⟩ := x
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = localIkA := by assumption
  have hx1 : s0.readReg64 (Reg.gpr 1#5) = localAddr := by assumption
  have hx2 : s0.readReg64 (Reg.gpr 2#5) = remoteIkA := by assumption
  have hx3 : s0.readReg64 (Reg.gpr 3#5) = remoteAddr := by assumption
  have h_or : localIk ≠ remoteIk ∨ DistinctSid parse localNameBytes remoteNameBytes := by assumption
  subst hx0 hx1 hx2 hx3
  rw [stackAt_isSameAccountDistinct_split_placed s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro b0_init
  apply SepWP.exists_elim; intro w0_init
  apply SepWP.exists_elim; intro w1_init
  cells_unfold
  wp_pull_exists
  apply sepWP_lscl_vm_step hcl0 (mid := lsmpl.base 212)
  by_vm_steps
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp_all, fun hcl1 hvm1 => ?_⟩
    wp_call hEq' (s0.readReg64 (Reg.gpr 0#5), localIk.publicKey,
      s0.readReg64 (Reg.gpr 2#5), remoteIk.publicKey, s0.sp - 80#64)
    have hvm_eq := vm_chain hvm1 ‹_›
    by_cases hpk : (localIk.publicKey == remoteIk.publicKey) = true
    · have hik_eq : localIk = remoteIk := by
        cases localIk; cases remoteIk
        have hpk' := of_decide_eq_true hpk
        subst hpk'; rfl
      have hDist : DistinctSid parse localNameBytes remoteNameBytes :=
        h_or.resolve_left (not_not.mpr hik_eq)
      simp only [hpk, ↓reduceIte] at *
      apply sepWP_lscl_vm_step (by assumption) (mid := lsmpl.base 206)
      by_vm_steps
        wp_steps
        refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp_all, fun hcl2 hvm2 => ?_⟩
        have hvm_eq2 := vm_chain hvm_eq hvm2
        wp_call hParse'
        have hvm_p1 := vm_chain hvm_eq2 ‹_›
        wp_steps
        wp_if hb0
        · apply sepWP_lscl_vm_step (by simpa using ‹LibsignalCodeLoaded lsmpl _›) (mid := lsmpl.base 206)
          by_vm_steps
            wp_steps
            refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp_all, fun hcl3 hvm3 => ?_⟩
            have hvm_p1_3 := vm_chain hvm_p1 hvm3
            wp_call hParse'
            have hvm_sofar := vm_chain hvm_p1_3 ‹_›
            wp_steps
            wp_if hb1
            · apply sepWP_vm_step (mid := s0.readReg64 (Reg.gpr 30#5))
              by_vm_steps
                wp_steps
                refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp_all, fun hvm4 => ?_⟩
                have hvm_tot := vm_chain hvm_sofar hvm4
                wp_done
            · wp_steps
              wp_if hb01
              · apply sepWP_vm_step (mid := s0.readReg64 (Reg.gpr 30#5))
                by_vm_steps
                  wp_steps
                  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp_all, fun hvm4 => ?_⟩
                  have hvm_tot := vm_chain hvm_sofar hvm4
                  wp_done
              · apply sepWP_vm_step (mid := s0.readReg64 (Reg.gpr 30#5))
                by_vm_steps
                  wp_steps
                  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp_all, fun hvm4 => ?_⟩
                  have hvm_tot := vm_chain hvm_sofar hvm4
                  have hrel1 : SidCellsRel (serviceIdParse parse localNameBytes) _ _ _ := ‹_›
                  have hrel2 : SidCellsRel (serviceIdParse parse remoteNameBytes) _ _ _ := ‹_›
                  have hne := cond_uuid_words_ne_placed (sidCellsRel_ne_of_distinct_placed hDist hrel1 hrel2
                    (by revert hb0; rcases sidCellsRel_b0_cases_placed hrel1 with rfl | rfl | rfl <;> decide)
                    (by revert hb1; rcases sidCellsRel_b0_cases_placed hrel2 with rfl | rfl | rfl <;> decide)
                    (by revert hb01; rcases sidCellsRel_b0_cases_placed hrel1 with rfl | rfl | rfl <;>
                        rcases sidCellsRel_b0_cases_placed hrel2 with rfl | rfl | rfl <;> decide))
                  wp_done
        · apply sepWP_vm_step (mid := s0.readReg64 (Reg.gpr 30#5))
          by_vm_steps
            wp_steps
            refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp_all, fun hvm3 => ?_⟩
            have hvm_tot := vm_chain hvm_p1 hvm3
            wp_done
    · simp only [hpk, Bool.false_eq_true, ↓reduceIte] at *
      apply sepWP_vm_step (mid := s0.readReg64 (Reg.gpr 30#5))
      by_vm_steps
        wp_steps
        refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp_all, fun hvm2 => ?_⟩
        have hvm_tot := vm_chain hvm_eq hvm2
        wp_done

/-- Block `17` meets `isSameAccountDistinctRawSpec parse` under `[LibsignalPlacement]`, discharging
Block `212` from `h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat` and taking `hParse` on Block `206`. -/
theorem isSameAccountDistinctRaw_placed_ok_of_parse_sat [LibsignalPlacement] {parse : UuidParser}
    {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (hParse : subroutine_ok ((blkPC_206).rebase (blkPl_206).base H) (blkPl_206).base
      (withLsCodeLoaded lsmpl (withVmPreserved (parseSidCodeSpec parse)))) :
    subroutine_ok ((blkPC_17).rebase (blkPl_17).base H) (blkPl_17).base
      (withLsCodeLoaded lsmpl (isSameAccountDistinctRawSpec parse)) :=
  isSameAccountDistinctRaw_placed_ok_of_callees_sat (publicKey_eq_mem_placed_vm_ok_16_sat h_bb) hParse

/-- Block `17` meets `isSameAccountDistinctRawSpec uuidTryParse` under `[LibsignalPlacement]`,
given `h_bb` and `huuid` (`withVmPreserved (uuidTryParseCodeSpec uuidTryParse)`) on Block `252`. -/
theorem isSameAccountDistinctRaw_placed_ok_sat [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H) (blkPl_252).base
      (withLsCodeLoaded lsmpl (withVmPreserved (uuidTryParseCodeSpec uuidTryParse)))) :
    subroutine_ok ((blkPC_17).rebase (blkPl_17).base H) (blkPl_17).base
      (withLsCodeLoaded lsmpl (isSameAccountDistinctRawSpec uuidTryParse)) :=
  isSameAccountDistinctRaw_placed_ok_of_parse_sat h_bb (parseSid_placed_ok_of_code H huuid)

/-- Block `17` meets `isSameAccountDistinctRawSpec uuidTryParse` under `[LibsignalPlacement]`,
given `h_bb` and plain `withVmPreserved (uuidTryParseSpec uuidTryParse)` on Block `252`. -/
theorem isSameAccountDistinctRaw_placed_ok_of_contract_sat [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H) (blkPl_252).base
      (withVmPreserved (uuidTryParseSpec uuidTryParse))) :
    subroutine_ok ((blkPC_17).rebase (blkPl_17).base H) (blkPl_17).base
      (withLsCodeLoaded lsmpl (isSameAccountDistinctRawSpec uuidTryParse)) :=
  isSameAccountDistinctRaw_placed_ok_of_parse_sat h_bb (parseSid_placed_ok_of_contract H huuid)

/-! ## 3. `isSameAccountEqDistinct_placed_ok_sat` on Block `17` -/

/-- Block `17` meets `isSameAccountDistinctSpec A parse` under `[LibsignalPlacement]`,
given `hEq` (`withVmPreserved publicKeyEqMemSpec16`) on Block `212` and `hParse` on Block `206`. -/
theorem isSameAccountEqDistinct_placed_ok_of_callees_sat [LibsignalPlacement] {parse : UuidParser}
    (A : RustAlloc) {H : String → Option (State → State)}
    (hEq : subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
      (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqMemSpec16)))
    (hParse : subroutine_ok ((blkPC_206).rebase (blkPl_206).base H) (blkPl_206).base
      (withLsCodeLoaded lsmpl (withVmPreserved (parseSidCodeSpec parse)))) :
    subroutine_ok ((blkPC_17).rebase (blkPl_17).base H) (blkPl_17).base
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpec A parse)) :=
  isSameAccountEqDistinct_of_raw_placed A (isSameAccountDistinctRaw_placed_ok_of_callees_sat hEq hParse)

/-- Block `17` meets `isSameAccountDistinctSpec A parse` under `[LibsignalPlacement]`,
discharging Block `212` from `h_bb` and taking `hParse` on Block `206`. -/
theorem isSameAccountEqDistinct_placed_ok_of_parse_sat [LibsignalPlacement] {parse : UuidParser}
    (A : RustAlloc) {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (hParse : subroutine_ok ((blkPC_206).rebase (blkPl_206).base H) (blkPl_206).base
      (withLsCodeLoaded lsmpl (withVmPreserved (parseSidCodeSpec parse)))) :
    subroutine_ok ((blkPC_17).rebase (blkPl_17).base H) (blkPl_17).base
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpec A parse)) :=
  isSameAccountEqDistinct_of_raw_placed A (isSameAccountDistinctRaw_placed_ok_of_parse_sat h_bb hParse)

/-- Block `17` meets `isSameAccountDistinctSpec A uuidTryParse` under `[LibsignalPlacement]`,
given `h_bb` and `huuid` (`withVmPreserved (uuidTryParseCodeSpec uuidTryParse)`) on Block `252`. -/
theorem isSameAccountEqDistinct_placed_ok_sat [LibsignalPlacement]
    (A : RustAlloc) {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H) (blkPl_252).base
      (withLsCodeLoaded lsmpl (withVmPreserved (uuidTryParseCodeSpec uuidTryParse)))) :
    subroutine_ok ((blkPC_17).rebase (blkPl_17).base H) (blkPl_17).base
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpec A uuidTryParse)) :=
  isSameAccountEqDistinct_of_raw_placed A (isSameAccountDistinctRaw_placed_ok_sat h_bb huuid)

/-- Block `17` meets `isSameAccountDistinctSpec A uuidTryParse` under `[LibsignalPlacement]`,
given `h_bb` and plain `withVmPreserved (uuidTryParseSpec uuidTryParse)` on Block `252`. -/
theorem isSameAccountEqDistinct_placed_ok_of_contract_sat [LibsignalPlacement]
    (A : RustAlloc) {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H) (blkPl_252).base
      (withVmPreserved (uuidTryParseSpec uuidTryParse))) :
    subroutine_ok ((blkPC_17).rebase (blkPl_17).base H) (blkPl_17).base
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpec A uuidTryParse)) :=
  isSameAccountEqDistinct_of_raw_placed A (isSameAccountDistinctRaw_placed_ok_of_contract_sat h_bb huuid)

/-! ## 4. Caller-Lifted Cross-Block Bridges (`lsmpl.base 17`) -/

/-- Caller-lifted `isSameAccountDistinctRawSpec uuidTryParse` (`withLsCodeLoaded`) at `lsmpl.base 17`. -/
theorem isSameAccountDistinctRaw_placed_ok_at_sat [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H) (blkPl_252).base
      (withLsCodeLoaded lsmpl (withVmPreserved (uuidTryParseCodeSpec uuidTryParse))))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctRawSpec uuidTryParse)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg)
    (isSameAccountDistinctRaw_placed_ok_sat h_bb huuid) hi

/-- Caller-lifted `isSameAccountDistinctRawSpec uuidTryParse` (`withLsCl`) at `lsmpl.base 17`. -/
theorem isSameAccountDistinctRaw_placed_cl_ok_at_sat [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H) (blkPl_252).base
      (withLsCodeLoaded lsmpl (withVmPreserved (uuidTryParseCodeSpec uuidTryParse))))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 17)
      (withLsCl lsmpl (isSameAccountDistinctRawSpec uuidTryParse)) :=
  ls_subroutine_ok_cl_of_block (callerProg := callerProg)
    (isSameAccountDistinctRaw_placed_ok_sat h_bb huuid) hi

/-- Caller-lifted `isSameAccountDistinctSpec A uuidTryParse` (`withLsCodeLoaded`) at `lsmpl.base 17`. -/
theorem isSameAccountEqDistinct_placed_ok_at_sat [LibsignalPlacement]
    (A : RustAlloc) {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H) (blkPl_252).base
      (withLsCodeLoaded lsmpl (withVmPreserved (uuidTryParseCodeSpec uuidTryParse))))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpec A uuidTryParse)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg)
    (isSameAccountEqDistinct_placed_ok_sat A h_bb huuid) hi

/-- Caller-lifted `isSameAccountDistinctSpec A uuidTryParse` (`withLsCl`) at `lsmpl.base 17`. -/
theorem isSameAccountEqDistinct_placed_cl_ok_at_sat [LibsignalPlacement]
    (A : RustAlloc) {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H) (blkPl_252).base
      (withLsCodeLoaded lsmpl (withVmPreserved (uuidTryParseCodeSpec uuidTryParse))))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 17)
      (withLsCl lsmpl (isSameAccountDistinctSpec A uuidTryParse)) :=
  ls_subroutine_ok_cl_of_block (callerProg := callerProg)
    (isSameAccountEqDistinct_placed_ok_sat A h_bb huuid) hi

end LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountPlacedBudgetSat
