/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.EntryPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.HeadPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.TopPlacedBudgetAux
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Capacity-Explicit Entry and Loop-Head Helpers for Block `518` Exact Decode

Defines the capacity-explicit `SessionStructure` loop invariant (`b518x_vecU8Fresh0A`,
`b518x_prostSSGQAtCapA`, `b518x_overDecHeapCapA`) and verifies total-correctness `0`-event steps
for Block-`518` Entry (`+0x1ee8 → +0x216c`) and Loop Head (`+0x2160 → +0x216c` / `+0x2620`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ExactDecodePlacedBudgetAuxA

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (RustAlloc vecAt vecBuf vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAfter)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.E2E.Record.L1GX (kyberAt pidAt)
open CryptoVerification.E2E.Record.DeserializeGeneral (ChainG SSG prostChainGAt)
open Symbolic.Swarm.TRREF.B3DeserQ (ExtraGQ SSGQ)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkLib_eq_518 blkPl_518 lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (
  OverDecG OverDecRegsCroPlaced OverDecRegsPlaced
  overDecScratchPre overDecStackX overPrevElemAtExt overPrevElemRestExt
)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget (
  blkLib_518_noSvc0
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential (vecCap4Of)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsBudget (
  overPrevElemAtBudget overPrevElemRestBudget sepWPp_lift_cro_regs
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.TopPlacedBudgetAux (
  SepWPp_bind_sepWP_frame SepWPp_weaken_frame
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm] State.readReg32
attribute [local arm64_norm, local wp_norm]
  Arm64.calleeSavedVRegs_advancePC Arm64.calleeSavedVRegs_setPC Arm64.calleeSavedVRegs_setMem
  Arm64.calleeSavedVRegs_setPState Arm64.calleeSavedVRegs_writeReg64 Arm64.calleeSavedVRegs_writeReg32
  Arm64.calleeSavedVRegs_writeReg isCalleeSavedVReg

local macro "wp_steps_sync_518 " ext:term:max mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException $ext))
    blkLib_eq_518 blkLib_518_noSvc0 (mid := $mid)
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done
    (by first | wp_norm_lhs | simp_all [wp_norm, arm64_norm])
    (by first | wp_norm_lhs | simp_all [wp_norm, arm64_norm])
    fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

/-! ## Capacity-Explicit `SSGQ` and Loop-Heap Invariant -/

def b518x_vecU8Fresh0A (A : RustAlloc) (p : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  if bs = [] then ∃∗ ptr : BitVec 64, vecU8At A p 0#64 ptr []
  else vecU8 A p bs

def b518x_prostSSGQAtCapA (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) : SepProp :=
  b518x_vecU8Fresh0A A ss v.base.lik ∗
    b518x_vecU8Fresh0A A (ss + 0x18#64) v.base.rik ∗
    b518x_vecU8Fresh0A A (ss + 0x30#64) v.base.root ∗
    (∃∗ ptrRecv : BitVec 64,
      vecAt A 104 8 (fun c a => prostChainGAt A a c)
        (ss + 0x48#64) (BitVec.ofNat 64 (vecCap4Of v.base.recv.length)) ptrRecv v.base.recv) ∗
    b518x_vecU8Fresh0A A (ss + 0x60#64) v.ext.abk ∗
    b518x_vecU8Fresh0A A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.base.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗
         pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) ∗
    kyberAt A ss v.ext.kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

def b518x_overDecHeapCapA {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (g : OverDecG) (rest : List (BitVec 8))
    (v : SSGQ) : SepProp :=
  overPrevElemRestBudget A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
    sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest ∗
    b518x_prostSSGQAtCapA A.repAlloc (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
    memRegion (g.q + 0xbf0#64) 128 ∗
    stackAt g.q overDecStackX ∗ A.pool lim st s

/-! ## Entry (`+0x1ee8 → +0x216c`) into `b518x_overDecHeapCapA` -/

private theorem b518x_enc_len_ofNat64_ne_zero {enc : List (BitVec 8)}
    (hne : enc ≠ []) (hlen : enc.length < 2 ^ 62) :
    BitVec.ofNat 64 enc.length ≠ 0#64 := by
  have hpos : 0 < enc.length := List.length_pos_iff.mpr hne
  intro h0
  have hnat := congrArg BitVec.toNat h0
  rw [BitVec.toNat_ofNat, BitVec.toNat_zero,
      Nat.mod_eq_of_lt (by omega : enc.length < 2 ^ 64)] at hnat
  omega

private theorem b518x_overPrevElemAt_entails_of_ne_nil {A : RustAlloc}
    {prevCap prevPtr encCap encPtr : BitVec 64} {enc : List (BitVec 8)}
    (hne : enc ≠ []) :
    overPrevElemAtExt A prevCap prevPtr encCap encPtr enc ⊢
      overPrevElemRestExt A prevCap prevPtr encCap encPtr enc ∗ (encPtr ↦ₛ enc) := by
  by_cases hcap : encCap = 0
  · have hpos : 0 < enc.length := List.length_pos_iff.mpr hne
    unfold overPrevElemAtExt vecU8At
    refine Entails.trans (Entails.of_eq (Q :=
      ⌜enc.length ≤ encCap.toNat ∧ encCap.toNat < 2 ^ 63 ∧ encPtr ≠ 0⌝ ∗
        (⌜1 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
          A.live prevPtr (prevCap.toNat * 24) 8 ∗
          vecHeader prevPtr encCap encPtr (BitVec.ofNat 64 enc.length) ∗
          (if encCap = 0 then emp else
            A.live encPtr encCap.toNat 1 ∗ (encPtr ↦ₛ enc) ∗
              memRegion (encPtr + BitVec.ofNat 64 enc.length) (encCap.toNat - enc.length)) ∗
          memRegion (prevPtr + 24#64) ((prevCap.toNat - 1) * 24))) (by sep_ac_rfl)) ?_
    refine Entails.pure_left fun hφ => False.elim ?_
    have hzero : encCap.toNat = 0 := by subst hcap; rfl
    omega
  · unfold overPrevElemAtExt overPrevElemRestExt vecU8At
    simp only [hcap, ↓reduceIte]
    exact Entails.of_eq (by sep_ac_rfl)

private theorem b518x_sepWPp_exists_left {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ x : α, SepWPp prog ret s (P x ∗ F) Q Qp) :
    SepWPp prog ret s ((∃∗ x : α, P x) ∗ F) Q Qp := by
  intro R hm hL
  rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨x, hm⟩
  exact h x R hm hL

private theorem b518x_memRegion_succ8_entry (a : BitVec 64) (n : Nat) (hn : n < 2000) :
    memRegion a (n + 8) = (∃∗ w : BitVec 64, a ↦₆₄ w) ∗ memRegion (a + 8#64) n := by
  rw [Nat.add_comm n 8, memRegion_split a 8 n (by omega), ProofLib.memRegion_eight]

private def b518x_entryScratchCells (q : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
     w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 : BitVec 64) : SepProp :=
  ((q + 0x920#64) ↦₆₄ w0) ∗ ((q + 0x928#64) ↦₆₄ w1) ∗
  ((q + 0x930#64) ↦₆₄ w2) ∗ ((q + 0x938#64) ↦₆₄ w3) ∗ ((q + 0x940#64) ↦₆₄ w4) ∗
  ((q + 0x948#64) ↦₆₄ w5) ∗ ((q + 0x950#64) ↦₆₄ w6) ∗ ((q + 0x958#64) ↦₆₄ w7) ∗
  ((q + 0x960#64) ↦₆₄ w8) ∗ ((q + 0x968#64) ↦₆₄ w9) ∗ ((q + 0x970#64) ↦₆₄ w10) ∗
  ((q + 0x978#64) ↦₆₄ w11) ∗ ((q + 0x980#64) ↦₆₄ w12) ∗ ((q + 0x988#64) ↦₆₄ w13) ∗
  ((q + 0x990#64) ↦₆₄ w14) ∗ ((q + 0x998#64) ↦₆₄ w15) ∗ ((q + 0x9a0#64) ↦₆₄ w16) ∗
  ((q + 0x9a8#64) ↦₆₄ w17) ∗ ((q + 0x9b0#64) ↦₆₄ w18) ∗ ((q + 0x9b8#64) ↦₆₄ w19) ∗
  ((q + 0x9c0#64) ↦₆₄ w20) ∗ ((q + 0xa28#64) ↦₆₄ w21) ∗ ((q + 0xa58#64) ↦₆₄ w22) ∗
  ((q + 0xa78#64) ↦₆₄ w23) ∗ ((q + 0xa80#64) ↦₆₄ w24) ∗ ((q + 0xbe8#64) ↦₆₄ w25)

private def b518x_entryScratchKeep (q : BitVec 64) : SepProp :=
  memRegion (q + 0x9c8#64) 96 ∗ memRegion (q + 0xa30#64) 40 ∗
  memRegion (q + 0xa60#64) 24 ∗ memRegion (q + 0xa88#64) 8 ∗
  memRegion (q + 0xa90#64) 344 ∗ memRegion (q + 0xbf0#64) 128

set_option maxHeartbeats 400000 in
private theorem b518x_overDecScratchPre_split (q : BitVec 64) :
    overDecScratchPre q =
      (∃∗ w25 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ w23 : BitVec 64, ∃∗ w22 : BitVec 64,
       ∃∗ w21 : BitVec 64, ∃∗ w20 : BitVec 64, ∃∗ w19 : BitVec 64, ∃∗ w18 : BitVec 64,
       ∃∗ w17 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w15 : BitVec 64, ∃∗ w14 : BitVec 64,
       ∃∗ w13 : BitVec 64, ∃∗ w12 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64,
       ∃∗ w9 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64,
       ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64,
       ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        b518x_entryScratchCells q w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
          w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25) ∗
      b518x_entryScratchKeep q := by
  unfold overDecScratchPre b518x_entryScratchKeep
  rw [memRegion_split (q + 0x990#64) 56 200 (by decide),
      memRegion_split (q + 0x990#64 + 56#64) 96 104 (by decide),
      memRegion_split (q + 0x990#64 + 56#64 + 96#64) 8 96 (by decide),
      memRegion_split (q + 0x990#64 + 56#64 + 96#64 + 8#64) 40 56 (by decide),
      memRegion_split (q + 0x990#64 + 56#64 + 96#64 + 8#64 + 40#64) 8 48 (by decide),
      memRegion_split (q + 0x990#64 + 56#64 + 96#64 + 8#64 + 40#64 + 8#64) 24 24 (by decide),
      memRegion_split (q + 0x990#64 + 56#64 + 96#64 + 8#64 + 40#64 + 8#64 + 24#64) 16 8 (by decide),
      memRegion_split (q + 0xbe8#64) 8 128 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  conv_lhs =>
    arg 1
    simp (discharger := decide) only [b518x_memRegion_succ8_entry, ProofLib.memRegion_zero,
      sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  conv_lhs =>
    arg 2; arg 1; arg 1
    simp (discharger := decide) only [b518x_memRegion_succ8_entry, ProofLib.memRegion_zero,
      sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  rw [ProofLib.memRegion_eight (q + 0xa28#64),
      ProofLib.memRegion_eight (q + 0xa58#64),
      ProofLib.memRegion_eight (q + 0xbe8#64)]
  conv_lhs =>
    arg 2; arg 1; arg 2; arg 2; arg 2; arg 2; arg 2; arg 2; arg 1
    simp (discharger := decide) only [b518x_memRegion_succ8_entry, ProofLib.memRegion_zero,
      sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  unfold b518x_entryScratchCells
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat' (apply congrArg sepExists; funext _)
  sep_ac_rfl

private def b518x_ssRawCells_entry (q : BitVec 64) : SepProp :=
  (((q + 0x930#64) ↦₆₄ 0#64) ∗ ((q + 0x938#64) ↦₆₄ 1#64) ∗ ((q + 0x940#64) ↦₆₄ 0#64)) ∗
  (((q + 0x948#64) ↦₆₄ 0#64) ∗ ((q + 0x950#64) ↦₆₄ 1#64) ∗ ((q + 0x958#64) ↦₆₄ 0#64)) ∗
  (((q + 0x960#64) ↦₆₄ 0#64) ∗ ((q + 0x968#64) ↦₆₄ 1#64) ∗ ((q + 0x970#64) ↦₆₄ 0#64)) ∗
  (((q + 0x978#64) ↦₆₄ 0#64) ∗ ((q + 0x980#64) ↦₆₄ 8#64) ∗ ((q + 0x988#64) ↦₆₄ 0#64)) ∗
  (((q + 0x990#64) ↦₆₄ 0#64) ∗ ((q + 0x998#64) ↦₆₄ 1#64) ∗ ((q + 0x9a0#64) ↦₆₄ 0#64)) ∗
  (((q + 0x9a8#64) ↦₆₄ 0#64) ∗ ((q + 0x9b0#64) ↦₆₄ 1#64) ∗ ((q + 0x9b8#64) ↦₆₄ 0#64)) ∗
  ((q + 0x9c0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
  ((q + 0xa28#64) ↦₆₄ 0xffffffffffffffff#64) ∗
  ((q + 0xa58#64) ↦₆₄ 0xffffffffffffffff#64) ∗
  ((q + 0xa78#64) ↦₆₄ 0#64) ∗
  ((q + 0xa80#64) ↦₆₄ 0#64)

private theorem b518x_empty_vecU8Fresh0A_intro (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
      b518x_vecU8Fresh0A A v [] := by
  unfold b518x_vecU8Fresh0A
  simp only [↓reduceIte]
  refine Entails.sepExists_right 1#64 ?_
  unfold vecU8At vecHeader
  have hp : (⌜([] : List (BitVec 8)).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0⌝ : SepProp) = emp := by
    simp
  have hite : (if (0#64 : BitVec 64) = 0 then emp else
      A.live 1#64 (0#64 : BitVec 64).toNat 1 ∗ (1#64 ↦ₛ ([] : List (BitVec 8))) ∗
        memRegion (1#64 + BitVec.ofNat 64 ([] : List (BitVec 8)).length)
          ((0#64 : BitVec 64).toNat - ([] : List (BitVec 8)).length)) = emp := rfl
  rw [hp, hite]
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, emp_sepConj, sepConj_emp]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem b518x_empty_vecChainGCap0_intro (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 8#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
      ∃∗ ptrRecv : BitVec 64,
        vecAt A 104 8 (fun c a => prostChainGAt A a c) v 0#64 ptrRecv [] := by
  refine Entails.sepExists_right 8#64 ?_
  unfold vecAt vecHeader vecBuf
  have hp : (⌜([] : List ChainG).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0⌝ : SepProp) = emp := by
    simp
  rw [hp]
  simp only [emp_sepConj]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem b518x_prostSSGQAtCapA_empty_intro (A : RustAlloc) (q : BitVec 64) :
    b518x_ssRawCells_entry q ∗
      memRegion (q + 0x9c8#64) 96 ∗
      memRegion (q + 0xa30#64) 40 ∗
      memRegion (q + 0xa60#64) 24 ⊢
      b518x_prostSSGQAtCapA A (q + 0x930#64) SSGQ.empty := by
  unfold b518x_prostSSGQAtCapA SSGQ.empty SSG.empty ExtraGQ.empty kyberAt b518x_ssRawCells_entry
  dsimp only
  have hcap0 : BitVec.ofNat 64 (vecCap4Of ([] : List ChainG).length) = 0#64 := rfl
  rw [hcap0]
  have h1 := b518x_empty_vecU8Fresh0A_intro A (q + 0x930#64)
  have h2 := b518x_empty_vecU8Fresh0A_intro A (q + 0x930#64 + 0x18#64)
  have h3 := b518x_empty_vecU8Fresh0A_intro A (q + 0x930#64 + 0x30#64)
  have h4 := b518x_empty_vecChainGCap0_intro A (q + 0x930#64 + 0x48#64)
  have h5 := b518x_empty_vecU8Fresh0A_intro A (q + 0x930#64 + 0x60#64)
  have h6 := b518x_empty_vecU8Fresh0A_intro A (q + 0x930#64 + 0x78#64)
  have hnone : (0xffffffffffffffff#64 : BitVec 64) = noneCap := rfl
  have hp64_1 : ((q + 0xa78#64) ↦₆₄ 0#64) =
      ((q + 0xa78#64) ↦₃₂ 0#32) ∗ ((q + 0xa78#64 + 4#64) ↦₃₂ 0#32) := by
    simpa using pointsTo64_split32 (q + 0xa78#64) 0#64
  have hp64_2 : ((q + 0xa80#64) ↦₆₄ 0#64) =
      ((q + 0xa80#64) ↦₃₂ 0#32) ∗ ((q + 0xa80#64 + 4#64) ↦₃₂ 0#32) := by
    simpa using pointsTo64_split32 (q + 0xa80#64) 0#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1 h2 h3 h4 h5 h6 ⊢
  rw [hp64_1, hp64_2, hnone]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
    (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3
      (sepConj_mono h4 (sepConj_mono h5 (sepConj_mono h6 (Entails.refl _)))))))

private theorem b518x_sliceCursorAfter_self (slot ptr : BitVec 64) (bs : List (BitVec 8)) :
    (slot ↦₆₄ ptr) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (ptr ↦ₛ bs) =
      sliceCursorAfter slot ptr bs bs := by
  unfold sliceCursorAfter
  rw [Nat.sub_self, show (BitVec.ofNat 64 0 : BitVec 64) = 0#64 from rfl, BitVec.add_zero]

set_option maxHeartbeats 800000 in
private theorem b518x_entry_placed_wp_budget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (s : State) (g : OverDecG)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
     w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 : BitVec 64)
    (hlen_nz : BitVec.ofNat 64 g.enc.length ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x1ee8#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = g.q)
    (hal : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = g.r19)
    (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x216c#64) s
      (vecHeader g.prevPtr g.encCap g.encPtr (BitVec.ofNat 64 g.enc.length) ∗
       b518x_entryScratchCells g.q w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
         w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          vecHeader g.prevPtr g.encCap g.encPtr (BitVec.ofNat 64 g.enc.length) ∗
          ((g.q + 0x920#64) ↦₆₄ g.encPtr) ∗
          ((g.q + 0x928#64) ↦₆₄ BitVec.ofNat 64 g.enc.length) ∗
          ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
          b518x_ssRawCells_entry g.q ∗
          A.pool lim st s1) ∧
        s1.sp = g.q ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = g.r19 ∧
        s1.readReg64 .x20 = g.r20 ∧
        s1.readReg64 .x21 = g.q + 0x930#64 ∧
        s1.readReg64 .x24 = 1#64 ∧
        s1.readReg64 .x25 = 0xffffffffffffffff#64 ∧
        s1.readReg64 .x26 = g.r26 ∧
        s1.readReg64 .x27 = g.prevPtr ∧
        s1.readReg64 .x28 = g.q + 0xa90#64 ∧
        s1.readReg64 .x29 = g.q + 0xc70#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  dsimp only [vecHeader, b518x_entryScratchCells] at ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have hx29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  wp_steps_sync_518 ext ((blkPl_518).base + 0x216c#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨Entails.of_eq (by unfold b518x_ssRawCells_entry; sep_ac_rfl),
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

set_option maxHeartbeats 800000 in
/-- Capacity-explicit Block-`518` Entry (`+0x1ee8 → +0x216c`, `0` events). -/
theorem b518x_entry_cro_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) (st : M.σ) (s0 s : State) (g : OverDecG)
    (henc_ne : g.enc ≠ []) (henc_lt : g.enc.length < 2 ^ 62)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (_hcl : (lsProg_518 ext).CodeLoaded s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1ee8#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = g.q)
    (hal : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = g.r19)
    (hx20 : s.readReg64 .x20 = g.r20)
    (hx26 : s.readReg64 .x26 = g.r26)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx27 : s.readReg64 .x27 = g.prevPtr)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs g.sv) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x216c#64) s
      (overPrevElemAtBudget A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
        overDecScratchPre g.q ∗ stackAt g.q overDecStackX ∗ A.pool lim st s)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x216c#64 sf ∧
        (P_f ⊢ b518x_overDecHeapCapA A lim st sf g g.enc SSGQ.empty))
      (fun _ _ => False) := by
  refine sepWPp_lift_cro_regs hcro ?_
  have hlen_nz := b518x_enc_len_ofNat64_ne_zero henc_ne henc_lt
  unfold overPrevElemAtBudget
  refine SepWPp_weaken_frame (b518x_overPrevElemAt_entails_of_ne_nil (A := A.repAlloc) henc_ne)
    (by sep_focus) ?_
  rw [b518x_overDecScratchPre_split g.q]
  refine SepWPp_weaken_frame (Entails.of_eq (by sep_ac_rfl))
    (show (overPrevElemRestExt A.repAlloc g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
          (g.encPtr ↦ₛ g.enc)) ∗
        ((∃∗ w25 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ w23 : BitVec 64, ∃∗ w22 : BitVec 64,
          ∃∗ w21 : BitVec 64, ∃∗ w20 : BitVec 64, ∃∗ w19 : BitVec 64, ∃∗ w18 : BitVec 64,
          ∃∗ w17 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w15 : BitVec 64, ∃∗ w14 : BitVec 64,
          ∃∗ w13 : BitVec 64, ∃∗ w12 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64,
          ∃∗ w9 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64,
          ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64,
          ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
            b518x_entryScratchCells g.q w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
              w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25) ∗
          b518x_entryScratchKeep g.q) ∗
        stackAt g.q overDecStackX ∗ A.pool lim st s =
      (∃∗ w25 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ w23 : BitVec 64, ∃∗ w22 : BitVec 64,
       ∃∗ w21 : BitVec 64, ∃∗ w20 : BitVec 64, ∃∗ w19 : BitVec 64, ∃∗ w18 : BitVec 64,
       ∃∗ w17 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w15 : BitVec 64, ∃∗ w14 : BitVec 64,
       ∃∗ w13 : BitVec 64, ∃∗ w12 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64,
       ∃∗ w9 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64,
       ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64,
       ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        b518x_entryScratchCells g.q w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
          w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25) ∗
      (overPrevElemRestExt A.repAlloc g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
        (g.encPtr ↦ₛ g.enc) ∗ b518x_entryScratchKeep g.q ∗
        stackAt g.q overDecStackX ∗ A.pool lim st s) by sep_ac_rfl) ?_
  repeat' (apply b518x_sepWPp_exists_left; intro _)
  rename_i w25 w24 w23 w22 w21 w20 w19 w18 w17 w16 w17_0 w14 w13 w12 w11 w10 w9 w8 w7 w6 w5 w4 w3 w2 w1 w0
  have hstep := b518x_entry_placed_wp_budget A lim st ext s g
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
    w14 w17_0 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25
    hlen_nz hpc hrun hsp hal hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx29
  unfold overPrevElemRestExt
  refine SepWPp_bind_sepWP_frame hstep (by sep_focus)
    fun sf hpcf hrunf hclf hpost => ?_
  rcases hpost with ⟨hsp_f, htr_f, hx19_f, hx20_f, hx21_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, hvregs_f⟩
  have hal_f : (sf.sp &&& 15#64 == 0#64) = true := by rwa [hsp_f, ← hsp]
  refine SepWPp.done hpcf hrunf ⟨⟨hpcf, hrunf, hsp_f, hal_f, htr_f.trans htr, hclf,
    hx19_f, hx20_f, hx26_f, hx21_f, hx24_f, hx25_f, hx27_f, hx28_f, hx29_f, hvregs_f.trans hvregs⟩, ?_⟩
  have hss := b518x_prostSSGQAtCapA_empty_intro A.repAlloc g.q
  have hcur := b518x_sliceCursorAfter_self (g.q + 0x920#64) g.encPtr g.enc
  rw [show g.q + 0x920#64 + 8#64 = g.q + 0x928#64 by bv_omega] at hcur
  let F_post : SepProp :=
    overPrevElemRestExt A.repAlloc g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
    sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc g.enc ∗
    memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
    memRegion (g.q + 0xbf0#64) 128 ∗
    stackAt g.q overDecStackX ∗ A.pool lim st sf
  refine Entails.trans (Q := (b518x_ssRawCells_entry g.q ∗ memRegion (g.q + 0x9c8#64) 96 ∗
      memRegion (g.q + 0xa30#64) 40 ∗ memRegion (g.q + 0xa60#64) 24) ∗ F_post)
    (Entails.of_eq (by unfold F_post overPrevElemRestExt b518x_entryScratchKeep; rw [← hcur]; sep_ac_rfl))
    (Entails.trans (sepConj_mono_left (Q := F_post) hss)
      (Entails.of_eq (by unfold b518x_overDecHeapCapA overPrevElemRestBudget F_post; sep_ac_rfl)))

/-! ## Loop Head (`+0x2160 → +0x216c` / `+0x2620`) -/

private theorem b518x_rest_len_ofNat64_ne_zero {rest enc : List (BitVec 8)}
    (hne : rest ≠ []) (hsuf : rest <:+ enc) (hlen : enc.length < 2 ^ 62) :
    BitVec.ofNat 64 rest.length ≠ 0#64 := by
  have hpos : 0 < rest.length := List.length_pos_iff.mpr hne
  rcases hsuf with ⟨t, ht⟩
  have hle : rest.length ≤ enc.length := by rw [← ht, List.length_append]; omega
  intro h0
  have hnat := congrArg BitVec.toNat h0
  rw [BitVec.toNat_ofNat, BitVec.toNat_zero,
      Nat.mod_eq_of_lt (by omega : rest.length < 2 ^ 64)] at hnat
  omega

set_option maxHeartbeats 400000 in
private theorem b518x_head_cons_placed_wp_budget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State)) (s : State) (g : OverDecG) (rest : List (BitVec 8))
    (hlen_nz : BitVec.ofNat 64 rest.length ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x2160#64) (hrun : s.status = .Running) (hsp : s.sp = g.q)
    (hx19 : s.readReg64 .x19 = g.r19) (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64) (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr) (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x216c#64) s
      (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
       sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest ∗ A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢ ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
          sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest ∗ A.pool lim st s1) ∧
        s1.sp = g.q ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = g.r19 ∧ s1.readReg64 .x20 = g.r20 ∧
        s1.readReg64 .x21 = g.q + 0x930#64 ∧ s1.readReg64 .x24 = 1#64 ∧
        s1.readReg64 .x25 = 0xffffffffffffffff#64 ∧ s1.readReg64 .x26 = g.r26 ∧
        s1.readReg64 .x27 = g.prevPtr ∧ s1.readReg64 .x28 = g.q + 0xa90#64 ∧
        s1.readReg64 .x29 = g.q + 0xc70#64 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  dsimp only [sliceCursorAfter] at ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  wp_steps_sync_518 ext ((blkPl_518).base + 0x216c#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl),
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

set_option maxHeartbeats 400000 in
private theorem b518x_head_nil_placed_wp_budget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State)) (s : State) (g : OverDecG)
    (hpc : s.pc = (blkPl_518).base + 0x2160#64) (hrun : s.status = .Running) (hsp : s.sp = g.q)
    (hx19 : s.readReg64 .x19 = g.r19) (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64) (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr) (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x2620#64) s
      (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
       sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc [] ∗ A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢ ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
          sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc [] ∗ A.pool lim st s1) ∧
        s1.sp = g.q ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = g.r19 ∧ s1.readReg64 .x20 = g.r20 ∧
        s1.readReg64 .x21 = g.q + 0x930#64 ∧ s1.readReg64 .x24 = 1#64 ∧
        s1.readReg64 .x25 = 0xffffffffffffffff#64 ∧ s1.readReg64 .x26 = g.r26 ∧
        s1.readReg64 .x27 = g.prevPtr ∧ s1.readReg64 .x28 = g.q + 0xa90#64 ∧
        s1.readReg64 .x29 = g.q + 0xc70#64 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  dsimp only [sliceCursorAfter, List.length_nil, BitVec.ofNat_eq_ofNat] at ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  wp_steps_sync_518 ext ((blkPl_518).base + 0x2620#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl),
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

/-- Capacity-explicit loop head (`+0x2160 → +0x216c`) when `rest ≠ []` (`0` events). -/
theorem b518x_headCons_cro_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) (st : M.σ) (s0 s : State)
    (g : OverDecG) (v : SSGQ) (rest : List (BitVec 8))
    (hne : rest ≠ []) (hsuf : rest <:+ g.enc) (hlen : g.enc.length < 2 ^ 62)
    (hregs : OverDecRegsCroPlaced ext s0 g 0x2160#64 s) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x216c#64) s
      (b518x_overDecHeapCapA A lim st s g rest v)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x216c#64 sf ∧
        (P_f ⊢ b518x_overDecHeapCapA A lim st sf g rest v))
      (fun _ _ => False) := by
  rcases hregs with ⟨hcro, hpc, hrun, hsp, hal, htr, _hcl,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  refine sepWPp_lift_cro_regs hcro ?_
  have hlen_nz := b518x_rest_len_ofNat64_ne_zero hne hsuf hlen
  have hstep := b518x_head_cons_placed_wp_budget A lim st ext s g rest hlen_nz
    hpc hrun hsp hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
  unfold b518x_overDecHeapCapA
  refine SepWPp_bind_sepWP_frame hstep (by sep_focus)
    fun sf hpcf hrunf hclf hpost => ?_
  rcases hpost with ⟨hsp_f, htr_f, hx19_f, hx20_f, hx21_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, hvregs_f⟩
  have hal_f : (sf.sp &&& 15#64 == 0#64) = true := by rwa [hsp_f, ← hsp]
  refine SepWPp.done hpcf hrunf ⟨⟨hpcf, hrunf, hsp_f, hal_f, htr_f.trans htr, hclf,
    hx19_f, hx20_f, hx26_f, hx21_f, hx24_f, hx25_f, hx27_f, hx28_f, hx29_f, hvregs_f.trans hvregs⟩, ?_⟩
  exact Entails.of_eq (by sep_ac_rfl)

/-- Capacity-explicit loop head (`+0x2160 → +0x2620`) when `rest = []` (`0` events). -/
theorem b518x_headNil_cro_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) (st : M.σ) (s0 s : State)
    (g : OverDecG) (v : SSGQ)
    (hregs : OverDecRegsCroPlaced ext s0 g 0x2160#64 s) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2620#64) s
      (b518x_overDecHeapCapA A lim st s g [] v)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x2620#64 sf ∧
        (P_f ⊢ b518x_overDecHeapCapA A lim st sf g [] v))
      (fun _ _ => False) := by
  rcases hregs with ⟨hcro, hpc, hrun, hsp, hal, htr, _hcl,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  refine sepWPp_lift_cro_regs hcro ?_
  have hstep := b518x_head_nil_placed_wp_budget A lim st ext s g
    hpc hrun hsp hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
  unfold b518x_overDecHeapCapA
  refine SepWPp_bind_sepWP_frame hstep (by sep_focus)
    fun sf hpcf hrunf hclf hpost => ?_
  rcases hpost with ⟨hsp_f, htr_f, hx19_f, hx20_f, hx21_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, hvregs_f⟩
  have hal_f : (sf.sp &&& 15#64 == 0#64) = true := by rwa [hsp_f, ← hsp]
  refine SepWPp.done hpcf hrunf ⟨⟨hpcf, hrunf, hsp_f, hal_f, htr_f.trans htr, hclf,
    hx19_f, hx20_f, hx26_f, hx21_f, hx24_f, hx25_f, hx27_f, hx28_f, hx29_f, hvregs_f.trans hvregs⟩, ?_⟩
  exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ExactDecodePlacedBudgetAuxA
