/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmBytesPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmVarintBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmVarintPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ExactDecodePlacedBudgetAuxA
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5Budget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5PlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import ProofLib.Hoare.SubroutineOk
import ProofLib.SepLogic.WPp

/-!
# Capacity-Explicit Varint Arms (Tags 1, 5, 10, 11) for Block `518` Exact Decode

Verifies `b518x_arm_varint_cro_placed_of_alloc` (`overDecArmOff fl → +0x2160`, `0` events) for
tags 1, 5, 10, and 11 on Block `518`, preserving `b518x_overDecHeapCapA`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ExactDecodePlacedBudgetAuxC

open Arm64 ProofLib SepProp
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement lsmpl withLsCl withLsCodeLoaded
)
open CryptoVerification.RustHeap (RustAlloc vecAt vecU8)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalProtoCodec (
  decodeVarint encodeVarint decodeVarint_encodeVarint
)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  DecodeVarintSlowGhost sliceCursorAfter sliceCursorAt
)
open CryptoVerification.E2E.Record.L1GX (kyberAt pidAt)
open CryptoVerification.E2E.Record.DeserializeGeneral (SSG prostChainGAt)
open Symbolic.Swarm.TRREF.B3DeserQ (GenFieldQ SSGQ)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkPl_518 lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (
  OverDecG OverDecRegsCroPlaced OverDecRegsPlaced OverDecSavedRegsPl OverDecVarintField
  overDecArmOff overDecStackX overDecWt
  overDec_payload_suffix_and_len sliceCursorAfter_split_sub sliceCursorAfter_unsplit_sub
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH (decodeVarint2StackX)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (
  DecodeVarintSliceEnv decodeVarintSliceEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential (vecCap4Of)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget (
  mergeFieldQEvents
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5Budget (
  DecodeVarint2Env decodeVarint2SpecX
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5PlacedBudget (
  DecodeVarint5PlacedOkExtX decodeVarint5_placed_ok_ext_x
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmVarintPlacedBudget (
  overDecVarint_post_tag1_placed overDecVarint_post_tag5_placed
  overDecVarint_post_tag10_placed overDecVarint_post_tag11_placed
  overDecVarint_pre_tag1_placed overDecVarint_pre_tag5_placed
  overDecVarint_pre_tag10_placed overDecVarint_pre_tag11_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsBudget (
  overPrevElemRestBudget sepWPp_lift_cro_regs
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ExactDecodePlacedBudgetAuxA (
  b518x_overDecHeapCapA b518x_prostSSGQAtCapA b518x_vecU8Fresh0A
)

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

private def b518x_prostSSGQVarintHead (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) : SepProp :=
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
    kyberAt A ss v.ext.kyber emp

private theorem b518x_kyberAt_sep (A : RustAlloc) (ss : BitVec 64)
    (kyb : Option (BitVec 32 × List (BitVec 8))) (R : SepProp) :
    kyberAt A ss kyb R = kyberAt A ss kyb emp ∗ R := by
  cases kyb <;> simp only [kyberAt, sepConj_emp, sepConj_assoc]

private theorem b518x_prostSSGQAtCapA_varint_split (A : RustAlloc) (q : BitVec 64) (v : SSGQ) :
    b518x_prostSSGQAtCapA A (q + 0x930#64) v =
      b518x_prostSSGQVarintHead A (q + 0x930#64) v ∗
        ((q + 0xa78#64) ↦₃₂ v.base.version) ∗
        ((q + 0xa7c#64) ↦₃₂ v.base.prevCounter) ∗
        ((q + 0xa80#64) ↦₃₂ v.ext.remReg) ∗
        ((q + 0xa84#64) ↦₃₂ v.ext.locReg) := by
  have h148 : (q + 0x930#64) + 0x148#64 = q + 0xa78#64 := by bv_omega
  have h14c : (q + 0x930#64) + 0x14c#64 = q + 0xa7c#64 := by bv_omega
  have h150 : (q + 0x930#64) + 0x150#64 = q + 0xa80#64 := by bv_omega
  have h154 : (q + 0x930#64) + 0x154#64 = q + 0xa84#64 := by bv_omega
  unfold b518x_prostSSGQAtCapA b518x_prostSSGQVarintHead
  rw [b518x_kyberAt_sep, h148, h14c, h150, h154]
  sep_ac_rfl

private theorem b518x_stackAt_sub_eq (sp : BitVec 64) (M N : Nat) (hMN : N ≤ M := by decide)
    (hbound : M < 2 ^ 64 := by decide) :
    stackAt sp M = stackAt sp N ∗ memRegion (sp - BitVec.ofNat 64 M) (M - N) := by
  have h1 : M = N + (M - N) := (Nat.add_sub_of_le hMN).symm
  have h2 := ProofLib.stackAt_split_bottom sp N (M - N) (by omega)
  rw [← h1] at h2; rw [h2, sepConj_comm]

private theorem b518x_lscl_of_cl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h : DecodeVarint5PlacedOkExtX A lim ext) :
    subroutine_ok (lsProg_518 ext) (lsmpl.base 515)
      (withLsCodeLoaded lsmpl (decodeVarint2SpecX A lim)) :=
  subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => by
    dsimp only [withLsCl, withLsCodeLoaded] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq; exact hq.2)

private theorem b518x_dv2Env_encodeVarint_iff (val : BitVec 32) (rest : List (BitVec 8))
    (evs : List AllocEvent) :
    DecodeVarint2Env (encodeVarint (val.setWidth 64) ++ rest) evs ↔ evs = [] := by
  unfold DecodeVarint2Env DecodeVarintSliceEnv decodeVarintSliceEvents
  simp [decodeVarint_encodeVarint (val.setWidth 64) rest]

private theorem b518x_fitsEnv_dv2 {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (val : BitVec 32) (rest : List (BitVec 8)) :
    FitsEnv M lim st (DecodeVarint2Env (encodeVarint (val.setWidth 64) ++ rest)) := by
  intro evs hevs; rw [b518x_dv2Env_encodeVarint_iff] at hevs; subst hevs; trivial

private theorem b518x_savedRegsPl_of_cs {g : OverDecG} {s1 s2 : State}
    (hs1 : OverDecSavedRegsPl g s1) (hcs : CalleeSavedPreserved s1 s2) :
    OverDecSavedRegsPl g s2 := by
  rcases hs1 with ⟨h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  rcases hcs with ⟨c19, c20, c21, _, _, c24, c25, c26, c27, c28, c29, cv⟩
  exact ⟨c19.trans h19, c20.trans h20, c26.trans h26, c21.trans h21, c24.trans h24,
    c25.trans h25, c27.trans h27, c28.trans h28, c29.trans h29, cv.trans hv⟩

private theorem b518x_sepWPp_bind_vm {Inv : Memory → Prop}
    {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hInv : Inv s.mem) (hInv_kf : ∀ {m m' : Memory}, Inv m → m.KeepsFrozen m' → Inv m')
    (hstep : SepWP prog mid s P_step
      (fun sm P_step' => VmPreserved s sm ∧ (P_step' ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, VmPreserved s sm → sm.pc = mid → sm.status = .Running →
      prog.CodeLoaded sm.mem → Inv sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hvm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hent) hmm
  have hLm := hsteps.codeLoaded hL
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hvm hpc hrun hLm (hInv_kf hInv hsteps.keepsFrozen) hregs R hmm' hLm
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

private theorem b518x_sepWPp_ret_vm {prog : Program} {ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hstep : SepWP prog ret s P_step
      (fun sf P_step' => VmPreserved s sf ∧ (P_step' ⊢ P_step_post) ∧ Q_regs sf))
    (hP : P = P_step ∗ F)
    (hpost : ∀ sf : State, VmPreserved s sf → sf.pc = ret → sf.status = .Running →
      prog.CodeLoaded sf.mem → Q_regs sf → Q sf (P_step_post ∗ F)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_step', hmf, hvm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  refine ⟨sf, hsteps, .inl ⟨hpc, hrun, P_step_post ∗ F, ?_,
    hpost sf hvm hpc hrun (hsteps.codeLoaded hL) hregs⟩⟩
  rw [sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hent) hmf

private theorem b518x_call_dv5_lscl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {ret : BitVec 64} {s0 s : State}
    {bufRef slot ptr : BitVec 64} {val : BitVec 32} {rest : List (BitVec 8)}
    {F : SepProp} {Q : State → SepProp → Prop}
    (hDv5 : subroutine_ok (lsProg_518 ext) (lsmpl.base 515)
      (withLsCodeLoaded lsmpl (decodeVarint2SpecX A lim)))
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hpc : s.pc = lsmpl.base 515) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = bufRef)
    (hlen : (encodeVarint (val.setWidth 64) ++ rest).length < 2 ^ 63)
    (hnext : ∀ s2 : State, s2.pc = s.readReg64 .lr → s2.status = .Running →
      s2.sp = s.sp → s2.spAligned = true → CalleeSavedPreserved s s2 →
      (lsProg_518 ext).CodeLoaded s2.mem →
      s2.readReg64 .x0 = 0#64 → s2.readReg64 .x1 = val.setWidth 64 →
      s2.trace = s0.trace →
      SepWPp (lsProg_518 ext) ret s2
        (((bufRef ↦₆₄ slot) ∗
          sliceCursorAfter slot ptr (encodeVarint (val.setWidth 64) ++ rest) rest ∗
          A.pool lim st s2 ∗ stackAt s.sp decodeVarint2StackX) ∗ F)
        Q (fun _ _ => False)) :
    SepWPp (lsProg_518 ext) ret s
      (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr (encodeVarint (val.setWidth 64) ++ rest) ∗
        A.pool lim st s ∗ stackAt s.sp decodeVarint2StackX) ∗ F)
      Q (fun _ _ => False) := by
  intro R hm hL
  let x : DecodeVarintSlowGhost := ⟨bufRef, slot, ptr, encodeVarint (val.setWidth 64) ++ rest⟩
  have hm' : s.mem ⊨ (withLsCodeLoaded lsmpl (decodeVarint2SpecX A lim)).pre (x, st) s ∗ (F ∗ R) := by
    dsimp only [withLsCodeLoaded, decodeVarint2SpecX, x]
    rw [sepConj_assoc, sepConj_left_comm _ (⌜LibsignalCodeLoaded _ _⌝), satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hlen, b518x_fitsEnv_dv2 val rest⟩, ?_⟩
    simpa only [sepConj_assoc] using hm
  obtain ⟨sm, hsteps, hout, _⟩ :=
    hDv5.no_fault_before_outcome (x, st) (F ∗ R) s hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · dsimp only [withLsCodeLoaded, decodeVarint2SpecX, x] at hpost
    rw [decodeVarint_encodeVarint (val.setWidth 64) rest] at hpost; dsimp only at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hx0m, hx1m⟩, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htrm, hpost⟩
    have hpost_ex : sm.mem ⊨
        (∃∗ evs : List AllocEvent,
          ⌜DecodeVarint2Env (encodeVarint (val.setWidth 64) ++ rest) evs⌝ ∗
          A.pool lim (M.stepEvents evs st) sm) ∗
        (((bufRef ↦₆₄ slot) ∗
          sliceCursorAfter slot ptr (encodeVarint (val.setWidth 64) ++ rest) rest ∗
          stackAt s.sp decodeVarint2StackX) ∗ (F ∗ R)) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost_ex
    obtain ⟨evs, hpost_ex⟩ := hpost_ex
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_ex
    rcases hpost_ex with ⟨hevs, hpost_ex⟩
    rw [b518x_dv2Env_encodeVarint_iff] at hevs; subst hevs
    rw [M.stepEvents_nil] at hpost_ex
    have hpost_fin : sm.mem ⊨
        (((bufRef ↦₆₄ slot) ∗
          sliceCursorAfter slot ptr (encodeVarint (val.setWidth 64) ++ rest) rest ∗
          A.pool lim st sm ∗ stackAt s.sp decodeVarint2StackX) ∗ F) ∗ R :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost_ex
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm (hsteps.codeLoaded hL)
        hx0m hx1m (htrm.trans htr) R hpost_fin (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

set_option maxHeartbeats 600000 in
private theorem b518x_varint_one [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {s0 s : State} {g : OverDecG} {v v' : SSGQ} {fl : GenFieldQ} {rest : List (BitVec 8)}
    {armOff retOff spOff : BitVec 64} {oldVal val : BitVec 32} {otherCells : SepProp}
    (hDv5 : subroutine_ok (lsProg_518 ext) (lsmpl.base 515)
      (withLsCodeLoaded lsmpl (decodeVarint2SpecX A lim)))
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpay : fl.payload = encodeVarint (val.setWidth 64))
    (hsuf : (fl.enc ++ rest) <:+ g.enc) (hlen : g.enc.length < 2 ^ 62)
    (hregs : OverDecRegsPlaced ext s0 g armOff s)
    (hcell_in : b518x_prostSSGQAtCapA A.repAlloc (g.q + 0x930#64) v =
      b518x_prostSSGQVarintHead A.repAlloc (g.q + 0x930#64) v ∗
        ((g.q + spOff) ↦₃₂ oldVal) ∗ otherCells)
    (hcell_out : b518x_prostSSGQVarintHead A.repAlloc (g.q + 0x930#64) v ∗
        ((g.q + spOff) ↦₃₂ val) ∗ otherCells =
      b518x_prostSSGQAtCapA A.repAlloc (g.q + 0x930#64) v')
    (hpre_step : SepWP (lsProg_518 ext) (lsmpl.base 515) s
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))
      (fun s1 P1 => VmPreserved s s1 ∧ (P1 ⊢ ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))) ∧
        s1.sp = g.q ∧ s1.trace = s0.trace ∧ s1.readReg64 .x0 = g.q + 0xbe8#64 ∧
        s1.readReg64 .lr = (blkPl_518).base + retOff ∧ OverDecSavedRegsPl g s1))
    (hpost_step : ∀ s2 : State, s2.pc = (blkPl_518).base + retOff → s2.status = .Running →
      s2.sp = g.q → (s2.sp &&& 15#64 == 0#64) = true → s2.trace = s0.trace →
      s2.readReg64 .x0 = 0#64 → s2.readReg64 .x1 = val.setWidth 64 →
      OverDecSavedRegsPl g s2 →
      SepWP (lsProg_518 ext) ((blkPl_518).base + 8544#64) s2 ((g.q + spOff) ↦₃₂ oldVal)
        (fun sf P_f => VmPreserved s2 sf ∧ (P_f ⊢ ((g.q + spOff) ↦₃₂ val)) ∧
          sf.sp = g.q ∧ sf.trace = s0.trace ∧ OverDecSavedRegsPl g sf)) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 8544#64) s
      (b518x_overDecHeapCapA A lim st s g (fl.payload ++ rest) v)
      (fun sf P_f => OverDecRegsPlaced ext s0 g 8544#64 sf ∧
        (P_f ⊢ b518x_overDecHeapCapA A lim st sf g rest v'))
      (fun _ _ => False) := by
  rcases hregs with ⟨_hpc, _hrun, hsp, hsp_align, _htr, _hL, _hsaved⟩
  have hq_align : (g.q &&& 15#64 == 0#64) = true := by rwa [← hsp]
  obtain ⟨pfx, hpfx, hpay_len⟩ := overDec_payload_suffix_and_len hsuf hlen
  have hlen63 : (encodeVarint (val.setWidth 64) ++ rest).length < 2 ^ 63 := by rw [← hpay]; omega
  have hcur_split :
      sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc (fl.payload ++ rest) =
        (g.encPtr ↦ₛ pfx) ∗
          sliceCursorAt (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
            (encodeVarint (val.setWidth 64) ++ rest) := by
    conv_lhs => arg 3; rw [hpfx]
    rw [sliceCursorAfter_split_sub (g.q + 0x920#64) g.encPtr pfx (fl.payload ++ rest), hpay]
  let frameRest :=
    overPrevElemRestBudget A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
      (g.encPtr ↦ₛ pfx) ∗ b518x_prostSSGQVarintHead A.repAlloc (g.q + 0x930#64) v ∗
      otherCells ∗ memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
      memRegion (g.q + 0xbf0#64) 128 ∗
      memRegion (g.q - BitVec.ofNat 64 overDecStackX) (overDecStackX - decodeVarint2StackX)
  have hsplit : b518x_overDecHeapCapA A lim st s g (fl.payload ++ rest) v =
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
        (sliceCursorAt (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
          (encodeVarint (val.setWidth 64) ++ rest) ∗
          A.pool lim st s ∗ stackAt g.q decodeVarint2StackX ∗
          ((g.q + spOff) ↦₃₂ oldVal) ∗ frameRest) := by
    unfold b518x_overDecHeapCapA frameRest
    rw [hcur_split, hcell_in, b518x_stackAt_sub_eq g.q overDecStackX decodeVarint2StackX]
    sep_ac_rfl
  rw [hsplit]
  refine b518x_sepWPp_bind_vm hcl (fun hcl' hkf => hcl'.of_keepsFrozen hkf) hpre_step rfl
    fun s1 hvm1 hpc1 hrun1 _hL1 hcl1 ⟨hsp1, htr1, hx0_1, hlr1, hsaved1⟩ => ?_
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hq_align
  have hframe_eq :
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
        (sliceCursorAt (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
          (encodeVarint (val.setWidth 64) ++ rest) ∗
          A.pool lim st s ∗ stackAt g.q decodeVarint2StackX ∗
          ((g.q + spOff) ↦₃₂ oldVal) ∗ frameRest) =
      (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
        sliceCursorAt (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
          (encodeVarint (val.setWidth 64) ++ rest) ∗
        A.pool lim st s1 ∗ stackAt s1.sp decodeVarint2StackX) ∗
        (((g.q + spOff) ↦₃₂ oldVal) ∗ frameRest) := by
    rw [A.pool_transport lim st s s1 hvm1, hsp1]; simp only [sepConj_assoc]
  rw [hframe_eq]
  refine b518x_call_dv5_lscl hDv5 hcl1 htr1 hpc1 hrun1 hsp1_al hx0_1 hlen63
    fun s2 hpc2_lr hrun2 hsp2_1 _hsp2_al hcs2 _hL2 hx0_2 hx1_2 htr2 => ?_
  have hpc2 : s2.pc = (blkPl_518).base + retOff := hpc2_lr.trans hlr1
  have hsp2 : s2.sp = g.q := hsp2_1.trans hsp1
  have hsp2_al : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hq_align
  have hsaved2 := b518x_savedRegsPl_of_cs hsaved1 hcs2
  rw [hsp1]
  refine b518x_sepWPp_ret_vm
    (hpost_step s2 hpc2 hrun2 hsp2 hsp2_al htr2 hx0_2 hx1_2 hsaved2)
    (F := ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAfter (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
        (encodeVarint (val.setWidth 64) ++ rest) rest ∗
      A.pool lim st s2 ∗ stackAt g.q decodeVarint2StackX ∗ frameRest)
    (by sep_ac_rfl)
    fun sf hvm2 hpcf hrunf hLf ⟨hspf, htrf, hsavedf⟩ => ?_
  have hspf_al : (sf.sp &&& 15#64 == 0#64) = true := by rw [hspf]; exact hq_align
  refine ⟨⟨hpcf, hrunf, hspf, hspf_al, htrf, hLf, hsavedf⟩, Entails.of_eq ?_⟩
  have hcur_unsplit :
      (g.encPtr ↦ₛ pfx) ∗
        sliceCursorAfter (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
          (encodeVarint (val.setWidth 64) ++ rest) rest =
      sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest := by
    rw [← hpay, sliceCursorAfter_unsplit_sub (g.q + 0x920#64) g.encPtr pfx fl.payload rest, ← hpfx]
  unfold b518x_overDecHeapCapA frameRest
  rw [A.pool_transport lim st s2 sf hvm2, ← hcell_out, ← hcur_unsplit,
      b518x_stackAt_sub_eq g.q overDecStackX decodeVarint2StackX]
  sep_ac_rfl

/-- Capacity-explicit varint arms (Tags `1, 5, 10, 11`, `0` events) preserving `b518x_overDecHeapCapA`. -/
theorem b518x_arm_varint_cro_placed_of_alloc [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hAlloc : AllocContractsPlaced M A lim ext)
    (st : M.σ) (s0 s : State) (g : OverDecG) (v : SSGQ) (fl : GenFieldQ) (rest : List (BitVec 8))
    (hP : OverDecVarintField fl) (hsuf : (fl.enc ++ rest) <:+ g.enc) (hlen : g.enc.length < 2 ^ 62)
    (hregs_cro : OverDecRegsCroPlaced ext s0 g (overDecArmOff fl) s)
    (hx0 : s.readReg64 .x0 = overDecWt fl) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 8544#64) s
      (b518x_overDecHeapCapA A lim st s g (fl.payload ++ rest) v)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 8544#64 sf ∧
        (P_f ⊢ b518x_overDecHeapCapA A lim
          (M.stepEvents (mergeFieldQEvents (vecCap4Of v.base.recv.length) v.base.recv.length fl) st)
          sf g rest (v.apply fl)))
      (fun _ _ => False) := by
  have hDv5 := b518x_lscl_of_cl (decodeVarint5_placed_ok_ext_x hAlloc)
  rcases hregs_cro with ⟨hcro, hregs⟩
  refine sepWPp_lift_cro_regs hcro ?_
  rcases fl with fb | _ | _ | val | val | _ | _ | _
  · rcases fb with val | _ | _ | _ | val | _ | _ | _
    · have hev : mergeFieldQEvents (vecCap4Of v.base.recv.length) v.base.recv.length (.base (.version val)) = [] := rfl
      rw [hev, M.stepEvents_nil]
      exact b518x_varint_one hDv5 hcro.1 rfl hsuf hlen hregs
        (by rw [b518x_prostSSGQAtCapA_varint_split])
        (by rw [b518x_prostSSGQAtCapA_varint_split]; dsimp only [SSGQ.apply, SSG.apply, b518x_prostSSGQVarintHead])
        (overDecVarint_pre_tag1_placed hregs hx0) overDecVarint_post_tag1_placed
    · cases hP
    · cases hP
    · cases hP
    · have hev : mergeFieldQEvents (vecCap4Of v.base.recv.length) v.base.recv.length (.base (.prevCounter val)) = [] := rfl
      rw [hev, M.stepEvents_nil]
      exact b518x_varint_one hDv5 hcro.1 rfl hsuf hlen hregs
        (by rw [b518x_prostSSGQAtCapA_varint_split]; sep_ac_rfl)
        (by rw [b518x_prostSSGQAtCapA_varint_split]; dsimp only [SSGQ.apply, SSG.apply, b518x_prostSSGQVarintHead]; sep_ac_rfl)
        (overDecVarint_pre_tag5_placed hregs hx0) overDecVarint_post_tag5_placed
    · cases hP
    · cases hP
    · cases hP
  · cases hP
  · cases hP
  · have hev : mergeFieldQEvents (vecCap4Of v.base.recv.length) v.base.recv.length (.remReg val) = [] := rfl
    rw [hev, M.stepEvents_nil]
    exact b518x_varint_one hDv5 hcro.1 rfl hsuf hlen hregs
      (by rw [b518x_prostSSGQAtCapA_varint_split]; sep_ac_rfl)
      (by rw [b518x_prostSSGQAtCapA_varint_split]; dsimp only [SSGQ.apply, b518x_prostSSGQVarintHead]; sep_ac_rfl)
      (overDecVarint_pre_tag10_placed hregs hx0) overDecVarint_post_tag10_placed
  · have hev : mergeFieldQEvents (vecCap4Of v.base.recv.length) v.base.recv.length (.locReg val) = [] := rfl
    rw [hev, M.stepEvents_nil]
    exact b518x_varint_one hDv5 hcro.1 rfl hsuf hlen hregs
      (by rw [b518x_prostSSGQAtCapA_varint_split]; sep_ac_rfl)
      (by rw [b518x_prostSSGQAtCapA_varint_split]; dsimp only [SSGQ.apply, b518x_prostSSGQVarintHead]; sep_ac_rfl)
      (overDecVarint_pre_tag11_placed hregs hx0) overDecVarint_post_tag11_placed
  · cases hP
  · cases hP
  · cases hP

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ExactDecodePlacedBudgetAuxC
