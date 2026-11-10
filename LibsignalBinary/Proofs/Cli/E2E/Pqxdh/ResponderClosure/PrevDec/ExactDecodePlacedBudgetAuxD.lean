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
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmBytesPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ExactDecodePlacedBudgetAuxA
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWPlacedBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ProstMergeBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Capacity-Explicit Bytes Arms (Tags 2, 3, 4, 13, 15) for Block `518` Exact Decode

Verifies `b518x_arm_bytes_cro_placed_of_bm6w` (`overDecArmOff fl → +0x2160`) for tags 2, 3, 4, 13,
and 15 on Block `518`, stepping exact `mergeFieldQEvents` on fresh `Vec<u8>` fields (`valCap = 0#64`)
and preserving `b518x_overDecHeapCapA`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ExactDecodePlacedBudgetAuxD

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (RustAlloc vecAt vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalProtoCodec (encodeVarint mergeBytes)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  BytesMergeGhost sliceCursorAfter sliceCursorAt
)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.E2E.Record.L1GX (kyberAt pidAt)
open CryptoVerification.E2E.Record.DeserializeGeneral (GenField SSG prostChainGAt)
open Symbolic.Swarm.TRREF.B3DeserQ (GenFieldQ SSGQ)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkPl_518 lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (
  OverDecBytesField OverDecG OverDecRegsCroPlaced OverDecRegsPlaced
  bytesMerge3Stack overDecArmOff overDecWt
  overDec_mergeBytes_eq overDec_payload_suffix_and_len
  sliceCursorAfter_split_sub sliceCursorAfter_unsplit_sub
  stackAt_overDec_to_bytesMerge3
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (
  BytesMergeEnv bytesMergeEventsCore doReserveClearEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential (vecCap4Of)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ProstMergeBudget (
  bytesDropEvents bytesMergeAllocEvents bytesMergeEvents doReserveEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget (
  GenFieldQ.FreshBytes basicFieldByteLen mergeFieldQEvents
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWDefsBudget (
  bytesMerge3RawSpecW
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWPlacedBudget (
  BytesMerge6Placed514OkExtW
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmBytesPlacedBudget (
  overDec_cbz_placed_pool_wp
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsBudget (
  overPrevElemRestBudget sepWPp_lift_cro_regs
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ExactDecodePlacedBudgetAuxA (
  b518x_overDecHeapCapA b518x_prostSSGQAtCapA b518x_vecU8Fresh0A
)

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

private theorem b518x_bytesMergeEventsCore_zero_eq {bs b rest : List (BitVec 8)}
    (hmerge : mergeBytes .lengthDelimited bs = some (b, rest)) (hb_ne : b ≠ []) :
    bytesMergeEventsCore .lengthDelimited 0#64 bs = bytesMergeEvents 0 b.length := by
  have hpos : 0 < b.length := List.length_pos_iff.mpr hb_ne
  have hlen_ne : b.length ≠ 0 := Nat.ne_of_gt hpos
  have hnot_le : ¬ b.length ≤ 0 := by omega
  unfold bytesMergeEventsCore bytesMergeEvents bytesMergeAllocEvents bytesDropEvents doReserveEvents
  rw [hmerge]
  simp only [hlen_ne, hpos, hnot_le, doReserveClearEvents, BitVec.toNat_zero, ↓reduceIte,
    List.append_assoc]

private theorem b518x_weaken_frame {prog : Program} {ret : BitVec 64} {s : State}
    {P P₁ P₂ F : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P₁ ⊢ P₂) (hP : P = P₁ ∗ F) (hnext : SepWPp prog ret s (P₂ ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL; rw [hP, sepConj_assoc] at hm
  exact hnext R (by rw [sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hent) hm) hL

private theorem b518x_ret_frame {prog : Program} {ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs Q_pool : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hstep : SepWP prog ret s P_step
      (fun sf P_step' => ((P_step' ⊢ P_step_post) ∧ Q_regs sf) ∧ Q_pool sf))
    (hP : P = P_step ∗ F)
    (hpost : ∀ sf : State, sf.pc = ret → sf.status = .Running →
      prog.CodeLoaded sf.mem → Q_regs sf → Q_pool sf → Q sf (P_step_post ∗ F)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL; rw [hP, sepConj_assoc] at hm
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_step', hmf, ⟨hent, hregs⟩, hpool⟩ | ⟨_, _hoom⟩⟩ :=
    hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  refine ⟨sf, hsteps, .inl ⟨hpc, hrun, P_step_post ∗ F, ?_,
    hpost sf hpc hrun (hsteps.codeLoaded hL) hregs hpool⟩⟩
  rw [sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hent) hmf

private theorem b518x_bind_cro {prog : Program} {mid ret : BitVec 64} {s : State}
    [LibsignalPlacement] {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P_step (fun sm P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      prog.CodeLoaded sm.mem → LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL; rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hent) hmm
  have hLm := hsteps.codeLoaded hL
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hpc hrun hLm (hcro.of_keepsFrozen hsteps.keepsFrozen) hregs R hmm' hLm
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

private theorem b518x_call_bm6w_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {prog : Program}
    {target ret lrVal : BitVec 64} {st : M.σ} {s : State} {x : BytesMergeGhost}
    {T P F : SepProp} {Q : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hok : subroutine_ok prog target (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecW A lim)))
    (hpc : s.pc = target) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hlr : s.readReg64 .x30 = lrVal)
    (hpre_eq : (bytesMerge3RawSpecW A lim).pre (x, st) s =
      ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
        s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 62 ∧
        FitsEnv M lim st (BytesMergeEnv x)⌝ ∗ T)
    (hφ : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 62 ∧
      FitsEnv M lim st (BytesMergeEnv x))
    (hP : P = T ∗ F)
    (hnext : ∀ sm : State, sm.pc = lrVal → sm.status = .Running →
      sm.sp = s.sp → sm.spAligned = true → CalleeSavedPreserved s sm →
      prog.CodeLoaded sm.mem →
      SepWPp prog ret sm ((bytesMerge3RawSpecW A lim).post (x, st) s sm ∗ F) Q
        (fun _ _ => False)) :
    SepWPp prog ret s P Q (fun _ _ => False) := by
  intro R hm hL
  have hm' : s.mem ⊨
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecW A lim)).pre (x, st) s ∗ (F ∗ R) := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm _ (⌜LibsignalCodeRoLoaded _ _⌝), satisfies_pure_sepConj]
    refine ⟨hcro, ?_⟩; rw [hpre_eq, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hφ, ?_⟩; rw [hP, sepConj_assoc] at hm; exact hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, hpost, hspm, hcsm⟩ | ⟨_, hoom⟩⟩ :=
    subroutine_ok_apply_full (oom := fun _ => False) hok (x, st) (F ∗ R) hpc hrun hm' hsp_al
      (by intro _ _ hp; dsimp only [withLsCodeRoLoaded, bytesMerge3RawSpecW] at hp
          exact not_satisfies_false_sepConj hp)
      (by intro _ _ _ he; dsimp only [withLsCodeRoLoaded, bytesMerge3RawSpecW] at he
          exact not_satisfies_false_sepConj he)
      (by intro _ _ ho; dsimp only [withLsCodeRoLoaded, bytesMerge3RawSpecW] at ho
          exact not_satisfies_false_sepConj ho) hL
  · have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp_al
    dsimp only [withLsCodeRoLoaded] at hpost; rw [← sepConj_assoc] at hpost
    have hLm := hsteps.codeLoaded hL
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm (hpcm.trans hlr) hrunm hspm hsp_alm hcsm hLm R hpost hLm
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact hoom.elim

private abbrev B518xArmPrePost [LibsignalPlacement] (s : State) (g : OverDecG)
    (valPtr lrOff : BitVec 64) (s1 : State) (P_f : SepProp) : Prop :=
  (P_f ⊢ emp) ∧ s1.sp = g.q ∧ s1.trace = s.trace ∧
  s1.readReg64 .x0 = 2#64 ∧ s1.readReg64 .x1 = valPtr ∧ s1.readReg64 .x2 = g.q + 0xbe8#64 ∧
  s1.readReg64 .x19 = g.r19 ∧ s1.readReg64 .x20 = g.r20 ∧
  s1.readReg64 .x21 = g.q + 0x930#64 ∧ s1.readReg64 .x24 = 1#64 ∧
  s1.readReg64 .x25 = 0xffffffffffffffff#64 ∧ s1.readReg64 .x26 = g.r26 ∧
  s1.readReg64 .x27 = g.prevPtr ∧ s1.readReg64 .x28 = g.q + 0xa90#64 ∧
  s1.readReg64 .x29 = g.q + 0xc70#64 ∧ s1.readReg64 .x30 = (blkPl_518).base + lrOff ∧
  calleeSavedVRegs s1 = calleeSavedVRegs s ∧
  (∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ),
    A.pool lim st s1 = A.pool lim st s)

local macro "b518x_prove_arm_pre" : tactic => `(tactic| (
  have hx0' : _ = 2#64 := ‹_›
  have hx19' : _ = _ := ‹_›; have hx20' : _ = _ := ‹_›; have hx21' : _ = _ := ‹_›
  have hx24' : _ = _ := ‹_›; have hx25' : _ = _ := ‹_›; have hx26' : _ = _ := ‹_›
  have hx27' : _ = _ := ‹_›; have hx28' : _ = _ := ‹_›; have hx29' : _ = _ := ‹_›
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp_all [arm64_norm, wp_norm]) ?_
  refine ⟨Entails.refl _, by simp_all [arm64_norm, wp_norm], by simp_all [arm64_norm, wp_norm],
    by simp_all [arm64_norm, wp_norm], by simp_all [arm64_norm, wp_norm],
    by simp_all [arm64_norm, wp_norm], by simp_all [arm64_norm, wp_norm],
    by simp_all [arm64_norm, wp_norm], by simp_all [arm64_norm, wp_norm],
    by simp_all [arm64_norm, wp_norm], by simp_all [arm64_norm, wp_norm],
    by simp_all [arm64_norm, wp_norm], by simp_all [arm64_norm, wp_norm],
    by simp_all [arm64_norm, wp_norm], by simp_all [arm64_norm, wp_norm],
    by simp_all [arm64_norm, wp_norm], by simp_all [arm64_norm, wp_norm],
    fun A lim st => by simp only [arm64_norm, wp_norm]⟩
))

set_option maxHeartbeats 400000 in
private theorem b518x_arm_tag2_pre [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (g : OverDecG) (hpc : s.pc = (blkPl_518).base + 8908#64)
    (hrun : s.status = .Running) (hsp : s.sp = g.q) (hx0 : s.readReg64 .x0 = 2#64)
    (hx19 : s.readReg64 .x19 = g.r19) (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64) (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr) (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 514) s emp
      (B518xArmPrePost s g (g.q + 0x930#64) 8920#64) := by
  have _ : s.readReg64 (Reg.gpr 0#5) = 2#64 := hx0
  have _ : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have _ : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have _ : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have _ : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have _ : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have _ : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have _ : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have _ : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have _ : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  b518x_prove_arm_pre

set_option maxHeartbeats 400000 in
private theorem b518x_arm_tag3_pre [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (g : OverDecG) (hpc : s.pc = (blkPl_518).base + 8888#64)
    (hrun : s.status = .Running) (hsp : s.sp = g.q) (hx0 : s.readReg64 .x0 = 2#64)
    (hx19 : s.readReg64 .x19 = g.r19) (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64) (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr) (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 514) s emp
      (B518xArmPrePost s g (g.q + 0x930#64 + 0x18#64) 8900#64) := by
  have _ : s.readReg64 (Reg.gpr 0#5) = 2#64 := hx0
  have _ : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have _ : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have _ : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have _ : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have _ : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have _ : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have _ : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have _ : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have _ : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  b518x_prove_arm_pre

set_option maxHeartbeats 400000 in
private theorem b518x_arm_tag4_pre [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (g : OverDecG) (hpc : s.pc = (blkPl_518).base + 8848#64)
    (hrun : s.status = .Running) (hsp : s.sp = g.q) (hx0 : s.readReg64 .x0 = 2#64)
    (hx19 : s.readReg64 .x19 = g.r19) (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64) (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr) (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 514) s emp
      (B518xArmPrePost s g (g.q + 0x930#64 + 0x30#64) 8860#64) := by
  have _ : s.readReg64 (Reg.gpr 0#5) = 2#64 := hx0
  have _ : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have _ : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have _ : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have _ : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have _ : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have _ : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have _ : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have _ : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have _ : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  b518x_prove_arm_pre

set_option maxHeartbeats 400000 in
private theorem b518x_arm_tag13_pre [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (g : OverDecG) (hpc : s.pc = (blkPl_518).base + 8660#64)
    (hrun : s.status = .Running) (hsp : s.sp = g.q) (hx0 : s.readReg64 .x0 = 2#64)
    (hx19 : s.readReg64 .x19 = g.r19) (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64) (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr) (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 514) s emp
      (B518xArmPrePost s g (g.q + 0x930#64 + 0x60#64) 8672#64) := by
  have _ : s.readReg64 (Reg.gpr 0#5) = 2#64 := hx0
  have _ : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have _ : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have _ : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have _ : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have _ : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have _ : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have _ : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have _ : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have _ : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  b518x_prove_arm_pre

set_option maxHeartbeats 400000 in
private theorem b518x_arm_tag15_pre [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (g : OverDecG) (hpc : s.pc = (blkPl_518).base + 8704#64)
    (hrun : s.status = .Running) (hsp : s.sp = g.q) (hx0 : s.readReg64 .x0 = 2#64)
    (hx19 : s.readReg64 .x19 = g.r19) (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64) (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr) (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 514) s emp
      (B518xArmPrePost s g (g.q + 0x930#64 + 0x78#64) 8716#64) := by
  have _ : s.readReg64 (Reg.gpr 0#5) = 2#64 := hx0
  have _ : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have _ : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have _ : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have _ : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have _ : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have _ : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have _ : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have _ : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have _ : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  b518x_prove_arm_pre

set_option maxHeartbeats 600000 in
private theorem b518x_bytes_call_one [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) (hBM6W : BytesMerge6Placed514OkExtW A lim ext)
    (retOff valPtr : BitVec 64) (b rest : List (BitVec 8)) (restSS : SepProp)
    (st : M.σ) (s0 s1 : State) (g : OverDecG) (v v' : SSGQ) (fl : GenFieldQ)
    (hcro1 : LibsignalCodeRoLoaded lsmpl s1.mem)
    (hret : retOff = 0x22d8#64 ∨ retOff = 0x22c4#64 ∨ retOff = 0x229c#64 ∨
            retOff = 0x21e0#64 ∨ retOff = 0x220c#64)
    (hpay : fl.payload = encodeVarint (BitVec.ofNat 64 b.length) ++ b)
    (hb32 : b.length < 2 ^ 32) (hb_ne : b ≠ [])
    (hsuf : (fl.enc ++ rest) <:+ g.enc) (hlen : g.enc.length < 2 ^ 62)
    (hev_eq : mergeFieldQEvents (vecCap4Of v.base.recv.length) v.base.recv.length fl =
      bytesMergeEvents 0 b.length)
    (hfit : FitsEvents M lim st
      (mergeFieldQEvents (vecCap4Of v.base.recv.length) v.base.recv.length fl))
    (hsplit : b518x_prostSSGQAtCapA A.repAlloc (g.q + 0x930#64) v =
      b518x_vecU8Fresh0A A.repAlloc valPtr [] ∗ restSS)
    (hunsplit : vecU8 A.repAlloc valPtr b ∗ restSS =
      b518x_prostSSGQAtCapA A.repAlloc (g.q + 0x930#64) v')
    (hpc1 : s1.pc = lsmpl.base 514) (hrun1 : s1.status = .Running) (hsp1 : s1.sp = g.q)
    (hal1 : (s1.sp &&& 15#64 == 0#64) = true) (htr1 : s1.trace = s0.trace)
    (hx0_1 : s1.readReg64 .x0 = 2#64) (hx1_1 : s1.readReg64 .x1 = valPtr)
    (hx2_1 : s1.readReg64 .x2 = g.q + 0xbe8#64)
    (hx19_1 : s1.readReg64 .x19 = g.r19) (hx20_1 : s1.readReg64 .x20 = g.r20)
    (hx21_1 : s1.readReg64 .x21 = g.q + 0x930#64) (hx24_1 : s1.readReg64 .x24 = 1#64)
    (hx25_1 : s1.readReg64 .x25 = 0xffffffffffffffff#64) (hx26_1 : s1.readReg64 .x26 = g.r26)
    (hx27_1 : s1.readReg64 .x27 = g.prevPtr) (hx28_1 : s1.readReg64 .x28 = g.q + 0xa90#64)
    (hx29_1 : s1.readReg64 .x29 = g.q + 0xc70#64)
    (hx30_1 : s1.readReg64 .x30 = (blkPl_518).base + retOff)
    (hvregs_1 : calleeSavedVRegs s1 = calleeSavedVRegs g.sv) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 8544#64) s1
      (b518x_overDecHeapCapA A lim st s1 g (fl.payload ++ rest) v)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ b518x_overDecHeapCapA A lim
          (M.stepEvents (mergeFieldQEvents (vecCap4Of v.base.recv.length) v.base.recv.length fl) st)
          sf g rest v'))
      (fun _ _ => False) := by
  refine sepWPp_lift_cro_regs hcro1 ?_
  obtain ⟨pfx, hpfx, hpay_len⟩ := overDec_payload_suffix_and_len hsuf hlen
  have hmerge : mergeBytes .lengthDelimited (fl.payload ++ rest) = some (b, rest) := by
    rw [hpay]; exact overDec_mergeBytes_eq b rest (by omega)
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned] using hal1
  have hcur_split :
      sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc (fl.payload ++ rest) =
        (g.encPtr ↦ₛ pfx) ∗
          sliceCursorAt (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
            (fl.payload ++ rest) := by
    conv_lhs => arg 3; rw [hpfx]
    exact sliceCursorAfter_split_sub (g.q + 0x920#64) g.encPtr pfx (fl.payload ++ rest)
  have hfresh0 : b518x_vecU8Fresh0A A.repAlloc valPtr [] =
      ∃∗ ptr0 : BitVec 64, vecU8At A.repAlloc valPtr 0#64 ptr0 [] := by
    simp [b518x_vecU8Fresh0A]
  unfold b518x_overDecHeapCapA
  rw [hcur_split, hsplit, hfresh0, stackAt_overDec_to_bytesMerge3 g.q]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun ptr0 => ?_
  let xbm : BytesMergeGhost :=
    ⟨.lengthDelimited, valPtr, 0#64, ptr0, [], g.q + 0xbe8#64, g.q + 0x920#64,
     g.encPtr + BitVec.ofNat 64 pfx.length, fl.payload ++ rest⟩
  have hcore_eq : bytesMergeEventsCore xbm.wt xbm.valCap xbm.bs =
      mergeFieldQEvents (vecCap4Of v.base.recv.length) v.base.recv.length fl := by
    dsimp only [xbm]; rw [b518x_bytesMergeEventsCore_zero_eq hmerge hb_ne, hev_eq]
  have hfit_bm : FitsEnv M lim st (BytesMergeEnv xbm) := by
    intro evs hevs; unfold BytesMergeEnv at hevs; rw [hevs, hcore_eq]; exact hfit
  have hx0_w8 : (s1.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 xbm.wt.toNat := by rw [hx0_1]; rfl
  refine b518x_call_bm6w_cro (x := xbm) (st := st)
    (T := vecU8At A.repAlloc valPtr 0#64 ptr0 [] ∗
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAt (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
        (fl.payload ++ rest) ∗
      A.pool lim st s1 ∗ stackAt g.q bytesMerge3Stack)
    hcro1 hBM6W hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [bytesMerge3RawSpecW]; rw [hsp1])
    ⟨hx0_w8, hx1_1, hx2_1, hpay_len, hfit_bm⟩
    (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _hsp2_al hcs2 _hL2 => ?_)
  dsimp only [bytesMerge3RawSpecW, xbm]; rw [hmerge]; dsimp only; rw [hsp1]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' =>
    SepWPp.exists_elim fun evs => SepWPp.pure_elim fun htr2_1 => ?_
  refine b518x_weaken_frame (P₁ := ⌜BytesMergeEnv xbm evs⌝) (P₂ := ⌜BytesMergeEnv xbm evs⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun hevs_bm => ?_
  refine b518x_weaken_frame (P₁ := ⌜s2.readReg64 .x0 = 0#64⌝) (P₂ := ⌜s2.readReg64 .x0 = 0#64⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun hx0_2 => ?_
  refine b518x_weaken_frame (P₁ := vecU8At A.repAlloc valPtr cap' ptr' b)
    (P₂ := vecU8 A.repAlloc valPtr b)
    (Entails.sepExists_right cap' (Entails.sepExists_right ptr' (Entails.refl _)))
    (by sep_focus) ?_
  have hsp2 : s2.sp = g.q := hsp2_1.trans hsp1
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, _, _, hx24_cs, hx25_cs, hx26_cs, hx27_cs, hx28_cs,
    hx29_cs, hvregs_cs⟩
  have hstep_cbz := overDec_cbz_placed_pool_wp ext retOff s2 g hret
    hpc2 hrun2 hsp2 hx0_2 (hx19_cs.trans hx19_1) (hx20_cs.trans hx20_1) (hx21_cs.trans hx21_1)
    (hx24_cs.trans hx24_1) (hx25_cs.trans hx25_1) (hx26_cs.trans hx26_1) (hx27_cs.trans hx27_1)
    (hx28_cs.trans hx28_1) (hx29_cs.trans hx29_1)
  refine b518x_ret_frame hstep_cbz (by rw [emp_sepConj])
    fun sf hpcf hrunf hLf hregsf hpool_sf => ?_
  rcases hregsf with ⟨hsp_f, htr_f, hx19_f, hx20_f, hx21_f, hx24_f, hx25_f, hx26_f, hx27_f,
    hx28_f, hx29_f, hvregs_f⟩
  have hal_f : (sf.sp &&& 15#64 == 0#64) = true := by rwa [hsp_f, ← hsp1]
  have hevs_eq : evs = mergeFieldQEvents (vecCap4Of v.base.recv.length) v.base.recv.length fl := by
    unfold BytesMergeEnv at hevs_bm; exact hevs_bm.trans hcore_eq
  refine ⟨⟨hpcf, hrunf, hsp_f, hal_f, htr_f.trans (htr2_1.trans htr1), hLf,
    hx19_f, hx20_f, hx26_f, hx21_f, hx24_f, hx25_f, hx27_f, hx28_f, hx29_f,
    hvregs_f.trans (hvregs_cs.trans hvregs_1)⟩, ?_⟩
  have hcur_unsplit :
      (g.encPtr ↦ₛ pfx) ∗
        sliceCursorAfter (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
          (fl.payload ++ rest) rest =
      sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest := by
    rw [sliceCursorAfter_unsplit_sub (g.q + 0x920#64) g.encPtr pfx fl.payload rest, ← hpfx]
  have hpool_eq : A.pool lim (M.stepEvents evs st) s2 = A.pool lim (M.stepEvents evs st) sf :=
    (hpool_sf A lim (M.stepEvents evs st)).symm
  rw [hpool_eq, hevs_eq, ← hunsplit, ← hcur_unsplit]
  refine Entails.of_eq ?_; simp only [emp_sepConj, sepConj_assoc]; sep_ac_rfl

private theorem b518x_vecU8Fresh0A_ne {A : RustAlloc} {p : BitVec 64} {b : List (BitVec 8)}
    (hb_ne : b ≠ []) : b518x_vecU8Fresh0A A p b = vecU8 A p b := by
  simp [b518x_vecU8Fresh0A, hb_ne]

private def b518x_ssgqRecvAndTail (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) : SepProp :=
  (∃∗ ptrRecv : BitVec 64,
    vecAt A 104 8 (fun c a => prostChainGAt A a c)
      (ss + 0x48#64) (BitVec.ofNat 64 (vecCap4Of v.base.recv.length)) ptrRecv v.base.recv) ∗
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

private theorem b518x_prostSSGQAtCapA_5vec (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) :
    b518x_prostSSGQAtCapA A ss v =
      b518x_vecU8Fresh0A A ss v.base.lik ∗
        b518x_vecU8Fresh0A A (ss + 0x18#64) v.base.rik ∗
        b518x_vecU8Fresh0A A (ss + 0x30#64) v.base.root ∗
        b518x_vecU8Fresh0A A (ss + 0x60#64) v.ext.abk ∗
        b518x_vecU8Fresh0A A (ss + 0x78#64) v.ext.pq ∗
        b518x_ssgqRecvAndTail A ss v := by
  unfold b518x_prostSSGQAtCapA b518x_ssgqRecvAndTail; sep_ac_rfl

private theorem b518x_ssgqRecvAndTail_lik (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) (b : List (BitVec 8)) :
    b518x_ssgqRecvAndTail A ss (v.apply (.base (.lik b))) = b518x_ssgqRecvAndTail A ss v := rfl

private theorem b518x_ssgqRecvAndTail_rik (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) (b : List (BitVec 8)) :
    b518x_ssgqRecvAndTail A ss (v.apply (.base (.rik b))) = b518x_ssgqRecvAndTail A ss v := rfl

private theorem b518x_ssgqRecvAndTail_root (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) (b : List (BitVec 8)) :
    b518x_ssgqRecvAndTail A ss (v.apply (.base (.root b))) = b518x_ssgqRecvAndTail A ss v := rfl

private theorem b518x_ssgqRecvAndTail_abk (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) (b : List (BitVec 8)) :
    b518x_ssgqRecvAndTail A ss (v.apply (.abk b)) = b518x_ssgqRecvAndTail A ss v := rfl

private theorem b518x_ssgqRecvAndTail_pq (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) (b : List (BitVec 8)) :
    b518x_ssgqRecvAndTail A ss (v.apply (.pq b)) = b518x_ssgqRecvAndTail A ss v := rfl

private theorem b518x_swap2 (P1 P2 R : SepProp) : P1 ∗ P2 ∗ R = P2 ∗ P1 ∗ R := by
  rw [sepConj_left_comm]

private theorem b518x_swap3 (P1 P2 P3 R : SepProp) : P1 ∗ P2 ∗ P3 ∗ R = P3 ∗ P1 ∗ P2 ∗ R := by
  rw [sepConj_left_comm P2 P3 R, sepConj_left_comm P1 P3 (P2 ∗ R)]

private theorem b518x_swap4 (P1 P2 P3 P4 R : SepProp) :
    P1 ∗ P2 ∗ P3 ∗ P4 ∗ R = P4 ∗ P1 ∗ P2 ∗ P3 ∗ R := by
  rw [b518x_swap3 P2 P3 P4 R, sepConj_left_comm P1 P4 (P2 ∗ P3 ∗ R)]

private theorem b518x_swap5 (P1 P2 P3 P4 P5 R : SepProp) :
    P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ R = P5 ∗ P1 ∗ P2 ∗ P3 ∗ P4 ∗ R := by
  rw [b518x_swap4 P2 P3 P4 P5 R, sepConj_left_comm P1 P5 (P2 ∗ P3 ∗ P4 ∗ R)]

set_option maxHeartbeats 600000 in
/-- Capacity-explicit bytes arms (Tags `2, 3, 4, 13, 15`) preserving `b518x_overDecHeapCapA`. -/
theorem b518x_arm_bytes_cro_placed_of_bm6w [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hBM6W : BytesMerge6Placed514OkExtW A lim ext)
    (st : M.σ) (s0 s : State) (g : OverDecG) (v : SSGQ) (fl : GenFieldQ) (rest : List (BitVec 8))
    (hP : OverDecBytesField fl) (hok : fl.Ok) (hfr : fl.Fresh v) (hfb : GenFieldQ.FreshBytes v fl)
    (hpq_ne : ∀ b, fl = .pq b → b ≠ [])
    (hsuf : (fl.enc ++ rest) <:+ g.enc) (hlen : g.enc.length < 2 ^ 62)
    (hfit : FitsEvents M lim st
      (mergeFieldQEvents (vecCap4Of v.base.recv.length) v.base.recv.length fl))
    (hregs_cro : OverDecRegsCroPlaced ext s0 g (overDecArmOff fl) s)
    (hx0 : s.readReg64 .x0 = overDecWt fl) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 8544#64) s
      (b518x_overDecHeapCapA A lim st s g (fl.payload ++ rest) v)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ b518x_overDecHeapCapA A lim
          (M.stepEvents (mergeFieldQEvents (vecCap4Of v.base.recv.length) v.base.recv.length fl) st)
          sf g rest (v.apply fl)))
      (fun _ _ => False) := by
  rcases hregs_cro with ⟨hcro, hpc, hrun, hsp, hal, htr, _hL,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  let ss := g.q + 0x930#64
  cases fl with
  | base f =>
    cases f with
    | lik b =>
      have hb_pos : 0 < b.length := by dsimp only [GenFieldQ.Ok, GenField.Ok] at hok; omega
      have hb_ne : b ≠ [] := List.length_pos_iff.mp hb_pos
      have hold : v.base.lik = [] := hfb
      refine b518x_bind_cro hcro
        (b518x_arm_tag2_pre ext s g hpc hrun hsp hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29)
        (by rw [emp_sepConj]) fun s1 hpc1 hrun1 _hL1 hcro1 hregs1 => ?_
      rw [emp_sepConj]
      rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1,
        hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1, hpool1⟩
      have hheap1 : b518x_overDecHeapCapA A lim st s g ((GenFieldQ.base (.lik b)).payload ++ rest) v =
          b518x_overDecHeapCapA A lim st s1 g ((GenFieldQ.base (.lik b)).payload ++ rest) v := by
        unfold b518x_overDecHeapCapA; rw [hpool1 A lim st]
      rw [hheap1]
      exact b518x_bytes_call_one ext hBM6W 0x22d8#64 ss b rest
        (b518x_vecU8Fresh0A A.repAlloc (ss + 0x18#64) v.base.rik ∗
          b518x_vecU8Fresh0A A.repAlloc (ss + 0x30#64) v.base.root ∗
          b518x_vecU8Fresh0A A.repAlloc (ss + 0x60#64) v.ext.abk ∗
          b518x_vecU8Fresh0A A.repAlloc (ss + 0x78#64) v.ext.pq ∗
          b518x_ssgqRecvAndTail A.repAlloc ss v)
        st s0 s1 g v (v.apply (.base (.lik b))) (.base (.lik b)) hcro1 (Or.inl rfl) rfl
        (by dsimp only [GenFieldQ.Ok, GenField.Ok] at hok; omega) hb_ne hsuf hlen rfl hfit
        (by rw [b518x_prostSSGQAtCapA_5vec, hold])
        (by rw [b518x_prostSSGQAtCapA_5vec, b518x_ssgqRecvAndTail_lik]; dsimp only [SSGQ.apply, SSG.apply]
            rw [b518x_vecU8Fresh0A_ne hb_ne])
        hpc1 hrun1 hsp1 (by rwa [hsp1, ← hsp]) (htr1.trans htr)
        hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hx30_1
        (hvregs_1.trans hvregs)
    | rik b =>
      have hb_pos : 0 < b.length := by dsimp only [GenFieldQ.Ok, GenField.Ok] at hok; omega
      have hb_ne : b ≠ [] := List.length_pos_iff.mp hb_pos
      have hold : v.base.rik = [] := hfb
      refine b518x_bind_cro hcro
        (b518x_arm_tag3_pre ext s g hpc hrun hsp hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29)
        (by rw [emp_sepConj]) fun s1 hpc1 hrun1 _hL1 hcro1 hregs1 => ?_
      rw [emp_sepConj]
      rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1,
        hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1, hpool1⟩
      have hheap1 : b518x_overDecHeapCapA A lim st s g ((GenFieldQ.base (.rik b)).payload ++ rest) v =
          b518x_overDecHeapCapA A lim st s1 g ((GenFieldQ.base (.rik b)).payload ++ rest) v := by
        unfold b518x_overDecHeapCapA; rw [hpool1 A lim st]
      rw [hheap1]
      exact b518x_bytes_call_one ext hBM6W 0x22c4#64 (ss + 0x18#64) b rest
        (b518x_vecU8Fresh0A A.repAlloc ss v.base.lik ∗
          b518x_vecU8Fresh0A A.repAlloc (ss + 0x30#64) v.base.root ∗
          b518x_vecU8Fresh0A A.repAlloc (ss + 0x60#64) v.ext.abk ∗
          b518x_vecU8Fresh0A A.repAlloc (ss + 0x78#64) v.ext.pq ∗
          b518x_ssgqRecvAndTail A.repAlloc ss v)
        st s0 s1 g v (v.apply (.base (.rik b))) (.base (.rik b)) hcro1 (Or.inr (Or.inl rfl)) rfl
        (by dsimp only [GenFieldQ.Ok, GenField.Ok] at hok; omega) hb_ne hsuf hlen rfl hfit
        (by rw [b518x_prostSSGQAtCapA_5vec, hold]; exact b518x_swap2 _ _ _)
        (by rw [b518x_prostSSGQAtCapA_5vec, b518x_ssgqRecvAndTail_rik]; dsimp only [SSGQ.apply, SSG.apply]
            rw [b518x_vecU8Fresh0A_ne hb_ne]; exact (b518x_swap2 _ _ _).symm)
        hpc1 hrun1 hsp1 (by rwa [hsp1, ← hsp]) (htr1.trans htr)
        hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hx30_1
        (hvregs_1.trans hvregs)
    | root b =>
      have hb_pos : 0 < b.length := by dsimp only [GenFieldQ.Ok, GenField.Ok] at hok; omega
      have hb_ne : b ≠ [] := List.length_pos_iff.mp hb_pos
      have hold : v.base.root = [] := hfb
      refine b518x_bind_cro hcro
        (b518x_arm_tag4_pre ext s g hpc hrun hsp hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29)
        (by rw [emp_sepConj]) fun s1 hpc1 hrun1 _hL1 hcro1 hregs1 => ?_
      rw [emp_sepConj]
      rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1,
        hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1, hpool1⟩
      have hheap1 : b518x_overDecHeapCapA A lim st s g ((GenFieldQ.base (.root b)).payload ++ rest) v =
          b518x_overDecHeapCapA A lim st s1 g ((GenFieldQ.base (.root b)).payload ++ rest) v := by
        unfold b518x_overDecHeapCapA; rw [hpool1 A lim st]
      rw [hheap1]
      exact b518x_bytes_call_one ext hBM6W 0x229c#64 (ss + 0x30#64) b rest
        (b518x_vecU8Fresh0A A.repAlloc ss v.base.lik ∗
          b518x_vecU8Fresh0A A.repAlloc (ss + 0x18#64) v.base.rik ∗
          b518x_vecU8Fresh0A A.repAlloc (ss + 0x60#64) v.ext.abk ∗
          b518x_vecU8Fresh0A A.repAlloc (ss + 0x78#64) v.ext.pq ∗
          b518x_ssgqRecvAndTail A.repAlloc ss v)
        st s0 s1 g v (v.apply (.base (.root b))) (.base (.root b)) hcro1 (Or.inr (Or.inr (Or.inl rfl))) rfl
        (by dsimp only [GenFieldQ.Ok, GenField.Ok] at hok; omega) hb_ne hsuf hlen rfl hfit
        (by rw [b518x_prostSSGQAtCapA_5vec, hold]; exact b518x_swap3 _ _ _ _)
        (by rw [b518x_prostSSGQAtCapA_5vec, b518x_ssgqRecvAndTail_root]; dsimp only [SSGQ.apply, SSG.apply]
            rw [b518x_vecU8Fresh0A_ne hb_ne]; exact (b518x_swap3 _ _ _ _).symm)
        hpc1 hrun1 hsp1 (by rwa [hsp1, ← hsp]) (htr1.trans htr)
        hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hx30_1
        (hvregs_1.trans hvregs)
    | version _ | prevCounter _ | sender _ | recv _ | pending _ => cases hP
  | abk b =>
    have hb_pos : 0 < b.length := by dsimp only [GenFieldQ.Ok] at hok; omega
    have hb_ne : b ≠ [] := List.length_pos_iff.mp hb_pos
    have hold : v.ext.abk = [] := hfr.1
    refine b518x_bind_cro hcro
      (b518x_arm_tag13_pre ext s g hpc hrun hsp hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29)
      (by rw [emp_sepConj]) fun s1 hpc1 hrun1 _hL1 hcro1 hregs1 => ?_
    rw [emp_sepConj]
    rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1,
      hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1, hpool1⟩
    have hheap1 : b518x_overDecHeapCapA A lim st s g ((GenFieldQ.abk b).payload ++ rest) v =
        b518x_overDecHeapCapA A lim st s1 g ((GenFieldQ.abk b).payload ++ rest) v := by
      unfold b518x_overDecHeapCapA; rw [hpool1 A lim st]
    rw [hheap1]
    exact b518x_bytes_call_one ext hBM6W 0x21e0#64 (ss + 0x60#64) b rest
      (b518x_vecU8Fresh0A A.repAlloc ss v.base.lik ∗
        b518x_vecU8Fresh0A A.repAlloc (ss + 0x18#64) v.base.rik ∗
        b518x_vecU8Fresh0A A.repAlloc (ss + 0x30#64) v.base.root ∗
        b518x_vecU8Fresh0A A.repAlloc (ss + 0x78#64) v.ext.pq ∗
        b518x_ssgqRecvAndTail A.repAlloc ss v)
      st s0 s1 g v (v.apply (.abk b)) (.abk b) hcro1 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) rfl
      (by dsimp only [GenFieldQ.Ok] at hok; omega) hb_ne hsuf hlen rfl hfit
      (by rw [b518x_prostSSGQAtCapA_5vec, hold]; exact b518x_swap4 _ _ _ _ _)
      (by rw [b518x_prostSSGQAtCapA_5vec, b518x_ssgqRecvAndTail_abk]; dsimp only [SSGQ.apply]
          rw [b518x_vecU8Fresh0A_ne hb_ne]; exact (b518x_swap4 _ _ _ _ _).symm)
      hpc1 hrun1 hsp1 (by rwa [hsp1, ← hsp]) (htr1.trans htr)
      hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hx30_1
      (hvregs_1.trans hvregs)
  | pq b =>
    have hb_ne : b ≠ [] := hpq_ne b rfl
    have hold : v.ext.pq = [] := hfr
    refine b518x_bind_cro hcro
      (b518x_arm_tag15_pre ext s g hpc hrun hsp hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29)
      (by rw [emp_sepConj]) fun s1 hpc1 hrun1 _hL1 hcro1 hregs1 => ?_
    rw [emp_sepConj]
    rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1,
      hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1, hpool1⟩
    have hheap1 : b518x_overDecHeapCapA A lim st s g ((GenFieldQ.pq b).payload ++ rest) v =
        b518x_overDecHeapCapA A lim st s1 g ((GenFieldQ.pq b).payload ++ rest) v := by
      unfold b518x_overDecHeapCapA; rw [hpool1 A lim st]
    rw [hheap1]
    exact b518x_bytes_call_one ext hBM6W 0x220c#64 (ss + 0x78#64) b rest
      (b518x_vecU8Fresh0A A.repAlloc ss v.base.lik ∗
        b518x_vecU8Fresh0A A.repAlloc (ss + 0x18#64) v.base.rik ∗
        b518x_vecU8Fresh0A A.repAlloc (ss + 0x30#64) v.base.root ∗
        b518x_vecU8Fresh0A A.repAlloc (ss + 0x60#64) v.ext.abk ∗
        b518x_ssgqRecvAndTail A.repAlloc ss v)
      st s0 s1 g v (v.apply (.pq b)) (.pq b) hcro1 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) rfl
      hok hb_ne hsuf hlen rfl hfit
      (by rw [b518x_prostSSGQAtCapA_5vec, hold]; exact b518x_swap5 _ _ _ _ _ _)
      (by rw [b518x_prostSSGQAtCapA_5vec, b518x_ssgqRecvAndTail_pq]; dsimp only [SSGQ.apply]
          rw [b518x_vecU8Fresh0A_ne hb_ne]; exact (b518x_swap5 _ _ _ _ _ _).symm)
      hpc1 hrun1 hsp1 (by rwa [hsp1, ← hsp]) (htr1.trans htr)
      hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hx30_1
      (hvregs_1.trans hvregs)
  | pendingId _ _ | pendingSpk _ _ _ | remReg _ | locReg _ | kyber _ _ => cases hP

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ExactDecodePlacedBudgetAuxD
