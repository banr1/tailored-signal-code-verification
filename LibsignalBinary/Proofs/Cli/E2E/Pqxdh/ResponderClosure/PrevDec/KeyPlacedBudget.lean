/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.KeyPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5PlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Key Decode and Jump-Table Dispatch

Total-correctness (`RustCliAllocBudget M`) verification of key decoding and `.rodata` jump-table
dispatch (`OverDecKeyCroPlacedAt A lim ext`, `OverDecKeyPlacedStmt A lim`, `0` allocations) on
Block `518` (`lsProg_518 ext`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.KeyPlacedBudget

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection SepProp
open CryptoVerification (
  LibsignalCodeLoaded LibsignalHooks LibsignalPlacement LibsignalRoLoaded
  lsmpl lsρ withLsCl withLsCodeLoaded
)
open CryptoVerification.LibsignalProtoCodec (decodeVarint decodeVarint_encodeVarint encodeKey)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  DecodeVarintSlowGhost sliceCursorAfter sliceCursorAt
)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.E2E.Record.DeserializeGeneral (GenField)
open Symbolic.Swarm.TRREF.B3DeserQ (GenFieldQ SSGQ prostSSGQAt)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkPl_518 lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (
  OverDecAnyField OverDecG OverDecRegsCroPlaced OverDecRegsPlaced
  overDecArmOff overDecJtabByte overDecJtabBytes overDecJtabSym
  overDecKeyVal overDecStackX overDecWt
  rodata_overDecJtabByte_of_table rodata_overDecJtab_placed_intro
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH (decodeVarint2StackX)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (
  DecodeVarintSliceEnv decodeVarintSliceEvents
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5Budget (
  DecodeVarint2Env decodeVarint2SpecX
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5PlacedBudget (
  DecodeVarint5PlacedOkExtX decodeVarint5_placed_ok_ext_x
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsBudget (
  OverDecKeyCroPlacedAt OverDecKeyPlacedStmt overDecHeapBudget overPrevElemRestBudget
)

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

private theorem vmPreserved_of_fields {s sm : State}
    (h1 : sm.brkStart = s.brkStart)
    (h2 : sm.brk = s.brk)
    (h3 : sm.tpidrEl0 = s.tpidrEl0)
    (h4 : sm.physMemAvail = s.physMemAvail)
    (h5 : sm.mem = s.mem)
    (h6 : sm.fs = s.fs := by first | rfl | simp_all) :
    VmPreserved s sm :=
  ⟨⟨h1, h2, h3⟩, h4, fun _ => by rw [h5], LibsignalBinary.Heap.FdsHiFrame.of_fs_eq h6⟩

private theorem lscl_of_cl {α : Type} {P : Program} {pl : Obj.MultiPlacement}
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok P entry (withLsCl pl spec)) :
    subroutine_ok P entry (withLsCodeLoaded pl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      dsimp only [withLsCl, withLsCodeLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)

private theorem SepWPp_bind_sepWP_frame_cro_key_budget_pl [LibsignalPlacement]
    {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P_step
      (fun sm P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      prog.CodeLoaded sm.mem → LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent) hmm
  have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hpc hrun hLm (hcro.of_keepsFrozen hsteps.keepsFrozen) hregs R hmm' hLm
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

private theorem stackAt_sub_eq_key_budget_pl (sp : BitVec 64) (M N : Nat) (hMN : N ≤ M := by decide)
    (hbound : M < 2 ^ 64 := by decide) :
    stackAt sp M = stackAt sp N ∗ memRegion (sp - BitVec.ofNat 64 M) (M - N) := by
  have h1 : M = N + (M - N) := (Nat.add_sub_of_le hMN).symm
  have h2 := ProofLib.stackAt_split_bottom sp N (M - N) (by omega)
  rw [← h1] at h2
  rw [h2, sepConj_comm]

private theorem overDecWt_toNat_eq_budget_pl (fl : GenFieldQ) :
    (overDecWt fl).toNat = fl.wt.toNat := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> rfl

private theorem decodeVarint_fl_enc_budget_pl (fl : GenFieldQ) (rest : List (BitVec 8)) :
    decodeVarint (fl.enc ++ rest) = some (overDecKeyVal fl, fl.payload ++ rest) := by
  rw [GenFieldQ.enc, List.append_assoc, encodeKey, overDecKeyVal, overDecWt_toNat_eq_budget_pl fl]
  exact decodeVarint_encodeVarint _ _

private theorem fitsEnv_dv2_fl_enc_budget_pl {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (fl : GenFieldQ) (rest : List (BitVec 8)) :
    FitsEnv M lim st (DecodeVarint2Env (fl.enc ++ rest)) := by
  intro evs hevs
  simp only [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents,
    decodeVarint_fl_enc_budget_pl fl rest] at hevs
  subst hevs
  trivial

private theorem fl_payload_rest_len_le_budget_pl (fl : GenFieldQ) (rest : List (BitVec 8)) :
    (fl.payload ++ rest).length ≤ (fl.enc ++ rest).length := by
  simp only [GenFieldQ.enc, List.length_append]
  omega

private theorem sliceCursorAfter_split_of_append_budget_pl (slot ptr : BitVec 64)
    (bs1 bs2 : List (BitVec 8)) :
    sliceCursorAfter slot ptr (bs1 ++ bs2) bs2 =
      sliceCursorAt slot (ptr + BitVec.ofNat 64 bs1.length) bs2 ∗ (ptr ↦ₛ bs1) := by
  unfold sliceCursorAfter sliceCursorAt
  have hsub : (bs1 ++ bs2).length - bs2.length = bs1.length := by
    rw [List.length_append]; omega
  rw [hsub, pointsToBytes_append ptr bs1 bs2]
  sep_ac_rfl

private theorem sliceCursorAfter_unsplit_of_append_budget_pl (slot ptr : BitVec 64)
    (bs1 bs2 bs3 : List (BitVec 8)) (hle : bs3.length ≤ bs2.length) :
    sliceCursorAfter slot (ptr + BitVec.ofNat 64 bs1.length) bs2 bs3 ∗ (ptr ↦ₛ bs1) =
      sliceCursorAfter slot ptr (bs1 ++ bs2) bs3 := by
  unfold sliceCursorAfter
  have hadd : (ptr + BitVec.ofNat 64 bs1.length) + BitVec.ofNat 64 (bs2.length - bs3.length) =
      ptr + BitVec.ofNat 64 ((bs1 ++ bs2).length - bs3.length) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    rw [List.length_append]
    omega
  rw [hadd, pointsToBytes_append ptr bs1 bs2]
  sep_ac_rfl

/-! ## Stage 1 (`+0x216c → lsmpl.base 515 → +0x2174`): `decode_varint [local#4]` Call -/

set_option maxHeartbeats 400000 in
private theorem overDecKey_precall_pool_wp_placed [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s0 s : State) (g : OverDecG)
    (hregs : OverDecRegsPlaced ext s0 g 0x216c#64 s) :
    SepWP (lsProg_518 ext) (lsmpl.base 515) s emp
      (fun sm P' => (P' ⊢ emp) ∧
        sm.sp = g.q ∧ (sm.sp &&& 15#64 == 0#64) = true ∧ sm.trace = s0.trace ∧
        sm.readReg64 .x0 = g.q + 0xbe8#64 ∧
        sm.readReg64 .lr = (blkPl_518).base + 0x2174#64 ∧
        sm.readReg64 .x19 = g.r19 ∧ sm.readReg64 .x20 = g.r20 ∧ sm.readReg64 .x26 = g.r26 ∧
        sm.readReg64 .x21 = g.q + 0x930#64 ∧ sm.readReg64 .x24 = 1#64 ∧
        sm.readReg64 .x25 = 0xffffffffffffffff#64 ∧ sm.readReg64 .x27 = g.prevPtr ∧
        sm.readReg64 .x28 = g.q + 0xa90#64 ∧ sm.readReg64 .x29 = g.q + 0xc70#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs g.sv ∧
        (∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ),
          A.pool lim st sm = A.pool lim st s)) := by
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, _hcl,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  have h19 : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have h26 : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have h21 : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have h24 : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have h27 : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have h28 : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have h29 : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  refine ⟨Entails.refl _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hsp, arm64_norm]
  · simp only [hal, arm64_norm]
  · simp only [htr, arm64_norm]
  · simp only [arm64_norm]
  · simp only [arm64_norm]
  · simp only [h19, arm64_norm]
  · simp only [h20, arm64_norm]
  · simp only [h26, arm64_norm]
  · simp only [h21, arm64_norm]
  · simp only [h24, arm64_norm]
  · simp only [h25, arm64_norm]
  · simp only [h27, arm64_norm]
  · simp only [h28, arm64_norm]
  · simp only [h29, arm64_norm]
  · simp only [hvregs, arm64_norm]
  · refine fun A lim st => (A.pool_of_vmPreserved (vmPreserved_of_fields ?_ ?_ ?_ ?_ ?_)).symm
    all_goals rfl

private theorem overDec_call_decodeVarint5_lscl_budget_pl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {st : M.σ} {s0 sm : State} {g : OverDecG} {fl : GenFieldQ}
    {pfx rest : List (BitVec 8)} {F : SepProp} {Q : State → SepProp → Prop}
    (hV : subroutine_ok (lsProg_518 ext) (lsmpl.base 515)
      (withLsCodeLoaded lsmpl (decodeVarint2SpecX A lim)))
    (hcrom : LibsignalCodeRoLoaded lsmpl sm.mem)
    (htrm : sm.trace = s0.trace)
    (hpcm : sm.pc = lsmpl.base 515)
    (hrunm : sm.status = .Running) (hspm : sm.sp = g.q)
    (halm : (sm.sp &&& 15#64 == 0#64) = true)
    (hx0m : sm.readReg64 .x0 = g.q + 0xbe8#64)
    (hlrm : sm.readReg64 .lr = (blkPl_518).base + 8564#64)
    (hlen63 : (fl.enc ++ rest).length < 2 ^ 63)
    (hnext : ∀ s2 : State,
      s2.pc = (blkPl_518).base + 8564#64 →
      s2.status = .Running → s2.sp = g.q →
      (lsProg_518 ext).CodeLoaded s2.mem →
      LibsignalCodeRoLoaded lsmpl s2.mem → s2.trace = s0.trace →
      CalleeSavedPreserved sm s2 →
      s2.readReg64 .x0 = 0#64 → s2.readReg64 .x1 = overDecKeyVal fl →
      SepWPp (lsProg_518 ext) ret s2
        (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64) ∗
          sliceCursorAfter (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
            (fl.enc ++ rest) (fl.payload ++ rest) ∗
          A.pool lim st s2 ∗
          stackAt g.q decodeVarint2StackX) ∗ F)
        Q (fun _ _ => False)) :
    SepWPp (lsProg_518 ext) ret sm
      (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64) ∗
        sliceCursorAt (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length) (fl.enc ++ rest) ∗
        A.pool lim st sm ∗
        stackAt g.q decodeVarint2StackX) ∗ F)
      Q (fun _ _ => False) := by
  intro R hm hL
  let x : DecodeVarintSlowGhost :=
    ⟨g.q + 0xbe8#64, g.q + 0x920#64, g.encPtr + BitVec.ofNat 64 pfx.length, fl.enc ++ rest⟩
  have hpre : sm.mem ⊨
      (withLsCodeLoaded lsmpl (decodeVarint2SpecX A lim)).pre (x, st) sm ∗ (F ∗ R) := by
    dsimp only [withLsCodeLoaded, decodeVarint2SpecX, x]
    rw [sepConj_assoc, sepConj_left_comm _ (⌜LibsignalCodeLoaded _ _⌝), satisfies_pure_sepConj]
    refine ⟨hcrom.1, ?_⟩
    rw [hspm, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0m, hlen63, fitsEnv_dv2_fl_enc_budget_pl fl rest⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  have hsp_al : sm.spAligned = true := halm
  obtain ⟨s2, hsteps, ⟨hpc2, hrun2, hpost, hsp2, hcs2⟩ | ⟨_, hoom⟩⟩ :=
    subroutine_ok_apply_full (oom := fun _ => False) hV (x, st) (F ∗ R) hpcm hrunm hpre hsp_al
      (by intro _ _ hp; dsimp only [withLsCodeLoaded, decodeVarint2SpecX] at hp
          exact not_satisfies_false_sepConj hp)
      (by intro _ _ _ he; dsimp only [withLsCodeLoaded, decodeVarint2SpecX] at he
          exact not_satisfies_false_sepConj he)
      (by intro _ _ ho; dsimp only [withLsCodeLoaded, decodeVarint2SpecX] at ho
          exact not_satisfies_false_sepConj ho)
      hL
  · rw [hlrm] at hpc2; rw [hspm] at hsp2
    dsimp only [withLsCodeLoaded, decodeVarint2SpecX, x] at hpost
    rw [decodeVarint_fl_enc_budget_pl fl rest, hspm] at hpost
    dsimp only at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hx0_2, hx1_2⟩, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htr2, hpost⟩
    have hpool_exs :
        (∃∗ evs : List AllocEvent, ⌜DecodeVarint2Env (fl.enc ++ rest) evs⌝ ∗
          A.pool lim (M.stepEvents evs st) s2) ⊢
        A.pool lim st s2 := by
      apply Entails.sepExists_elim; intro evs
      apply Entails.pure_left; intro hevs
      simp only [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents,
        decodeVarint_fl_enc_budget_pl fl rest] at hevs
      subst hevs
      simp only [AllocCostModel.stepEvents_nil]
      exact Entails.refl _
    have hpost1 : s2.mem ⊨
        (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64) ∗
          A.pool lim st s2 ∗
          stackAt g.q decodeVarint2StackX ∗
          sliceCursorAfter (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
            (fl.enc ++ rest) (fl.payload ++ rest)) ∗
          (F ∗ R)) := by
      refine Satisfies.mono ?_ hpost
      refine sepConj_mono_left ?_
      exact sepConj_mono_right (sepConj_mono_left hpool_exs)
    have hpost' : s2.mem ⊨ (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64) ∗
        sliceCursorAfter (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
          (fl.enc ++ rest) (fl.payload ++ rest) ∗
        A.pool lim st s2 ∗
        stackAt g.q decodeVarint2StackX) ∗ F) ∗ R :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost1
    have hL2 : (lsProg_518 ext).CodeLoaded s2.mem := hsteps.codeLoaded hL
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext s2 hpc2 hrun2 hsp2 hL2 (hcrom.of_keepsFrozen hsteps.keepsFrozen) (htr2.trans htrm)
        hcs2 hx0_2 hx1_2 R hpost' hL2
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact hoom.elim

/-! ## Stage 2 (`+0x2174 → overDecArmOff fl`): Jump-Table Dispatch -/

@[local simp, local arm64_norm]
private theorem overDecKeyVal_lsr32_bpl (fl : GenFieldQ) :
    overDecKeyVal fl >>> 32#64 = 0#64 := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecKeyVal, overDecWt, GenFieldQ.tag, GenField.tag, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecKeyVal_lsr32_nat_bpl (fl : GenFieldQ) :
    overDecKeyVal fl >>> 32 = 0#64 := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecKeyVal, overDecWt, GenFieldQ.tag, GenField.tag, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecKeyVal_and7_bpl (fl : GenFieldQ) :
    overDecKeyVal fl &&& 7#64 = overDecWt fl := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecKeyVal, overDecWt, GenFieldQ.tag, GenField.tag, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecWt_ule6_bpl (fl : GenFieldQ) :
    (6#64).ule (overDecWt fl) = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecWt, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecKeyVal_trunc32_zext64_bpl (fl : GenFieldQ) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (overDecKeyVal fl)) = overDecKeyVal fl := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecKeyVal, overDecWt, GenFieldQ.tag, GenField.tag, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecKeyVal_lsr3_bpl (fl : GenFieldQ) :
    overDecKeyVal fl >>> 3 = BitVec.ofNat 64 fl.tag := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecKeyVal, overDecWt, GenFieldQ.tag, GenField.tag, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecKeyVal_wlsr3_bpl (fl : GenFieldQ) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (overDecKeyVal fl) >>> 3#32) =
      BitVec.ofNat 64 fl.tag := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecKeyVal, overDecWt, GenFieldQ.tag, GenField.tag, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecKeyVal_wlsr3_nat_bpl (fl : GenFieldQ) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (overDecKeyVal fl) >>> 3) =
      BitVec.ofNat 64 fl.tag := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecKeyVal, overDecWt, GenFieldQ.tag, GenField.tag, GenFieldQ.wt, GenField.wt]

@[local simp, local arm64_norm]
private theorem overDecTag_trunc32_zext64_bpl (fl : GenFieldQ) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 fl.tag)) =
      BitVec.ofNat 64 fl.tag := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_beq_zero_bpl (fl : GenFieldQ) :
    (BitVec.ofNat 64 fl.tag == 0#64) = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_w32_beq_zero_bpl (fl : GenFieldQ) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 fl.tag) == 0#32) = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_sub1_64_bpl (fl : GenFieldQ) :
    BitVec.ofNat 64 fl.tag - 1#64 = BitVec.ofNat 64 (fl.tag - 1) := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_add_neg1_64_bpl (fl : GenFieldQ) :
    BitVec.ofNat 64 fl.tag + 0xffffffffffffffff#64 = BitVec.ofNat 64 (fl.tag - 1) := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_w32_sub1_bpl (fl : GenFieldQ) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 fl.tag) - 1#32) =
      BitVec.ofNat 64 (fl.tag - 1) := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_w32_add_neg1_bpl (fl : GenFieldQ) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 fl.tag) + 4294967295#32) =
      BitVec.ofNat 64 (fl.tag - 1) := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_sub1_trunc32_zext64_bpl (fl : GenFieldQ) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 (fl.tag - 1))) =
      BitVec.ofNat 64 (fl.tag - 1) := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_sub1_ult14_bpl (fl : GenFieldQ) :
    (14#32).ult (BitVec.setWidth 32 (BitVec.ofNat 64 (fl.tag - 1))) = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecTag_sub1_ult14_64_bpl (fl : GenFieldQ) :
    (14#64).ult (BitVec.ofNat 64 (fl.tag - 1)) = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [GenFieldQ.tag, GenField.tag]

@[local simp, local arm64_norm]
private theorem overDecJtabByte_add_armOff_bpl (fl : GenFieldQ) :
    8636#64 + (BitVec.setWidth 64 (overDecJtabByte fl) <<< 2#64) = overDecArmOff fl := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecJtabByte, overDecArmOff]

@[local simp, local arm64_norm]
private theorem overDecJtabByte_add_armOff_nat_bpl (fl : GenFieldQ) :
    8636#64 + (BitVec.setWidth 64 (overDecJtabByte fl) <<< 2) = overDecArmOff fl := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecJtabByte, overDecArmOff]

@[local simp, local arm64_norm]
private theorem overDecJtabByte_zext_add_armOff_bpl (fl : GenFieldQ) :
    8636#64 + (BitVec.zeroExtend 64 (overDecJtabByte fl) <<< 2) = overDecArmOff fl := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;>
    simp (config := { decide := true }) only [overDecJtabByte, overDecArmOff]

private theorem sepWPp_intro_overDecJtabByte_budget_pl [LibsignalPlacement]
    {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hro : ∀ (R : SepProp), s.mem ⊨ R →
      s.mem ⊨ ((lsρ overDecJtabSym) ↦ᵣ overDecJtabBytes) ∗ R)
    (fl : GenFieldQ)
    (h : SepWPp prog ret s
      (((lsρ overDecJtabSym + BitVec.ofNat 64 (fl.tag - 1)) ↦₈ᵣ overDecJtabByte fl) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  refine h R ?_ hL
  rw [sepConj_assoc]
  exact rodata_overDecJtabByte_of_table fl (hro (P ∗ R) hm)

private theorem drop_left_sepWPp_budget_pl {prog : Program} {ret : BitVec 64}
    {s : State} {Drop P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s (Drop ∗ P) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm) hL

set_option maxHeartbeats 600000 in
private theorem overDecKey_jtab_pool_wp_placed [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s0 s2 : State) (g : OverDecG) (fl : GenFieldQ)
    (hregs : OverDecRegsPlaced ext s0 g 0x2174#64 s2)
    (hx0 : s2.readReg64 .x0 = 0#64)
    (hx1 : s2.readReg64 .x1 = overDecKeyVal fl) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + overDecArmOff fl) s2
      ((lsρ overDecJtabSym + BitVec.ofNat 64 (fl.tag - 1)) ↦₈ᵣ overDecJtabByte fl)
      (fun sf P' =>
        (P' ⊢ ((lsρ overDecJtabSym + BitVec.ofNat 64 (fl.tag - 1)) ↦₈ᵣ overDecJtabByte fl)) ∧
        sf.sp = g.q ∧ (sf.sp &&& 15#64 == 0#64) = true ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x0 = overDecWt fl ∧
        sf.readReg64 .x22 = overDecKeyVal fl ∧
        sf.readReg64 .x19 = g.r19 ∧ sf.readReg64 .x20 = g.r20 ∧ sf.readReg64 .x26 = g.r26 ∧
        sf.readReg64 .x21 = g.q + 0x930#64 ∧ sf.readReg64 .x24 = 1#64 ∧
        sf.readReg64 .x25 = 0xffffffffffffffff#64 ∧ sf.readReg64 .x27 = g.prevPtr ∧
        sf.readReg64 .x28 = g.q + 0xa90#64 ∧ sf.readReg64 .x29 = g.q + 0xc70#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs g.sv ∧
        (∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ),
          A.pool lim st sf = A.pool lim st s2)) := by
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, _hcl,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  have h0 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h1 : s2.readReg64 (Reg.gpr 1#5) = overDecKeyVal fl := hx1
  have h19 : s2.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have h20 : s2.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have h26 : s2.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have h21 : s2.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have h24 : s2.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have h25 : s2.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have h27 : s2.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have h28 : s2.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have h29 : s2.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  iterate 17 wp_step
  refine SepWP.done (by simp only [arm64_norm, BitVec.add_assoc])
    (by simp only [hrun, arm64_norm]) ?_
  refine ⟨Entails.refl _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hsp, arm64_norm]
  · simp only [hal, arm64_norm]
  · simp only [htr, arm64_norm]
  · simp only [arm64_norm]
  · simp only [arm64_norm]
  · simp only [h19, arm64_norm]
  · simp only [h20, arm64_norm]
  · simp only [h26, arm64_norm]
  · simp only [h21, arm64_norm]
  · simp only [h24, arm64_norm]
  · simp only [h25, arm64_norm]
  · simp only [h27, arm64_norm]
  · simp only [h28, arm64_norm]
  · simp only [h29, arm64_norm]
  · simp only [hvregs, arm64_norm]
  · refine fun A lim st => (A.pool_of_vmPreserved (vmPreserved_of_fields ?_ ?_ ?_ ?_ ?_)).symm
    all_goals rfl

/-! ## Main Budget-Threaded Key Dispatch Theorems -/

set_option maxHeartbeats 600000 in
/-- Fixed-`ext` `LibsignalCodeRoLoaded` budget-threaded key dispatch (`OverDecKeyCroPlacedAt A lim ext`), parameterized by `withLsCodeLoaded`-wrapped `decodeVarint2SpecX` at `lsmpl.base 515`. -/
theorem overDecKey_cro_placed_of_lscl_dv5 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hDv5 : subroutine_ok (lsProg_518 ext) (lsmpl.base 515)
      (withLsCodeLoaded lsmpl (decodeVarint2SpecX A lim))) :
    OverDecKeyCroPlacedAt A lim ext := by
  intro st s0 s g v fl rest _hAny _hok hsuf hlen ⟨hcro, hregs⟩
  rcases hsuf with ⟨pfx, hpfx⟩
  have hlen63 : (fl.enc ++ rest).length < 2 ^ 63 := by
    have hle : (fl.enc ++ rest).length ≤ g.enc.length := by
      have hlen_eq := congrArg List.length hpfx
      rw [List.length_append] at hlen_eq
      omega
    omega
  refine SepWPp_bind_sepWP_frame_cro_key_budget_pl hcro
    (overDecKey_precall_pool_wp_placed ext s0 s g hregs)
    (F := overDecHeapBudget A lim st s g (fl.enc ++ rest) v)
    (by simp only [emp_sepConj])
    fun sm hpcm hrunm _hLm hcrom hregsm => ?_
  rcases hregsm with ⟨hspm, halm, htrm, hx0m, hlrm,
    hx19m, hx20m, hx26m, hx21m, hx24m, hx25m, hx27m, hx28m, hx29m, hvregsm, hpoolm⟩
  have hheap_split :
      emp ∗ overDecHeapBudget A lim st s g (fl.enc ++ rest) v =
        (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64) ∗
          sliceCursorAt (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length) (fl.enc ++ rest) ∗
          A.pool lim st sm ∗
          stackAt g.q decodeVarint2StackX) ∗
         (overPrevElemRestBudget A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
          (g.encPtr ↦ₛ pfx) ∗
          prostSSGQAt A.repAlloc (g.q + 0x930#64) v ∗
          memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
          memRegion (g.q + 0xbf0#64) 128 ∗
          memRegion (g.q - BitVec.ofNat 64 overDecStackX)
            (overDecStackX - decodeVarint2StackX))) := by
    have hcur :
        sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc (fl.enc ++ rest) =
          sliceCursorAt (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length) (fl.enc ++ rest) ∗
            (g.encPtr ↦ₛ pfx) := by
      rw [← hpfx]
      exact sliceCursorAfter_split_of_append_budget_pl (g.q + 0x920#64) g.encPtr pfx (fl.enc ++ rest)
    unfold overDecHeapBudget
    rw [hcur, ← hpoolm A lim st,
      stackAt_sub_eq_key_budget_pl g.q overDecStackX decodeVarint2StackX (by decide) (by decide),
      emp_sepConj]
    sep_ac_rfl
  rw [hheap_split]
  refine overDec_call_decodeVarint5_lscl_budget_pl hDv5 hcrom htrm hpcm hrunm hspm halm hx0m hlrm hlen63
    fun s2 hpc2 hrun2 hsp2 hL2 hcro2 htr2 hcs2 hx0_2 hx1_2 => ?_
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, _, _, hx24_cs, hx25_cs, hx26_cs, hx27_cs, hx28_cs, hx29_cs, hvregs_cs⟩
  have hal2 : (s2.sp &&& 15#64 == 0#64) = true := by simpa only [hsp2, hspm] using halm
  have hregs2 : OverDecRegsPlaced ext s0 g 0x2174#64 s2 :=
    ⟨hpc2, hrun2, hsp2, hal2, htr2, hL2,
     hx19_cs.trans hx19m, hx20_cs.trans hx20m, hx26_cs.trans hx26m,
     hx21_cs.trans hx21m, hx24_cs.trans hx24m, hx25_cs.trans hx25m,
     hx27_cs.trans hx27m, hx28_cs.trans hx28m, hx29_cs.trans hx29m,
     hvregs_cs.trans hvregsm⟩
  have hheap_unsplit :
      (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64) ∗
        sliceCursorAfter (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
          (fl.enc ++ rest) (fl.payload ++ rest) ∗
        A.pool lim st s2 ∗
        stackAt g.q decodeVarint2StackX) ∗
       (overPrevElemRestBudget A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
        (g.encPtr ↦ₛ pfx) ∗
        prostSSGQAt A.repAlloc (g.q + 0x930#64) v ∗
        memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
        memRegion (g.q + 0xbf0#64) 128 ∗
        memRegion (g.q - BitVec.ofNat 64 overDecStackX)
          (overDecStackX - decodeVarint2StackX))) =
      overDecHeapBudget A lim st s2 g (fl.payload ++ rest) v := by
    have hunsplit :=
      sliceCursorAfter_unsplit_of_append_budget_pl (g.q + 0x920#64) g.encPtr pfx (fl.enc ++ rest)
        (fl.payload ++ rest) (fl_payload_rest_len_le_budget_pl fl rest)
    rw [hpfx] at hunsplit
    unfold overDecHeapBudget
    rw [← hunsplit,
      stackAt_sub_eq_key_budget_pl g.q overDecStackX decodeVarint2StackX (by decide) (by decide)]
    sep_ac_rfl
  rw [hheap_unsplit]
  refine sepWPp_intro_overDecJtabByte_budget_pl
    (fun R hR => rodata_overDecJtab_placed_intro hcro2.2 hR) fl ?_
  refine SepWPp_bind_sepWP_frame_cro_key_budget_pl hcro2
    (overDecKey_jtab_pool_wp_placed ext s0 s2 g fl hregs2 hx0_2 hx1_2)
    rfl
    fun sf hpcf hrunf hLf hcrof hregsf => ?_
  apply drop_left_sepWPp_budget_pl
  rcases hregsf with ⟨hspf, half, htrf, hx0f, hx22f,
    hx19f, hx20f, hx26f, hx21f, hx24f, hx25f, hx27f, hx28f, hx29f, hvregsf, hpoolf⟩
  refine SepWPp.done hpcf hrunf
    ⟨⟨hcrof, hpcf, hrunf, hspf, half, htrf, hLf,
      hx19f, hx20f, hx26f, hx21f, hx24f, hx25f, hx27f, hx28f, hx29f, hvregsf⟩,
     hx0f, hx22f, Entails.of_eq ?_⟩
  unfold overDecHeapBudget
  rw [hpoolf A lim st]

theorem overDecKey_cro_placed_of_dv5 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hDv5 : DecodeVarint5PlacedOkExtX A lim ext) :
    OverDecKeyCroPlacedAt A lim ext :=
  overDecKey_cro_placed_of_lscl_dv5 (lscl_of_cl hDv5)

/-- Fixed-`ext` `LibsignalCodeRoLoaded` budget-threaded key dispatch (`OverDecKeyCroPlacedAt A lim ext`) from `AllocContractsPlaced M A lim ext`. -/
theorem overDecKey_cro_placed_of_alloc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hAlloc : AllocContractsPlaced M A lim ext) :
    OverDecKeyCroPlacedAt A lim ext :=
  overDecKey_cro_placed_of_dv5 (decodeVarint5_placed_ok_ext_x hAlloc)

alias overDecKey_cro_placed_of_hooks := overDecKey_cro_placed_of_alloc

theorem overDecKey_placed_of_callees [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hDv5 : ∀ ext, DecodeVarint5PlacedOkExtX A lim ext) :
    OverDecKeyPlacedStmt A lim :=
  fun ext => overDecKey_cro_placed_of_dv5 (hDv5 ext)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.KeyPlacedBudget
