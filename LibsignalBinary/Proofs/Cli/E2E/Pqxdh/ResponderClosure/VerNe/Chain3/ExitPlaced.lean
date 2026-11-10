/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Exit
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.CodePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Fields
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import ProofLib.SepLogic.WPp

/-!
# Placed `message::merge<Chain> [local#4]`: Exit Slice

`[LibsignalPlacement]` Block-`516` counterpart of `VerNe.Chain3.Exit` (`Chain3ExitPlacedStmt`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAt sliceCursorAfter)
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open Proofs.libsignal.Hooks2
open CryptoVerification.CodeLayout
open CryptoVerification.CliHandshake.Placed

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg
attribute [local arm64_norm ↓, local wp_norm ↓]
  ChainMergeStateSimp.calleeSavedVRegs_setPC_pre_seedChain
  ChainMergeStateSimp.calleeSavedVRegs_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.sp_setPC_pre_seedChain
  ChainMergeStateSimp.sp_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg64_setPC_pre_seedChain
  ChainMergeStateSimp.readReg64_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg32_setPC_pre_seedChain
  ChainMergeStateSimp.readReg32_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg_setPC_pre_seedChain
  ChainMergeStateSimp.readReg_setMem_setPC_pre_seedChain

attribute [local simp, local arm64_norm] ChainMergeStateSimp.getLsbD_63_eq_seedChain

set_option maxHeartbeats 400000 in
theorem step_chain3Exit_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (bufRef slot ptr sp0 : BitVec 64)
    (tail : List (BitVec 8))
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = lsmpl.base 516 + 0xa8#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 0xf0#64)
    (hsp_sub_align : s0.sp &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hlr_init : s_init.readReg64 .lr = ret)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx21 : s0.readReg64 .x21 = BitVec.ofNat 64 tail.length)
    (hx26 : s0.readReg64 .x26 = s_init.readReg64 .x26)
    (hx27 : s0.readReg64 .x27 = s_init.readReg64 .x27)
    (hx28 : s0.readReg64 .x28 = s_init.readReg64 .x28)
    (hnext : ∀ (sm : State),
      sm.pc = ret →
      sm.status = .Running →
      sm.sp = sp0 →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.trace = s_init.trace →
      sm.readReg64 .x0 = 0#64 →
      CalleeSavedPreserved s_init sm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot ptr tail ∗
          stackAt sp0 chainMerge3StackX) ∗ F)
        Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s0
      (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr tail ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX ∗
        chain3SavedRegs sp0 s_init) ∗ F)
      Q Qp := by
  have hsp_restore : sp0 - 0xf0#64 + 0xf0#64 = sp0 := BitVec.sub_add_cancel sp0 0xf0#64
  have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h21 : s0.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := hx21
  have h26 : s0.readReg64 (Reg.gpr 26#5) = s_init.readReg64 (Reg.gpr 26#5) := hx26
  have h27 : s0.readReg64 (Reg.gpr 27#5) = s_init.readReg64 (Reg.gpr 27#5) := hx27
  have h28 : s0.readReg64 (Reg.gpr 28#5) = s_init.readReg64 (Reg.gpr 28#5) := hx28
  have h30_init : s_init.readReg64 (Reg.gpr 30#5) = ret := hlr_init
  refine SepWPp.of_sepWP_lscl_c3 (mid := ret) hcl ?_
  change s0.pc = (blkPl_516).base + 0xa8#64 at hpc
  unfold sliceCursorAt chain3SavedRegs
  simp only [sepConj_assoc]
  iterate 14 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hcl1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm])
    (by simp only [hrun, arm64_norm])
    (by simp only [arm64_norm])
    hcl1 (by simp only [htr, arm64_norm])
    (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [h26, arm64_norm],
     by simp only [h27, arm64_norm],
     by simp only [h28, arm64_norm],
     by simp only [arm64_norm],
     by simp only [hvregs, arm64_norm]⟩)
  refine Entails.trans ?_ (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
    (chain3_stack_restore sp0 s_init))))
  unfold sliceCursorAt chain3SavedRegs
  exact sep_ac_seedChain (by ac_rfl)

set_option maxHeartbeats 400000 in
/-- Placed exit slice stepping `Chain3LoopPlacedAtW` with all fields consumed to `Chain3RetPlacedAtW`. -/
theorem chain3Exit_placed_ok [LibsignalPlacement] (ext : String → Option (State → State)) :
    Chain3ExitPlacedStmt ext := by
  intro x R s0 s hs
  rcases hs with ⟨hpc, hrun, htr, hvregs, hcl, hsp, hal, _, hx19, _, hx21, _, _, _,
    hx26, hx27, hx28, _, _, hmem⟩
  have hpc' : s.pc = lsmpl.base 516 + 0xa8#64 := hpc
  have hsp_sub_align : s.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using hal
  rw [chainGAfter_fields x.c, List.drop_length, List.flatMap_nil, List.nil_append,
    sliceCursorAfter_append_eq_seedChain x.slot x.ptr x.c.payload x.tail] at hmem
  let ptrEnd := x.ptr + BitVec.ofNat 64 x.c.payload.length
  have hmem' : s.mem ⊨
      (((x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAt x.slot ptrEnd x.tail ∗
        stackAt (s0.sp - 0xf0#64) chainMerge3SubStackX ∗
        chain3SavedRegs s0.sp s0) ∗
        (prostChainGAt A0 x.a x.c ∗ (x.ptr ↦ₛ x.c.payload))) ∗ R := by
    dsimp only [ptrEnd]
    exact Satisfies.mono (Entails.trans
      (sepConj_mono_left (chain3GAt_entails_prostChainGAt A0 x.a x.c))
      (sep_ac_seedChain (by ac_rfl))) hmem
  have hwp : SepWPp (lsProg_516 (Rust.withPanics ext)) (s0.readReg64 .lr) s
      (((x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAt x.slot ptrEnd x.tail ∗
        stackAt (s0.sp - 0xf0#64) chainMerge3SubStackX ∗
        chain3SavedRegs s0.sp s0) ∗
        (prostChainGAt A0 x.a x.c ∗ (x.ptr ↦ₛ x.c.payload)))
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (Pf ⊢ chainMerge3PlacedSpecW.post x s0 sf))
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ chainMerge3PlacedSpecW.onPanic x s0 sf ∗ R)) := by
    refine step_chain3Exit_placed x.bufRef x.slot ptrEnd s0.sp x.tail
      hpc' hrun hsp hsp_sub_align hcl htr hvregs rfl hx19 hx21 hx26 hx27 hx28 ?_
    intro sf hpcf hrunf hspf hclf htrf hx0f hcsf
    refine SepWPp.done hpcf hrunf ⟨hspf, hcsf, ?_⟩
    dsimp only [chainMerge3PlacedSpecW, withLsCl, chainMerge3RawSpecW]
    rw [pure_sepConj_of_true hclf, pure_sepConj_of_true ⟨htrf, hx0f⟩,
      sliceCursorAfter_append_eq_seedChain x.slot x.ptr x.c.payload x.tail]
    dsimp only [ptrEnd]
    exact sep_ac_seedChain (by ac_rfl)
  intro hL
  obtain ⟨sf, hsteps, hex⟩ := hwp R hmem' hL
  rcases hex with ⟨hpc_f, hrun_f, Pf, hmf, hsp_f, hcs_f, hent_f⟩ | ⟨hpan, Pf, hmf, htr_f⟩ | ⟨_, hoom⟩
  · exact ⟨sf, hsteps, Or.inl ⟨⟨hpc_f, hsp_f, hrun_f⟩, ⟨hsp_f, hcs_f⟩,
      Satisfies.mono (sepConj_mono_left hent_f) hmf⟩⟩
  · exact ⟨sf, hsteps, Or.inr ⟨hpan, htr_f hmf⟩⟩
  · exact (not_satisfies_false_sepConj hoom).elim

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
