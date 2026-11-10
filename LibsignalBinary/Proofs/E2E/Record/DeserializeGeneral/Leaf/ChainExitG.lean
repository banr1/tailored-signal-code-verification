/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.ChainDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Fields
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.BodyDefs
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Exit Segment Leaf (`chainExitG_ok`) for General `message::merge<Chain>`

Proves `chainExitG_ok` (`+0x120 → ret`) when all fields of `x.c` have been decoded, establishing
`chainMergeGenSpec.post`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainExitG

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAt sliceCursorAfter)
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? sessionImg0
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

/-- Step from the outer loop head `+0x120` when remaining equals `tail.length` through `+0x674`
and the epilogue `+0x0f0..+0x10c` to `ret`. -/
theorem step_chainExitG (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (bufRef slot ptr sp0 : BitVec 64)
    (tail : List (BitVec 8))
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x120#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 256#64)
    (hsp_sub_align : s0.sp &&& 15#64 = 0#64)
    (hF : sessionImg0.FrozenLoaded s0)
    (hsym : s0.symtab = sessionImg0.symtab)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hlr_init : s_init.readReg64 .lr = ret)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (sm : State),
      sm.pc = ret →
      sm.status = .Running →
      sm.sp = sp0 →
      sessionImg0.FrozenLoaded sm →
      sm.symtab = sessionImg0.symtab →
      sm.trace = s_init.trace →
      sm.readReg64 .x0 = 0#64 →
      CalleeSavedPreserved s_init sm →
      SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret sm
        (((bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot ptr tail ∗
          stackAt sp0 chainMergeStack) ∗ F)
        Q Qp) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s0
      (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr tail ∗
        stackAt (sp0 - 256#64) chainMergeSubStack ∗
        chainMergeSavedRegs sp0 s_init) ∗ F)
      Q Qp := by
  have hsp_restore : sp0 - 256#64 + 256#64 = sp0 := BitVec.sub_add_cancel sp0 256#64
  chainMerge_fetches_range sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x120 0x12c
  chainMerge_fetches_range sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x674 0x67c
  chainMerge_fetches_range sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x0f0 0x10c
  dsimp only [tripleRatchetProgAt, chainMergeName] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase sessionImg0.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
  examples_hide_fetches
  have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hx24
  have h30_init : s_init.readReg64 (Reg.gpr 30#5) = ret := hlr_init
  refine SepWPp.of_sepWP_frozen_seedChain (mid := ret) hF hsym ?_
  unfold sliceCursorAt chainMergeSavedRegs
  simp only [sepConj_assoc]
  iterate 15 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm])
    (by simp only [hrun, arm64_norm])
    (by simp only [arm64_norm])
    hF1 hsym1 (by simp only [htr, arm64_norm])
    (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [hvregs, arm64_norm]⟩)
  rw [stackAt_chainMergeStack_split_seedChain sp0]
  unfold sliceCursorAt
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Entails.trans ?_
    (Entails.sepExists_right (s_init.readReg64 .x29)
      (Entails.sepExists_right (s_init.readReg64 .x30)
        (Entails.sepExists_right (s_init.readReg64 .x28)
          (Entails.sepExists_right (s_init.readReg64 .x27)
            (Entails.sepExists_right (s_init.readReg64 .x26)
              (Entails.sepExists_right (s_init.readReg64 .x25)
                (Entails.sepExists_right (s_init.readReg64 .x24)
                  (Entails.sepExists_right (s_init.readReg64 .x23)
                    (Entails.sepExists_right (s_init.readReg64 .x22)
                      (Entails.sepExists_right (s_init.readReg64 .x21)
                        (Entails.sepExists_right (s_init.readReg64 .x20)
                          (Entails.sepExists_right (s_init.readReg64 .x19)
                            (Entails.refl _)))))))))))))
  exact sep_ac_seedChain (by ac_rfl)

theorem chainExitG_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (x : ChainMergeGenGhost) (R : SepProp) (s0 s : State)
    (hs : ChainLoopG C ctl x R s0 x.c.fields.length s) :
    ChainStepG C ctl x R s0 s (ChainRetG x R s0) abs := by
  rcases hs with ⟨hpc, hrun, htr, hvregs, hsym, hF, hsp, hal, _, hx19, _, hx24, _, _, _, _, _, _, hmem⟩
  have hpc' : s.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName + 0x120#64 := hpc
  have hsp_sub_align : s.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using hal
  rw [chainGAfter_fields x.c, List.drop_length, List.flatMap_nil, List.nil_append,
    sliceCursorAfter_append_eq_seedChain x.slot x.ptr x.c.payload x.tail] at hmem
  let ptrEnd := x.ptr + BitVec.ofNat 64 x.c.payload.length
  have hmem' : s.mem ⊨
      (((x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAt x.slot ptrEnd x.tail ∗
        stackAt (s0.sp - 256#64) chainMergeSubStack ∗
        chainMergeSavedRegs s0.sp s0) ∗
        (prostChainGAt A0 x.a x.c ∗ (x.ptr ↦ₛ x.c.payload))) ∗ R := by
    dsimp only [ptrEnd]
    exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
  have hwp : SepWPp (recordProg C ctl abs) (s0.readReg64 .lr) s
      (((x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAt x.slot ptrEnd x.tail ∗
        stackAt (s0.sp - 256#64) chainMergeSubStack ∗
        chainMergeSavedRegs s0.sp s0) ∗
        (prostChainGAt A0 x.a x.c ∗ (x.ptr ↦ₛ x.c.payload)))
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (Pf ⊢ chainMergeGenSpec.post x s0 sf))
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ chainMergeGenSpec.onPanic x s0 sf ∗ R)) := by
    refine step_chainExitG C ctl x.bufRef x.slot ptrEnd s0.sp x.tail
      hpc' hrun hsp hsp_sub_align hF hsym htr hvregs rfl hx19 hx24 ?_
    intro sf hpcf hrunf hspf _ _ htrf hx0f hcsf
    refine SepWPp.done hpcf hrunf ⟨hspf, hcsf, ?_⟩
    dsimp only [chainMergeGenSpec]
    rw [pure_sepConj_of_true ⟨htrf, hx0f⟩,
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

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainExitG

