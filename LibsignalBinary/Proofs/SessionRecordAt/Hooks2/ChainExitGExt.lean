/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsX
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Fields
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false
/-!
# `message::merge<Chain>` Loop-Exit Leaf Proof (`chainExitG_ok`)

Proves the loop-exit segment (`+0x120 → ret` once all fields are consumed) of
`prost::encoding::message::merge<Chain>`, including X-stack (`_atW`, `_atWA`) and relocatable
`[LibsignalPlacement]` (`lsProg_11 H`, Block `11`) variants.
-/

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainExitG

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAt sliceCursorAfter)
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open Proofs.libsignal.Hooks2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace ChainMergeStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
theorem calleeSavedVRegs_setPC_pre_seedChain (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem calleeSavedVRegs_setMem_setPC_pre_seedChain (s : State) (pc : BitVec 64) (m : Memory) :
    calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre_seedChain (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre_seedChain (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre_seedChain (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre_seedChain (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre_seedChain (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre_seedChain (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre_seedChain (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre_seedChain (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local simp, local arm64_norm]
theorem getLsbD_63_eq_seedChain (v : BitVec 64) :
    v.getLsbD 63 = !(v >>> 56).ult 128#64 := by
  bv_robdd

end ChainMergeStateSimp
open ChainMergeStateSimp

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
and the epilogue `+0x0f0..+0x10c` to `ret`, parameterized by `img` on `SP2Ext img.base ext` at `chainMergeStackX`. -/
theorem step_chainExitG_extW (img : Obj.Image)
    {ext : String → Option (State → State)}
    (bufRef slot ptr sp0 : BitVec 64)
    (tail : List (BitVec 8))
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x120#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 256#64)
    (hsp_sub_align : s0.sp &&& 15#64 = 0#64)
    (hF : img.FrozenLoaded s0)
    (hsym : s0.symtab = img.symtab)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hlr_init : s_init.readReg64 .lr = ret)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (sm : State),
      sm.pc = ret →
      sm.status = .Running →
      sm.sp = sp0 →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s_init.trace →
      sm.readReg64 .x0 = 0#64 →
      CalleeSavedPreserved s_init sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot ptr tail ∗
          stackAt sp0 chainMergeStackX) ∗ F)
        Q Qp) :
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr tail ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX ∗
        chainMergeSavedRegs sp0 s_init) ∗ F)
      Q Qp := by
  have hsp_restore : sp0 - 256#64 + 256#64 = sp0 := BitVec.sub_add_cancel sp0 256#64
  chainMerge_fetches_range img.base
    (Rust.withPanics ext) 0x120 0x12c
  chainMerge_fetches_range img.base
    (Rust.withPanics ext) 0x674 0x67c
  chainMerge_fetches_range img.base
    (Rust.withPanics ext) 0x0f0 0x10c
  dsimp only [SP2Ext, contractProg, chainMergeName] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
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
  rw [stackAt_chainMergeStackX_split_seedChain sp0]
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

/-- The return of the chain merge with its post at `img` and `chainMergeStackX`. -/
def ChainRetGAtW (img : Obj.Image) (x : ChainMergeGenGhost) (R : SepProp) (s0 sf : State) : Prop :=
  Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧
    (sf.mem ⊨ (chainMergeGenSpecAtW img).post x s0 sf ∗ R)

/-- Leaf CM-exit: `+0x120` with all fields done `→ ret` with `(chainMergeGenSpecAtW img).post` on `SP2Ext img.base ext`. -/
theorem chainExitG_ok_atW (img : Obj.Image)
    {ext : String → Option (State → State)}
    (x : ChainMergeGenGhost) (R : SepProp) (s0 s : State)
    (hs : ChainLoopGAtW img ext x R s0 x.c.fields.length s) :
    ChainStepGAtW img ext x R s0 s (ChainRetGAtW img x R s0) := by
  rcases hs with ⟨hpc, hrun, htr, hvregs, hsym, hF, hsp, hal, _, hx19, _, hx24, _, _, _, _, _, _, hmem⟩
  have hpc' : s.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x120#64 := hpc
  have hsp_sub_align : s.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using hal
  rw [chainGAfter_fields x.c, List.drop_length, List.flatMap_nil, List.nil_append,
    sliceCursorAfter_append_eq_seedChain x.slot x.ptr x.c.payload x.tail] at hmem
  let ptrEnd := x.ptr + BitVec.ofNat 64 x.c.payload.length
  have hmem' : s.mem ⊨
      (((x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAt x.slot ptrEnd x.tail ∗
        stackAt (s0.sp - 256#64) chainMergeSubStackX ∗
        chainMergeSavedRegs s0.sp s0) ∗
        (prostChainGAt A0 x.a x.c ∗ (x.ptr ↦ₛ x.c.payload))) ∗ R := by
    dsimp only [ptrEnd]
    exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
  have hwp : SepWPp (SP2Ext img.base ext) (s0.readReg64 .lr) s
      (((x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAt x.slot ptrEnd x.tail ∗
        stackAt (s0.sp - 256#64) chainMergeSubStackX ∗
        chainMergeSavedRegs s0.sp s0) ∗
        (prostChainGAt A0 x.a x.c ∗ (x.ptr ↦ₛ x.c.payload)))
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (Pf ⊢ (chainMergeGenSpecAtW img).post x s0 sf))
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ (chainMergeGenSpecAtW img).onPanic x s0 sf ∗ R)) := by
    refine step_chainExitG_extW img x.bufRef x.slot ptrEnd s0.sp x.tail
      hpc' hrun hsp hsp_sub_align hF hsym htr hvregs rfl hx19 hx24 ?_
    intro sf hpcf hrunf hspf _ _ htrf hx0f hcsf
    refine SepWPp.done hpcf hrunf ⟨hspf, hcsf, ?_⟩
    dsimp only [chainMergeGenSpecAtW]
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

/-- Leaf CM-exit (`*WA`): `+0x120` with all fields done `→ ret` with
`(chainMergeGenSpecAtWA A img).post` on `SP2Ext img.base ext` for arbitrary `(A : RustAlloc)`. -/
theorem chainExitG_ok_atWA (img : Obj.Image) (A : RustAlloc)
    {ext : String → Option (State → State)}
    (x : ChainMergeGenGhost) (R : SepProp) (s0 s : State)
    (hs : ChainLoopGAtWA img A ext x R s0 x.c.fields.length s) :
    ChainStepGAtWA img A ext x R s0 s (Proofs.libsignal.Hooks2.ChainRetGAtWA img A x R s0) := by
  rcases hs with ⟨hpc, hrun, htr, hvregs, hsym, hF, hsp, hal, _, hx19, _, hx24, _, _, _, _, _, _, hmem⟩
  have hpc' : s.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x120#64 := hpc
  have hsp_sub_align : s.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using hal
  rw [chainGAfter_fields x.c, List.drop_length, List.flatMap_nil, List.nil_append,
    sliceCursorAfter_append_eq_seedChain x.slot x.ptr x.c.payload x.tail] at hmem
  let ptrEnd := x.ptr + BitVec.ofNat 64 x.c.payload.length
  have hmem' : s.mem ⊨
      (((x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAt x.slot ptrEnd x.tail ∗
        stackAt (s0.sp - 256#64) chainMergeSubStackX ∗
        chainMergeSavedRegs s0.sp s0) ∗
        (prostChainGAt A x.a x.c ∗ (x.ptr ↦ₛ x.c.payload) ∗ A.pool)) ∗ R := by
    dsimp only [ptrEnd]
    exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
  have hwp : SepWPp (SP2Ext img.base ext) (s0.readReg64 .lr) s
      (((x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAt x.slot ptrEnd x.tail ∗
        stackAt (s0.sp - 256#64) chainMergeSubStackX ∗
        chainMergeSavedRegs s0.sp s0) ∗
        (prostChainGAt A x.a x.c ∗ (x.ptr ↦ₛ x.c.payload) ∗ A.pool))
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (Pf ⊢ (chainMergeGenSpecAtWA A img).post x s0 sf))
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ (chainMergeGenSpecAtWA A img).onPanic x s0 sf ∗ R)) := by
    refine step_chainExitG_extW img x.bufRef x.slot ptrEnd s0.sp x.tail
      hpc' hrun hsp hsp_sub_align hF hsym htr hvregs rfl hx19 hx24 ?_
    intro sf hpcf hrunf hspf _ _ htrf hx0f hcsf
    refine SepWPp.done hpcf hrunf ⟨hspf, hcsf, ?_⟩
    dsimp only [chainMergeGenSpecAtWA]
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

/-! ## Relocatable `[LibsignalPlacement]` Proof of `message::merge<Chain>` Loop Exit (`lsProg_11 H`) -/

section Placed

open Arm64.Obj CryptoVerification.E2E.Record.Placed

theorem L1_ChainExitGExt_Placed : True := trivial

private theorem step_chainExitG_placedW [LibsignalPlacement]
    {H : LibsignalHooks}
    (bufRef slot ptr sp0 : BitVec 64)
    (tail : List (BitVec 8))
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_11).base + 0x120#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 256#64)
    (hsp_sub_align : s0.sp &&& 15#64 = 0#64)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hlr_init : s_init.readReg64 .lr = ret)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (sm : State),
      sm.pc = ret →
      sm.status = .Running →
      sm.sp = sp0 →
      sm.trace = s_init.trace →
      sm.readReg64 .x0 = 0#64 →
      CalleeSavedPreserved s_init sm →
      SepWPp (lsProg_11 H) ret sm
        (((bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot ptr tail ∗
          stackAt sp0 chainMergeStackX) ∗ F)
        Q Qp) :
    SepWPp (lsProg_11 H) ret s0
      (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr tail ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX ∗
        chainMergeSavedRegs sp0 s_init) ∗ F)
      Q Qp := by
  have hsp_restore : sp0 - 256#64 + 256#64 = sp0 := BitVec.sub_add_cancel sp0 256#64
  have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hx24
  have h30_init : s_init.readReg64 (Reg.gpr 30#5) = ret := hlr_init
  refine SepWPp.of_sepWP (mid := ret) ?_
  unfold sliceCursorAt chainMergeSavedRegs
  simp only [sepConj_assoc]
  iterate 15 wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm])
    (by simp only [hrun, arm64_norm])
    (by simp only [arm64_norm])
    (by simp only [htr, arm64_norm])
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
  rw [stackAt_chainMergeStackX_split_seedChain sp0]
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

/-- Relocatable `message::merge<Chain>` loop exit (`+0x120` → `ret`) on `lsProg_11 H`. -/
theorem chainExitG_placed_okW [LibsignalPlacement] (H : LibsignalHooks)
    (x : ChainMergeGenGhost) (R : SepProp) (s0 s : State)
    (hs : ChainLoopGPlacedW x R s0 x.c.fields.length s) :
    ChainStepGPlacedW H x R s0 s
      (fun sf => Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧
        (sf.mem ⊨ chainMergeGenPlacedSpecW.post x s0 sf ∗ R)) := by
  rcases hs with ⟨hpc, hrun, htr, hvregs, _hcrl, hsp, hal, _, hx19, _, hx24, _, _, _, _, _, _, hmem⟩
  have hpc' : s.pc = (blkPl_11).base + 0x120#64 := hpc
  have hsp_sub_align : s.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using hal
  rw [chainGAfter_fields x.c, List.drop_length, List.flatMap_nil, List.nil_append,
    sliceCursorAfter_append_eq_seedChain x.slot x.ptr x.c.payload x.tail] at hmem
  let ptrEnd := x.ptr + BitVec.ofNat 64 x.c.payload.length
  have hmem' : s.mem ⊨
      (((x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAt x.slot ptrEnd x.tail ∗
        stackAt (s0.sp - 256#64) chainMergeSubStackX ∗
        chainMergeSavedRegs s0.sp s0) ∗
        (prostChainGAt A0 x.a x.c ∗ (x.ptr ↦ₛ x.c.payload))) ∗ R := by
    dsimp only [ptrEnd]
    exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
  have hwp : SepWPp (lsProg_11 H) (s0.readReg64 .lr) s
      (((x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAt x.slot ptrEnd x.tail ∗
        stackAt (s0.sp - 256#64) chainMergeSubStackX ∗
        chainMergeSavedRegs s0.sp s0) ∗
        (prostChainGAt A0 x.a x.c ∗ (x.ptr ↦ₛ x.c.payload)))
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (Pf ⊢ chainMergeGenPlacedSpecW.post x s0 sf))
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ chainMergeGenPlacedSpecW.onPanic x s0 sf ∗ R)) := by
    refine step_chainExitG_placedW x.bufRef x.slot ptrEnd s0.sp x.tail
      hpc' hrun hsp hsp_sub_align htr hvregs rfl hx19 hx24 ?_
    intro sf hpcf hrunf hspf htrf hx0f hcsf
    refine SepWPp.done hpcf hrunf ⟨hspf, hcsf, ?_⟩
    dsimp only [chainMergeGenPlacedSpecW, LibsignalTripleRatchet.withLsCodeRoLoaded,
      chainMergeGenRawSpecW]
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

end Placed

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainExitG

