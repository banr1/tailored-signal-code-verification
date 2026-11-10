/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHookPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCallees
public import LibsignalBinary.Proofs.E2E.Pqxdh.TopLevel.SessionInitiateACommon
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Relocatable `SessionState::set_unacknowledged_pre_key_message` at `UNIX_EPOCH`

Verifies Block `33` (`<SessionState>::set_unacknowledged_pre_key_message`) at `now = UNIX_EPOCH`
(`x5 = 0`, `w6 = 0`) against `setUnackPreKeyMsgExactStackEpochSpecPlaced` under
`[LibsignalPlacement]`, with cross-block (`i < 619`) and `cliGhostExterns` specializations.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace CryptoVerification.SignalSession.Cli.Slots

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection ProofLib.Variant
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.E2E.Bin CryptoVerification.E2E.HooksE
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.TopLevel
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops

private abbrev allocHookStack : Nat := 4096

/-- Image-free inner `Spec` of Block `33` (`<SessionState>::set_unacknowledged_pre_key_message`) at `now = UNIX_EPOCH` (`x5 = 0`, `w6 = 0`). -/
def setUnackPreKeyMsgEpochInnerSpec (A : RustAlloc) :
    Spec Pqxdh.TopLevel.SetUnackExactGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x5 = 0#64 ∧ (s.readReg64 .x6).setWidth 32 = 0#32⌝ ∗
      ⌜s.readReg64 .x0 = g.statePtr ∧
        (s.readReg64 .x1).setWidth 32 = g.optOpkTag ∧
        (s.readReg64 .x2).setWidth 32 = g.optOpkVal ∧
        (s.readReg64 .x3).setWidth 32 = g.spkId ∧
        s.readReg64 .x4 = g.baseKeyPtr ∧
        g.baseKeyBytes.length = 32⌝ ∗
      (g.baseKeyPtr ↦ₛ Initiator.bytesToBv8 g.baseKeyBytes) ∗
      ((g.statePtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      memRegion (g.statePtr + 0x100#64) 40 ∗
      stackAt (s.sp - 144#64) (allocHookStack + 32) ∗
      cells (s.sp - 144#64) 18 ∗
      A.pool
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (g.baseKeyPtr ↦ₛ Initiator.bytesToBv8 g.baseKeyBytes) ∗
      Pqxdh.Initiator.vecU8 A (g.statePtr + 0xf8#64)
        (Initiator.bytesToBv8 (Pqxdh.Initiator.encodeEC g.baseKeyBytes)) ∗
      ((g.statePtr + 0x110#64) ↦₃₂ g.optOpkTag) ∗
      ((g.statePtr + 0x114#64) ↦₃₂ g.optOpkVal) ∗
      ((g.statePtr + 0x118#64) ↦₆₄ 0#64) ∗
      ((g.statePtr + 0x120#64) ↦₃₂ g.spkId) ∗
      memRegion (g.statePtr + 0x124#64) 4 ∗
      stackAt (s0.sp - 144#64) (allocHookStack + 32) ∗
      cells (s0.sp - 144#64) 18 ∗
      A.pool
  onPanic := Pqxdh.Initiator.rustPanicOnOomPlaced

/-- Relocatable `[LibsignalPlacement]` `UNIX_EPOCH` specification for Block `33`, wrapped in `withLsCodeRoLoaded lsmpl`. -/
abbrev setUnackPreKeyMsgExactStackEpochSpecPlaced [LibsignalPlacement] (A : RustAlloc) :
    Spec Pqxdh.TopLevel.SetUnackExactGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (setUnackPreKeyMsgEpochInnerSpec A)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit Initiator.bv_sub_add_lit' BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
attribute [-arm64_norm]
  SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
  SpqrV1.Kdf.HkdfToSliceProof.read8_write64_264_271
  SpqrV1.Kdf.HkdfToSliceProof.read8_write64_408_415
  Memory.read8_write64_base_off_disjoint
  Memory.read64_write8_base_off_disjoint

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_lt_subs_neg1_1_true_epoch_placed :
    ConditionHolds CondCode.LT (subsPState64 0xffffffffffffffff#64 1#64) = true := by
  simp only [ConditionHolds, subsPState64]; decide

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_ite_zero64_epoch_placed (b : Bool) :
    (if b = true then 0#64 else 0#64) = 0#64 := by
  cases b <;> rfl

private theorem memRegion_16_split_64_epoch_placed (a : BitVec 64) :
    memRegion a 16 =
      (∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64, (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) := by
  rw [ProofLib.memRegion_split a 8 8 (by decide), ProofLib.memRegion_eight a,
    ProofLib.memRegion_eight (a + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

private theorem memRegion_24_split_64_epoch_placed (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2)) := by
  rw [ProofLib.memRegion_split a 8 16 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
    ProofLib.memRegion_eight (a + 8#64 + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]

private theorem pointsTo64_triple_entails_memRegion24_epoch_placed (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
  rw [memRegion_24_split_64_epoch_placed a]
  exact Entails.sepExists_right w2 (Entails.sepExists_right w1
    (Entails.sepExists_right w0 (Entails.refl _)))

private theorem memRegion_40_unack_split_epoch_placed (statePtr : BitVec 64) :
    memRegion (statePtr + 0x100#64) 40 =
      (∃∗ w100 : BitVec 64, (statePtr + 0x100#64) ↦₆₄ w100) ∗
      (∃∗ w108 : BitVec 64, (statePtr + 0x108#64) ↦₆₄ w108) ∗
      (∃∗ w110 : BitVec 32, (statePtr + 0x110#64) ↦₃₂ w110) ∗
      (∃∗ w114 : BitVec 32, (statePtr + 0x114#64) ↦₃₂ w114) ∗
      (∃∗ w118 : BitVec 64, (statePtr + 0x118#64) ↦₆₄ w118) ∗
      (∃∗ w120 : BitVec 32, (statePtr + 0x120#64) ↦₃₂ w120) ∗
      memRegion (statePtr + 0x124#64) 4 := by
  rw [ProofLib.memRegion_split (statePtr + 0x100#64) 8 32 (by decide),
    ProofLib.memRegion_split (statePtr + 0x100#64 + 8#64) 8 24 (by decide),
    ProofLib.memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64) 4 20 (by decide),
    ProofLib.memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64 + 4#64) 4 16 (by decide),
    ProofLib.memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64 + 4#64 + 4#64) 8 8 (by decide),
    ProofLib.memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64) 4 4
      (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_four, ProofLib.memRegion_four,
    ProofLib.memRegion_eight, ProofLib.memRegion_four]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_setUnack_call_epoch_placed (sp : BitVec 64) :
    stackAt (sp - 144#64) (allocHookStack + 32) =
      stackAt (sp - 176#64) allocHookStack ∗ cells (sp - 176#64) 4 := by
  have h1 := ProofLib.stackAt_split_cells (sp - 144#64) allocHookStack 4 (by decide)
  have h2 : sp - 144#64 - BitVec.ofNat 64 (8 * 4) = sp - 176#64 := by bv_arith
  rw [h2] at h1
  exact h1

private theorem stackAt_setUnack_hooks_epoch_placed (sp : BitVec 64) :
    stackAt (sp - 176#64) allocHookStack ∗ cells (sp - 176#64) 4 =
      memRegion (sp - 4272#64) 32 ∗ stackAt (sp - 144#64) allocHookStack := by
  rw [← stackAt_setUnack_call_epoch_placed sp]
  have h1 := Initiator.stackAt_split_top (sp - 144#64) 32 allocHookStack (by decide)
  have h2 : (32 + allocHookStack : Nat) = allocHookStack + 32 := by decide
  have h3 : BitVec.ofNat 64 (32 + allocHookStack) = 4128#64 := rfl
  have h4 : sp - 144#64 - 4128#64 = sp - 4272#64 := by bv_arith
  rw [h3, h4] at h1
  rw [← h2, h1]

private theorem pointsToBytes_entails_memRegion_33_epoch_placed (p : BitVec 64)
    (bs : List (BitVec 8)) (h : bs.length = 33) : (p ↦ₛ bs) ⊢ memRegion p 33 := by
  rw [← h]; exact ProofLib.pointsToBytes_entails_memRegion p bs

private theorem cells_pre_unfold_18_epoch_placed (sp : BitVec 64) :
    cells (sp - 144#64) 18 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64,
       ∃∗ c3 : BitVec 64, ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64,
       ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64, ∃∗ c8 : BitVec 64,
       ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
       ∃∗ c12 : BitVec 64, ∃∗ c13 : BitVec 64, ∃∗ c14 : BitVec 64,
       ∃∗ c15 : BitVec 64, ∃∗ c16 : BitVec 64, ∃∗ c17 : BitVec 64,
        ((sp - 144#64) ↦₆₄ c0) ∗ ((sp - 136#64) ↦₆₄ c1) ∗ ((sp - 128#64) ↦₆₄ c2) ∗
        ((sp - 120#64) ↦₆₄ c3) ∗ ((sp - 112#64) ↦₆₄ c4) ∗ ((sp - 104#64) ↦₆₄ c5) ∗
        ((sp - 96#64) ↦₆₄ c6) ∗ ((sp - 88#64) ↦₆₄ c7) ∗ ((sp - 80#64) ↦₆₄ c8) ∗
        ((sp - 72#64) ↦₆₄ c9) ∗ ((sp - 64#64) ↦₆₄ c10) ∗ ((sp - 56#64) ↦₆₄ c11) ∗
        ((sp - 48#64) ↦₆₄ c12) ∗ ((sp - 40#64) ↦₆₄ c13) ∗ ((sp - 32#64) ↦₆₄ c14) ∗
        ((sp - 24#64) ↦₆₄ c15) ∗ ((sp - 16#64) ↦₆₄ c16) ∗ ((sp - 8#64) ↦₆₄ c17)) := by
  cells_unfold

private theorem bytesToBv8_encodeEC_epoch_placed (bs : Initiator.Bytes) :
    Initiator.bytesToBv8 (Initiator.encodeEC bs) = 5#8 :: Initiator.bytesToBv8 bs := rfl

private theorem SepWPp.of_sepWP_lscl {prog : Program} {pl : Obj.MultiPlacement}
    {mid ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P
      (fun sm Pm => LibsignalCodeLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ (h : LibsignalCodeLoaded pl _) hkf => h.of_keepsFrozen hkf) hcl h

private theorem SepWPp.call_lscl {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (withLsCl pl spec))
    (hcl : LibsignalCodeLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      LibsignalCodeLoaded pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.call (x := x) (F := F) hcall hpc hrun hsp hlr ?_ hexit hpanic ?_
    (fun sf R' hoom_s hm => (hoom sf _ hoom_s hm).elim)
  · intro R hm
    dsimp only [withLsCl]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, hpre R hm⟩
  · intro sf hpcm hrunm hspm hcsm
    dsimp only [withLsCl]
    rw [sepConj_assoc]
    exact SepWPp.pure_elim (hnext sf hpcm hrunm hspm hcsm)

private theorem SepWPp.call_frame_lscl {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (withLsCl pl spec))
    (hcl : LibsignalCodeLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = ⌜φ⌝ ∗ T)
    (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      LibsignalCodeLoaded pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.call_lscl (x := x) (F := F) hcall hcl hpc hrun hsp hlr ?_ hexit hpanic hnext hoom
  intro R hm
  rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
  exact ⟨hφ, hm⟩

set_option maxRecDepth 200000 in
set_option maxHeartbeats 3200000 in
/-- Block `33` satisfies `withLsCodeLoaded lsmpl (setUnackPreKeyMsgEpochInnerSpec A)` under `[LibsignalPlacement]`. -/
theorem setUnackPreKeyMsg_exact_stack_epoch_placed_cl_ok [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hTime : HookSat H lsDurationSinceSym durationSinceEpochAllocSpec) :
    subroutine_ok ((blkPC_33).rebase (blkPl_33).base H) (blkPl_33).base
      (withLsCodeLoaded lsmpl (setUnackPreKeyMsgEpochInnerSpec A)) := by
  have hshim' : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsRustNoAllocShimSym) noAllocShimSpec := ls_hook_ok_of_mem hshim
  have halloc' : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsRustAllocSym) (rustAllocSpec A) := ls_hook_ok_of_mem halloc
  have hmemcpy' : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsMemcpySym) sessionMemcpyRegionSpec := ls_hook_ok_of_mem hmemcpy
  have htime' : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsDurationSinceSym) durationSinceEpochAllocSpec := ls_hook_ok_of_mem hTime
  have hdealloc' : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A) := ls_hook_ok_of_mem hdealloc
  have hpanic' : ((blkPC_33).rebase (blkPl_33).base H).externAt? (lsρ lsHandleErrorSym) =
      some Rust.panicked := (ls_externAt?_of_mem (sym := lsHandleErrorSym)).trans hpanic
  unfold withLsCodeLoaded setUnackPreKeyMsgEpochInnerSpec rustPanicOnOomPlaced
  wpp_init g s0
  obtain ⟨statePtr, optOpkTag, optOpkVal, spkId, baseKeyPtr, baseKeyBytes⟩ := g
  dsimp only at *
  have hser := ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_33).rebase (blkPl_33).base H)
    (ecPubKeySerializeRaw_placed_ok hshim halloc hpanic)
  change subroutine_ok _ (lsmpl.base 205) (withLsCl lsmpl (ecPubKeySerializeRawPlacedSpec A)) at hser
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hx5 : s0.readReg64 (.gpr 5#5) = 0#64 := ‹_›
  have hx6 : (s0.readReg64 (.gpr 6#5)).setWidth 32 = 0#32 := ‹_›
  have hx6_ext : (s0.readReg64 (.gpr 6#5)).extractLsb' 0 32 = 0#32 := by
    ext i hi
    have := congrArg (fun v => v[i]) hx6
    simpa using this
  have hlen_base : baseKeyBytes.length = 32 := ‹_›
  subst statePtr optOpkTag optOpkVal spkId baseKeyPtr
  have hlen_enc : (Initiator.bytesToBv8 (Initiator.encodeEC baseKeyBytes)).length = 33 := by
    rw [bytesToBv8_encodeEC_epoch_placed]; simp [Initiator.bytesToBv8, hlen_base]
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 33 1 := ⟨by decide, hpow2, by decide⟩
  rw [memRegion_40_unack_split_epoch_placed (s0.readReg64 (.gpr 0#5))]
  rw (occs := .pos [1]) [cells_pre_unfold_18_epoch_placed s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun c0 => SepWPp.exists_elim fun c1 => SepWPp.exists_elim fun c2 => ?_
  repeat (refine SepWPp.exists_elim fun _ => ?_)
  rw (occs := .pos [1]) [stackAt_setUnack_call_epoch_placed s0.sp]
  rw [pointsTo64_split32' (s0.sp - 128#64)]
  simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  apply SepWPp.of_sepWP_lscl hcl0 (mid := lsmpl.base 205)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  refine SepWPp.call_frame_lscl (x := (s0.readReg64 (.gpr 4#5), baseKeyBytes)) hser hcl1
    (by wp_norm_lhs) (by wp_norm_lhs)
    (by simp only [State.spAligned, arm64_norm, hsp_align])
    (ret_pc := (blkPl_33).base + 64#64) (by wp_norm_lhs)
    (by dsimp only [ecPubKeySerializeRawPlacedSpec]; simp only [arm64_norm, BitVec.sub_sub,
      BitVec.reduceAdd]; rfl)
    hlen_base
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sm _ hm => by
      dsimp only [ecPubKeySerializeRawPlacedSpec, rustPanicOnOomPlaced] at hm
      rw [← sepConj_assoc]
      exact allowPanic_frame (by simp only [allocFailedIn, arm64_norm]; exact id) hm)
    (fun sm hpcm hrunm hspm hcsm _hclm => ?_)
  simp only [arm64_norm] at hspm
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm
  rcases hcsm with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hcs29⟩
  simp only [arm64_norm] at hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29
  clear hpre
  dsimp only [ecPubKeySerializeRawPlacedSpec]
  simp only [arm64_norm, BitVec.sub_sub, BitVec.reduceAdd,
    sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun slicePtr => ?_
  refine SepWPp.pure_left fun ⟨htr_sm, hx0_sm, hx1_sm, hne_slice⟩ => ?_
  apply SepWPp.of_sepWP (mid := (blkPl_33).base + 116#64)
  apply Initiator.SepWP.replace_pre (by sep_focus) (Entails.of_eq
    (stackAt_setUnack_hooks_epoch_placed s0.sp))
  wp_steps
  wp_call hshim' ()
  wp_steps
  wp_call halloc' (33, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true]
    refine Initiator.sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic') fun hm =>
      ⟨Initiator.allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm]; rw [htrace,
        ‹sf.trace = sm.trace›, htr_sm]),
        Arm64.Satisfies.mono (sepConj_mono_left (ent_anyHeap _)) hm⟩
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine Initiator.sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    rw [← hlen_enc]
    wp_call hmemcpy' (sf_1.readReg64 (Reg.gpr 0#5), slicePtr,
      Initiator.bytesToBv8 (Initiator.encodeEC baseKeyBytes))
    wp_steps
    have h136_eq : s0.sp - 136#64 + 8#64 = s0.sp - 128#64 := by bv_arith
    have h136_12 : s0.sp - 136#64 + 12#64 = s0.sp - 124#64 := by bv_arith
    have h120_8 : s0.sp - 120#64 + 8#64 = s0.sp - 112#64 := by bv_arith
    have h120_16 : s0.sp - 120#64 + 16#64 = s0.sp - 104#64 := by bv_arith
    have h124_ent : ∀ v, ((s0.sp - 124#64) ↦₃₂ v) ⊢ memRegion (s0.sp - 136#64 + 12#64) 4 := by
      intro v; rw [h136_12]; exact pointsTo32_entails_memRegion (s0.sp - 124#64) v
    rw [← h136_eq]
    apply Initiator.SepWP.replace_pre (by sep_focus) (h124_ent _)
    apply Initiator.SepWP.replace_pre (by sep_focus)
      (h120_8 ▸ h120_16 ▸ pointsTo64_triple_entails_memRegion24_epoch_placed (s0.sp - 120#64) _ _ _)
    have hsp2 : sf_2.sp = s0.sp - 144#64 := by rw [‹sf_2.sp = sf_1.sp›, ‹sf_1.sp =
      sf.sp›, ‹sf.sp = sm.sp›, hspm]
    rw [‹sf.sp = sm.sp›, hspm]
    wp_call htime' (s0.sp - 136#64, s0.sp - 120#64)
    rw [hsp2]
    rw [memRegion_16_split_64_epoch_placed (s0.sp - 136#64), h136_eq]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    wp_pull_exists
    wp_steps
    apply Initiator.SepWP.replace_pre (by sep_focus)
      (pointsToBytes_entails_memRegion_33_epoch_placed slicePtr _ hlen_enc)
    rw [← hsp2, ← ‹sf_3.sp = sf_2.sp›]
    wp_call hdealloc' (slicePtr, 33, 1)
    wp_steps
    simp only [ite_self, *] at *
    apply Initiator.SepWP.replace_pre (by sep_focus)
      (Entails.of_eq ((stackAt_setUnack_call_epoch_placed s0.sp).trans
        (stackAt_setUnack_hooks_epoch_placed s0.sp)).symm)
    dsimp only [Initiator.vecU8]
    rw [cells_pre_unfold_18_epoch_placed s0.sp]
    wp_done

theorem setUnackPreKeyMsg_exact_stack_epoch_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hTime : HookSat H lsDurationSinceSym durationSinceEpochAllocSpec) :
    subroutine_ok ((blkPC_33).rebase (blkPl_33).base H) (blkPl_33).base
      (setUnackPreKeyMsgExactStackEpochSpecPlaced A) :=
  LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (setUnackPreKeyMsg_exact_stack_epoch_placed_cl_ok hshim halloc hdealloc hmemcpy hpanic hTime)

/-- Transfers `setUnackPreKeyMsg_exact_stack_epoch_placed_ok` to any caller block `i < 619`. -/
theorem setUnackPreKeyMsg_exact_stack_epoch_placed_at_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {A : RustAlloc} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hTime : HookSat H lsDurationSinceSym durationSinceEpochAllocSpec)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_33).base
      (setUnackPreKeyMsgExactStackEpochSpecPlaced A) := by
  have hrocl := @ls_subroutine_ok_rocl_of_block _ _ callerProg
    ((blkPC_33).rebase (blkPl_33).base H) i 33 H
    hcaller (instIsLsBlockProg_33 H) (blkPl_33).base _
    (setUnackPreKeyMsg_exact_stack_epoch_placed_ok hshim halloc hdealloc hmemcpy hpanic hTime)
    _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_
  intro x R s0 sf hpost
  dsimp only [withLsRoCl] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

theorem setUnackPreKeyMsg_exact_stack_epoch_placed_ok_cli [LibsignalPlacement]
    {callerProg : Program} {i : Nat} (mmpl : Obj.MultiPlacement)
    (g : CryptoVerification.SignalSession.Cli.RunGlue.CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg callerProg i
      (CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hshim : HookSat
      (CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W))
      lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat
      (CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W))
      lsRustAllocSym (rustAllocSpec E2E.HooksE.A0))
    (hdealloc : HookSat
      (CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W))
      lsRustDeallocSym (rustDeallocSpec E2E.HooksE.A0))
    (hmemcpy : HookSat
      (CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W))
      lsMemcpySym sessionMemcpyRegionSpec)
    (hpanic :
      CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W)
        lsHandleErrorSym = some Rust.panicked)
    (hTime : HookSat
      (CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns g (cliExternsPlaced mmpl W))
      lsDurationSinceSym durationSinceEpochAllocSpec)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_33).base
      (setUnackPreKeyMsgExactStackEpochSpecPlaced E2E.HooksE.A0) :=
  setUnackPreKeyMsg_exact_stack_epoch_placed_at_block hshim halloc hdealloc hmemcpy hpanic hTime hi

end CryptoVerification.SignalSession.Cli.Slots
