/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBob
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.ResponderCoreCodeSym
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp

/-!
# Relocatable `initialize_bob_session` (Block `75`): Specifications and Session-Build Tail

Specifications, `SepWPp` framing combinators, 344-byte `SessionState` layout predicates, and
post-`spqr::initial_state` session-build proofs (`+252 → +564 → RET`) for unmutated Block `75`
under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.E2E.Pqxdh.ResponderCore

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.Initiator

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

@[local arm64_norm ↓, local wp_norm ↓]
private theorem calleeSavedVRegs_setPC_pre_bob_placed (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem calleeSavedVRegs_setMem_setPC_pre_bob_placed (s : State) (pc : BitVec 64)
    (m : Memory) :
    calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem calleeSavedVRegs_writeVReg128_0_bob_placed (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 0#5 v) = calleeSavedVRegs s := rfl

private theorem bv_add_sub_lit_bob_placed (x a b : BitVec 64) :
    (x + a) - b = x + (a - b) := by bv_omega

@[local arm64_norm, local wp_norm]
private theorem bv_sub_add_lit_bob_placed (x a b : BitVec 64) :
    (x - a) + b = x - (a - b) := Initiator.bv_sub_add_lit' x a b

@[local simp, local arm64_norm, local wp_norm]
private theorem cond_ne_subs64_0_1_bob_placed :
    ConditionHolds CondCode.NE (subsPState64 0#64 1#64) = true := by
  simp only [ConditionHolds, subsPState64]; decide

/-! ## `SepWPp` Framing Combinators -/

/-- Call a `withLsCodeRoLoaded pl spec` subroutine inside a `SepWPp` proof while preserving
`Keys.LsFrozenInv pl` across the call. -/
theorem SepWPp.call_lscro_frame {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : Keys.LsFrozenInv pl s)
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      Keys.LsFrozenInv pl sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro sf; first | rfl | simp only [withLsCodeRoLoaded]) :
    SepWPp prog ret s P Q Qp := by
  have hcall' : subroutine_ok prog entry
      { withLsCodeRoLoaded pl spec with
        pre := fun x' s0' => ⌜Keys.LsFrozenInv pl s0'⌝ ∗ spec.pre x' s0'
        post := fun x' s0' sf => ⌜Keys.LsFrozenInv pl sf⌝ ∗ spec.post x' s0' sf } := by
    refine Arm64.subroutine_ok.of_codeLoaded fun x' R s0' hpc0 hrun0 hpre0 hsp0 hL0 => ?_
    dsimp only at hpre0
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
    rcases hpre0 with ⟨hF0, hm0⟩
    have hm0' : s0'.mem ⊨ (withLsCodeRoLoaded pl spec).pre x' s0' ∗ R := by
      dsimp only [withLsCodeRoLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨⟨hF0.1, hF0.2⟩, hm0⟩
    obtain ⟨sf, hsteps, hout, -⟩ := hcall.no_fault_before_outcome x' R s0' hpc0 hrun0 hm0' hsp0 hL0
    refine Arm64.reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
    rcases hout with ⟨hret, hcc, hpost⟩ | hrest
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withLsCodeRoLoaded] at hpost ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hF0.of_keepsFrozen hsteps.keepsFrozen, hpost⟩
    · exact Or.inr hrest
  refine SepWPp.call (x := x) (F := F) hcall' hpc hrun hsp hlr ?_
    (fun sm code R' hex hpost => by
      dsimp only [withLsCodeRoLoaded] at hpost
      exact hexit sm code R' hex hpost)
    (fun sm hpan => by
      dsimp only [withLsCodeRoLoaded]
      exact hpanic sm hpan)
    (fun sm hpcm hrunm hspm hcsm => by
      have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
      dsimp only
      rw [sepConj_assoc]
      exact SepWPp.pure_elim (hnext sm hpcm hrunm hspm hsp_alm hcsm))
    (fun sm R' _ hoom_post => by
      dsimp only [withLsCodeRoLoaded] at hoom_post
      rw [hoom sm] at hoom_post
      exact (not_satisfies_false_sepConj hoom_post).elim)
  intro R hm
  dsimp only
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hF, ?_⟩
  rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
  exact ⟨hφ, hm⟩

private def withLsClBob {α : Type} (pl : Obj.MultiPlacement) (spec : Spec α) : Spec α :=
  { spec with
    pre := fun x s0 => spec.pre x s0 ∗ ⌜LibsignalCodeLoaded pl s0.mem⌝
    post := fun x s0 sf => ⌜LibsignalCodeLoaded pl sf.mem⌝ ∗ spec.post x s0 sf }

private theorem ls_subroutine_ok_cl_of_block_bob [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec))
    (_hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsClBob lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hcl0, _⟩ := extract_withLsCodeLoaded hpre
  have hQL : calleeProg.CodeLoaded s0.mem :=
    hcallee_prog.eq_blockProgram ▸ hcl0 j (Nat.lt_of_lt_of_le hj (by decide)) hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hclf : LibsignalCodeLoaded lsmpl sf.mem := hcl0.of_keepsFrozen hstepsQ.keepsFrozen
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  refine reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsClBob]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hclf, hpost⟩
  · exact Or.inr hrest

private theorem ls_subroutine_ok_cl_of_plain_bob [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry spec)
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsClBob lsmpl spec) :=
  ls_subroutine_ok_cl_of_block_bob (callerProg := callerProg)
    (subroutine_ok_withLsCodeLoaded_of_plain hcallee) hi hj hj_unmut

private theorem SepWPp.of_sepWP_lscl_bob {prog : Program} {pl : Obj.MultiPlacement}
    {mid ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P
      (fun sm Pm => LibsignalCodeLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ (h : LibsignalCodeLoaded pl _) hkf => h.of_keepsFrozen hkf) hcl h

private theorem SepWPp.call_frame_lscl_bob {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (withLsClBob pl spec))
    (hcl : LibsignalCodeLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = ⌜φ⌝ ∗ T)
    (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      LibsignalCodeLoaded pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.call (x := x) (F := F) hcall hpc hrun hsp hlr ?_ hexit hpanic ?_
    (fun sf R' hoom_s hm => (hoom sf _ hoom_s hm).elim)
  · intro R hm
    dsimp only [withLsClBob]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  · intro sf hpcm hrunm hspm hcsm
    dsimp only [withLsClBob]
    rw [sepConj_assoc]
    exact SepWPp.pure_elim (hnext sf hpcm hrunm hspm hcsm)

attribute [local irreducible] withLsClBob

/-! ## Relocatable `[LibsignalPlacement]` Specifications -/

/-- Relocatable inner contract for `Pqxdh::accept` (Block `79`), stated using only
`[LibsignalPlacement]` (`lsLogFilterAddr`) so callers in unmutated Block `75` can take a
`subroutine_ok` hypothesis at `lsmpl.base 79` without requiring `[LibsignalFullPlacement]`. -/
def pqxdhAcceptOptFieldsInnerPlacedSpec [LibsignalPlacement] (P : Primitives) (A : RustAlloc) :
    Spec AcceptFieldsCallGhost where
  pre := fun (g : AcceptFieldsCallGhost) s =>
    ⌜s.readReg64 .x0 = g.argPtr ∧ s.readReg64 .x8 = g.outPtr ∧ g.inp.trustedPeer = true ∧
      g.inp.replayOk = true ∧ g.inp.hdr.opkId?.isSome = g.inp.opkBSk?.isSome ∧
      WellSizedAcceptKeysInput g.inp⌝ ∗
      pqxdhAcceptOptFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.inp ∗
      memRegion g.outPtr 104 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s.sp pqxdhEntryStack ∗
      A.pool
  post := fun (g : AcceptFieldsCallGhost) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      pqxdhAcceptOptFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.inp ∗
      (match Model.acceptKeys P g.inp with
       | some drKey =>
         g.outPtr ↦ₛ bytesToBv8 (handshakeKeysResultOk104 drKey)
       | none =>
         pqxdhAcceptErrStrong2At g.outPtr ∗ anyHeap) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      stackAt s0.sp pqxdhEntryStack ∗ A.pool
  onPanic := rustPanicOnOomPlaced

def pqxdhAcceptOptFieldsPlacedSpec [LibsignalPlacement] (P : Primitives) (A : RustAlloc) :
    Spec AcceptFieldsCallGhost :=
  withLsCodeRoLoaded lsmpl (pqxdhAcceptOptFieldsInnerPlacedSpec P A)

/-- Relocatable inner contract for `initialize_bob_session` (Block `75`). -/
def initializeBobSessionInnerPlacedSpec [LibsignalPlacement] (P : Primitives) (A : RustAlloc) :
    Spec InitBobCallGhost where
  pre := fun (g : InitBobCallGhost) s =>
    ⌜s.readReg64 .x0 = g.argPtr ∧
      s.readReg64 .x1 = g.ratchetKeyPairPtr ∧
      s.readReg64 .x8 = g.outPtr ∧
      g.inp.trustedPeer = true ∧
      g.inp.replayOk = true ∧
      g.inp.hdr.opkId?.isSome = g.inp.opkBSk?.isSome ∧
      WellSizedAcceptKeysInput g.inp ∧
      g.ikBPk.length = 32 ∧
      g.spkBPk.length = 32⌝ ∗
    bobParamsFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
      g.inp g.ikBPk g.spkBPk g.sameAccountByte ∗
    memRegion g.outPtr 344 ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗
    stackAt s.sp (768 + pqxdhEntryStack) ∗
    A.pool
  post := fun (g : InitBobCallGhost) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    bobParamsFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.ratchetKeyPairPtr
      g.inp g.ikBPk g.spkBPk g.sameAccountByte ∗
    (match Model.acceptKeys P g.inp with
     | some drKey =>
       ∃∗ localIkBoxPtr : BitVec 64,
       ∃∗ remoteIkBoxPtr : BitVec 64,
       ∃∗ rootKeyBoxPtr : BitVec 64,
       ∃∗ baseKeyBoxPtr : BitVec 64,
       ∃∗ ratchetPubBoxPtr : BitVec 64,
       ∃∗ ratchetPrivBoxPtr : BitVec 64,
       ∃∗ chainKeyBoxPtr : BitVec 64,
       ∃∗ pad_f4 : BitVec 32,
       ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64,
       ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64,
         ⌜localIkBoxPtr ≠ 0 ∧ remoteIkBoxPtr ≠ 0 ∧ rootKeyBoxPtr ≠ 0 ∧ baseKeyBoxPtr ≠ 0 ∧
           ratchetPubBoxPtr ≠ 0 ∧ ratchetPrivBoxPtr ≠ 0 ∧ chainKeyBoxPtr ≠ 0⌝ ∗
         (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC g.ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
         (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC g.inp.hdr.ikAPk)) ∗
         A.live remoteIkBoxPtr 33 1 ∗
         (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
         (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC g.inp.hdr.ekAPk)) ∗
         A.live baseKeyBoxPtr 33 1 ∗
         (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC g.spkBPk)) ∗ A.live ratchetPubBoxPtr 33 1 ∗
         (ratchetPrivBoxPtr ↦ₛ bytesToBv8 g.inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
         (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
         (g.outPtr ↦ₛ bobSession344Bv8 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
           0#64 1#64 ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
           pad_f4 c0 c1 c2 c3 c4 d0 d1 d2)
     | none =>
       initBobErrAt g.outPtr ∗
       anyHeap) ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗
    stackAt s0.sp (768 + pqxdhEntryStack) ∗
    A.pool
  onPanic := rustPanicOnOomPlaced

def initializeBobSessionPlacedSpec [LibsignalPlacement] (P : Primitives) (A : RustAlloc) :
    Spec InitBobCallGhost :=
  withLsCodeRoLoaded lsmpl (initializeBobSessionInnerPlacedSpec P A)

/-! ## SPQR-V1 Session Layout and Frame Predicates -/

/-- `bobHead144Bv8` with general SPQR `Vec<u8>` length `spqrLen` at `+0x88`. -/
def bobHead144Bv8V1 (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
    spqrCap spqrBufPtr spqrLen : BitVec 64) : List (BitVec 8) :=
  unpack64 33#64 ++ unpack64 localIkBoxPtr ++ unpack64 33#64 ++
  unpack64 33#64 ++ unpack64 remoteIkBoxPtr ++ unpack64 33#64 ++
  unpack64 32#64 ++ unpack64 rootKeyBoxPtr ++ unpack64 32#64 ++
  unpack64 0#64 ++ unpack64 8#64 ++ unpack64 0#64 ++
  unpack64 33#64 ++ unpack64 baseKeyBoxPtr ++ unpack64 33#64 ++
  unpack64 spqrCap ++ unpack64 spqrBufPtr ++ unpack64 spqrLen

@[local simp]
theorem bobHead144Bv8V1_length (p1 p2 p3 p4 c5 p5 l5 : BitVec 64) :
    (bobHead144Bv8V1 p1 p2 p3 p4 c5 p5 l5).length = 144 := by
  simp [bobHead144Bv8V1]

theorem bobHead144Bv8_eq_V1 (p1 p2 p3 p4 c5 p5 : BitVec 64) :
    bobHead144Bv8 p1 p2 p3 p4 c5 p5 = bobHead144Bv8V1 p1 p2 p3 p4 c5 p5 0#64 := rfl

theorem bobHead144V1_eq_pointsToBytes (ptr p1 p2 p3 p4 c5 p5 l5 : BitVec 64) :
    (ptr ↦₆₄ 33#64) ∗
    ((ptr + 0x08#64) ↦₆₄ p1) ∗
    ((ptr + 0x10#64) ↦₆₄ 33#64) ∗
    ((ptr + 0x18#64) ↦₆₄ 33#64) ∗
    ((ptr + 0x20#64) ↦₆₄ p2) ∗
    ((ptr + 0x28#64) ↦₆₄ 33#64) ∗
    ((ptr + 0x30#64) ↦₆₄ 32#64) ∗
    ((ptr + 0x38#64) ↦₆₄ p3) ∗
    ((ptr + 0x40#64) ↦₆₄ 32#64) ∗
    ((ptr + 0x48#64) ↦₆₄ 0#64) ∗
    ((ptr + 0x50#64) ↦₆₄ 8#64) ∗
    ((ptr + 0x58#64) ↦₆₄ 0#64) ∗
    ((ptr + 0x60#64) ↦₆₄ 33#64) ∗
    ((ptr + 0x68#64) ↦₆₄ p4) ∗
    ((ptr + 0x70#64) ↦₆₄ 33#64) ∗
    ((ptr + 0x78#64) ↦₆₄ c5) ∗
    ((ptr + 0x80#64) ↦₆₄ p5) ∗
    ((ptr + 0x88#64) ↦₆₄ l5) =
      (ptr ↦ₛ bobHead144Bv8V1 p1 p2 p3 p4 c5 p5 l5) := by
  unfold bobHead144Bv8V1
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length,
    BitVec.add_assoc, BitVec.reduceAdd, ← pointsTo64_eq_pointsToBytes]

/-- 344-byte `SessionState` built by `initialize_bob_session` with SPQR `Vec<u8>` header
`(spqrCap, spqrBufPtr, spqrLen)` at `+0x78`. -/
def bobSession344Bv8V1 (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
    spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) : List (BitVec 8) :=
  bobHead144Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
    spqrLen ++
  senderChainBytes100 ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr 0#32 ++ unpack32 pad_f4 ++
  bobTail96Bv8 c0 c1 c2 c3 c4 d0 d1 d2

@[local simp]
theorem bobSession344Bv8V1_length (p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) :
    (bobSession344Bv8V1 p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2).length =
      344 := by
  simp [bobSession344Bv8V1]

theorem bobSession344Bv8_eq_V1 (p1 p2 p3 p4 c5 p5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) :
    bobSession344Bv8 p1 p2 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 =
      bobSession344Bv8V1 p1 p2 p3 p4 c5 p5 0#64 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 := rfl

theorem bobSession344V1_pack (ptr localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
    spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) :
    (ptr ↦ₛ bobHead144Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap
      spqrBufPtr spqrLen) ∗
    senderChainFieldsAt ptr ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr 0#32 ∗
    ((ptr + 0xf4#64) ↦ₛ (unpack32 pad_f4 ++ bobTail96Bv8 c0 c1 c2 c3 c4 d0 d1 d2)) =
      (ptr ↦ₛ bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap
        spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
        pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) := by
  unfold bobSession344Bv8V1
  rw [senderChainFieldsAt_eq_pointsToBytes]
  simp only [List.append_assoc, pointsToBytes_append, bobHead144Bv8V1_length,
    senderChainBytes100_length, BitVec.add_assoc, BitVec.reduceAdd]

/-- Twelve callee-saved words stored by `initialize_bob_session`'s prologue at `sp0 - 96`. -/
def initBobSavedRegs (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 96#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗ ((sp0 - 88#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
  ((sp0 - 80#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗ ((sp0 - 72#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
  ((sp0 - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗ ((sp0 - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗ ((sp0 - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗ ((sp0 - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗ ((sp0 - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))

theorem initBobSavedRegs_entails_memRegion96 (sp0 : BitVec 64) (s0 : State) :
    initBobSavedRegs sp0 s0 ⊢ memRegion (sp0 - 96#64) 96 := by
  rw [(ProofLib.memRegion_cells (sp0 - 96#64) 12 (by decide) :
    memRegion (sp0 - 96#64) 96 = cells (sp0 - 96#64) 12)]
  exact cells12_sub96_merge sp0 _ _ _ _ _ _ _ _ _ _ _ _

/-- Cells of `initialize_bob_session`'s frame at `spqr::initial_state`'s entry outside
`bobSpqrCutCells`, `initBobSavedRegs`, and `stackAt (sp0 - 768) pqxdhEntryStack`. -/
def bobFrameAtSpqr (sp0 : BitVec 64) (rk pq ck : Bytes) : SepProp :=
  ((sp0 - 768#64) ↦ₛ bytesToBv8 rk) ∗ ((sp0 - 736#64) ↦ₛ bytesToBv8 pq) ∗
  ((sp0 - 704#64) ↦ₛ bytesToBv8 ck) ∗ ((sp0 - 672#64) ↦₃₂ 0#32) ∗
  memRegion (sp0 - 668#64) 12 ∗ ((sp0 - 592#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 588#64) 12 ∗
  memRegion (sp0 - 544#64) 56 ∗
  ((sp0 - 452#64) ↦ₛ bytesToBv8 pq) ∗ ((sp0 - 420#64) ↦ₛ bytesToBv8 ck) ∗
  ((sp0 - 388#64) ↦₃₂ 0#32) ∗ memRegion (sp0 - 384#64) 288

private theorem sub488_split_v1 (sp : BitVec 64) :
    memRegion (sp - 488#64) 344 =
      cells (sp - 488#64) 19 ∗
      memRegion (sp - 336#64) 92 ∗
      (∃∗ pad_f4 : BitVec 32, (sp - 244#64) ↦₃₂ pad_f4) ∗
      memRegion (sp - 240#64) 96 := by
  rw [ProofLib.memRegion_split' (b := sp - 488#64) (n := 152) (k := 192)
      (b' := sp - 336#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 336#64) (n := 92) (k := 100)
      (b' := sp - 244#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 244#64) (n := 4) (k := 96)
      (b' := sp - 240#64) rfl (by bv_omega) (by decide),
    (ProofLib.memRegion_cells (sp - 488#64) 19 (by decide) :
      memRegion (sp - 488#64) 152 = cells (sp - 488#64) 19),
    ProofLib.memRegion_four (sp - 244#64)]

/-! ## Post-`spqr::initial_state` Code Proofs (`+252 → +564 → RET`) -/

set_option maxHeartbeats 800000 in
/-- Relocatable epilogue (`(blkPl_75).base + 564#64 → RET`) of `initialize_bob_session`
(Block `75`) under `[LibsignalPlacement]`. -/
theorem initBob_epilogue_placed [LibsignalPlacement] {H : LibsignalHooks}
    (s0 s : State) (Frame : SepProp)
    (hsp0_align : s0.sp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_75).base + 564#64)
    (hsp : s.sp = s0.sp - 768#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (lsProg_75 H) (s0.readReg64 (.gpr 30#5)) s
      (initBobSavedRegs s0.sp s0 ∗ Frame)
      (fun sf Pf =>
        (Pf ⊢ memRegion (s0.sp - 96#64) 96 ∗ Frame) ∧ sf.status = ExecStatus.Running ∧
        sf.pc = s0.readReg64 (.gpr 30#5) ∧ sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧ sf.trace = s.trace) := by
  have hs0 : s0.sp = s.sp + 768#64 := by rw [hsp]; bv_omega
  have hal : s.sp &&& 15#64 == 0#64 := by rw [hsp]; revert hsp0_align; bv_bits
  have hfold := initBobSavedRegs_entails_memRegion96 (s.sp + 768#64) s0
  dsimp only [initBobSavedRegs] at hfold ⊢
  simp only [bv_add_sub_lit_bob_placed, BitVec.reduceSub] at hfold
  rw [hs0]
  clear hsp hsp0_align hs0
  simp only [bv_add_sub_lit_bob_placed, BitVec.reduceSub, sepConj_assoc]
  wp_steps
  refine SepWP.fold hfold (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
     by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
     by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by simp only [arm64_norm, *]⟩,
    by wp_norm_goal⟩

def BobPlacedPanicOom (s0 sf : State) (Pf : SepProp) : Prop :=
  ∀ R : SepProp, (sf.mem ⊨ Pf ∗ R) →
    (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)

set_option maxHeartbeats 2400000 in
/-- Relocatable session-build segment (`(blkPl_75).base + 252#64 → (blkPl_75).base + 564#64`) of
`initialize_bob_session` (Block `75`) under `[LibsignalPlacement]`, from `spqr::initial_state`'s
`Ok((spqrCap, spqrBufPtr, spqrLen))` return to the epilogue. -/
theorem initBob_session_build_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (s0 s : State) (argPtr rkp outPtr : BitVec 64)
    (spqrCap spqrBufPtr spqrLen : BitVec 64)
    (ikBPk ikAPk ekAPk spkBPk spkBSk rk ck : Bytes)
    (Frame : SepProp)
    (hcl0 : LibsignalCodeLoaded lsmpl s.mem)
    (hikB_len : ikBPk.length = 32)
    (hikA_len : ikAPk.length = 32)
    (hekA_len : ekAPk.length = 32)
    (hspkPk_len : spkBPk.length = 32)
    (hspkSk_len : spkBSk.length = 32)
    (hrk_len : rk.length = 32)
    (hck_len : ck.length = 32)
    (hsp0_align : s0.sp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_75).base + 252#64)
    (hsp : s.sp = s0.sp - 768#64)
    (hx19 : s.readReg64 (.gpr 19#5) = outPtr)
    (hx20 : s.readReg64 (.gpr 20#5) = rkp)
    (hx21 : s.readReg64 (.gpr 21#5) = argPtr)
    (hx23 : s.readReg64 (.gpr 23#5) = s0.sp - 768#64)
    (hx27 : s.readReg64 (.gpr 27#5) = s0.sp - 488#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_75 H) ((blkPl_75).base + 564#64) s
      (((s0.sp - 768#64) ↦₆₄ 0#64) ∗ ((s0.sp - 760#64) ↦₆₄ spqrCap) ∗
       ((s0.sp - 752#64) ↦₆₄ spqrBufPtr) ∗ ((s0.sp - 744#64) ↦₆₄ spqrLen) ∗
       ((s0.sp - 656#64) ↦ₛ bytesToBv8 rk) ∗ ((s0.sp - 624#64) ↦ₛ bytesToBv8 ck) ∗
       ((s0.sp - 592#64) ↦₃₂ 0#32) ∗
       memRegion (s0.sp - 488#64) 344 ∗
       (argPtr ↦ₛ bytesToBv8 ikBPk) ∗ ((argPtr + 128#64) ↦ₛ bytesToBv8 ikAPk) ∗
       ((argPtr + 160#64) ↦ₛ bytesToBv8 ekAPk) ∗
       (rkp ↦ₛ bytesToBv8 spkBPk) ∗ ((rkp + 32#64) ↦ₛ bytesToBv8 spkBSk) ∗
       memRegion outPtr 344 ∗
       stackAt (s0.sp - 768#64) pqxdhEntryStack ∗ A.pool ∗ Frame)
      (fun sf P_f =>
        ∃ (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
           ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
          (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64),
          localIkBoxPtr ≠ 0#64 ∧ remoteIkBoxPtr ≠ 0#64 ∧ rootKeyBoxPtr ≠ 0#64 ∧
          baseKeyBoxPtr ≠ 0#64 ∧ ratchetPubBoxPtr ≠ 0#64 ∧ ratchetPrivBoxPtr ≠ 0#64 ∧
          chainKeyBoxPtr ≠ 0#64 ∧ (P_f ⊢
            (outPtr ↦ₛ bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
              spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
              pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
            memRegion (s0.sp - 768#64) 32 ∗
            ((s0.sp - 656#64) ↦ₛ bytesToBv8 rk) ∗ ((s0.sp - 624#64) ↦ₛ bytesToBv8 ck) ∗
            ((s0.sp - 592#64) ↦₃₂ 0#32) ∗
            memRegion (s0.sp - 488#64) 344 ∗
            (argPtr ↦ₛ bytesToBv8 ikBPk) ∗ ((argPtr + 128#64) ↦ₛ bytesToBv8 ikAPk) ∗
            ((argPtr + 160#64) ↦ₛ bytesToBv8 ekAPk) ∗
            (rkp ↦ₛ bytesToBv8 spkBPk) ∗ ((rkp + 32#64) ↦ₛ bytesToBv8 spkBSk) ∗
            (localIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
            (remoteIkBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ikAPk)) ∗ A.live remoteIkBoxPtr 33 1 ∗
            (rootKeyBoxPtr ↦ₛ bytesToBv8 rk) ∗ A.live rootKeyBoxPtr 32 1 ∗
            (baseKeyBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC ekAPk)) ∗ A.live baseKeyBoxPtr 33 1 ∗
            (ratchetPubBoxPtr ↦ₛ bytesToBv8 (Model.encodeEC spkBPk)) ∗
            A.live ratchetPubBoxPtr 33 1 ∗
            (ratchetPrivBoxPtr ↦ₛ bytesToBv8 spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
            (chainKeyBoxPtr ↦ₛ bytesToBv8 ck) ∗ A.live chainKeyBoxPtr 32 1 ∗
            stackAt (s0.sp - 768#64) pqxdhEntryStack ∗ A.pool ∗ Frame) ∧
          LibsignalCodeLoaded lsmpl sf.mem ∧
          sf.status = ExecStatus.Running ∧
          sf.pc = (blkPl_75).base + 564#64 ∧
          sf.sp = s0.sp - 768#64 ∧ sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0)
      (BobPlacedPanicOom s0) := by
  have hsp_align : s.spAligned = true := by
    simp only [State.spAligned, hsp]
    revert hsp0_align; bv_bits
  have hserPub := ls_subroutine_ok_cl_of_plain_bob (callerProg := lsProg_75 H)
    (ecPubKeySerialize_alloc_placed_ok hshim halloc hpanic)
  change subroutine_ok _ (lsmpl.base 205) (withLsClBob lsmpl (ecPubKeySerializeAllocPlacedSpec A))
    at hserPub
  have hwithSender := ls_subroutine_ok_cl_of_block_bob (callerProg := lsProg_75 H)
    (withSenderChain_none_placed_ok hshim halloc hdealloc hmemcpy hpanic)
  change subroutine_ok _ (lsmpl.base 27) (withLsClBob lsmpl (withSenderChainNonePlacedSpec A))
    at hwithSender
  have hshim' : subroutine_ok (lsProg_75 H) (lsρ lsRustNoAllocShimSym) noAllocShimSpec :=
    ls_hook_ok_of_mem hshim
  have halloc' : subroutine_ok (lsProg_75 H) (lsρ lsRustAllocSym) (rustAllocSpec A) :=
    ls_hook_ok_of_mem halloc
  have hpan_rawvec : (lsProg_75 H).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked :=
    (ls_externAt?_of_mem (sym := lsHandleErrorSym)).trans hpanic
  obtain ⟨rk0, rk1, rk2, rk3, _, hrk_cells⟩ :=
    exists_unpack64_of_length_32 (bs := bytesToBv8 rk) (by simp [bytesToBv8, hrk_len])
  conv =>
    arg 4
    rw [hrk_cells (s0.sp - 656#64), stackAt_entry_some_split (s0.sp - 768#64)]
    simp (config := { maxSteps := 1000000 }) only [
      Initiator.bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  apply SepWPp.of_sepWP_lscl_bob hcl0 (mid := lsmpl.base 205)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  refine SepWPp.call_frame_lscl_bob (x := (argPtr, ikBPk)) hserPub hcl1
    (by wp_norm_lhs) (by wp_norm_lhs)
    (by simp only [*, State.spAligned, arm64_norm])
    (ret_pc := (blkPl_75).base + 400#64) (by wp_norm_lhs)
    (by
      conv =>
        lhs
        dsimp only [ecPubKeySerializeAllocPlacedSpec]
        simp only [arm64_norm, hsp, Initiator.bv_sub_add_lit', BitVec.reduceSub])
    hikB_len
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sm _ R hm => by
      dsimp only [ecPubKeySerializeAllocPlacedSpec, rustPanicOnOomPlaced] at hm
      simpa only [sepConj_assoc] using
        allowPanic_frame (fun h =>
          allocFailedIn_of_trace_eq (s0 := s0)
            (by simp only [*, arm64_norm]) h) hm)
    (fun sm1 hpcm1 hrunm1 hspm1 hcsm1 hclm1 => ?_)
  simp only [*, arm64_norm] at hspm1
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm1
  rcases hcsm1 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
    hcs2_27, hcs2_28, hcs2_29, hcs2_vregs⟩
  simp only [*, arm64_norm]
    at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28 hcs2_29
       hcs2_vregs
  conv =>
    arg 4
    dsimp only [ecPubKeySerializeAllocPlacedSpec]
    simp only [arm64_norm, hsp, Initiator.bv_sub_add_lit', BitVec.reduceSub,
      sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun localIkBoxPtr => ?_
  refine SepWPp.pure_left fun ⟨htr2, hx0_1, hx1_1, hne_localIk⟩ => ?_
  apply SepWPp.of_sepWP_lscl_bob hclm1 (mid := lsmpl.base 205)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl2
  refine SepWPp.call_frame_lscl_bob (x := (argPtr + 128#64, ikAPk)) hserPub hcl2
    (by wp_norm_lhs) (by wp_norm_lhs)
    (by simp only [*, State.spAligned, arm64_norm])
    (ret_pc := (blkPl_75).base + 416#64) (by wp_norm_lhs)
    (by
      conv =>
        lhs
        dsimp only [ecPubKeySerializeAllocPlacedSpec]
        simp only [arm64_norm, hspm1, Initiator.bv_sub_add_lit', BitVec.reduceSub])
    hikA_len
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sm _ R hm => by
      dsimp only [ecPubKeySerializeAllocPlacedSpec, rustPanicOnOomPlaced] at hm
      simpa only [sepConj_assoc] using
        allowPanic_frame (fun h =>
          allocFailedIn_of_trace_eq (s0 := s0)
            (by simp only [*, arm64_norm]) h) hm)
    (fun sm2 hpcm2 hrunm2 hspm2 hcsm2 hclm2 => ?_)
  simp only [*, arm64_norm] at hspm2
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm2
  rcases hcsm2 with ⟨hcs3_19, hcs3_20, hcs3_21, hcs3_22, hcs3_23, hcs3_24, hcs3_25, hcs3_26,
    hcs3_27, hcs3_28, hcs3_29, hcs3_vregs⟩
  simp only [*, arm64_norm]
    at hcs3_19 hcs3_20 hcs3_21 hcs3_22 hcs3_23 hcs3_24 hcs3_25 hcs3_26 hcs3_27 hcs3_28 hcs3_29
       hcs3_vregs
  conv =>
    arg 4
    dsimp only [ecPubKeySerializeAllocPlacedSpec]
    simp only [arm64_norm, hspm1, Initiator.bv_sub_add_lit', BitVec.reduceSub,
      sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun remoteIkBoxPtr => ?_
  refine SepWPp.pure_left fun ⟨htr3, hx0_2, hx1_2, hne_remoteIk⟩ => ?_
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay32 : LayoutOk 32 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP_lscl_bob hclm2 (mid := (blkPl_75).base + 440#64)
  wp_steps
  wp_call hshim' ()
  wp_steps
  wp_call halloc' (32, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl3
  by_cases hoom1 : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · conv =>
      arg 4
      simp only [hoom1, ite_true]
    refine sepWPp_pure_mid fun htrace_oom => ?_
    apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpan_rawvec) fun R hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (Initiator.allocFailedIn_of_eq (by simp only [*, Rust.panicked, arm64_norm])) hm
  · have hm32_rk : memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
        cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 :=
      ProofLib.memRegion_cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 (by decide)
    conv =>
      arg 4
      simp only [hoom1, ite_false, ‹sf.sp = sm2.sp›, hspm2, hm32_rk, cells, sepConj_emp,
        sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
        sepConj_assoc]
    refine SepWPp.exists_elim fun r0 => SepWPp.exists_elim fun r1 =>
      SepWPp.exists_elim fun r2 => SepWPp.exists_elim fun r3 => ?_
    refine sepWPp_pure_mid fun ⟨hmod_rk, htr4⟩ => ?_
    apply SepWPp.of_sepWP_lscl_bob hcl3 (mid := lsmpl.base 205)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcl4
    refine SepWPp.call_frame_lscl_bob (x := (argPtr + 160#64, ekAPk)) hserPub hcl4
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simp only [*, State.spAligned, arm64_norm])
      (ret_pc := (blkPl_75).base + 464#64) (by wp_norm_lhs)
      (by
        conv =>
          lhs
          dsimp only [ecPubKeySerializeAllocPlacedSpec]
          simp only [arm64_norm, ‹sf_1.sp = sf.sp›, ‹sf.sp = sm2.sp›, hspm2,
            Initiator.bv_sub_add_lit', BitVec.reduceSub])
      hekA_len
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (fun sm _ R hm => by
        dsimp only [ecPubKeySerializeAllocPlacedSpec, rustPanicOnOomPlaced] at hm
        simpa only [sepConj_assoc] using
          allowPanic_frame (fun h =>
            allocFailedIn_of_trace_eq (s0 := s0)
              (by simp only [*, arm64_norm]) h) hm)
      (fun sm3 hpcm3 hrunm3 hspm3 hcsm3 hclm3 => ?_)
    simp only [*, arm64_norm] at hspm3
    dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm3
    rcases hcsm3 with ⟨hcs4_19, hcs4_20, hcs4_21, hcs4_22, hcs4_23, hcs4_24, hcs4_25, hcs4_26,
      hcs4_27, hcs4_28, hcs4_29, hcs4_vregs⟩
    simp only [*, arm64_norm]
      at hcs4_19 hcs4_20 hcs4_21 hcs4_22 hcs4_23 hcs4_24 hcs4_25 hcs4_26 hcs4_27 hcs4_28 hcs4_29
         hcs4_vregs
    conv =>
      arg 4
      dsimp only [ecPubKeySerializeAllocPlacedSpec]
      simp only [arm64_norm, ‹sf_1.sp = sf.sp›, ‹sf.sp = sm2.sp›, hspm2,
        Initiator.bv_sub_add_lit', BitVec.reduceSub,
        sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun baseKeyBoxPtr => ?_
    refine SepWPp.pure_left fun ⟨htr5, hx0_3, hx1_3, hne_baseKey⟩ => ?_
    apply SepWPp.of_sepWP_lscl_bob hclm3 (mid := lsmpl.base 27)
    conv =>
      arg 4
      rw [sub488_split_v1 s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    wp_pull_exists
    rename_i pad_f4
    conv =>
      arg 4
      simp (config := { maxSteps := 1000000 }) only [
        cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
        Initiator.bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    wp_pull_exists
    conv =>
      arg 4
      rw [(ProofLib.memRegion_cells (s0.sp - 240#64) 12 (by decide) :
        memRegion (s0.sp - 240#64) 96 = cells (s0.sp - 240#64) 12)]
      simp (config := { maxSteps := 1000000 }) only [
        cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
        Initiator.bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    wp_pull_exists
    rename_i w_f8 c0 c1 c2 c3 c4 w_128 d0 d1 d2 w_148 w_150
    wp_steps
    refine SepWP.fold (Entails.of_eq (hrk_cells (sf_1.readReg64 (.gpr 0#5))).symm)
      (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (by
      have h := (hrk_cells (s0.sp - 656#64)).symm
      simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
      exact h)) (by sep_focus) ?_
    refine SepWP.fold (cells4_sub768_merge s0.sp _ _ _ _) (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (memRegion_160_sub5024 s0.sp)) (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (by
      have h := bobHead144V1_eq_pointsToBytes (s0.sp - 488#64) localIkBoxPtr remoteIkBoxPtr
        (sf_1.readReg64 (.gpr 0#5)) baseKeyBoxPtr spqrCap spqrBufPtr spqrLen
      simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
      exact h)) (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (by
      have h := post100_pack (s0.sp - 488#64) pad_f4 c0 c1 c2 c3 c4 d0 d1 d2
      simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
      exact h)) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcl5
    have hφ_ws : spkBPk.length = 32 ∧ spkBSk.length = 32 ∧ ck.length = 32 ∧
        (bobHead144Bv8V1 localIkBoxPtr remoteIkBoxPtr (sf_1.readReg64 (.gpr 0#5)) baseKeyBoxPtr
          spqrCap spqrBufPtr spqrLen).length = 144 ∧
        (unpack32 pad_f4 ++ bobTail96Bv8 c0 c1 c2 c3 c4 d0 d1 d2).length = 100 :=
      ⟨hspkPk_len, hspkSk_len, hck_len, bobHead144Bv8V1_length _ _ _ _ _ _ _,
        by simp [unpack32]⟩
    refine SepWPp.call_frame_lscl_bob (x :=
      ⟨outPtr, s0.sp - 488#64, rkp, spkBPk, spkBSk, s0.sp - 624#64, ck, 0#32,
        bobHead144Bv8V1 localIkBoxPtr remoteIkBoxPtr (sf_1.readReg64 (.gpr 0#5)) baseKeyBoxPtr
          spqrCap spqrBufPtr spqrLen,
        unpack32 pad_f4 ++ bobTail96Bv8 c0 c1 c2 c3 c4 d0 d1 d2⟩) hwithSender hcl5
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simp only [*, State.spAligned, arm64_norm])
      (ret_pc := (blkPl_75).base + 564#64) (by wp_norm_lhs)
      (by
        conv =>
          lhs
          dsimp only [withSenderChainNonePlacedSpec]
          simp only [arm64_norm, hspm3, hcs4_19, hcs3_19, hcs2_19, hx19,
            hcs4_20, hcs3_20, hcs2_20, hx20, Initiator.bv_sub_add_lit', BitVec.reduceSub])
      hφ_ws
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (fun sm _ R hm => by
        dsimp only [withSenderChainNonePlacedSpec, rustPanicOnOomPlaced] at hm
        simpa only [sepConj_assoc] using
          allowPanic_frame (fun h =>
            allocFailedIn_of_trace_eq (s0 := s0)
              (by simp only [*, arm64_norm]) h) hm)
      (fun sm4 hpcm4 hrunm4 hspm4 hcsm4 hclm4 => ?_)
    simp only [*, arm64_norm] at hspm4
    dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm4
    rcases hcsm4 with ⟨hcs5_19, hcs5_20, hcs5_21, hcs5_22, hcs5_23, hcs5_24, hcs5_25, hcs5_26,
      hcs5_27, hcs5_28, hcs5_29, hcs5_vregs⟩
    simp only [*, arm64_norm]
      at hcs5_19 hcs5_20 hcs5_21 hcs5_22 hcs5_23 hcs5_24 hcs5_25 hcs5_26 hcs5_27 hcs5_28 hcs5_29
         hcs5_vregs
    conv =>
      arg 4
      dsimp only [withSenderChainNonePlacedSpec]
      simp only [arm64_norm, hspm3, Initiator.bv_sub_add_lit', BitVec.reduceSub,
        sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun ratchetPubBoxPtr =>
      SepWPp.exists_elim fun ratchetPrivBoxPtr =>
      SepWPp.exists_elim fun chainKeyBoxPtr => ?_
    refine SepWPp.pure_left fun ⟨htr6, hne_rPub, hne_rPriv, hne_ck⟩ => ?_
    apply SepWPp.of_sepWP_ret
    refine SepWP.fold (Entails.of_eq (bobSession344V1_pack outPtr
      localIkBoxPtr remoteIkBoxPtr (sf_1.readReg64 (.gpr 0#5)) baseKeyBoxPtr
      spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
      pad_f4 c0 c1 c2 c3 c4 d0 d1 d2))
      (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (by
      have h := bobSession344V1_pack (s0.sp - 488#64)
        localIkBoxPtr remoteIkBoxPtr (sf_1.readReg64 (.gpr 0#5)) baseKeyBoxPtr
        spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
        pad_f4 c0 c1 c2 c3 c4 d0 d1 d2
      simp only [Initiator.bv_sub_add_lit', BitVec.reduceSub] at h
      exact h)) (by sep_focus) ?_
    have h344_weaken :
        ((s0.sp - 488#64) ↦ₛ bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr
          (sf_1.readReg64 (.gpr 0#5)) baseKeyBoxPtr spqrCap spqrBufPtr spqrLen
          ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
          pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ⊢
        memRegion (s0.sp - 488#64) 344 := by
      have h := pointsToBytes_entails_memRegion (s0.sp - 488#64)
        (bobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr (sf_1.readReg64 (.gpr 0#5))
          baseKeyBoxPtr spqrCap spqrBufPtr spqrLen ratchetPubBoxPtr ratchetPrivBoxPtr
          chainKeyBoxPtr pad_f4 c0 c1 c2 c3 c4 d0 d1 d2)
      rwa [bobSession344Bv8V1_length] at h
    refine SepWP.fold h344_weaken (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (stackAt_entry_some_merge s0.sp)) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨localIkBoxPtr, remoteIkBoxPtr, sf_1.readReg64 (.gpr 0#5), baseKeyBoxPtr,
      ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr,
      pad_f4, c0, c1, c2, c3, c4, d0, d1, d2,
      hne_localIk, hne_remoteIk, hoom1, hne_baseKey,
      hne_rPub, hne_rPriv, hne_ck,
      Entails.of_eq (by ac_rfl),
      hclm4, by wp_norm_goal, by wp_norm_goal, by simp only [*, arm64_norm],
      by simp only [*, arm64_norm], by simp only [*, arm64_norm]⟩

end CryptoVerification.E2E.Pqxdh.ResponderCore
