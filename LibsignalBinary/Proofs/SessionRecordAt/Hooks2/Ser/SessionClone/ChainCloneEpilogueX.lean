/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneBaseX
public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneEpilogue
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SepWPpIn
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsX
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `Chain::clone [local#1]` Epilogue and Extern/Panic Helpers

Verifies the epilogue postcondition entailment, state-specialized stub wrappers, and allocation-panic
tails for `<session_structure::Chain as Clone>::clone [local#1]` (`0x24848`, Block `82`) on `SP2Ext`
and under relocatable `[LibsignalPlacement]`.
-/

namespace CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open Proofs.libsignal
open Proofs.libsignal.Hooks2
open Proofs.libsignal.Stage1X

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  fp_neg_48 fp_neg_40 fp_neg_32 fp_neg_24 fp_neg_12 fp_neg_8
  fp_neg_48_int fp_neg_40_int fp_neg_32_int fp_neg_24_int fp_neg_12_int fp_neg_8_int
attribute [local arm64_norm ↓, local wp_norm ↓]
  ChainCloneStateSimp.sp_setPC_pre ChainCloneStateSimp.sp_setMem_setPC_pre
  ChainCloneStateSimp.readReg64_setPC_pre ChainCloneStateSimp.readReg64_setMem_setPC_pre
  ChainCloneStateSimp.readReg32_setPC_pre ChainCloneStateSimp.readReg32_setMem_setPC_pre
  ChainCloneStateSimp.readReg_setPC_pre ChainCloneStateSimp.readReg_setMem_setPC_pre

theorem L1_ChainCloneEpilogueX : True := trivial

theorem chainClone_of_protoChainClone_x
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hclone : ProtoChainCloneLocal1OkX img A ext) :
    ChainCloneLocal1OkX img A ext := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, chainCloneSpecX, chainAt_eq_protoChainAt, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hsym⟩, ⟨hx0, hx1⟩, hmem⟩
  set P_rc : Prop := x.gc.1.srk.bytes.length = 33 ∧ x.gc.1.priv.bytes = []
  change s0.mem ⊨ memRegion x.dst 104 ∗ ⌜P_rc⌝ ∗ protoChainAt A x.gc x.src ∗
    A.pool ∗ stackAt s0.sp chainCloneStackX ∗ R at hmem
  have hmem_rearr :
      s0.mem ⊨
        memRegion x.dst 104 ∗ protoChainAt A x.gc x.src ∗
        A.pool ∗ stackAt s0.sp chainCloneStackX ∗ (⌜P_rc⌝ ∗ R) := by
    have heq :
        (memRegion x.dst 104 ∗ ⌜P_rc⌝ ∗ protoChainAt A x.gc x.src ∗
          A.pool ∗ stackAt s0.sp chainCloneStackX ∗ R) =
        (memRegion x.dst 104 ∗ protoChainAt A x.gc x.src ∗
          A.pool ∗ stackAt s0.sp chainCloneStackX ∗ (⌜P_rc⌝ ∗ R)) := by
      ac_rfl
    rwa [← heq]
  have hpre_clone :
      s0.mem ⊨ ((protoChainCloneSpecX A).inImage img).pre x s0 ∗ (⌜P_rc⌝ ∗ R) := by
    simp only [Spec.inImage, protoChainCloneSpecX, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hF, hsym⟩, ⟨hx0, hx1⟩, hmem_rearr⟩
  refine hclone.mono_outcome x (⌜P_rc⌝ ∗ R) s0 hpc hrun hpre_clone hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hexit, hpost⟩ | ⟨_, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    simp only [Spec.inImage, protoChainCloneSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htrace, hmem_f⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hmem_f
    rcases hmem_f with ⟨g', hmem_f⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hmem_f
    rcases hmem_f with ⟨⟨hsrk', hpriv', hkeys'⟩, hmem_f⟩
    have hpure_front :
        sf.mem ⊨
          ⌜P_rc⌝ ∗
          (protoChainAt A (g', x.gc.2) x.dst ∗ protoChainAt A x.gc x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStackX ∗ R) := by
      have heq :
          (protoChainAt A (g', x.gc.2) x.dst ∗ protoChainAt A x.gc x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStackX ∗ ⌜P_rc⌝ ∗ R) =
          (⌜P_rc⌝ ∗
            (protoChainAt A (g', x.gc.2) x.dst ∗ protoChainAt A x.gc x.src ∗
              A.pool ∗ stackAt s0.sp chainCloneStackX ∗ R)) := by
        ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hpure_front
    rcases hpure_front with ⟨⟨hsrk33, hpriv_nil⟩, hrest_f⟩
    simp only [Spec.inImage, chainCloneSpecX, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrace, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨g', ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hsrk', hpriv', hkeys'⟩, ?_⟩
    rw [chainAt_eq_protoChainAt A (g', x.gc.2) x.dst, chainAt_eq_protoChainAt A x.gc x.src]
    have hsrk33' : g'.srk.bytes.length = 33 := by rw [hsrk', hsrk33]
    have hpriv_nil' : g'.priv.bytes = [] := hpriv'.trans hpriv_nil
    set P_rc' : Prop := g'.srk.bytes.length = 33 ∧ g'.priv.bytes = []
    change sf.mem ⊨
      (⌜P_rc'⌝ ∗ protoChainAt A (g', x.gc.2) x.dst) ∗
      (⌜P_rc⌝ ∗ protoChainAt A x.gc x.src) ∗
      A.pool ∗ stackAt s0.sp chainCloneStackX ∗ R
    have heq2 :
        ((⌜P_rc'⌝ ∗ protoChainAt A (g', x.gc.2) x.dst) ∗
          (⌜P_rc⌝ ∗ protoChainAt A x.gc x.src) ∗
          A.pool ∗ stackAt s0.sp chainCloneStackX ∗ R) =
        (⌜P_rc'⌝ ∗ (⌜P_rc⌝ ∗
          (protoChainAt A (g', x.gc.2) x.dst ∗ protoChainAt A x.gc x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStackX ∗ R))) := by
      ac_rfl
    rw [heq2, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨⟨hsrk33', hpriv_nil'⟩, ⟨hsrk33, hpriv_nil⟩, hrest_f⟩
  · right; left
    refine ⟨hpan, ?_⟩
    simp only [Spec.inImage, protoChainCloneSpecX, chainCloneSpecX, sepConj_assoc,
      satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hp, hmem_f⟩
    refine ⟨hp, ?_⟩
    exact Satisfies.mono (by
      rw [← sepConj_assoc]
      exact sepConj_mono_left (entails_anyHeap _)) hmem_f
  · simp only [Spec.inImage, protoChainCloneSpecX, sepConj_assoc] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · simp only [Spec.inImage, protoChainCloneSpecX, sepConj_assoc] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

theorem senderChainClone_of_chainClone_x
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hclone : ProtoChainCloneLocal1OkX img A ext) :
    SenderChainCloneLocal1OkX img A ext := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hbridge := optSenderChainAt_some_eq_chainAt
  simp only [Spec.inImage, senderChainCloneSpecX, hbridge, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hsym⟩, ⟨hx0, hx1⟩, hmem⟩
  let P_sc : Prop :=
    x.g.priv.bytes = x.sc.ratchetKey.privateKey.bytes.toList ∧
      Ratchet.clampScalar x.sc.ratchetKey.privateKey.bytes = x.sc.ratchetKey.privateKey.bytes ∧
      x.g.srk.bytes.length = 33
  let gc0 : ChainGhost × ReceiverChain :=
    (⟨x.g.srk, x.g.priv, x.g.mkCap, x.g.mkPtr, [], x.g.ck⟩,
      ⟨x.sc.ratchetKey.publicKey, some x.sc.chainKey, []⟩)
  change s0.mem ⊨ memRegion x.dst 104 ∗ ⌜P_sc⌝ ∗ protoChainAt A gc0 x.src ∗
    A.pool ∗ stackAt s0.sp chainCloneStackX ∗ R at hmem
  have hmem_rearr :
      s0.mem ⊨
        memRegion x.dst 104 ∗ protoChainAt A gc0 x.src ∗
        A.pool ∗ stackAt s0.sp chainCloneStackX ∗ (⌜P_sc⌝ ∗ R) := by
    have heq :
        (memRegion x.dst 104 ∗ ⌜P_sc⌝ ∗ protoChainAt A gc0 x.src ∗
          A.pool ∗ stackAt s0.sp chainCloneStackX ∗ R) =
        (memRegion x.dst 104 ∗ protoChainAt A gc0 x.src ∗
          A.pool ∗ stackAt s0.sp chainCloneStackX ∗ (⌜P_sc⌝ ∗ R)) := by
      ac_rfl
    rwa [← heq]
  have hpre_clone :
      s0.mem ⊨ ((protoChainCloneSpecX A).inImage img).pre ⟨x.dst, x.src, gc0⟩ s0 ∗ (⌜P_sc⌝ ∗ R) := by
    simp only [Spec.inImage, protoChainCloneSpecX, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hF, hsym⟩, ⟨hx0, hx1⟩, hmem_rearr⟩
  refine hclone.mono_outcome ⟨x.dst, x.src, gc0⟩ (⌜P_sc⌝ ∗ R) s0 hpc hrun hpre_clone hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hexit, hpost⟩ | ⟨_, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    simp only [Spec.inImage, protoChainCloneSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htrace, hmem_f⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hmem_f
    rcases hmem_f with ⟨g', hmem_f⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hmem_f
    rcases hmem_f with ⟨⟨hsrk', hpriv', hkeys'⟩, hmem_f⟩
    have hkeys_nil : g'.keys = [] := List.eq_nil_of_length_eq_zero hkeys'
    have hpure_front :
        sf.mem ⊨
          ⌜P_sc⌝ ∗
          (protoChainAt A (g', gc0.2) x.dst ∗ protoChainAt A gc0 x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStackX ∗ R) := by
      have heq :
          (protoChainAt A (g', gc0.2) x.dst ∗ protoChainAt A gc0 x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStackX ∗ ⌜P_sc⌝ ∗ R) =
          (⌜P_sc⌝ ∗
            (protoChainAt A (g', gc0.2) x.dst ∗ protoChainAt A gc0 x.src ∗
              A.pool ∗ stackAt s0.sp chainCloneStackX ∗ R)) := by
        ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hpure_front
    rcases hpure_front with ⟨⟨hpriv_eq, hclamp, hsrk33⟩, hrest_f⟩
    let sg' : SenderChainGhost := ⟨g'.srk, g'.priv, g'.mkCap, g'.mkPtr, g'.ck⟩
    have hg'_eq : g' = ⟨sg'.srk, sg'.priv, sg'.mkCap, sg'.mkPtr, [], sg'.ck⟩ := by
      cases g'; dsimp [sg'] at hkeys_nil ⊢; subst hkeys_nil; rfl
    rw [hg'_eq] at hrest_f
    simp only [Spec.inImage, senderChainCloneSpecX, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrace, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨sg', ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hsrk', hpriv'⟩, ?_⟩
    rw [hbridge A x.dst sg' x.sc, hbridge A x.src x.g x.sc]
    have hpriv'_eq : sg'.priv.bytes = x.sc.ratchetKey.privateKey.bytes.toList :=
      hpriv'.trans hpriv_eq
    have hsrk33' : sg'.srk.bytes.length = 33 := by
      change g'.srk.bytes.length = 33
      rw [hsrk', hsrk33]
    let P_sc' : Prop :=
      sg'.priv.bytes = x.sc.ratchetKey.privateKey.bytes.toList ∧
        Ratchet.clampScalar x.sc.ratchetKey.privateKey.bytes = x.sc.ratchetKey.privateKey.bytes ∧
        sg'.srk.bytes.length = 33
    let gc' : ChainGhost × ReceiverChain :=
      (⟨sg'.srk, sg'.priv, sg'.mkCap, sg'.mkPtr, [], sg'.ck⟩, gc0.2)
    change sf.mem ⊨
      (⌜P_sc'⌝ ∗ protoChainAt A gc' x.dst) ∗
      (⌜P_sc⌝ ∗ protoChainAt A gc0 x.src) ∗
      A.pool ∗ stackAt s0.sp chainCloneStackX ∗ R
    have heq2 :
        ((⌜P_sc'⌝ ∗ protoChainAt A gc' x.dst) ∗
          (⌜P_sc⌝ ∗ protoChainAt A gc0 x.src) ∗
          A.pool ∗ stackAt s0.sp chainCloneStackX ∗ R) =
        (⌜P_sc'⌝ ∗ (⌜P_sc⌝ ∗
          (protoChainAt A gc' x.dst ∗ protoChainAt A gc0 x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStackX ∗ R))) := by
      ac_rfl
    rw [heq2, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨⟨hpriv'_eq, hclamp, hsrk33'⟩, ⟨hpriv_eq, hclamp, hsrk33⟩, hrest_f⟩
  · right; left
    refine ⟨hpan, ?_⟩
    simp only [Spec.inImage, protoChainCloneSpecX, senderChainCloneSpecX, sepConj_assoc,
      satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hp, hmem_f⟩
    refine ⟨hp, ?_⟩
    exact Satisfies.mono (by
      rw [← sepConj_assoc]
      exact sepConj_mono_left (entails_anyHeap _)) hmem_f
  · simp only [Spec.inImage, protoChainCloneSpecX, sepConj_assoc] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · simp only [Spec.inImage, protoChainCloneSpecX, sepConj_assoc] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

/-! ## Epilogue Postcondition and Steps -/

theorem epilogue_post_entails_x (A : RustAlloc) (x : ChainCloneGhost) (s0 sf : State)
    (srkPtr' privPtr' mkPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (keys' : List MessageKeyGhost) (ckPin' : VecPin)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : keys'.length = x.gc.2.messageKeys.length)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (htrace : sf.trace = s0.trace) :
    ((x.dst ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
      ((x.dst + 8#64) ↦₆₄ srkPtr') ∗
      ((x.dst + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
      ((x.dst + 24#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
      ((x.dst + 32#64) ↦₆₄ privPtr') ∗
      ((x.dst + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
      ((x.dst + 48#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
      ((x.dst + 56#64) ↦₆₄ mkPtr') ∗
      ((x.dst + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
      ((x.dst + 72#64) ↦₆₄ x25) ∗
      ((x.dst + 80#64) ↦₆₄ x28) ∗
      ((x.dst + 88#64) ↦₆₄ x25) ∗
      ((x.dst + 96#64) ↦₃₂ w27) ∗
      memRegion (x.dst + 100#64) 4 ∗
      vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
      vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
      vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr'
        (keys'.zip x.gc.2.messageKeys) ∗
      clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
      protoChainAt A x.gc x.src ∗
      A.pool ∗
      stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
      spillSlotsExist s0.sp ∗
      ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
      ((s0.sp - 136#64) ↦₆₄ v9) ∗
      ((s0.sp - 128#64) ↦₆₄ v10) ∗
      ((s0.sp - 104#64) ↦₆₄ v13) ∗
      savedRegsOnStack s0) ⊢
      (protoChainCloneSpecX A).post x s0 sf := by
  unfold protoChainCloneSpecX
  dsimp only
  apply Entails.pure_right htrace
  let g' := clonedChainGhost x.gc srkPtr' privPtr'
    (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr' keys' ckPin'
  have hg' :
      ((x.dst ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 8#64) ↦₆₄ srkPtr') ∗
        ((x.dst + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 24#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 32#64) ↦₆₄ privPtr') ∗
        ((x.dst + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 48#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 56#64) ↦₆₄ mkPtr') ∗
        ((x.dst + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 72#64) ↦₆₄ x25) ∗
        ((x.dst + 80#64) ↦₆₄ x28) ∗
        ((x.dst + 88#64) ↦₆₄ x25) ∗
        ((x.dst + 96#64) ↦₃₂ w27) ∗
        memRegion (x.dst + 100#64) 4 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr'
          (keys'.zip x.gc.2.messageKeys) ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey) ⊢
      (∃∗ g' : ChainGhost,
        ⌜g'.srk.bytes = x.gc.1.srk.bytes ∧ g'.priv.bytes = x.gc.1.priv.bytes ∧
          g'.keys.length = x.gc.1.keys.length⌝ ∗
        protoChainAt A (g', x.gc.2) x.dst) := by
    refine Entails.trans
      (fold_chainAt_dst A x.gc x.dst srkPtr' privPtr' mkPtr' x25 x28 w27 keys' ckPin'
        hsrk hmax hklen) ?_
    apply Entails.sepExists_right g'
    exact Entails.pure_right ⟨rfl, rfl, hklen.trans hsrc_klen.symm⟩ (Entails.refl _)
  have hst := fold_stackAt_chainClone_x s0
    (BitVec.ofNat 64 x.gc.2.messageKeys.length) v9 v10 v13
  have hgroup :
      ((x.dst ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 8#64) ↦₆₄ srkPtr') ∗
        ((x.dst + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 24#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 32#64) ↦₆₄ privPtr') ∗
        ((x.dst + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 48#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 56#64) ↦₆₄ mkPtr') ∗
        ((x.dst + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 72#64) ↦₆₄ x25) ∗
        ((x.dst + 80#64) ↦₆₄ x28) ∗
        ((x.dst + 88#64) ↦₆₄ x25) ∗
        ((x.dst + 96#64) ↦₃₂ w27) ∗
        memRegion (x.dst + 100#64) 4 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr'
          (keys'.zip x.gc.2.messageKeys) ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) =
      (((x.dst ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 8#64) ↦₆₄ srkPtr') ∗
        ((x.dst + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 24#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 32#64) ↦₆₄ privPtr') ∗
        ((x.dst + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 48#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 56#64) ↦₆₄ mkPtr') ∗
        ((x.dst + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 72#64) ↦₆₄ x25) ∗
        ((x.dst + 80#64) ↦₆₄ x28) ∗
        ((x.dst + 88#64) ↦₆₄ x25) ∗
        ((x.dst + 96#64) ↦₃₂ w27) ∗
        memRegion (x.dst + 100#64) 4 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr'
          (keys'.zip x.gc.2.messageKeys) ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey) ∗
       protoChainAt A x.gc x.src ∗
       A.pool ∗
       (stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)) := by
    ac_rfl
  rw [hgroup]
  exact sepConj_mono hg' (sepConj_mono_right (sepConj_mono_right hst))

elab "clone_fetches_range " b:term:max ext:term:max
    hfn:term:max kStart:num kEnd:num : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let k0 := kStart.getNat
    let k1 := kEnd.getNat
    for k in [k0:k1] do
      let byteOff := 4 * k
      let absOff := num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") + byteOff
      let decName := (`CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1).str s!"chainCloneLocal1Bin_decode_0x{hex5Str absOff}"
      let decId := Lean.mkIdent decName
      let byteOffLit := Lean.Syntax.mkNumLit (toString byteOff)
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        have := libsignalSessionCode_fetch_fnAddr (b := $b)
          (H := Rust.withPanics $ext)
          $hfn (k := $byteOffLit) (by decide) $decId))

attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

set_option maxHeartbeats 1600000 in
theorem chain_clone_epilogue_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State)
    (srkPtr' privPtr' mkPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (keys' : List MessageKeyGhost) (ckPin' : VecPin)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : keys'.length = x.gc.2.messageKeys.length)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainCloneLocal1Name + 736#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx9 : s.readReg64 (Reg.gpr 9#5) = mkPtr')
    (hx25 : s.readReg64 (Reg.gpr 25#5) = x25)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = x28)
    (hw27 : s.readReg32 (Reg.gpr 27#5) = w27)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr'
          (keys'.zip x.gc.2.messageKeys) ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpecX A).post x s0 sf))
      Qp := by
  intro _ _
  have hfn : libsignalSessionCode.fnOff chainCloneLocal1Name = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") :=
    libsignalSessionCode_fnOff_sym_24848
  clone_fetches_range img.base ext hfn 184 200
  clear hfn
  unfold SP2Ext at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr chainCloneLocal1Name = entry
  examples_hide_fetches
  rw [memRegion_104_eq_slots104 x.dst, sepExists_sepConj_left]
  refine SepWPp.exists_elim fun d => ?_
  unfold savedRegsOnStack
  simp only [sepConj_assoc]
  apply SepWPp.of_sepWP (mid := s0.readReg64 (Reg.gpr 30#5))
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  apply SepWPp.done (by simp_all) (by simp_all)
  refine ⟨by simp_all, ?_, ?_⟩
  · constructor <;> simp_all
  · rw [show BitVec.truncate 32 (s.readReg64 (Reg.gpr 27#5)) = w27 from hw27]
    refine Entails.trans ?_
      (epilogue_post_entails_x A x s0 _ srkPtr' privPtr' mkPtr' x25 x28 v9 v10 v13
        w27 keys' ckPin' hsrk hmax hklen hsrc_klen (by simp_all))
    unfold savedRegsOnStack
    exact Entails.of_eq (by ac_rfl)

/-! ## Stub contracts on `SP2Ext` -/

theorem panic_at_handle_error_x {b : BitVec 64} {ext : String → Option (State → State)} :
    (SP2Ext b ext).externAt?
      ((SP2Ext b ext).fnAddr chainCloneLocal1Name + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]")) =
      some Rust.panicked :=
  panic_at_handle_error_ext b ext chainCloneLocal1Name
    (num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
    (by fnoff_eq)

theorem shim_ok_at_x {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr chainCloneLocal1Name + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
      (Proofs.libsignal.Stage1X.session2ShimSpecX.inImage img) :=
  hC.alloc.shim_ok_at chainCloneLocal1Name (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
    (by fnoff_eq)

theorem alloc_ok_at_x {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr chainCloneLocal1Name + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
      ((Proofs.libsignal.Stage1X.rustAllocSpecWithStack A Stage1X.extHookStack).inImage img) :=
  hC.alloc.alloc_ok_at chainCloneLocal1Name (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
    (by fnoff_eq)

theorem memcpy_ok_at_x {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr chainCloneLocal1Name + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
      ((LibsignalTripleRatchet.sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img) :=
  hC.memcpy_ok_at chainCloneLocal1Name (num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
    (by fnoff_eq)

/-! ## Panic lemmas on `SP2Ext` -/

theorem chain_clone_panic_800_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainCloneLocal1Name + 800#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R)) := by
  intro _ _
  have hfn : libsignalSessionCode.fnOff chainCloneLocal1Name = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") :=
    libsignalSessionCode_fnOff_sym_24848
  have hpanic := panic_at_handle_error_x (b := img.base) (ext := ext)
  clone_fetches_range img.base ext hfn 200 203
  clear hfn
  unfold SP2Ext at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr chainCloneLocal1Name = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [protoChainCloneSpecX, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

theorem chain_clone_panic_812_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainCloneLocal1Name + 812#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R)) := by
  intro _ _
  have hfn : libsignalSessionCode.fnOff chainCloneLocal1Name = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") :=
    libsignalSessionCode_fnOff_sym_24848
  have hpanic := panic_at_handle_error_x (b := img.base) (ext := ext)
  clone_fetches_range img.base ext hfn 203 206
  clear hfn
  unfold SP2Ext at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr chainCloneLocal1Name = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [protoChainCloneSpecX, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

theorem chain_clone_panic_824_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainCloneLocal1Name + 824#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R)) := by
  intro _ _
  have hfn : libsignalSessionCode.fnOff chainCloneLocal1Name = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") :=
    libsignalSessionCode_fnOff_sym_24848
  have hpanic := panic_at_handle_error_x (b := img.base) (ext := ext)
  clone_fetches_range img.base ext hfn 206 209
  clear hfn
  unfold SP2Ext at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr chainCloneLocal1Name = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [protoChainCloneSpecX, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

theorem chain_clone_panic_836_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainCloneLocal1Name + 836#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R)) := by
  intro _ _
  have hfn : libsignalSessionCode.fnOff chainCloneLocal1Name = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") :=
    libsignalSessionCode_fnOff_sym_24848
  have hpanic := panic_at_handle_error_x (b := img.base) (ext := ext)
  clone_fetches_range img.base ext hfn 209 212
  clear hfn
  unfold SP2Ext at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr chainCloneLocal1Name = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [protoChainCloneSpecX, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

theorem chain_clone_panic_848_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainCloneLocal1Name + 848#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R)) := by
  intro _ _
  have hfn : libsignalSessionCode.fnOff chainCloneLocal1Name = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") :=
    libsignalSessionCode_fnOff_sym_24848
  have hpanic := panic_at_handle_error_x (b := img.base) (ext := ext)
  clone_fetches_range img.base ext hfn 212 215
  clear hfn
  unfold SP2Ext at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr chainCloneLocal1Name = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [protoChainCloneSpecX, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

theorem chain_clone_panic_860_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainCloneLocal1Name + 860#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R)) := by
  intro _ _
  have hfn : libsignalSessionCode.fnOff chainCloneLocal1Name = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") :=
    libsignalSessionCode_fnOff_sym_24848
  have hpanic := panic_at_handle_error_x (b := img.base) (ext := ext)
  clone_fetches_range img.base ext hfn 215 218
  clear hfn
  unfold SP2Ext at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr chainCloneLocal1Name = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [protoChainCloneSpecX, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

/-! ## Relocatable `[LibsignalPlacement]` epilogue and stub helpers (Block `82`) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem chainClone_of_protoChainClone_placed_x [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (hclone : ProtoChainCloneLocal1PlacedOkX A H) :
    ChainCloneLocal1PlacedOkX A H := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [chainCloneSpecX, chainAt_eq_protoChainAt, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hmem⟩
  set P_rc : Prop := x.gc.1.srk.bytes.length = 33 ∧ x.gc.1.priv.bytes = []
  change s0.mem ⊨ memRegion x.dst 104 ∗ ⌜P_rc⌝ ∗ protoChainAt A x.gc x.src ∗
    A.pool ∗ stackAt s0.sp chainCloneStackX ∗ R at hmem
  have hmem_rearr :
      s0.mem ⊨
        memRegion x.dst 104 ∗ protoChainAt A x.gc x.src ∗
        A.pool ∗ stackAt s0.sp chainCloneStackX ∗ (⌜P_rc⌝ ∗ R) := by
    have heq :
        (memRegion x.dst 104 ∗ ⌜P_rc⌝ ∗ protoChainAt A x.gc x.src ∗
          A.pool ∗ stackAt s0.sp chainCloneStackX ∗ R) =
        (memRegion x.dst 104 ∗ protoChainAt A x.gc x.src ∗
          A.pool ∗ stackAt s0.sp chainCloneStackX ∗ (⌜P_rc⌝ ∗ R)) := by
      ac_rfl
    rwa [← heq]
  have hpre_clone :
      s0.mem ⊨ (withLsCodeLoaded lsmpl (protoChainCloneSpecX A)).pre x s0 ∗ (⌜P_rc⌝ ∗ R) := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [protoChainCloneSpecX, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1⟩, hmem_rearr⟩
  refine hclone.mono_outcome x (⌜P_rc⌝ ∗ R) s0 hpc hrun hpre_clone hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hexit, hpost⟩ | ⟨_, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    simp only [withLsCodeLoaded, protoChainCloneSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htrace, hmem_f⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hmem_f
    rcases hmem_f with ⟨g', hmem_f⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hmem_f
    rcases hmem_f with ⟨⟨hsrk', hpriv', hkeys'⟩, hmem_f⟩
    have hpure_front :
        sf.mem ⊨
          ⌜P_rc⌝ ∗
          (protoChainAt A (g', x.gc.2) x.dst ∗ protoChainAt A x.gc x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStackX ∗ R) := by
      have heq :
          (protoChainAt A (g', x.gc.2) x.dst ∗ protoChainAt A x.gc x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStackX ∗ ⌜P_rc⌝ ∗ R) =
          (⌜P_rc⌝ ∗
            (protoChainAt A (g', x.gc.2) x.dst ∗ protoChainAt A x.gc x.src ∗
              A.pool ∗ stackAt s0.sp chainCloneStackX ∗ R)) := by
        ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hpure_front
    rcases hpure_front with ⟨⟨hsrk33, hpriv_nil⟩, hrest_f⟩
    simp only [withLsCodeLoaded, chainCloneSpecX, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrace, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨g', ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hsrk', hpriv', hkeys'⟩, ?_⟩
    rw [chainAt_eq_protoChainAt A (g', x.gc.2) x.dst, chainAt_eq_protoChainAt A x.gc x.src]
    have hsrk33' : g'.srk.bytes.length = 33 := by rw [hsrk', hsrk33]
    have hpriv_nil' : g'.priv.bytes = [] := hpriv'.trans hpriv_nil
    set P_rc' : Prop := g'.srk.bytes.length = 33 ∧ g'.priv.bytes = []
    change sf.mem ⊨
      (⌜P_rc'⌝ ∗ protoChainAt A (g', x.gc.2) x.dst) ∗
      (⌜P_rc⌝ ∗ protoChainAt A x.gc x.src) ∗
      A.pool ∗ stackAt s0.sp chainCloneStackX ∗ R
    have heq2 :
        ((⌜P_rc'⌝ ∗ protoChainAt A (g', x.gc.2) x.dst) ∗
          (⌜P_rc⌝ ∗ protoChainAt A x.gc x.src) ∗
          A.pool ∗ stackAt s0.sp chainCloneStackX ∗ R) =
        (⌜P_rc'⌝ ∗ (⌜P_rc⌝ ∗
          (protoChainAt A (g', x.gc.2) x.dst ∗ protoChainAt A x.gc x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStackX ∗ R))) := by
      ac_rfl
    rw [heq2, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨⟨hsrk33', hpriv_nil'⟩, ⟨hsrk33, hpriv_nil⟩, hrest_f⟩
  · right; left
    refine ⟨hpan, ?_⟩
    simp only [withLsCodeLoaded, protoChainCloneSpecX, chainCloneSpecX, sepConj_assoc,
      satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hp, hmem_f⟩
    refine ⟨hp, ?_⟩
    exact Satisfies.mono (by
      rw [← sepConj_assoc]
      exact sepConj_mono_left (entails_anyHeap _)) hmem_f
  · simp only [withLsCodeLoaded, protoChainCloneSpecX, sepConj_assoc] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · simp only [withLsCodeLoaded, protoChainCloneSpecX, sepConj_assoc] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

theorem senderChainClone_of_chainClone_placed_x [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (hclone : ProtoChainCloneLocal1PlacedOkX A H) :
    SenderChainCloneLocal1PlacedOkX A H := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hbridge := optSenderChainAt_some_eq_chainAt
  have ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [senderChainCloneSpecX, hbridge, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hmem⟩
  let P_sc : Prop :=
    x.g.priv.bytes = x.sc.ratchetKey.privateKey.bytes.toList ∧
      Ratchet.clampScalar x.sc.ratchetKey.privateKey.bytes = x.sc.ratchetKey.privateKey.bytes ∧
      x.g.srk.bytes.length = 33
  let gc0 : ChainGhost × ReceiverChain :=
    (⟨x.g.srk, x.g.priv, x.g.mkCap, x.g.mkPtr, [], x.g.ck⟩,
      ⟨x.sc.ratchetKey.publicKey, some x.sc.chainKey, []⟩)
  change s0.mem ⊨ memRegion x.dst 104 ∗ ⌜P_sc⌝ ∗ protoChainAt A gc0 x.src ∗
    A.pool ∗ stackAt s0.sp chainCloneStackX ∗ R at hmem
  have hmem_rearr :
      s0.mem ⊨
        memRegion x.dst 104 ∗ protoChainAt A gc0 x.src ∗
        A.pool ∗ stackAt s0.sp chainCloneStackX ∗ (⌜P_sc⌝ ∗ R) := by
    have heq :
        (memRegion x.dst 104 ∗ ⌜P_sc⌝ ∗ protoChainAt A gc0 x.src ∗
          A.pool ∗ stackAt s0.sp chainCloneStackX ∗ R) =
        (memRegion x.dst 104 ∗ protoChainAt A gc0 x.src ∗
          A.pool ∗ stackAt s0.sp chainCloneStackX ∗ (⌜P_sc⌝ ∗ R)) := by
      ac_rfl
    rwa [← heq]
  have hpre_clone :
      s0.mem ⊨ (withLsCodeLoaded lsmpl (protoChainCloneSpecX A)).pre ⟨x.dst, x.src, gc0⟩ s0 ∗ (⌜P_sc⌝ ∗ R) := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [protoChainCloneSpecX, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1⟩, hmem_rearr⟩
  refine hclone.mono_outcome ⟨x.dst, x.src, gc0⟩ (⌜P_sc⌝ ∗ R) s0 hpc hrun hpre_clone hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hexit, hpost⟩ | ⟨_, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    simp only [withLsCodeLoaded, protoChainCloneSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htrace, hmem_f⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hmem_f
    rcases hmem_f with ⟨g', hmem_f⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hmem_f
    rcases hmem_f with ⟨⟨hsrk', hpriv', hkeys'⟩, hmem_f⟩
    have hkeys_nil : g'.keys = [] := List.eq_nil_of_length_eq_zero hkeys'
    have hpure_front :
        sf.mem ⊨
          ⌜P_sc⌝ ∗
          (protoChainAt A (g', gc0.2) x.dst ∗ protoChainAt A gc0 x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStackX ∗ R) := by
      have heq :
          (protoChainAt A (g', gc0.2) x.dst ∗ protoChainAt A gc0 x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStackX ∗ ⌜P_sc⌝ ∗ R) =
          (⌜P_sc⌝ ∗
            (protoChainAt A (g', gc0.2) x.dst ∗ protoChainAt A gc0 x.src ∗
              A.pool ∗ stackAt s0.sp chainCloneStackX ∗ R)) := by
        ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hpure_front
    rcases hpure_front with ⟨⟨hpriv_eq, hclamp, hsrk33⟩, hrest_f⟩
    let sg' : SenderChainGhost := ⟨g'.srk, g'.priv, g'.mkCap, g'.mkPtr, g'.ck⟩
    have hg'_eq : g' = ⟨sg'.srk, sg'.priv, sg'.mkCap, sg'.mkPtr, [], sg'.ck⟩ := by
      cases g'; dsimp [sg'] at hkeys_nil ⊢; subst hkeys_nil; rfl
    rw [hg'_eq] at hrest_f
    simp only [withLsCodeLoaded, senderChainCloneSpecX, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrace, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨sg', ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hsrk', hpriv'⟩, ?_⟩
    rw [hbridge A x.dst sg' x.sc, hbridge A x.src x.g x.sc]
    have hpriv'_eq : sg'.priv.bytes = x.sc.ratchetKey.privateKey.bytes.toList :=
      hpriv'.trans hpriv_eq
    have hsrk33' : sg'.srk.bytes.length = 33 := by
      change g'.srk.bytes.length = 33
      rw [hsrk', hsrk33]
    let P_sc' : Prop :=
      sg'.priv.bytes = x.sc.ratchetKey.privateKey.bytes.toList ∧
        Ratchet.clampScalar x.sc.ratchetKey.privateKey.bytes = x.sc.ratchetKey.privateKey.bytes ∧
        sg'.srk.bytes.length = 33
    let gc' : ChainGhost × ReceiverChain :=
      (⟨sg'.srk, sg'.priv, sg'.mkCap, sg'.mkPtr, [], sg'.ck⟩, gc0.2)
    change sf.mem ⊨
      (⌜P_sc'⌝ ∗ protoChainAt A gc' x.dst) ∗
      (⌜P_sc⌝ ∗ protoChainAt A gc0 x.src) ∗
      A.pool ∗ stackAt s0.sp chainCloneStackX ∗ R
    have heq2 :
        ((⌜P_sc'⌝ ∗ protoChainAt A gc' x.dst) ∗
          (⌜P_sc⌝ ∗ protoChainAt A gc0 x.src) ∗
          A.pool ∗ stackAt s0.sp chainCloneStackX ∗ R) =
        (⌜P_sc'⌝ ∗ (⌜P_sc⌝ ∗
          (protoChainAt A gc' x.dst ∗ protoChainAt A gc0 x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStackX ∗ R))) := by
      ac_rfl
    rw [heq2, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨⟨hpriv'_eq, hclamp, hsrk33'⟩, ⟨hpriv_eq, hclamp, hsrk33⟩, hrest_f⟩
  · right; left
    refine ⟨hpan, ?_⟩
    simp only [withLsCodeLoaded, protoChainCloneSpecX, senderChainCloneSpecX, sepConj_assoc,
      satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hp, hmem_f⟩
    refine ⟨hp, ?_⟩
    exact Satisfies.mono (by
      rw [← sepConj_assoc]
      exact sepConj_mono_left (entails_anyHeap _)) hmem_f
  · simp only [withLsCodeLoaded, protoChainCloneSpecX, sepConj_assoc] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · simp only [withLsCodeLoaded, protoChainCloneSpecX, sepConj_assoc] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

set_option maxHeartbeats 1600000 in
theorem chain_clone_epilogue_placed_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {Qp : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State)
    (srkPtr' privPtr' mkPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (keys' : List MessageKeyGhost) (ckPin' : VecPin)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : keys'.length = x.gc.2.messageKeys.length)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpc : s.pc = (blkPl_82).base + 736#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 x.gc.1.srk.bytes.length)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = srkPtr')
    (hx23 : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 x.gc.1.priv.bytes.length)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = privPtr')
    (hx9 : s.readReg64 (Reg.gpr 9#5) = mkPtr')
    (hx25 : s.readReg64 (Reg.gpr 25#5) = x25)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = x28)
    (hw27 : s.readReg32 (Reg.gpr 27#5) = w27)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPpLs (lsProg_82 H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr'
          (keys'.zip x.gc.2.messageKeys) ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpecX A).post x s0 sf))
      Qp := by
  intro _
  rw [memRegion_104_eq_slots104 x.dst, sepExists_sepConj_left]
  refine SepWPp.exists_elim fun d => ?_
  unfold savedRegsOnStack
  simp only [sepConj_assoc]
  apply SepWPp.of_sepWP (mid := s0.readReg64 (Reg.gpr 30#5))
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  apply SepWPp.done (by simp_all) (by simp_all)
  refine ⟨by simp_all, ?_, ?_⟩
  · constructor <;> simp_all
  · rw [show BitVec.truncate 32 (s.readReg64 (Reg.gpr 27#5)) = w27 from hw27]
    refine Entails.trans ?_
      (epilogue_post_entails_x A x s0 _ srkPtr' privPtr' mkPtr' x25 x28 v9 v10 v13
        w27 keys' ckPin' hsrk hmax hklen hsrc_klen (by simp_all))
    unfold savedRegsOnStack
    exact Entails.of_eq (by ac_rfl)

theorem shim_placed_ok_at_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H) :
    subroutine_ok (lsProg_82 H)
      (lsρ CryptoVerification.lsRustNoAllocShimSym)
      (withLsCl lsmpl Proofs.libsignal.Stage1X.session2ShimSpecX) :=
  hC.alloc.shim (callerProg := lsProg_82 H)

theorem alloc_placed_ok_at_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H) :
    subroutine_ok (lsProg_82 H)
      (lsρ CryptoVerification.lsRustAllocSym)
      (withLsCl lsmpl (Proofs.libsignal.Stage1X.rustAllocSpecWithStack A Stage1X.extHookStack)) :=
  hC.alloc.alloc (callerProg := lsProg_82 H)

theorem memcpy_placed_ok_at_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H) :
    subroutine_ok (lsProg_82 H)
      (lsρ CryptoVerification.lsMemcpySym)
      (withLsCl lsmpl (LibsignalTripleRatchet.sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack)) :=
  hC.memcpy (callerProg := lsProg_82 H)

theorem chain_clone_panic_800_placed_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {Q : State → SepProp → Prop}
    (hC : SerContractsXPlaced A H)
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_82).base + 800#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpLs (lsProg_82 H) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R)) :=
  fun _ => chain_clone_local1_placed_panic_800 (A := A) hC.alloc.panic_handle_error x s0 s P R hpc hrun htrace

theorem chain_clone_panic_812_placed_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {Q : State → SepProp → Prop}
    (hC : SerContractsXPlaced A H)
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_82).base + 812#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpLs (lsProg_82 H) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R)) :=
  fun _ => chain_clone_local1_placed_panic_812 (A := A) hC.alloc.panic_handle_error x s0 s P R hpc hrun htrace

theorem chain_clone_panic_824_placed_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {Q : State → SepProp → Prop}
    (hC : SerContractsXPlaced A H)
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_82).base + 824#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpLs (lsProg_82 H) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R)) :=
  fun _ => chain_clone_local1_placed_panic_824 (A := A) hC.alloc.panic_handle_error x s0 s P R hpc hrun htrace

theorem chain_clone_panic_836_placed_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {Q : State → SepProp → Prop}
    (hC : SerContractsXPlaced A H)
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_82).base + 836#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpLs (lsProg_82 H) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R)) :=
  fun _ => chain_clone_local1_placed_panic_836 (A := A) hC.alloc.panic_handle_error x s0 s P R hpc hrun htrace

theorem chain_clone_panic_848_placed_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {Q : State → SepProp → Prop}
    (hC : SerContractsXPlaced A H)
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_82).base + 848#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpLs (lsProg_82 H) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R)) :=
  fun _ => chain_clone_local1_placed_panic_848 (A := A) hC.alloc.panic_handle_error x s0 s P R hpc hrun htrace

theorem chain_clone_panic_860_placed_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {Q : State → SepProp → Prop}
    (hC : SerContractsXPlaced A H)
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_82).base + 860#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpLs (lsProg_82 H) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpecX A).onPanic x s0 sf ∗ R)) :=
  fun _ => chain_clone_local1_placed_panic_860 (A := A) hC.alloc.panic_handle_error x s0 s P R hpc hrun htrace

end Placed

end CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1
