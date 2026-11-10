/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.ChainCloneBasePart2
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.WPX
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `Chain::clone [local#1]`: Fetch Tactic, Epilogue, and Extern/Panic Helpers
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt.ChainCloneLocal1
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

theorem chainAt_eq_protoChainAt (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) :
    chainAt A gc a =
      (⌜gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗ protoChainAt A gc a) := by
  simp only [chainAt, protoChainAt, ← sepConj_assoc, pure_sepConj_pure]
  have hp :
      (PublicKey.deserialize gc.1.srk.bytes = Except.ok gc.2.senderRatchetKey ∧
        gc.2.messageKeys.length ≤ maxMessageKeys ∧
        gc.1.keys.length = gc.2.messageKeys.length ∧
        gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []) =
      ((gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []) ∧
        PublicKey.deserialize gc.1.srk.bytes = Except.ok gc.2.senderRatchetKey ∧
        gc.2.messageKeys.length ≤ maxMessageKeys ∧
        gc.1.keys.length = gc.2.messageKeys.length) := by
    exact propext ⟨fun ⟨h1, h2, h3, h4, h5⟩ => ⟨⟨h4, h5⟩, h1, h2, h3⟩,
      fun ⟨⟨h4, h5⟩, h1, h2, h3⟩ => ⟨h1, h2, h3, h4, h5⟩⟩
  rw [hp]

theorem optSenderChainAt_some_eq_chainAt (A : RustAlloc) (a : BitVec 64)
    (g : SenderChainGhost) (sc : SenderChain) :
    optSenderChainAt A a (some g) (some sc) =
      (⌜g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
        Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
        g.srk.bytes.length = 33⌝ ∗
        protoChainAt A (⟨g.srk, g.priv, g.mkCap, g.mkPtr, [], g.ck⟩,
          ⟨sc.ratchetKey.publicKey, some sc.chainKey, []⟩) a) := by
  simp only [optSenderChainAt, protoChainAt, optChainKeyAt, List.length_nil, Nat.zero_le,
    true_and, and_true, ← sepConj_assoc, pure_sepConj_pure]
  have hp :
      (PublicKey.deserialize g.srk.bytes = Except.ok sc.ratchetKey.publicKey ∧
        g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
        Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
        g.srk.bytes.length = 33) =
      ((g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
        Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
        g.srk.bytes.length = 33) ∧
        PublicKey.deserialize g.srk.bytes = Except.ok sc.ratchetKey.publicKey) := by
    exact propext ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h2, h3, h4⟩, h1⟩,
      fun ⟨⟨h2, h3, h4⟩, h1⟩ => ⟨h1, h2, h3, h4⟩⟩
  rw [hp]; rfl

theorem chainClone_of_protoChainClone
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hclone : ProtoChainCloneLocal1Ok img A ext) :
    ChainCloneLocal1Ok img A ext := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ (chainCloneSpecX A).pre x s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [chainCloneSpecX, chainAt_eq_protoChainAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
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
      s0.mem ⊨ ((protoChainCloneSpec A).inImage img).pre x s0 ∗ (⌜P_rc⌝ ∗ R) := by
    refine satisfies_inImage_pre hinv ?_
    simp only [Spec.inImage, protoChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1⟩, hmem_rearr⟩
  refine subroutine_ok.mono_outcome hclone x (⌜P_rc⌝ ∗ R) s0 hpc hrun hpre_clone hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hexit, hpost⟩ | ⟨_, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    simp only [Spec.inImage, protoChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj] at hpost
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
    simp only [Spec.inImage, protoChainCloneSpec, chainCloneSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hp, hmem_f⟩
    refine ⟨hp, ?_⟩
    exact Satisfies.mono (by
      rw [← sepConj_assoc]
      exact sepConj_mono_left (entails_anyHeap _)) hmem_f
  · simp only [Spec.inImage, protoChainCloneSpec, sepConj_assoc] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · simp only [Spec.inImage, protoChainCloneSpec, sepConj_assoc] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

theorem senderChainClone_of_chainClone
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hbridge : ∀ A a g sc, optSenderChainAt A a (some g) (some sc) =
      ⌜g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
        Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
        g.srk.bytes.length = 33⌝ ∗
      protoChainAt A (⟨g.srk, g.priv, g.mkCap, g.mkPtr, [], g.ck⟩,
        ⟨sc.ratchetKey.publicKey, some sc.chainKey, []⟩) a)
    (hclone : ProtoChainCloneLocal1Ok img A ext) :
    SenderChainCloneLocal1Ok img A ext := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ (senderChainCloneSpecX A).pre x s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [senderChainCloneSpecX, hbridge, sepConj_assoc, satisfies_pure_sepConj] at hpre
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
      s0.mem ⊨ ((protoChainCloneSpec A).inImage img).pre ⟨x.dst, x.src, gc0⟩ s0 ∗ (⌜P_sc⌝ ∗ R) := by
    refine satisfies_inImage_pre hinv ?_
    simp only [Spec.inImage, protoChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1⟩, hmem_rearr⟩
  refine subroutine_ok.mono_outcome hclone ⟨x.dst, x.src, gc0⟩ (⌜P_sc⌝ ∗ R) s0 hpc hrun hpre_clone hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hexit, hpost⟩ | ⟨_, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    simp only [Spec.inImage, protoChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj] at hpost
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
    simp only [Spec.inImage, protoChainCloneSpec, senderChainCloneSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hp, hmem_f⟩
    refine ⟨hp, ?_⟩
    exact Satisfies.mono (by
      rw [← sepConj_assoc]
      exact sepConj_mono_left (entails_anyHeap _)) hmem_f
  · simp only [Spec.inImage, protoChainCloneSpec, sepConj_assoc] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · simp only [Spec.inImage, protoChainCloneSpec, sepConj_assoc] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  fp_neg_48 fp_neg_40 fp_neg_32 fp_neg_24 fp_neg_12 fp_neg_8
  fp_neg_48_int fp_neg_40_int fp_neg_32_int fp_neg_24_int fp_neg_12_int fp_neg_8_int
attribute [local arm64_norm ↓, local wp_norm ↓]
  ChainCloneStateSimp.sp_setPC_pre ChainCloneStateSimp.sp_setMem_setPC_pre
  ChainCloneStateSimp.readReg64_setPC_pre ChainCloneStateSimp.readReg64_setMem_setPC_pre
  ChainCloneStateSimp.readReg32_setPC_pre ChainCloneStateSimp.readReg32_setMem_setPC_pre
  ChainCloneStateSimp.readReg_setPC_pre ChainCloneStateSimp.readReg_setMem_setPC_pre
attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

def hex5Str (n : Nat) : String :=
  let d (k : Nat) : Char :=
    let v := (n >>> (4 * k)) &&& 0xf
    if v < 10 then Char.ofNat ('0'.toNat + v) else Char.ofNat ('a'.toNat + v - 10)
  String.ofList [d 4, d 3, d 2, d 1, d 0]

/-- Introduces `fetch` hypotheses on `tripleRatchetProgAtExt` for instruction indices `k ∈ [kStart, kEnd)` of `Chain::clone [local#1]`. -/
elab "clone_fetches_range " b:term:max ext:term:max
    hfn:term:max kStart:num kEnd:num : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let k0 := kStart.getNat
    let k1 := kEnd.getNat
    for k in [k0:k1] do
      let byteOff := 4 * k
      let absOff := num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") + byteOff
      let decName := (`CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt.ChainCloneLocal1).str s!"chainCloneLocal1Bin_decode_{"0x" ++ String.ofList (Nat.toDigits 16 absOff)}"
      let decId := Lean.mkIdent decName
      let byteOffLit := Lean.Syntax.mkNumLit (toString byteOff)
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        have := libsignalSessionCode_fetch_fnAddr (b := $b)
          (H := Rust.withPanics $ext)
          $hfn (k := $byteOffLit) (by decide) $decId))

structure Slots104 where
  v0 : BitVec 64
  v1 : BitVec 64
  v2 : BitVec 64
  v3 : BitVec 64
  v4 : BitVec 64
  v5 : BitVec 64
  v6 : BitVec 64
  v7 : BitVec 64
  v8 : BitVec 64
  v9 : BitVec 64
  v10 : BitVec 64
  v11 : BitVec 64
  w12 : BitVec 32

theorem entails_sepExists_left {α : Type} {P : α → SepProp} {Q : SepProp}
    (h : ∀ x, P x ⊢ Q) : (∃∗ x, P x) ⊢ Q := by
  exact Entails.sepExists_elim h

theorem entails_sepExists_sepConj_left {α : Type} {P : α → SepProp} {Q R : SepProp}
    (h : ∀ x, P x ∗ Q ⊢ R) : (∃∗ x, P x) ∗ Q ⊢ R := by
  rw [sepExists_sepConj_left]
  exact entails_sepExists_left h

theorem entails_pull_exists {α : Type} {A : SepProp} {P : α → SepProp} {Q R : SepProp}
    (h : ∀ x, (A ∗ P x) ∗ Q ⊢ R) : A ∗ (∃∗ x, P x) ∗ Q ⊢ R := by
  rw [← sepConj_assoc, sepExists_sepConj_right, sepExists_sepConj_left]
  exact entails_sepExists_left h

theorem memRegion_104_eq_slots104 (ptr : BitVec 64) :
    memRegion ptr 104 =
      ∃∗ d : Slots104,
        (ptr ↦₆₄ d.v0) ∗
        ((ptr + 8#64) ↦₆₄ d.v1) ∗
        ((ptr + 16#64) ↦₆₄ d.v2) ∗
        ((ptr + 24#64) ↦₆₄ d.v3) ∗
        ((ptr + 32#64) ↦₆₄ d.v4) ∗
        ((ptr + 40#64) ↦₆₄ d.v5) ∗
        ((ptr + 48#64) ↦₆₄ d.v6) ∗
        ((ptr + 56#64) ↦₆₄ d.v7) ∗
        ((ptr + 64#64) ↦₆₄ d.v8) ∗
        ((ptr + 72#64) ↦₆₄ d.v9) ∗
        ((ptr + 80#64) ↦₆₄ d.v10) ∗
        ((ptr + 88#64) ↦₆₄ d.v11) ∗
        ((ptr + 96#64) ↦₃₂ d.w12) ∗
        memRegion (ptr + 100#64) 4 := by
  rw [memRegion_104_eq_slots ptr]
  apply sepProp_eq_of_entails
  · refine entails_sepExists_sepConj_left fun v0 => ?_
    refine entails_pull_exists fun v1 => ?_
    refine entails_pull_exists fun v2 => ?_
    refine entails_pull_exists fun v3 => ?_
    refine entails_pull_exists fun v4 => ?_
    refine entails_pull_exists fun v5 => ?_
    refine entails_pull_exists fun v6 => ?_
    refine entails_pull_exists fun v7 => ?_
    refine entails_pull_exists fun v8 => ?_
    refine entails_pull_exists fun v9 => ?_
    refine entails_pull_exists fun v10 => ?_
    refine entails_pull_exists fun v11 => ?_
    refine entails_pull_exists fun w12 => ?_
    apply Entails.sepExists_right ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, w12⟩
    dsimp only
    simp only [sepConj_assoc]
    exact Entails.refl _
  · refine entails_sepExists_left fun d => ?_
    exact sepConj_mono (Entails.sepExists_right d.v0 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v1 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v2 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v3 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v4 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v5 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v6 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v7 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v8 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v9 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v10 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v11 (Entails.refl _))
      (sepConj_mono_left (Entails.sepExists_right d.w12 (Entails.refl _))))))))))))))

theorem epilogue_post_entails (A : RustAlloc) (x : ChainCloneGhost) (s0 sf : State)
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
      stackAt (s0.sp - 208#64) extHookStack ∗
      spillSlotsExist s0.sp ∗
      ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
      ((s0.sp - 136#64) ↦₆₄ v9) ∗
      ((s0.sp - 128#64) ↦₆₄ v10) ∗
      ((s0.sp - 104#64) ↦₆₄ v13) ∗
      savedRegsOnStack s0) ⊢
      (protoChainCloneSpec A).post x s0 sf := by
  unfold protoChainCloneSpec
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
  have hst := fold_stackAt_chainClone s0
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
        stackAt (s0.sp - 208#64) extHookStack ∗
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
       (stackAt (s0.sp - 208#64) extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)) := by
    ac_rfl
  rw [hgroup]
  exact sepConj_mono hg' (sepConj_mono_right (sepConj_mono_right hst))

set_option maxHeartbeats 1200000 in
theorem chain_clone_epilogue {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State)
    (srkPtr' privPtr' mkPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (keys' : List MessageKeyGhost) (ckPin' : VecPin)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : keys'.length = x.gc.2.messageKeys.length)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr chainCloneLocal1Name + 736#64)
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
    SepWPpX img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr'
          (keys'.zip x.gc.2.messageKeys) ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) extHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (protoChainCloneSpec A).post x s0 sf))
      Qp := by
  have hfn : libsignalSessionCode.fnOff chainCloneLocal1Name = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") :=
    fnOff_chainCloneLocal1
  clone_fetches_range img.base ext hfn 184 200
  clear hfn
  unfold tripleRatchetProgAtExt at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr chainCloneLocal1Name = entry
  examples_hide_fetches
  rw [memRegion_104_eq_slots104 x.dst, sepExists_sepConj_left]
  refine SepWPpX.exists_elim fun d => ?_
  unfold savedRegsOnStack
  simp only [sepConj_assoc]
  apply SepWPpX.of_sepWP (mid := s0.readReg64 (Reg.gpr 30#5))
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  apply SepWPpX.done (by simp_all) (by simp_all)
  refine ⟨by simp_all, ?_, ?_⟩
  · constructor <;> simp_all
  · rw [show BitVec.truncate 32 (s.readReg64 (Reg.gpr 27#5)) = w27 from hw27]
    refine Entails.trans ?_
      (epilogue_post_entails A x s0 _ srkPtr' privPtr' mkPtr' x25 x28 v9 v10 v13
        w27 keys' ckPin' hsrk hmax hklen hsrc_klen (by simp_all))
    unfold savedRegsOnStack
    exact Entails.of_eq (by ac_rfl)

/-! ## Extern Hook and Panic Tail Lemmas -/

/-- No-op shim spec that records trace preservation. -/
def sessionShimSpec (A : RustAlloc) : Spec Unit where
  pre := fun _ s0 => A.pool ∗ stackAt s0.sp extHookStack
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp extHookStack

def sessionMemcpySpec (A : RustAlloc) : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
     s0.readReg64 .x1 = src ∧
     (s0.readReg64 .x2).toNat = bs.length⌝ ∗
    memRegion dst bs.length ∗
    (src ↦ₛ bs) ∗
    A.pool ∗ stackAt s0.sp extHookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
    (dst ↦ₛ bs) ∗
    (src ↦ₛ bs) ∗
    A.pool ∗ stackAt s0.sp extHookStack

theorem panic_at_handle_error {img : Obj.Image}
    {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt img.base ext).externAt?
      ((tripleRatchetProgAtExt img.base ext).fnAddr chainCloneLocal1Name + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]")) =
      some Rust.panicked :=
  panic_at_panicSymbol fnOff_chainCloneLocal1 (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]")) (by decide)
    (by decide) (ls_hook% "alloc::raw_vec::handle_error") (by simp [Rust.isPanicSymbol])

theorem shim_ok_at {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr chainCloneLocal1Name + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
      ((sessionShimSpec A).inImage img) := by
  have hraw := hA.session_shim_ok_at chainCloneLocal1Name
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
    (hk := by simp only [fnOff_chainCloneLocal1, shimName, arm64_norm])
  refine subroutine_ok_frame_weaken_inImage (fun _ _ => A.pool) hraw
    (fun _ _ => ?_) (fun _ _ _ => ?_) (fun _ _ _ => Entails.pure_left False.elim)
  · simp only [sessionShimSpec, withStack, LibsignalTripleRatchet.sessionShimSpec, emp_sepConj]
    exact Entails.of_eq (by ac_rfl)
  · simp only [sessionShimSpec, withStack, LibsignalTripleRatchet.sessionShimSpec]
    exact Entails.of_eq (by ac_rfl)

theorem alloc_ok_at {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr chainCloneLocal1Name + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
      ((rustAllocSpecWithStack A extHookStack).inImage img) :=
  hA.alloc_ok_at chainCloneLocal1Name
    (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
    (hk := by simp only [fnOff_chainCloneLocal1, allocName, arm64_norm])

theorem memcpy_ok_at {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr chainCloneLocal1Name + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
      ((sessionMemcpySpec A).inImage img) := by
  have hraw := hA.session_memcpy_ok_at chainCloneLocal1Name
    (num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
    (hk := by simp only [fnOff_chainCloneLocal1, memcpyName, arm64_norm])
  refine subroutine_ok_frame_weaken_inImage (fun _ _ => A.pool) hraw
    (fun _ _ => ?_) (fun _ _ _ => ?_) (fun _ _ _ => Entails.pure_left False.elim)
  · simp only [sessionMemcpySpec, LibsignalTripleRatchet.sessionMemcpySpec, libcMemcpySpec]
    exact Entails.of_eq (by ac_rfl)
  · simp only [sessionMemcpySpec, LibsignalTripleRatchet.sessionMemcpySpec, libcMemcpySpec]
    exact Entails.of_eq (by ac_rfl)

theorem allocFailedIn_of_eq {s0 sf : State}
    (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  refine ⟨?_, ⟨[allocFailedEvent], h.symm⟩⟩
  simp [allocFailedIn, h]

theorem ofNat_ne_zero_of_pos {n : Nat} (hpos : 0 < n) (h64 : n < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64] at ht
  change n = 0 at ht
  omega

theorem beq_ofNat_zero_eq_false {n : Nat} (hpos : 0 < n) (h64 : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact ofNat_ne_zero_of_pos hpos h64

theorem sepWP_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {post : State → SepProp → Prop}
    (h : φ → SepWP prog ret s (A ∗ B ∗ C) post) :
    SepWP prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) post := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWP.pure_elim h

theorem sepWPp_pure_mid {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPpX img prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPpX img prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPpX.pure_elim h

theorem chain_clone_panic_800 {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr chainCloneLocal1Name + 800#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff chainCloneLocal1Name = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") :=
    fnOff_chainCloneLocal1
  have hpanic := panic_at_handle_error (img := img) (ext := ext)
  clone_fetches_range img.base ext hfn 200 203
  clear hfn
  unfold tripleRatchetProgAtExt at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr chainCloneLocal1Name = entry
  examples_hide_fetches
  apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPpX.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

theorem chain_clone_panic_812 {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr chainCloneLocal1Name + 812#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff chainCloneLocal1Name = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") :=
    fnOff_chainCloneLocal1
  have hpanic := panic_at_handle_error (img := img) (ext := ext)
  clone_fetches_range img.base ext hfn 203 206
  clear hfn
  unfold tripleRatchetProgAtExt at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr chainCloneLocal1Name = entry
  examples_hide_fetches
  apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPpX.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

theorem chain_clone_panic_824 {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr chainCloneLocal1Name + 824#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff chainCloneLocal1Name = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") :=
    fnOff_chainCloneLocal1
  have hpanic := panic_at_handle_error (img := img) (ext := ext)
  clone_fetches_range img.base ext hfn 206 209
  clear hfn
  unfold tripleRatchetProgAtExt at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr chainCloneLocal1Name = entry
  examples_hide_fetches
  apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPpX.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

theorem chain_clone_panic_836 {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr chainCloneLocal1Name + 836#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff chainCloneLocal1Name = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") :=
    fnOff_chainCloneLocal1
  have hpanic := panic_at_handle_error (img := img) (ext := ext)
  clone_fetches_range img.base ext hfn 209 212
  clear hfn
  unfold tripleRatchetProgAtExt at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr chainCloneLocal1Name = entry
  examples_hide_fetches
  apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPpX.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

theorem chain_clone_panic_848 {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr chainCloneLocal1Name + 848#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff chainCloneLocal1Name = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") :=
    fnOff_chainCloneLocal1
  have hpanic := panic_at_handle_error (img := img) (ext := ext)
  clone_fetches_range img.base ext hfn 212 215
  clear hfn
  unfold tripleRatchetProgAtExt at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr chainCloneLocal1Name = entry
  examples_hide_fetches
  apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPpX.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

theorem chain_clone_panic_860 {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr chainCloneLocal1Name + 860#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn : libsignalSessionCode.fnOff chainCloneLocal1Name = num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]") :=
    fnOff_chainCloneLocal1
  have hpanic := panic_at_handle_error (img := img) (ext := ext)
  clone_fetches_range img.base ext hfn 215 218
  clear hfn
  unfold tripleRatchetProgAtExt at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr chainCloneLocal1Name = entry
  examples_hide_fetches
  apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPpX.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt.ChainCloneLocal1
