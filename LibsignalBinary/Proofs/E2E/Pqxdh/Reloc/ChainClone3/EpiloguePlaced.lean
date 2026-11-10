/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.RelocCodeSym
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneBase
import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneEpilogue
import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.SepLogic.WPp

/-!
# Relocatable Epilogue and Panic Tails for `Chain::clone [local#3]` (Block `468`)

Program-generic `protoChainCloneSpec` lifts (`chainClone_of_protoChainClone_gen`,
`senderChainClone_of_chainClone_gen`) and Block `468` epilogue (`+736..+796`) / allocation-failure
panic-tail (`+800..+860`) lemmas under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.LibsignalTripleRatchet.ChainClone3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  fp_neg_48 fp_neg_40 fp_neg_32 fp_neg_24 fp_neg_12 fp_neg_8
  fp_neg_48_int fp_neg_40_int fp_neg_32_int fp_neg_24_int fp_neg_12_int fp_neg_8_int
attribute [local arm64_norm ↓, local wp_norm ↓]
  BS5.sp_setPC_pre BS5.sp_setMem_setPC_pre
  BS5.readReg64_setPC_pre BS5.readReg64_setMem_setPC_pre
  BS5.readReg32_setPC_pre BS5.readReg32_setMem_setPC_pre
  BS5.readReg_setPC_pre BS5.readReg_setMem_setPC_pre
attribute [local simp, local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

/-! ## 1. Program-Generic `protoChainCloneSpec` -> `chainCloneSpec` / `senderChainCloneSpec` Bridges -/

theorem chainClone_of_protoChainClone_gen {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hclone : subroutine_ok prog entry (protoChainCloneSpec A)) :
    subroutine_ok prog entry (chainCloneSpec A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [chainCloneSpec, chainAt_eq_protoChainAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hmem⟩
  set P_rc : Prop := x.gc.1.srk.bytes.length = 33 ∧ x.gc.1.priv.bytes = []
  change s0.mem ⊨ memRegion x.dst 104 ∗ ⌜P_rc⌝ ∗ protoChainAt A x.gc x.src ∗
    A.pool ∗ stackAt s0.sp chainCloneStack ∗ R at hmem
  have hmem_rearr :
      s0.mem ⊨
        memRegion x.dst 104 ∗ protoChainAt A x.gc x.src ∗
        A.pool ∗ stackAt s0.sp chainCloneStack ∗ (⌜P_rc⌝ ∗ R) := by
    have heq :
        (memRegion x.dst 104 ∗ ⌜P_rc⌝ ∗ protoChainAt A x.gc x.src ∗
          A.pool ∗ stackAt s0.sp chainCloneStack ∗ R) =
        (memRegion x.dst 104 ∗ protoChainAt A x.gc x.src ∗
          A.pool ∗ stackAt s0.sp chainCloneStack ∗ (⌜P_rc⌝ ∗ R)) := by
      ac_rfl
    rwa [← heq]
  have hpre_clone :
      s0.mem ⊨ (protoChainCloneSpec A).pre x s0 ∗ (⌜P_rc⌝ ∗ R) := by
    simp only [protoChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1⟩, hmem_rearr⟩
  refine hclone.mono_outcome x (⌜P_rc⌝ ∗ R) s0 hpc hrun hpre_clone hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hexit, hpost⟩ | ⟨_, hoom⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    simp only [protoChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htrace, hmem_f⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hmem_f
    rcases hmem_f with ⟨g', hmem_f⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hmem_f
    rcases hmem_f with ⟨⟨hsrk', hpriv', hkeys'⟩, hmem_f⟩
    have hpure_front :
        sf.mem ⊨
          ⌜P_rc⌝ ∗
          (protoChainAt A (g', x.gc.2) x.dst ∗ protoChainAt A x.gc x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStack ∗ R) := by
      have heq :
          (protoChainAt A (g', x.gc.2) x.dst ∗ protoChainAt A x.gc x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStack ∗ ⌜P_rc⌝ ∗ R) =
          (⌜P_rc⌝ ∗
            (protoChainAt A (g', x.gc.2) x.dst ∗ protoChainAt A x.gc x.src ∗
              A.pool ∗ stackAt s0.sp chainCloneStack ∗ R)) := by
        ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hpure_front
    rcases hpure_front with ⟨⟨hsrk33, hpriv_nil⟩, hrest_f⟩
    simp only [chainCloneSpec, sepConj_assoc, satisfies_pure_sepConj]
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
      A.pool ∗ stackAt s0.sp chainCloneStack ∗ R
    have heq2 :
        ((⌜P_rc'⌝ ∗ protoChainAt A (g', x.gc.2) x.dst) ∗
          (⌜P_rc⌝ ∗ protoChainAt A x.gc x.src) ∗
          A.pool ∗ stackAt s0.sp chainCloneStack ∗ R) =
        (⌜P_rc'⌝ ∗ (⌜P_rc⌝ ∗
          (protoChainAt A (g', x.gc.2) x.dst ∗ protoChainAt A x.gc x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStack ∗ R))) := by
      ac_rfl
    rw [heq2, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨⟨hsrk33', hpriv_nil'⟩, ⟨hsrk33, hpriv_nil⟩, hrest_f⟩
  · right; left
    refine ⟨hpan, ?_⟩
    simp only [protoChainCloneSpec, chainCloneSpec, sepConj_assoc,
      satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hp, hmem_f⟩
    refine ⟨hp, ?_⟩
    exact Satisfies.mono (by
      rw [← sepConj_assoc]
      exact sepConj_mono_left (entails_anyHeap _)) hmem_f
  · right; right; left
    exact ⟨code, hexit, by
      simp only [protoChainCloneSpec] at hpost
      exact False.elim (not_satisfies_false_sepConj hpost)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem senderChainClone_of_chainClone_gen {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hbridge : ∀ A a g sc, optSenderChainAt A a (some g) (some sc) =
      ⌜g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
        Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
        g.srk.bytes.length = 33⌝ ∗
      protoChainAt A (⟨g.srk, g.priv, g.mkCap, g.mkPtr, [], g.ck⟩,
        ⟨sc.ratchetKey.publicKey, some sc.chainKey, []⟩) a)
    (hclone : subroutine_ok prog entry (protoChainCloneSpec A)) :
    subroutine_ok prog entry (senderChainCloneSpec A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [senderChainCloneSpec, hbridge, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hmem⟩
  let P_sc : Prop :=
    x.g.priv.bytes = x.sc.ratchetKey.privateKey.bytes.toList ∧
      Ratchet.clampScalar x.sc.ratchetKey.privateKey.bytes = x.sc.ratchetKey.privateKey.bytes ∧
      x.g.srk.bytes.length = 33
  let gc_init : ChainGhost × ReceiverChain :=
    (⟨x.g.srk, x.g.priv, x.g.mkCap, x.g.mkPtr, [], x.g.ck⟩,
      ⟨x.sc.ratchetKey.publicKey, some x.sc.chainKey, []⟩)
  change s0.mem ⊨ memRegion x.dst 104 ∗ ⌜P_sc⌝ ∗ protoChainAt A gc_init x.src ∗
    A.pool ∗ stackAt s0.sp chainCloneStack ∗ R at hmem
  have hmem_rearr :
      s0.mem ⊨
        memRegion x.dst 104 ∗ protoChainAt A gc_init x.src ∗
        A.pool ∗ stackAt s0.sp chainCloneStack ∗ (⌜P_sc⌝ ∗ R) := by
    have heq :
        (memRegion x.dst 104 ∗ ⌜P_sc⌝ ∗ protoChainAt A gc_init x.src ∗
          A.pool ∗ stackAt s0.sp chainCloneStack ∗ R) =
        (memRegion x.dst 104 ∗ protoChainAt A gc_init x.src ∗
          A.pool ∗ stackAt s0.sp chainCloneStack ∗ (⌜P_sc⌝ ∗ R)) := by
      ac_rfl
    rwa [← heq]
  have hpre_clone :
      s0.mem ⊨ (protoChainCloneSpec A).pre ⟨x.dst, x.src, gc_init⟩ s0 ∗ (⌜P_sc⌝ ∗ R) := by
    simp only [protoChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1⟩, hmem_rearr⟩
  refine hclone.mono_outcome ⟨x.dst, x.src, gc_init⟩ (⌜P_sc⌝ ∗ R) s0 hpc hrun hpre_clone hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hexit, hpost⟩ | ⟨_, hoom⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    simp only [protoChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htrace, hmem_f⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hmem_f
    rcases hmem_f with ⟨g', hmem_f⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hmem_f
    rcases hmem_f with ⟨⟨hsrk', hpriv', hkeys'⟩, hmem_f⟩
    have hkeys_nil : g'.keys = [] := List.eq_nil_of_length_eq_zero hkeys'
    have hpure_front :
        sf.mem ⊨
          ⌜P_sc⌝ ∗
          (protoChainAt A (g', gc_init.2) x.dst ∗ protoChainAt A gc_init x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStack ∗ R) := by
      have heq :
          (protoChainAt A (g', gc_init.2) x.dst ∗ protoChainAt A gc_init x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStack ∗ ⌜P_sc⌝ ∗ R) =
          (⌜P_sc⌝ ∗
            (protoChainAt A (g', gc_init.2) x.dst ∗ protoChainAt A gc_init x.src ∗
              A.pool ∗ stackAt s0.sp chainCloneStack ∗ R)) := by
        ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hpure_front
    rcases hpure_front with ⟨⟨hpriv_eq, hclamp, hsrk33⟩, hrest_f⟩
    let sg' : SenderChainGhost := ⟨g'.srk, g'.priv, g'.mkCap, g'.mkPtr, g'.ck⟩
    have hg'_eq : g' = ⟨sg'.srk, sg'.priv, sg'.mkCap, sg'.mkPtr, [], sg'.ck⟩ := by
      cases g'; dsimp [sg'] at hkeys_nil ⊢; subst hkeys_nil; rfl
    rw [hg'_eq] at hrest_f
    simp only [senderChainCloneSpec, sepConj_assoc, satisfies_pure_sepConj]
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
      (⟨sg'.srk, sg'.priv, sg'.mkCap, sg'.mkPtr, [], sg'.ck⟩, gc_init.2)
    change sf.mem ⊨
      (⌜P_sc'⌝ ∗ protoChainAt A gc' x.dst) ∗
      (⌜P_sc⌝ ∗ protoChainAt A gc_init x.src) ∗
      A.pool ∗ stackAt s0.sp chainCloneStack ∗ R
    have heq2 :
        ((⌜P_sc'⌝ ∗ protoChainAt A gc' x.dst) ∗
          (⌜P_sc⌝ ∗ protoChainAt A gc_init x.src) ∗
          A.pool ∗ stackAt s0.sp chainCloneStack ∗ R) =
        (⌜P_sc'⌝ ∗ (⌜P_sc⌝ ∗
          (protoChainAt A gc' x.dst ∗ protoChainAt A gc_init x.src ∗
            A.pool ∗ stackAt s0.sp chainCloneStack ∗ R))) := by
      ac_rfl
    rw [heq2, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨⟨hpriv'_eq, hclamp, hsrk33'⟩, ⟨hpriv_eq, hclamp, hsrk33⟩, hrest_f⟩
  · right; left
    refine ⟨hpan, ?_⟩
    simp only [protoChainCloneSpec, senderChainCloneSpec, sepConj_assoc,
      satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hp, hmem_f⟩
    refine ⟨hp, ?_⟩
    exact Satisfies.mono (by
      rw [← sepConj_assoc]
      exact sepConj_mono_left (entails_anyHeap _)) hmem_f
  · right; right; left
    exact ⟨code, hexit, by
      simp only [protoChainCloneSpec] at hpost
      exact False.elim (not_satisfies_false_sepConj hpost)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## 2. Epilogue & Panic Tail Lemmas on Block `468` -/

theorem chain_clone3_placed_epilogue [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (x : ChainCloneGhost) (s0 s : State)
    (srkPtr' privPtr' mkPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (keys' : List MessageKeyGhost) (ckPin' : VecPin)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : keys'.length = x.gc.2.messageKeys.length)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (hpc : s.pc = (blkPl_468).base + 736#64)
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
    SepWPp ((blkPC_468).rebase (blkPl_468).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 104 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr'
          (keys'.zip x.gc.2.messageKeys) ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
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
      (epilogue_post_entails A x s0 _ srkPtr' privPtr' mkPtr' x25 x28 v9 v10 v13
        w27 keys' ckPin' hsrk hmax hklen hsrc_klen (by simp_all))
    unfold savedRegsOnStack
    exact Entails.of_eq (by ac_rfl)

theorem panic_at_handle_error3_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    ((blkPC_468).rebase (blkPl_468).base H).externAt? (lsρ lsHandleErrorSym) =
      some Rust.panicked := by
  rw [ls_externAt?_of_mem, hpanic]

theorem chain_clone3_placed_panic_800 [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_468).base + 800#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_468).rebase (blkPl_468).base H) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hp := panic_at_handle_error3_placed hpanic
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hp) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

theorem chain_clone3_placed_panic_812 [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_468).base + 812#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_468).rebase (blkPl_468).base H) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hp := panic_at_handle_error3_placed hpanic
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hp) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

theorem chain_clone3_placed_panic_824 [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_468).base + 824#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_468).rebase (blkPl_468).base H) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hp := panic_at_handle_error3_placed hpanic
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hp) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

theorem chain_clone3_placed_panic_836 [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_468).base + 836#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_468).rebase (blkPl_468).base H) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hp := panic_at_handle_error3_placed hpanic
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hp) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

theorem chain_clone3_placed_panic_848 [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_468).base + 848#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_468).rebase (blkPl_468).base H) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hp := panic_at_handle_error3_placed hpanic
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hp) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

theorem chain_clone3_placed_panic_860 [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : ChainCloneGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_468).base + 860#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_468).rebase (blkPl_468).base H) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (protoChainCloneSpec A).onPanic x s0 sf ∗ R)) := by
  have hp := panic_at_handle_error3_placed hpanic
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hp) fun hm => ?_
  simpa only [protoChainCloneSpec, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

end CryptoVerification.LibsignalTripleRatchet.ChainClone3
