/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.ChainKey.FindReceiverChainKey
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.TripleRatchet.ChainKey.ChainKeyCodeSym
import ProofLib.SepLogic.WP.Apply

/-!
# Relocatable `VmPreserved` Contract for `RatchetState::find_receiver_chain_key` (Block `25`)

Verifies `<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_key` (Block `25`,
zero heap allocations) against `findReceiverChainKeyPlacedAllocSpec` and its `RustCliAllocBudget M`
specialization `findReceiverChainKeyPlacedSpec` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.ChainKey.FindReceiverChainKeyBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement LibsignalRoLoaded
  blkLib_eq_25 blkPC_25 blkPl_25
  libsignalRoLoaded_of_keepsFrozen lsBlackBoxU8Sym lsLogFilterAddr lsmpl lsro_intro_chk
  ls_subroutine_ok_of_block withLsCodeLoaded extract_withLsCodeLoaded
)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open LibsignalBinary.Heap (AllocCostModel RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs
open LibsignalBinary.Proofs.ConsumeMessageKey
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  mul_104_eq setWidth_32_16_of_64 setWidth_32_8_of_64 setWidth_16_of_64
  setWidth_8_of_64 setWidth_32_of_64 setWidth_16_of_32

@[local arm64_norm]
private theorem setWidth_8_of_32 (v : BitVec 8) :
    (BitVec.setWidth 32 v).setWidth 8 = v := by bv_bits

private theorem entails_of_eq {P P' Q : SepProp} (h : P = P') (hq : P' ⊢ Q) : P ⊢ Q :=
  h ▸ hq

private theorem SepWPp_conseq_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P ⊢ P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp :=
  fun R hm hL => h R (Satisfies.mono (sepConj_mono_left hP) hm) hL

private theorem SepWPp_eq_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp :=
  hP ▸ h

private theorem mr_cut' (sp : BitVec 64) (c c' n k N : Nat) (hN : n + k = N) (hc' : c - n = c')
    (hn : n ≤ c) (hc : c < 2 ^ 64) (h : N ≤ 2 ^ 64) :
    memRegion (sp - BitVec.ofNat 64 c) N =
      memRegion (sp - BitVec.ofNat 64 c) n ∗ memRegion (sp - BitVec.ofNat 64 c') k := by
  subst hN hc'
  refine memRegion_split' rfl ?_ h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have h1 : c % 2 ^ 64 = c := Nat.mod_eq_of_lt hc
  have h2 : (c - n) % 2 ^ 64 = c - n := Nat.mod_eq_of_lt (by omega)
  have h3 : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2, h3]
  omega

private theorem stackAt_findReceiverChainKeyStack (sp : BitVec 64) :
    stackAt sp findReceiverChainKeyStack =
      memRegion (sp - 2048#64) 944 ∗
      stackAt (sp - 80#64) 1024 ∗
      memRegion (sp - 80#64) 32 ∗
      (∃∗ v29 : BitVec 64, (sp - 48#64) ↦₆₄ v29) ∗
      (∃∗ v30 : BitVec 64, (sp - 40#64) ↦₆₄ v30) ∗
      (∃∗ v21 : BitVec 64, (sp - 32#64) ↦₆₄ v21) ∗
      memRegion (sp - 24#64) 8 ∗
      (∃∗ v20 : BitVec 64, (sp - 16#64) ↦₆₄ v20) ∗
      (∃∗ v19 : BitVec 64, (sp - 8#64) ↦₆₄ v19) := by
  unfold stackAt findReceiverChainKeyStack
  rw [mr_cut' sp 2048 1104 944 1104 2048 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 1104 80 1024 80 1104 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 80 48 32 48 80 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 48 40 8 40 48 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 40 32 8 32 40 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 32 24 8 24 32 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 24 16 8 16 24 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 16 8 8 8 16 rfl rfl (by decide) (by decide) (by decide)]
  rw [memRegion_eight (sp - 48#64), memRegion_eight (sp - 40#64), memRegion_eight (sp - 32#64),
      memRegion_eight (sp - 16#64), memRegion_eight (sp - 8#64)]
  have h1104 : sp - 80#64 - 1024#64 = sp - 1104#64 := by bv_omega
  rw [h1104]

private theorem stackAt_findReceiverChainKeyStack_repack (sp : BitVec 64)
    (v29 v30 v21 v20 v19 : BitVec 64) :
    memRegion (sp - 2048#64) 944 ∗
    stackAt (sp - 80#64) 1024 ∗
    memRegion (sp - 80#64) 32 ∗
    ((sp - 48#64) ↦₆₄ v29) ∗
    ((sp - 40#64) ↦₆₄ v30) ∗
    ((sp - 32#64) ↦₆₄ v21) ∗
    memRegion (sp - 24#64) 8 ∗
    ((sp - 16#64) ↦₆₄ v20) ∗
    ((sp - 8#64) ↦₆₄ v19) ⊢
      stackAt sp findReceiverChainKeyStack := by
  rw [stackAt_findReceiverChainKeyStack sp]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  refine sepConj_mono (Entails.sepExists_intro v29)
    (sepConj_mono (Entails.sepExists_intro v30)
      (sepConj_mono (Entails.sepExists_intro v21)
        (sepConj_mono_right (sepConj_mono (Entails.sepExists_intro v20)
          (Entails.sepExists_intro v19)))))

private theorem cap_add_one_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h1
  omega

local macro "findReceiverChainKey_cc_close" : tactic => `(tactic| (
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, applyWriteback,
    State.advancePC_eq_setPC, State.setPC_setPC, State.writeReg64_setPC, State.setPState_setPC,
    State.setPState_setPState, State.writeReg64_setPState, State.setMem_setPC, State.setMem_setMem,
    State.writeReg64_setMem, State.setPState_setMem, State.writeReg64_writeReg64_same,
    State.writeVReg128_setPC, State.writeVReg128_setPState, State.writeVReg128_setMem,
    arm64_norm, *]
  done))

/-- `VmPreserved`-strengthened relocatable specification of `RatchetState::find_receiver_chain_key`
(Block `25`, zero heap allocations). -/
def findReceiverChainKeyPlacedAllocSpec [LibsignalPlacement] (A : RustAlloc) :
    Spec FindReceiverChainKeyGhost :=
  withVmPreserved (CryptoVerification.LibsignalTripleRatchet.findReceiverChainKeyPlacedSpec A)

/-- Budget-allocator (`RustCliAllocBudget M`) specialization of
`findReceiverChainKeyPlacedAllocSpec` via `A.repAlloc`. -/
def findReceiverChainKeyPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) : Spec FindReceiverChainKeyGhost :=
  findReceiverChainKeyPlacedAllocSpec A.repAlloc

private theorem sepWPp_seq_lscl_ro {prog : Program} {ret mid : BitVec 64} {s : State} {P : SepProp}
    {pl : Obj.MultiPlacement} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem) (hro : LibsignalRoLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded pl sm.mem ∧ LibsignalRoLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen
    (fun (m _ : Memory) (hf : LibsignalCodeLoaded pl m ∧ LibsignalRoLoaded pl m) hkf =>
      ⟨hf.1.of_keepsFrozen hkf, libsignalRoLoaded_of_keepsFrozen hf.2 hkf⟩)
    ⟨hcl, hro⟩
    h

private theorem byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r
      fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hi' : i < xs.length := hi
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi']
      | case2 i r hni =>
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private theorem toUTF8_data_toList (s : String) :
    s.toUTF8.data.toList = s.toList.flatMap String.utf8EncodeChar := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [List.utf8Encode]

private theorem lsroCheck_missingReceiverChainKey :
    CryptoVerification.lsroCheck "libsignal_protocol:.rodata..Lanon.290"
      (invalidSessionStructureStr .missingReceiverChainKey) = true := by
  have h :
      invalidSessionStructureStr .missingReceiverChainKey =
        ("missing receiver chain key".toList.flatMap String.utf8EncodeChar).map
          fun b => BitVec.ofNat 8 b.toNat := by
    unfold invalidSessionStructureStr utf8
    dsimp only
    rw [byteArray_toList_eq_data, toUTF8_data_toList]
  rw [h]
  exact eagerReduce (Eq.refl true)

private theorem sepWPp_intro_rodata_missingReceiverChainKey_placed [LibsignalPlacement]
    {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (h : SepWPp prog ret s
      (((lsmpl.ρ "libsignal_protocol:.rodata..Lanon.290") ↦ᵣ
          invalidSessionStructureStr .missingReceiverChainKey) ∗ P)
      Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' :
      s.mem ⊨
        (((lsmpl.ρ "libsignal_protocol:.rodata..Lanon.290") ↦ᵣ
            invalidSessionStructureStr .missingReceiverChainKey) ∗ P) ∗ R := by
    rw [sepConj_assoc]
    exact lsro_intro_chk hro lsroCheck_missingReceiverChainKey hm
  exact h R hm' hL

private theorem findIndex_alloc_placed_ok_at_state [LibsignalPlacement] {prog : Program}
    {A : RustAlloc} {addr : BitVec 64} {s : State}
    (hfind : subroutine_ok prog addr (withLsCodeLoaded lsmpl (LoopBudget.findPlacedAllocSpec A)))
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    subroutine_ok prog addr
      ({ pre := fun (p, cs, theirA, their) s' =>
          ⌜s'.mem = s.mem ∧
            s'.readReg64 .x0 = p ∧ (s'.readReg64 .x1).toNat = cs.length ∧ s'.readReg64 .x2 = theirA ∧
            cs.length * 104 < 2 ^ 63⌝ ∗
          arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s'.sp 1024
         post := fun (p, cs, theirA, their) s0 sf =>
          ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace ∧
            (match (cs.map (·.2)).findIdx? (fun c => c.senderRatchetKey == their) with
             | some i => sf.readReg64 .x0 = 1#64 ∧ (sf.readReg64 .x1).toNat = i
             | none => sf.readReg64 .x0 = 0#64)⌝ ∗
          arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp 1024 } : Spec FindIndexGhost) := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨p, cs, theirA, their⟩ R s0 hpc hrun hm hsp
  refine hfind.mono_outcome (p, cs, theirA, their) R s0 hpc hrun ?_ hsp fun sf hout => ?_
  · dsimp only [withLsCodeLoaded, LoopBudget.findPlacedAllocSpec, withVmPreserved,
      FindReceiverChainIndex.findPlacedSpec] at hm ⊢
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm
    rcases hm with ⟨⟨hmem, hx0, hx1, hx2, hlt⟩, hspatial⟩
    refine ⟨hmem ▸ hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hlt, hsp⟩, hspatial⟩
  · rcases hout with ⟨hret, hcc, hpost⟩ | hrest
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withLsCodeLoaded, LoopBudget.findPlacedAllocSpec, withVmPreserved,
        FindReceiverChainIndex.findPlacedSpec] at hpost ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hpost.1, hpost.2.1.1, hpost.2.1.2⟩, hpost.2.2⟩
    · exact Or.inr hrest

set_option maxHeartbeats 1600000 in
theorem find_receiver_chain_key_alloc_placed_ok_of_find_index [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (hfind : subroutine_ok ((blkPC_25).rebase (blkPl_25).base H) (lsmpl.base 26)
      (withLsCodeLoaded lsmpl (LoopBudget.findPlacedAllocSpec A))) :
    subroutine_ok ((blkPC_25).rebase (blkPl_25).base H) (blkPl_25).base
      (withLsCodeLoaded lsmpl (findReceiverChainKeyPlacedAllocSpec A)) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp0
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [findReceiverChainKeyPlacedAllocSpec, withVmPreserved,
    CryptoVerification.LibsignalTripleRatchet.findReceiverChainKeyPlacedSpec,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hro0, hx0, hx1, hx8⟩, hmem⟩
  refine ⟨ratchetAt A x.self x.G x.st ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗ memRegion x.ret 40 ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp findReceiverChainKeyStack, R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  apply SepWPp_conseq_pre (sepConj_mono_left (ratchetAt_expose_findIndex A x.self x.G x.st))
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hchains_len, hcs_lt⟩ => ?_
  set cs := x.G.chains.zip x.st.receiverChains
  have hcs_toNat : (BitVec.ofNat 64 cs.length).toNat = cs.length := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [stackAt_findReceiverChainKeyStack s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v19 => SepWPp.exists_elim fun v20 =>
    SepWPp.exists_elim fun v21 => SepWPp.exists_elim fun v30 =>
    SepWPp.exists_elim fun v29 => ?_
  apply sepWPp_seq_lscl_ro (mid := lsmpl.base 26) hcl0 hro0
  apply sepWP_seg_ls_vm (Q := (blkPC_25).rebase (blkPl_25).base (hooksException H))
    blkLib_eq_25 (mid := lsmpl.base 26)
  intro _m_strip0
  wp_steps
  refine SepWP.done (by wp_norm_goal) (by wp_norm_goal) fun _m_real0 _hnsp0 => ?_
  have hvm0 : VmPreserved s0 _ := _hnsp0.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm0 ⊢
  refine SepWP.done (by wp_norm_goal) (by wp_norm_goal) fun ⟨hcl1, hro1⟩ => ?_
  have hfind1 := findIndex_alloc_placed_ok_at_state hfind hcl1
  apply sepWPp_seq_lscl_ro (mid := (blkPl_25).base + 44#64) hcl1 hro1
  wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro ⟨hcl2, hro2⟩
  have hvm_after_find : VmPreserved s0 sf := hvm0.trans (by assumption)
  have htr_find : sf.trace = s0.trace := by simp only [wp_norm, arm64_norm, *]
  have hmap_cs : cs.map (·.2) = x.st.receiverChains :=
    zip_map_snd x.G.chains x.st.receiverChains hchains_len
  have hidx_post : match x.st.findReceiverChainIndex x.their with
      | some i => sf.readReg64 (Reg.gpr 0#5) = 1#64 ∧ (sf.readReg64 (Reg.gpr 1#5)).toNat = i
      | none => sf.readReg64 (Reg.gpr 0#5) = 0#64 := by
    have h := hpost; rw [hmap_cs] at h; exact h
  cases hfind_res : x.st.findReceiverChainIndex x.their with
  | none =>
    rw [hfind_res] at hidx_post; dsimp only at hidx_post
    rw [memRegion40_unpack_none x.ret]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun t0 => ?_
    apply sepWPp_seq_lscl_ro (mid := s0.readReg64 Reg.lr) hcl2 hro2
    apply sepWP_seg_ls_vm (Q := (blkPC_25).rebase (blkPl_25).base (hooksException H))
      blkLib_eq_25 (mid := s0.readReg64 Reg.lr)
    intro _m_strip_none
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_goal) fun _m_real_none _hnsp_none => ?_
    have hvm_none : VmPreserved s0 _ :=
      hvm_after_find.trans (_hnsp_none.toVmPreserved (by wp_norm_lhs))
    simp only [State.setMem_setMem] at hvm_none ⊢
    refine SepWP.done (by wp_norm_goal) (by wp_norm_goal) fun ⟨_, hro3⟩ => ?_
    refine SepWPp.done (by wp_norm_goal) (by wp_norm_goal)
      ⟨fun hm => ?_, rfl, by findReceiverChainKey_cc_close⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    try simp only [withLsCodeLoaded, findReceiverChainKeyPlacedAllocSpec, withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.findReceiverChainKeyPlacedSpec]
    refine Entails.pure_right hvm_none ?_
    rw [findReceiverChainKey_of_none hfind_res]; dsimp only [findReceiverChainKeyResultAt]
    refine Entails.pure_right ⟨hro3, by simp only [wp_norm, arm64_norm, *]⟩ ?_
    have hrat := ratchetAt_reassemble_findIndex A x.self x.G x.st
    have hstk := stackAt_findReceiverChainKeyStack_repack s0.sp
      (s0.readReg64 Reg.x29) (s0.readReg64 Reg.lr) (s0.readReg64 Reg.x21)
      (s0.readReg64 Reg.x20) (s0.readReg64 Reg.x19)
    refine Entails.trans ?_
      (sepConj_mono hrat (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk))))
    exact entails_of_eq (by dsimp only [cs, Reg.x19, Reg.x20, Reg.x21, Reg.lr, Reg.x29]; sep_ac_rfl)
      (Entails.refl _)
  | some i =>
    rw [hfind_res] at hidx_post; rcases hidx_post with ⟨hx0_1, hx1_1⟩
    have hi_rc : i < x.st.receiverChains.length := findReceiverChainIndex_lt hfind_res
    have hi : i < cs.length := by rwa [zip_length_eq hchains_len]
    have hx1_eq : sf.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; rw [hx1_1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hule : (BitVec.ofNat 64 cs.length).ule (BitVec.ofNat 64 i) = false :=
      len_ule_idx_false hi hcs_lt
    rw [arrayAt_split_at (chainAt A) 104 x.G.chainsPtr cs hi]
    set elemAddr := x.G.chainsPtr + BitVec.ofNat 64 (i * 104)
    cases hck : cs[i].2.chainKey with
    | none =>
      rw [chainAt_none_expose A cs[i] elemAddr hck, memRegion40_unpack_err x.ret]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun l0 => SepWPp.exists_elim fun p0 =>
        SepWPp.exists_elim fun t0 => ?_
      apply sepWPp_seq_lscl_ro (mid := s0.readReg64 Reg.lr) hcl2 hro2
      apply sepWP_seg_ls_vm (Q := (blkPC_25).rebase (blkPl_25).base (hooksException H))
        blkLib_eq_25 (mid := s0.readReg64 Reg.lr)
      intro _m_strip_err
      wp_steps
      refine SepWP.done (by wp_norm_goal) (by wp_norm_goal) fun _m_real_err _hnsp_err => ?_
      have hvm_err : VmPreserved s0 _ :=
        hvm_after_find.trans (_hnsp_err.toVmPreserved (by wp_norm_lhs))
      simp only [State.setMem_setMem] at hvm_err ⊢
      refine SepWP.done (by wp_norm_goal) (by wp_norm_goal) fun ⟨_, hro3⟩ => ?_
      apply sepWPp_intro_rodata_missingReceiverChainKey_placed hro3
      refine SepWPp.done (by wp_norm_goal) (by wp_norm_goal)
        ⟨fun hm => ?_, rfl, by findReceiverChainKey_cc_close⟩
      refine Satisfies.mono (sepConj_mono_left ?_) hm
      try simp only [withLsCodeLoaded, findReceiverChainKeyPlacedAllocSpec, withVmPreserved,
        CryptoVerification.LibsignalTripleRatchet.findReceiverChainKeyPlacedSpec]
      refine Entails.pure_right hvm_err ?_
      rw [findReceiverChainKey_of_some_none hchains_len hfind_res hi hck]
      refine Entails.pure_right ⟨hro3, by simp only [wp_norm, arm64_norm, *]⟩ ?_
      have herr :=
        findReceiverChainKeyResultAt_err_repack x.ret (lsmpl.ρ "libsignal_protocol:.rodata..Lanon.290")
      have hrat := ratchetAt_reassemble_findIndex A x.self x.G x.st
      have hstk := stackAt_findReceiverChainKeyStack_repack s0.sp
        (s0.readReg64 Reg.x29) (s0.readReg64 Reg.lr) (s0.readReg64 Reg.x21)
        (s0.readReg64 Reg.x20) (s0.readReg64 Reg.x19)
      rw [arrayAt_split_at (chainAt A) 104 x.G.chainsPtr cs hi,
          chainAt_none_expose A cs[i] elemAddr hck] at hrat
      refine Entails.trans ?_
        (sepConj_mono hrat (sepConj_mono_right (sepConj_mono herr (sepConj_mono_right hstk))))
      exact entails_of_eq (by dsimp only [cs, elemAddr, Reg.x19, Reg.x20, Reg.x21, Reg.lr, Reg.x29]; sep_ac_rfl)
        (Entails.refl _)
    | some ck =>
      apply SepWPp_conseq_pre
        (sepConj_mono_left (sepConj_mono_left (chainAt_some_expose A cs[i] ck elemAddr hck)))
      apply SepWPp_eq_pre (by simp only [sepConj_assoc]; rfl)
      refine SepWPp.pure_elim fun hcap_lt => ?_
      have hcap_ne := cap_add_one_beq_zero_false hcap_lt
      have hlen_key : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
      obtain ⟨v0, v4, v6, v7, v15, v23, v31, hkey⟩ :=
        exists_findReceiverChainKeyKeyChunks_of_length_32 hlen_key
      rw [hkey cs[i].1.ck.ptr]; unfold findReceiverChainKeyKeyChunks
      rw [sp_scratch32_unpack s0.sp, memRegion40_unpack_some x.ret]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun r36 => SepWPp.exists_elim fun r35 =>
        SepWPp.exists_elim fun r27 => SepWPp.exists_elim fun r26 =>
        SepWPp.exists_elim fun r24 => SepWPp.exists_elim fun r23 =>
        SepWPp.exists_elim fun r19 => SepWPp.exists_elim fun r18 =>
        SepWPp.exists_elim fun r16 => SepWPp.exists_elim fun r8 =>
        SepWPp.exists_elim fun r4 => SepWPp.exists_elim fun r0 =>
        SepWPp.exists_elim fun s24 => SepWPp.exists_elim fun s16 =>
        SepWPp.exists_elim fun s3 => SepWPp.exists_elim fun s2 =>
        SepWPp.exists_elim fun s0_scr => ?_
      apply sepWPp_seq_lscl_ro (mid := (blkPl_25).base + 156#64) hcl2 hro2
      apply sepWP_seg_ls_vm (Q := (blkPC_25).rebase (blkPl_25).base (hooksException H))
        blkLib_eq_25 (mid := (blkPl_25).base + 156#64)
      intro _m_strip_some1
      wp_steps
      refine SepWP.done (by wp_norm_goal) (by wp_norm_goal) fun _m_real_some1 _hnsp_some1 => ?_
      have hvm_some1 : VmPreserved s0 _ :=
        hvm_after_find.trans (_hnsp_some1.toVmPreserved (by wp_norm_lhs))
      simp only [State.setMem_setMem] at hvm_some1 ⊢
      refine SepWP.done (by wp_norm_goal) (by wp_norm_goal) fun ⟨hcl3, hro3⟩ => ?_
      apply SepWPp_eq_pre (by simp only [sepConj_assoc, sp_11_repack_rest s0.sp v4 v6 v7]; rfl)
      apply sepWPp_seq_lscl_ro (mid := s0.readReg64 Reg.lr) hcl3 hro3
      apply sepWP_seg_ls_vm (Q := (blkPC_25).rebase (blkPl_25).base (hooksException H))
        blkLib_eq_25 (mid := s0.readReg64 Reg.lr)
      intro _m_strip_some2
      wp_steps
      refine SepWP.done (by wp_norm_goal) (by wp_norm_goal) fun _m_real_some2 _hnsp_some2 => ?_
      have hvm_some2 : VmPreserved s0 _ :=
        hvm_some1.trans (_hnsp_some2.toVmPreserved (by wp_norm_lhs))
      simp only [State.setMem_setMem] at hvm_some2 ⊢
      refine SepWP.done (by wp_norm_goal) (by wp_norm_goal) fun ⟨_, hro4⟩ => ?_
      refine SepWPp.done (by wp_norm_goal) (by wp_norm_goal)
        ⟨fun hm => ?_, rfl, by findReceiverChainKey_cc_close⟩
      refine Satisfies.mono (sepConj_mono_left ?_) hm
      try simp only [withLsCodeLoaded, findReceiverChainKeyPlacedAllocSpec, withVmPreserved,
        CryptoVerification.LibsignalTripleRatchet.findReceiverChainKeyPlacedSpec]
      refine Entails.pure_right hvm_some2 ?_
      rw [findReceiverChainKey_of_some_some hchains_len hfind_res hi hck]
      refine Entails.pure_right ⟨hro4, by simp only [wp_norm, arm64_norm, *]⟩ ?_
      have hres := findReceiverChainKeyResultAt_some_repack x.ret ck v0 v4 v6 v7 v15 v23 v31 hkey
      have hscr := sp_scratch32_repack s0.sp
        (v7.extractLsb' 0 40 ++ v6 ++ v4) (v7.extractLsb' 40 16) (v7.extractLsb' 56 8) v23 v31
      have hstk := stackAt_findReceiverChainKeyStack_repack s0.sp
        (s0.readReg64 Reg.x29) (s0.readReg64 Reg.lr) (s0.readReg64 Reg.x21)
        (s0.readReg64 Reg.x20) (s0.readReg64 Reg.x19)
      have hch := chainAt_some_reassemble A cs[i] ck elemAddr hck
      rw [hkey cs[i].1.ck.ptr] at hch; unfold findReceiverChainKeyKeyChunks at hch
      have hrat := ratchetAt_reassemble_findIndex A x.self x.G x.st
      rw [arrayAt_split_at (chainAt A) 104 x.G.chainsPtr cs hi] at hrat
      have hrat' := FindReceiverChainKeyFacts.ratchet_reassemble_chain hch hrat
      have hstk' := FindReceiverChainKeyFacts.stack_reassemble_scr hscr hstk
      rw [← hres]
      refine Entails.trans ?_
        (sepConj_mono hrat' (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk'))))
      exact entails_of_eq
        (by dsimp only [cs, elemAddr, Reg.x19, Reg.x20, Reg.x21, Reg.lr, Reg.x29]; sep_ac_rfl)
        (Entails.refl _)

theorem find_receiver_chain_key_placed_ok_of_find_index [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {H : String → Option (State → State)}
    (hfind : subroutine_ok ((blkPC_25).rebase (blkPl_25).base H) (lsmpl.base 26)
      (withLsCodeLoaded lsmpl (LoopBudget.findPlacedSpec A))) :
    subroutine_ok ((blkPC_25).rebase (blkPl_25).base H) (blkPl_25).base
      (withLsCodeLoaded lsmpl (findReceiverChainKeyPlacedSpec A)) :=
  find_receiver_chain_key_alloc_placed_ok_of_find_index hfind

theorem find_receiver_chain_key_alloc_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_25).rebase (blkPl_25).base H) (blkPl_25).base
      (withLsCodeLoaded lsmpl (findReceiverChainKeyPlacedAllocSpec A)) :=
  find_receiver_chain_key_alloc_placed_ok_of_find_index
    (ls_subroutine_ok_of_block (i := 25) (j := 26)
      (LoopBudget.find_receiver_chain_index_alloc_placed_ok A h_bb))

theorem find_receiver_chain_key_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_25).rebase (blkPl_25).base H) (blkPl_25).base
      (withLsCodeLoaded lsmpl (findReceiverChainKeyPlacedSpec A)) :=
  find_receiver_chain_key_placed_ok_of_find_index
    (ls_subroutine_ok_of_block (i := 25) (j := 26)
      (FindIndexBudget.find_receiver_chain_index_placed_ok A h_bb))

end LibsignalBinary.Proofs.TripleRatchet.ChainKey.FindReceiverChainKeyBudget
