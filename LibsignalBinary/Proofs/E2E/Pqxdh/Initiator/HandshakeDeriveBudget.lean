/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDerive
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded Relocatable Contract for `<HandshakeKeys>::derive` (Block `59`)

Defines `VmPreserved`-strengthened placed HKDF extract/expand contracts and proves allocator-free
(`handshakeKeysDerive_placed_vm_ok`) and `RustCliAllocBudget M` pool-preserving
(`handshakeKeysDerive_placed_ok`) contracts for `<HandshakeKeys>::derive` on Block `59`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget

open Arm64 Arm64.Obj ProofLib
open scoped ProofLib.ProgramReflection
open CryptoVerification (
  LibsignalHooks LibsignalPlacement blkLib_eq_59 blkPC_59 blkPl_59 lsmpl
)
open CryptoVerification.LibsignalTripleRatchet (sepWP_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Keys (
  LsFrozenInv SepWP.done_frozen frozenStop subroutine_ok_withLsCodeRoLoaded_rodata''
)
open CryptoVerification.E2E.Pqxdh.Initiator (
  Bytes HandshakeKeysDeriveGhost INFO_PQXDH Primitives StructuralPrims
  bv_add_neg64 bv_sub_add_lit' bv_sub_sub_lit bytesToBv8
  cells_sub160_14_merge cells_sub192_4_merge
  cells_sub224_4_merge cells_sub368_8_merge cells_sub464_12_merge cells_sub48_6_merge
  discontinuityBytes exists_unpack64_hkdfDerive96 fnFrame_split_derive_post
  handshakeKeysBytes100 hkdfExtractRef hkdfExtractRef_length hmacCore_split
  hmacState_merge_sub368 infoPqxdh memRegion_out_derive pqxdhEntryStack
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre
  readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre stackAt_pqxdh_derive stackAt_pqxdh_derive_pre
)
open CryptoVerification.E2E.Pqxdh.Initiator.Model (deriveDRKeys)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setMem_pre (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases s; cases w <;> cases r <;> rfl

/-! ## 1. `VmPreserved`-Strengthened HKDF Extract & Expand Placed Contracts -/

def pqxdhHkdfExtractNonePlacedSpec (P : Primitives) (pl : Obj.MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × Bytes × BitVec 64) :=
  withVmPreserved (CryptoVerification.E2E.Pqxdh.Initiator.pqxdhHkdfExtractNonePlacedSpec P pl)

def pqxdhHkdfExtractSomePlacedSpec (P : Primitives) (pl : Obj.MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × Bytes × BitVec 64 × Bytes × BitVec 64) :=
  withVmPreserved (CryptoVerification.E2E.Pqxdh.Initiator.pqxdhHkdfExtractSomePlacedSpec P pl)

def PqxdhHkdfExtractPlacedOk [LibsignalPlacement] (P : Primitives) (prog : Program) : Prop :=
  subroutine_ok prog (lsmpl.base 54)
    (pqxdhHkdfExtractNonePlacedSpec P lsmpl) ∧
  subroutine_ok prog (lsmpl.base 54)
    (pqxdhHkdfExtractSomePlacedSpec P lsmpl)

def pqxdhHkdfExpandCellsPlacedSpec (P : Primitives) (pl : Obj.MultiPlacement) (k : Nat) :
    Spec (BitVec 64 × Bytes × BitVec 64 × BitVec 64 × Bytes × BitVec 64 × BitVec 64) :=
  withVmPreserved (CryptoVerification.E2E.Pqxdh.Initiator.pqxdhHkdfExpandCellsPlacedSpec P pl k)

def PqxdhHkdfExpandMultiInfoPlacedOk [LibsignalPlacement] (P : Primitives) (prog : Program) :
    Prop :=
  ∀ k : Nat, subroutine_ok prog (lsmpl.base 53)
    (pqxdhHkdfExpandCellsPlacedSpec P lsmpl k)

/-! ## 2. `<HandshakeKeys>::derive` Placed Contracts & Proofs (Block `59`) -/

/-- Allocator-free `VmPreserved` contract for `<HandshakeKeys>::derive` (Block `59`). -/
def handshakeKeysDerivePlacedVmSpec (P : Primitives) :
    Spec HandshakeKeysDeriveGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x8 = g.outPtr ∧ s.readReg64 .x0 = g.secretsPtr ∧
      (s.readReg64 .x1).toNat = g.secrets.length ∧
      (g.secrets.length = 160 ∨ g.secrets.length = 192) ∧
      g.secrets.take 32 = discontinuityBytes⌝ ∗
    (g.secretsPtr ↦ₛ bytesToBv8 g.secrets) ∗ memRegion g.outPtr 100 ∗
    stackAt s.sp pqxdhEntryStack
  post := fun g s0 sf =>
    ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace⌝ ∗
    (g.secretsPtr ↦ₛ bytesToBv8 g.secrets) ∗
    (g.outPtr ↦ₛ bytesToBv8 (handshakeKeysBytes100 (deriveDRKeys P g.secrets))) ∗
    stackAt s0.sp pqxdhEntryStack

/-- Budget-pool-threaded contract for `<HandshakeKeys>::derive` (Block `59`) with `onPanic = ⌜False⌝`. -/
def handshakeKeysDerivePlacedBaseSpec (M : AllocCostModel) (P : Primitives)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (HandshakeKeysDeriveGhost × M.σ) where
  pre := fun (g, st) s =>
    ⌜s.readReg64 .x8 = g.outPtr ∧ s.readReg64 .x0 = g.secretsPtr ∧
      (s.readReg64 .x1).toNat = g.secrets.length ∧
      (g.secrets.length = 160 ∨ g.secrets.length = 192) ∧
      g.secrets.take 32 = discontinuityBytes⌝ ∗
    (g.secretsPtr ↦ₛ bytesToBv8 g.secrets) ∗ memRegion g.outPtr 100 ∗
    stackAt s.sp pqxdhEntryStack ∗ A.pool lim st s
  post := fun (g, st) s0 sf =>
    ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace⌝ ∗
    (g.secretsPtr ↦ₛ bytesToBv8 g.secrets) ∗
    (g.outPtr ↦ₛ bytesToBv8 (handshakeKeysBytes100 (deriveDRKeys P g.secrets))) ∗
    stackAt s0.sp pqxdhEntryStack ∗ A.pool lim st sf

private theorem sepWP_seq_lscro_inv {prog : Program} {pl : Obj.MultiPlacement}
    {mid target_pc : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hF : LsFrozenInv pl s)
    (h : SepWP prog mid s Pre
      (fun sm Pm => LsFrozenInv pl sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s Pre post :=
  sepWP_seq_lscro ⟨hF.1, hF.2⟩
    (SepWP.mono h fun _ _ _ _ hnext hcro => hnext ⟨hcro.1, hcro.2⟩)

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

private def infoPqxdhList : Bytes :=
  "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024".toList.flatMap String.utf8EncodeChar

private theorem toUTF8_data_toList (s : String) :
    s.toUTF8.data.toList = s.toList.flatMap String.utf8EncodeChar := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [List.utf8Encode]

private theorem INFO_PQXDH_eq_list : INFO_PQXDH = infoPqxdhList := by
  have h1 : infoPqxdh = INFO_PQXDH := by
    rw [infoPqxdh, INFO_PQXDH, byteArray_toList_eq_data]
  rw [← h1]
  unfold infoPqxdh infoPqxdhList
  exact toUTF8_data_toList "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024"

private theorem lsroCheck_infoPqxdh :
    CryptoVerification.lsroCheck "libsignal_protocol:.rodata..Lanon.352"
      (bytesToBv8 INFO_PQXDH) = true := by
  rw [INFO_PQXDH_eq_list]
  exact eagerReduce (Eq.refl true)

set_option maxHeartbeats 6000000 in
theorem handshakeKeysDerive_placed_vm_ok [LibsignalPlacement] {P : Primitives}
    {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (hext : PqxdhHkdfExtractPlacedOk P ((blkPC_59).rebase (blkPl_59).base H))
    (hexp : PqxdhHkdfExpandMultiInfoPlacedOk P ((blkPC_59).rebase (blkPl_59).base H)) :
    subroutine_ok ((blkPC_59).rebase (blkPl_59).base H) (blkPl_59).base
      (withLsCodeRoLoaded lsmpl (handshakeKeysDerivePlacedVmSpec P)) := by
  refine subroutine_ok_withLsCodeRoLoaded_rodata''
    (roSym := "libsignal_protocol:.rodata..Lanon.352")
    (roBytes := bytesToBv8 INFO_PQXDH) lsroCheck_infoPqxdh ?_
  have hext_none := hext.1
  have hexp' := hexp 12
  simp only [pqxdhHkdfExtractNonePlacedSpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.Initiator.pqxdhHkdfExtractNonePlacedSpec] at hext_none
  simp only [pqxdhHkdfExpandCellsPlacedSpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.Initiator.pqxdhHkdfExpandCellsPlacedSpec,
    cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd] at hexp'
  clear hext hexp
  wp_init x s0
  obtain ⟨secretsPtr, secrets, outPtr⟩ := x
  dsimp only [handshakeKeysDerivePlacedVmSpec] at *
  have hF0 : LsFrozenInv lsmpl s0 := ‹_›
  have hx1_bv : s0.readReg64 (.gpr 1#5) = BitVec.ofNat 64 secrets.length := by
    apply BitVec.eq_of_toNat_eq
    rw [‹(s0.readReg64 (.gpr 1#5)).toNat = secrets.length›, BitVec.toNat_ofNat]
    rcases ‹secrets.length = 160 ∨ secrets.length = 192› with h160 | h192 <;> omega
  subst outPtr secretsPtr
  have hinfo_len : BitVec.ofNat 64 INFO_PQXDH.length = 46#64 := by
    rw [INFO_PQXDH_eq_list]
    rfl
  have hprk_len : (bytesToBv8 (hkdfExtractRef P none secrets)).length = 32 := by
    simp [bytesToBv8, hkdfExtractRef_length]
  have hprk_len32 : (hkdfExtractRef P none secrets).length = 32 :=
    hkdfExtractRef_length P none secrets
  obtain ⟨p0, p1, p2, p3, -, hprk⟩ := exists_unpack64_of_length_32 hprk_len
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, hokm, hout⟩ :=
    exists_unpack64_hkdfDerive96 P hWF secrets
  rw [memRegion_out_derive (s0.readReg64 (.gpr 8#5))]
  rw (occs := .pos [1]) [stackAt_pqxdh_derive_pre s0.sp]
  wp_simp_pre_fast [sepConj_assoc]
  cells_pre_unfold_fast
  wp_extract_exists
  apply sepWP_seq_lscro_inv hF0 (mid := lsmpl.base 54)
  apply sepWP_seg_ls_vm (Q := (blkPC_59).rebase (blkPl_59).base (hooksException H))
    blkLib_eq_59 (mid := frozenStop (lsmpl.base 54))
  intro _m_strip1
  wp_steps
  refine SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real1 hnsp1 => ?_
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hF1 => ?_
  have hvm1 : VmPreserved s0 _ := hnsp1.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm1 hF1 ⊢
  try simp only [arm64_norm] at hF1
  apply sepWP_seq_lscro_inv hF1 (mid := lsmpl.base 53)
  wp_simp_pre_fast [hx1_bv]
  wp_call hext_none (s0.sp - 224#64, s0.readReg64 (.gpr 0#5), secrets, s0.sp - 464#64)
  have hvm_after_ext : VmPreserved s0 sf := hvm1.trans ‹_›
  wp_extract_exists
  rw [hprk (s0.sp - 224#64)]
  apply SepWP.replace_pre (by sep_focus) (hmacCore_split P (s0.sp - 192#64) _)
  wp_extract_exists
  rename_i hhmac
  wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  apply sepWP_seg_ls_vm (Q := (blkPC_59).rebase (blkPl_59).base (hooksException H))
    blkLib_eq_59 (mid := frozenStop (lsmpl.base 53))
  intro _m_strip2
  wp_steps
  refine SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 hnsp2 => ?_
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hF2 => ?_
  have hvm2 : VmPreserved sf _ := hnsp2.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm2 hF2 ⊢
  have hvm_pre_exp : VmPreserved s0 _ := hvm_after_ext.trans hvm2
  try simp only [arm64_norm] at hF2
  apply SepWP.replace_pre (by sep_focus)
    (hmacState_merge_sub368 P s0.sp (hkdfExtractRef P none secrets) hhmac)
  wp_simp_pre_fast [← hinfo_len]
  wp_call hexp' (s0.sp - 368#64, hkdfExtractRef P none secrets, s0.sp - 224#64,
    lsmpl.ρ "libsignal_protocol:.rodata..Lanon.352", INFO_PQXDH, s0.sp - 464#64, s0.sp - 464#64)
  have hvm_after_exp : VmPreserved s0 sf_1 := hvm_pre_exp.trans ‹_›
  wp_extract_exists
  wp_simp_pre_fast [hokm (s0.sp - 464#64), bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  apply sepWP_seg_ls_vm (Q := (blkPC_59).rebase (blkPl_59).base (hooksException H))
    blkLib_eq_59 (mid := s0.readReg64 (.gpr 30#5))
  intro _m_strip3
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real3 hnsp3 => ?_
  have hvm3 : VmPreserved sf_1 _ := hnsp3.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm3 ⊢
  have hvm_final : VmPreserved s0 _ := hvm_after_exp.trans hvm3
  apply SepWP.replace_pre (by sep_focus) (cells_sub464_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
  apply SepWP.replace_pre (by sep_focus) (cells_sub368_8_merge s0.sp _ _ _ _ _ _ _ _)
  apply SepWP.replace_pre (by sep_focus) (cells_sub224_4_merge s0.sp _ _ _ _)
  apply SepWP.replace_pre (by sep_focus) (cells_sub192_4_merge s0.sp _ _ _ _)
  apply SepWP.replace_pre (by sep_focus) (cells_sub160_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  apply SepWP.replace_pre (by sep_focus) (cells_sub48_6_merge s0.sp _ _ _ _ _ _)
  rw [stackAt_pqxdh_derive s0.sp, fnFrame_split_derive_post s0.sp, hout (s0.readReg64 (.gpr 8#5))]
  clear hext_none hexp' hprk hhmac hokm hout hinfo_len hx1_bv
    hvm1 hvm_after_ext hvm2 hvm_pre_exp hvm_after_exp hvm3
  simp only [sepConj_assoc, *]
  wp_done

theorem handshakeKeysDerive_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (hext : PqxdhHkdfExtractPlacedOk P ((blkPC_59).rebase (blkPl_59).base H))
    (hexp : PqxdhHkdfExpandMultiInfoPlacedOk P ((blkPC_59).rebase (blkPl_59).base H)) :
    subroutine_ok ((blkPC_59).rebase (blkPl_59).base H) (blkPl_59).base
      (withLsCodeRoLoaded lsmpl (handshakeKeysDerivePlacedBaseSpec M P A lim)) := by
  refine subroutine_ok_map (handshakeKeysDerive_placed_vm_ok hWF hext hexp) ?_
  rintro ⟨g, st⟩ R s0 hpre
  simp only [withLsCodeRoLoaded, handshakeKeysDerivePlacedBaseSpec,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  refine ⟨g, A.pool lim st s0 ∗ R, ?_, fun sf hpost => ?_⟩
  · simp only [withLsCodeRoLoaded, handshakeKeysDerivePlacedVmSpec,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpure, ?_⟩
    convert hmem using 1
    sep_ac_rfl
  · simp only [withLsCodeRoLoaded, handshakeKeysDerivePlacedVmSpec,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hvm, htr⟩, hpost_mem⟩
    simp only [handshakeKeysDerivePlacedBaseSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hvm, htr⟩, ?_⟩
    rw [A.pool_of_vmPreserved hvm]
    exact hpost_mem

end LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget
