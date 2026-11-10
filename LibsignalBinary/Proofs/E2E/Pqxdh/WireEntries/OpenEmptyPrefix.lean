/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.OpenBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.KeyPairCallees
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.IsCanonical
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.Bin.ApiEncResultLoose -- shake: keep

/-!
# Shared Prefix, Epilogue, and Empty-State Proof for `libsignal_pqxdh_e2e::open`

Proves the role-dispatch and allocation prefix (`+0x000..+0x1b8`), the 29-word `Call` copy epilogue
(`+0x2a4..+0x328`), and `openEmpty_subroutine_ok` (`x5 = 0#64`) for `libsignal_pqxdh_e2e::open`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Pqxdh.WireEntries

set_option warningAsError false
set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 800000

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ObjectLoad.RoDataFactsAux
open ProofLib.ProgramReflection CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.InMem

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  tpidrEl0_setPC_pre_open tpidrEl0_setMem_setPC_pre_open
  trace_setPC_pre_open trace_setMem_setPC_pre_open
  fastStateSP fastReadReg64 fastReadReg32 fastReadReg
attribute [-arm64_norm, -wp_norm]
  ProofLib.reduceStateSP
  ProofLib.reduceStateReadReg64
  ProofLib.reduceStateReadReg32
  ProofLib.reduceStateReadReg

@[local simp, local arm64_norm, local wp_norm]
private theorem extractLsb'_append_lo_openP (lo hi : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi_lt; simp [hi_lt]

@[local simp, local arm64_norm, local wp_norm]
private theorem extractLsb'_append_hi_openP (lo hi : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi_lt; simp [hi_lt]

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem spAligned_writeVReg128_openP (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).spAligned = s.spAligned := rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem sp_writeVReg128_openP (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).sp = s.sp := rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_writeVReg128_openP (s : State) (r : BitVec 5) (v : BitVec 128) (reg : Reg)
  :
    (s.writeVReg128 r v).readReg64 reg = s.readReg64 reg := rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_writeVReg128_openP (s : State) (r : BitVec 5) (v : BitVec 128) (reg : Reg)
  :
    (s.writeVReg128 r v).readReg32 reg = s.readReg32 reg := rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_writeVReg128_openP (s : State) (r : BitVec 5) (v : BitVec 128) (w :
  RegWidth) (reg : Reg) :
    (s.writeVReg128 r v).readReg w reg = s.readReg w reg := rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem tpidrEl0_writeVReg128_openP (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).tpidrEl0 = s.tpidrEl0 := rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem trace_writeVReg128_openP (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).trace = s.trace := rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem symtab_writeVReg128_openP (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).symtab = s.symtab := rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem symtab_setPC_openP (s : State) (pc : BitVec 64) :
    (s.setPC pc).symtab = s.symtab := by cases s; rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem symtab_setMem_setPC_openP (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).symtab = s.symtab := by cases s; rfl

def OpenX27VPreserved (s1 s2 : State) : Prop :=
  s1.readReg64 .x27 = s2.readReg64 .x27 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s2

@[simp, arm64_norm]
theorem OpenX27VPreserved_iff (s1 s2 : State) :
    OpenX27VPreserved s1 s2 ↔
      s1.readReg64 .x27 = s2.readReg64 .x27 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s2 :=
  Iff.rfl

theorem OpenX27VPreserved.trans {s1 s2 s3 : State}
    (h12 : OpenX27VPreserved s1 s2) (h23 : OpenX27VPreserved s2 s3) :
    OpenX27VPreserved s1 s3 :=
  ⟨h12.1.trans h23.1, h12.2.trans h23.2⟩

/-! ## Stack, Address, and Hook Helpers -/

def openSavedRegsAtP (s0 : State) : SepProp :=
  ((s0.sp - 0x60#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 0x58#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((s0.sp - 0x50#64) ↦₆₄ s0.readReg64 .x28) ∗ memRegion (s0.sp - 0x48#64) 8 ∗
  ((s0.sp - 0x40#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 0x38#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((s0.sp - 0x30#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 0x28#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 0x20#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 0x18#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 0x10#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 0x08#64) ↦₆₄ s0.readReg64 .x19)

abbrev openSavedUninitAtP (sp0 : BitVec 64) : SepProp :=
  (∃∗ v0 : BitVec 64, (sp0 - 0x60#64) ↦₆₄ v0) ∗ (∃∗ v1 : BitVec 64, (sp0 - 0x58#64) ↦₆₄ v1) ∗
  (∃∗ v2 : BitVec 64, (sp0 - 0x50#64) ↦₆₄ v2) ∗ memRegion (sp0 - 0x48#64) 8 ∗
  (∃∗ v3 : BitVec 64, (sp0 - 0x40#64) ↦₆₄ v3) ∗ (∃∗ v4 : BitVec 64, (sp0 - 0x38#64) ↦₆₄ v4) ∗
  (∃∗ v5 : BitVec 64, (sp0 - 0x30#64) ↦₆₄ v5) ∗ (∃∗ v6 : BitVec 64, (sp0 - 0x28#64) ↦₆₄ v6) ∗
  (∃∗ v7 : BitVec 64, (sp0 - 0x20#64) ↦₆₄ v7) ∗ (∃∗ v8 : BitVec 64, (sp0 - 0x18#64) ↦₆₄ v8) ∗
  (∃∗ v9 : BitVec 64, (sp0 - 0x10#64) ↦₆₄ v9) ∗ (∃∗ v10 : BitVec 64, (sp0 - 0x08#64) ↦₆₄ v10)

theorem openSavedRegsAtP_eq (s0 : State) :
    openSavedRegsAtP s0 = openPqxdhSavedRegsAt s0 := by
  unfold openSavedRegsAtP openPqxdhSavedRegsAt
  rw [ProofLib.memRegion_eight (s0.sp - 0x48#64)]

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")

theorem stackAt_openPqxdhStack_split (sp0 : BitVec 64) :
    stackAt sp0 openPqxdhStack =
      memRegion (sp0 - openPqxdhStack) (openPqxdhStack - 0x4b0) ∗
      memRegion (sp0 - 0x4b0#64) 0x450 ∗
      openSavedUninitAtP sp0 := by
  have h1 := stackAt_split_bottom_open sp0 0x4b0 (openPqxdhStack - 0x4b0) (by decide)
  rw [show 0x4b0 + (openPqxdhStack - 0x4b0) = openPqxdhStack by decide] at h1
  change stackAt sp0 openPqxdhStack =
    memRegion (sp0 - openPqxdhStack) (openPqxdhStack - 0x4b0) ∗ stackAt sp0 0x4b0 at h1
  rw [h1]
  have h2 : stackAt sp0 0x4b0 = memRegion (sp0 - 0x4b0#64) 0x450 ∗ memRegion (sp0 - 0x60#64)
    0x60 := by
    simp only [stackAt]
    rw [memRegion_split' (b := sp0 - 0x4b0#64) (b' := sp0 - 0x60#64)
      (N := 0x4b0) (n := 0x450) (k := 0x60) (by decide) (by bv_lin) (by decide)]
  rw [h2, show (0x60 : Nat) = 8 * 12 by rfl,
      LibsignalTripleRatchet.memRegion_cells (sp0 - 0x60#64) 12 (by decide)]
  simp only [ProofLib.cells_succ, ProofLib.cells_zero, openSavedUninitAtP, sepConj_emp,
    show sp0 - 0x60#64 + 8#64 = sp0 - 0x58#64 by bv_lin,
    show sp0 - 0x58#64 + 8#64 = sp0 - 0x50#64 by bv_lin,
    show sp0 - 0x50#64 + 8#64 = sp0 - 0x48#64 by bv_lin,
    show sp0 - 0x48#64 + 8#64 = sp0 - 0x40#64 by bv_lin,
    show sp0 - 0x40#64 + 8#64 = sp0 - 0x38#64 by bv_lin,
    show sp0 - 0x38#64 + 8#64 = sp0 - 0x30#64 by bv_lin,
    show sp0 - 0x30#64 + 8#64 = sp0 - 0x28#64 by bv_lin,
    show sp0 - 0x28#64 + 8#64 = sp0 - 0x20#64 by bv_lin,
    show sp0 - 0x20#64 + 8#64 = sp0 - 0x18#64 by bv_lin,
    show sp0 - 0x18#64 + 8#64 = sp0 - 0x10#64 by bv_lin,
    show sp0 - 0x10#64 + 8#64 = sp0 - 0x08#64 by bv_lin]
  rw [ProofLib.memRegion_eight (sp0 - 0x48#64)]
  simp only [← sepExists_sepConj_left]

theorem openPqxdhStack_reassemble (s0 : State) :
    memRegion (s0.sp - openPqxdhStack) (openPqxdhStack - 0x4b0) ∗
      memRegion (s0.sp - 0x4b0#64) 0x450 ∗ openSavedRegsAtP s0 ⊢
      stackAt s0.sp openPqxdhStack := by
  rw [stackAt_openPqxdhStack_split s0.sp]
  apply sepConj_mono_right; apply sepConj_mono_right
  unfold openSavedRegsAtP openSavedUninitAtP
  exact sepConj_mono (Entails.sepExists_right _ (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right _ (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right _ (Entails.refl _))
        (sepConj_mono (Entails.refl _)
          (sepConj_mono (Entails.sepExists_right _ (Entails.refl _))
            (sepConj_mono (Entails.sepExists_right _ (Entails.refl _))
              (sepConj_mono (Entails.sepExists_right _ (Entails.refl _))
                (sepConj_mono (Entails.sepExists_right _ (Entails.refl _))
                  (sepConj_mono (Entails.sepExists_right _ (Entails.refl _))
                    (sepConj_mono (Entails.sepExists_right _ (Entails.refl _))
                      (sepConj_mono (Entails.sepExists_right _ (Entails.refl _))
                        (Entails.sepExists_right _ (Entails.refl _))))))))))))

theorem memRegion_bottom_openPqxdh_split (sp0 sp1 : BitVec 64) (k : Nat)
    (hsp : sp1 = sp0 - 0x4b0#64) (hk : k + (openPqxdhStack - 0x4b0 - k) = openPqxdhStack - 0x4b0)
    (hle : k + (openPqxdhStack - 0x4b0 - k) ≤ 2 ^ 64) :
    memRegion (sp0 - openPqxdhStack) (openPqxdhStack - 0x4b0) =
      memRegion (sp0 - openPqxdhStack) (openPqxdhStack - 0x4b0 - k) ∗
      stackAt sp1 k := by
  subst hsp
  have h1 := stackAt_split_bottom_open (sp0 - 0x4b0#64) k (openPqxdhStack - 0x4b0 - k) hle
  rw [hk] at h1
  have h2 : sp0 - 0x4b0#64 - BitVec.ofNat 64 (openPqxdhStack - 0x4b0) = sp0 - openPqxdhStack := by
    change sp0 - 0x4b0#64 - BitVec.ofNat 64 (openPqxdhStack - 0x4b0) = sp0 - BitVec.ofNat 64
      openPqxdhStack
    simp only [openPqxdhStack, Nat.reduceAdd, Nat.reduceSub]
    bv_lin
  dsimp only [stackAt] at h1
  rw [h2] at h1
  exact h1

theorem spAligned_sub_0x4b0 {s0 sf : State} (hal0 : s0.spAligned = true)
    (hsp : sf.sp = s0.sp - 0x4b0#64) : sf.spAligned = true := by
  simp only [State.spAligned, hsp, beq_iff_eq] at hal0 ⊢
  apply BitVec.eq_of_toNat_eq
  have h1 := congrArg BitVec.toNat hal0
  simp only [BitVec.toNat_and, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.and_two_pow_sub_one_eq_mod _ 4] at h1 ⊢
  omega

theorem memRegion_0x450_head_split (sp1 : BitVec 64) :
    memRegion sp1 0x450 = (∃∗ v : BitVec 64, sp1 ↦₆₄ v) ∗ memRegion (sp1 + 8#64) 0x448 := by
  rw [memRegion_split' (b := sp1) (b' := sp1 + 8#64)
        (N := 0x450) (n := 8) (k := 0x448) (by decide) rfl (by decide),
      ProofLib.memRegion_eight sp1]

theorem memRegion_0x450_reassemble (sp1 : BitVec 64) (v : BitVec 64) :
    (sp1 ↦₆₄ v) ∗ memRegion (sp1 + 8#64) 0x448 ⊢ memRegion sp1 0x450 := by
  rw [memRegion_0x450_head_split sp1]
  exact sepConj_mono_left (Entails.sepExists_right v (Entails.refl _))

/-! ## Segment 2 (`+0x0bc..+0x1b8`) and Epilogue (`+0x2a4..+0x328`) Symbolic Execution -/

attribute [local simp, local arm64_norm, local wp_norm]
  bv16_extract_0 bv16_extract_8
  bv32_extract_0 bv32_extract_8 bv32_extract_16 bv32_extract_24
  bv64_extract_0 bv64_extract_8 bv64_extract_16 bv64_extract_24
  bv64_extract_32 bv64_extract_40 bv64_extract_48 bv64_extract_56
  clamp_lo_byte_zext8_mask
  bv16_setWidth_8 bv32_setWidth_8 bv32_setWidth_16
  bv64_setWidth_8 bv64_setWidth_16 bv64_setWidth_32
  zext64_bv16_setWidth_8 zext64_bv16_setWidth_16 zext64_bv16_setWidth_32
  zext32_bv16_setWidth_8 zext32_bv16_setWidth_16
  zext64_bv32_setWidth_8 zext64_bv32_setWidth_16 zext64_bv32_setWidth_32
  clamp_lo_byte_norm clamp_lo_byte_norm'
  clamp_hi_byte_norm clamp_hi_byte_norm' clamp_hi_byte_norm'' clamp_hi_bfm_norm
  zext64_bv8_setWidth_8
  bv64_mask_low32_orr_zext32 bv64_mask_high32_orr_lsl32 bv64_mask_low16_orr_zext16

open Lean Meta Elab Tactic in
local elab_rules : tactic
  | `(tactic| wp_sep_access) => do
    let g ← getMainGoal
    g.withContext do
      let ty ← instantiateMVars (← g.getType)
      let tyClean := ty.consumeMData
      let args := tyClean.getAppArgs
      let prf ←
        if tyClean.isAppOf ``SepLoad16 then
          try proveSepLoadBytes 2 args[0]! args[1]! args[2]!
          catch _ => sepAccess16Proof ty
        else if tyClean.isAppOf ``SepStore16 then
          try proveSepStoreBytes 2 args[0]! args[1]! args[2]! args[3]!
          catch _ => sepAccess16Proof ty
        else if tyClean.isAppOf ``SepLoad32 then
          try proveSepLoadBytes 4 args[0]! args[1]! args[2]!
          catch _ => sepAccess32Proof ty
        else if tyClean.isAppOf ``SepStore32 then
          try proveSepStoreBytes 4 args[0]! args[1]! args[2]! args[3]!
          catch _ => sepAccess32Proof ty
        else if tyClean.isAppOf ``SepLoad64 then
          try proveSepLoadBytes 8 args[0]! args[1]! args[2]!
          catch _ => sepAccessProof ty
        else if tyClean.isAppOf ``SepStore64 then
          try proveSepStoreBytes 8 args[0]! args[1]! args[2]! args[3]!
          catch _ => sepAccessProof ty
        else
          sepAccessProof ty
      unless ← isDefEq (← inferType prf) ty do throwError "wp_sep_access: type mismatch"
      g.assign prf
    replaceMainGoal []

def openSavedRegsSpAtP (sp : BitVec 64) (s0 : State) : SepProp :=
  ((sp + 1104#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp + 1112#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp + 1120#64) ↦₆₄ s0.readReg64 .x28) ∗ memRegion (sp + 1128#64) 8 ∗
  ((sp + 1136#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp + 1144#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp + 1152#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp + 1160#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp + 1168#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp + 1176#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp + 1184#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp + 1192#64) ↦₆₄ s0.readReg64 .x19)

theorem openSavedRegsAtP_eq_sp (s0 : State) (sp : BitVec 64) (hsp : sp = s0.sp - 0x4b0#64) :
    openSavedRegsAtP s0 = openSavedRegsSpAtP sp s0 := by
  subst hsp; unfold openSavedRegsAtP openSavedRegsSpAtP
  have h1 : s0.sp - 0x4b0#64 + 1104#64 = s0.sp - 0x60#64 := by bv_lin
  have h2 : s0.sp - 0x4b0#64 + 1112#64 = s0.sp - 0x58#64 := by bv_lin
  have h3 : s0.sp - 0x4b0#64 + 1120#64 = s0.sp - 0x50#64 := by bv_lin
  have h4 : s0.sp - 0x4b0#64 + 1128#64 = s0.sp - 0x48#64 := by bv_lin
  have h5 : s0.sp - 0x4b0#64 + 1136#64 = s0.sp - 0x40#64 := by bv_lin
  have h6 : s0.sp - 0x4b0#64 + 1144#64 = s0.sp - 0x38#64 := by bv_lin
  have h7 : s0.sp - 0x4b0#64 + 1152#64 = s0.sp - 0x30#64 := by bv_lin
  have h8 : s0.sp - 0x4b0#64 + 1160#64 = s0.sp - 0x28#64 := by bv_lin
  have h9 : s0.sp - 0x4b0#64 + 1168#64 = s0.sp - 0x20#64 := by bv_lin
  have h10 : s0.sp - 0x4b0#64 + 1176#64 = s0.sp - 0x18#64 := by bv_lin
  have h11 : s0.sp - 0x4b0#64 + 1184#64 = s0.sp - 0x10#64 := by bv_lin
  have h12 : s0.sp - 0x4b0#64 + 1192#64 = s0.sp - 0x08#64 := by bv_lin
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

/-! ## Segment 1 Composition (`+0x000..+0x0bc`) -/

theorem sepWP_bind_segExit_sp2 {α : Type} {C : Crypto} {ctl : BitVec 64}
    {img : Obj.Image} {abs : String → Option (State → State)}
    {spec : Spec α} {g : α} {R : SepProp} {P F : SepProp} {target_pc : BitVec 64} {s0 s : State}
    {post : State → SepProp → Prop} {next : State → Prop}
    (himg : Obj.Loads libsignalSessionImage img) (hm : s.mem ⊨ P ∗ F)
    (hwp : SepWP (tripleRatchetProgAt img.base C ctl abs) target_pc s P post)
    (hcont : ∀ s1 P_f, Steps (tripleRatchetProgAt img.base C ctl abs) s s1 →
      s1.pc = target_pc → s1.status = .Running → (s1.mem ⊨ P_f ∗ F) → post s1 P_f →
      SegExit (binProg img C ctl abs) spec g R s0 s1 next) :
    SegExit (binProg img C ctl abs) spec g R s0 s next := by
  intro hL
  have hprog : binProg img C ctl abs = tripleRatchetProgAt img.base C ctl abs :=
    tripleRatchetProg_eq_tripleRatchetProgAt himg
  obtain ⟨s1, hst1, ⟨hpc1, hrun1, P_f, hm1, hpost1⟩ | ⟨_, _hoom⟩⟩ := SepWP.elim hwp hm (hprog ▸ hL)
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hst1_bin : Steps (binProg img C ctl abs) s s1 := hprog ▸ hst1
  obtain ⟨sf, hst2, hout⟩ := hcont s1 P_f hst1 hpc1 hrun1 hm1 hpost1 (hst1_bin.codeLoaded hL)
  exact ⟨sf, Steps.trans hst1_bin hst2, hout⟩

theorem memRegion_36_elim (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 36 ∗ R) :
    ∃ (d0 d1 d2 d3 : BitVec 64) (dw8 : BitVec 32),
      m ⊨ ((a ↦₆₄ d0) ∗ ((a + 8#64) ↦₆₄ d1) ∗ ((a + 16#64) ↦₆₄ d2) ∗
            ((a + 24#64) ↦₆₄ d3) ∗ ((a + 32#64) ↦₃₂ dw8)) ∗ R := by
  rw [memRegion_36_words4_word32_split a] at hm
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc] at hm ⊢
  rcases hm with ⟨dw8, d3, d2, d1, d0, hm⟩
  exact ⟨d0, d1, d2, d3, dw8, hm⟩

theorem copy36_post_fold (src dst : BitVec 64) (bs : List (BitVec 8))
    (r0 r1 r2 r3 : BitVec 64) (rw8 : BitVec 32)
    (hro : ∀ a, (a ↦ᵣ bs) = (a ↦₆₄ᵣ r0) ∗ ((a + 8#64) ↦₆₄ᵣ r1) ∗ ((a + 16#64) ↦₆₄ᵣ r2) ∗
      ((a + 24#64) ↦₆₄ᵣ r3) ∗ ((a + 32#64) ↦₃₂ᵣ rw8))
    (hrw : ∀ a, (a ↦ₛ bs) = (a ↦₆₄ r0) ∗ ((a + 8#64) ↦₆₄ r1) ∗ ((a + 16#64) ↦₆₄ r2) ∗
      ((a + 24#64) ↦₆₄ r3) ∗ ((a + 32#64) ↦₃₂ rw8)) :
    ((src ↦₆₄ᵣ r0) ∗ ((src + 8#64) ↦₆₄ᵣ r1) ∗ ((src + 16#64) ↦₆₄ᵣ r2) ∗
     ((src + 24#64) ↦₆₄ᵣ r3) ∗ ((src + 32#64) ↦₃₂ᵣ rw8) ∗
     (dst ↦₆₄ r0) ∗ ((dst + 8#64) ↦₆₄ r1) ∗ ((dst + 16#64) ↦₆₄ r2) ∗
     ((dst + 24#64) ↦₆₄ r3) ∗ ((dst + 32#64) ↦₃₂ rw8)) =
      (src ↦ᵣ bs) ∗ (dst ↦ₛ bs) := by
  rw [hro src, hrw dst]; simp only [sepConj_assoc]

def OpenSeam0bcP (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (img : Obj.Image) (abs : String → Option (State → State))
    (outPtr mePtr statePtr stateLenBv : BitVec 64)
    (meBytes : List (BitVec 8)) (role : Role)
    (F_rest R : SepProp) (s0 s : State) : Prop :=
  s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr openPqxdhName + 0x0bc#64 ∧
    s.status = .Running ∧ s.spAligned = true ∧
    s0.spAligned = true ∧ openPqxdhStack ≤ s0.sp.toNat ∧
    s.sp = s0.sp - 0x4b0#64 ∧
    s.tpidrEl0 = s0.tpidrEl0 ∧ ExecOnlyIn (Program.ofImage img) s.mem ∧
    s.trace = s0.trace ∧
    s.readReg64 .x19 = outPtr ∧
    s.readReg64 .x20 = stateLenBv ∧
    s.readReg64 .x21 = statePtr ∧
    s.readReg64 .x22 = mePtr ∧
    OpenX27VPreserved s s0 ∧
    s.readReg64 .x29 = s0.sp - 0x60#64 ∧
    meBytes.length = 36 ∧
    img.FrozenLoaded s ∧
    ∃ (meBuf peerBuf : BitVec 64) (tlsCur : Option (BitVec 64 × BitVec 64)),
      s.readReg64 .x23 = meBuf ∧ s.readReg64 .x0 = peerBuf ∧
      meBuf ≠ 0#64 ∧ peerBuf ≠ 0#64 ∧
      (s.mem ⊨
        (meBuf ↦ₛ role.nameBytes) ∗ A.live meBuf 36 1 ∗
        (peerBuf ↦ₛ role.peer.nameBytes) ∗ A.live peerBuf 36 1 ∗
        memRegion s.sp 0x450 ∗ openSavedRegsAtP s0 ∗
        memRegion outPtr 232 ∗ (mePtr ↦ₛ meBytes) ∗
        tlsKeysAt (s0.tpidrEl0 + tlsKeysTpoff) tlsCur ∗
        A.pool ∗ memRegion (s0.sp - openPqxdhStack) (openPqxdhStack - 0x4b0) ∗
        F_rest ∗ R ∗ anyHeap)

end CryptoVerification.E2E.Pqxdh.WireEntries
