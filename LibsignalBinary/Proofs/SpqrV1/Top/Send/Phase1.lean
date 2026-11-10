/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::send::<HookRng>`: Phase 1 Prologue and Shared Epilogues (`0x3085c`, `0x31a5c..0x31a94`)

Proves `.rodata` jump-table extraction from `img.FrozenLoaded`, the prologue (`+0..+76`),
the register-restore epilogue (`+4632`), and the shared cleanup epilogues at `+4608` and `+904`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth hiding Entails.sepExists_elim
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.EncodeVarint
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  CryptoVerification.SpqrV1.Drop.none2Cap_add_two_beq_zero
  CryptoVerification.SpqrV1.Drop.noneCap_add_two_beq_zero

theorem fnAddr_spqrSend_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr spqrSendName = spqrSendEntry b := by
  dsimp only [tripleRatchetProgAtExt, spqrSendEntry]
  rw [Program.fnAddr_rebase, spqrSend_fnOff]

/-! ## `.rodata` Jump-Table Extraction -/

theorem rodata_spqrSendStatesJumpTable {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ spqrSendStatesJumpTableAt img.base ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_xref% 0x30a94 0x30a98)) (n := 22) (bs := spqrSendStatesJumpTableBytes)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

theorem rodata_spqrSendEncodeJumpTable {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ spqrSendEncodeJumpTableAt img.base ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_xref% 0x32310 0x32314)) (n := 22) (bs := spqrSendEncodeJumpTableBytes)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

theorem rodata_spqrSendDropJumpTable {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ spqrSendDropJumpTableAt img.base ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_xref% 0x32270 0x32274)) (n := 20) (bs := spqrSendDropJumpTableBytes)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

theorem rodata_optProtoInnerStateJumpTable {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ Drop.optProtoInnerStateJumpTableAt img.base ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_bytes% "220036000561663b870a")) (n := 10) (bs := Drop.optProtoInnerStateJumpTableBytes)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

theorem rodata_v1StateJumpTables {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ Prost.MessageMerge.v1StateJumpTablesAt img.base ∗ P := by
  unfold Prost.MessageMerge.v1StateJumpTablesAt
  rw [sepConj_assoc]
  exact Prost.MessageMerge.rodata_v1StateMergeJumpTableExpanded himg hF
    (rodata_optProtoInnerStateJumpTable himg hF hP)

theorem rodata_statesFromPbJumpTable {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ statesFromPbJumpTableAt img.base ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_xref% 0x54d28 0x54d2c)) (n := 22) (bs := statesFromPbJumpTableBytes)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

theorem rodata_statesIntoPbJumpTable {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ statesIntoPbJumpTableAt img.base ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_xref% 0x57a74 0x57a78)) (n := 22) (bs := statesIntoPbJumpTableBytes)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

/-- Extract the full `spqrSendRoAt img.base` bundle from `img.FrozenLoaded s`. -/
theorem rodata_spqrSendRoAt {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ spqrSendRoAt img.base ∗ P := by
  unfold spqrSendRoAt
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  refine rodata_spqrSendStatesJumpTable himg hF ?_
  refine rodata_spqrSendEncodeJumpTable himg hF ?_
  refine rodata_spqrSendDropJumpTable himg hF ?_
  refine rodata_v1StateJumpTables himg hF ?_
  refine rodata_statesFromPbJumpTable himg hF ?_
  refine rodata_statesIntoPbJumpTable himg hF ?_
  exact GF.UnacceleratedMul.rodata_reduceTable himg hF hP

/-! ## Shared Epilogue (`+4632..+4668`, `0x31a74..0x31a94`) -/

@[local arm64_norm, local wp_norm]
theorem sp_sub_96_add_16 (sp0 : BitVec 64) : (sp0 - 96#64) + 16#64 = sp0 - 80#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_sub_96_add_32 (sp0 : BitVec 64) : (sp0 - 96#64) + 32#64 = sp0 - 64#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_sub_96_add_48 (sp0 : BitVec 64) : (sp0 - 96#64) + 48#64 = sp0 - 48#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_sub_96_add_64 (sp0 : BitVec 64) : (sp0 - 96#64) + 64#64 = sp0 - 32#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_sub_96_add_80 (sp0 : BitVec 64) : (sp0 - 96#64) + 80#64 = sp0 - 16#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_sub_96_sub_4096 (sp0 : BitVec 64) : (sp0 - 96#64) - 4096#64 = sp0 - 4192#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_sub_4192_sub_3872 (sp0 : BitVec 64) : (sp0 - 4192#64) - 3872#64 = sp0 - 8064#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_sub_8064_add_4096 (sp0 : BitVec 64) : (sp0 - 8064#64) + 4096#64 = sp0 - 3968#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_sub_3968_add_3872 (sp0 : BitVec 64) : (sp0 - 3968#64) + 3872#64 = sp0 - 96#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_8064_add_7968 (sp0 : BitVec 64) : (sp0 - 8064#64) + 7968#64 = sp0 - 96#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_8064_add_7976 (sp0 : BitVec 64) : (sp0 - 8064#64) + 7976#64 = sp0 - 88#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_8064_add_7984 (sp0 : BitVec 64) : (sp0 - 8064#64) + 7984#64 = sp0 - 80#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_8064_add_7992 (sp0 : BitVec 64) : (sp0 - 8064#64) + 7992#64 = sp0 - 72#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_8064_add_8000 (sp0 : BitVec 64) : (sp0 - 8064#64) + 8000#64 = sp0 - 64#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_8064_add_8008 (sp0 : BitVec 64) : (sp0 - 8064#64) + 8008#64 = sp0 - 56#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_8064_add_8016 (sp0 : BitVec 64) : (sp0 - 8064#64) + 8016#64 = sp0 - 48#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_8064_add_8024 (sp0 : BitVec 64) : (sp0 - 8064#64) + 8024#64 = sp0 - 40#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_8064_add_8032 (sp0 : BitVec 64) : (sp0 - 8064#64) + 8032#64 = sp0 - 32#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_8064_add_8040 (sp0 : BitVec 64) : (sp0 - 8064#64) + 8040#64 = sp0 - 24#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_8064_add_8048 (sp0 : BitVec 64) : (sp0 - 8064#64) + 8048#64 = sp0 - 16#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_8064_add_8056 (sp0 : BitVec 64) : (sp0 - 8064#64) + 8056#64 = sp0 - 8#64 := by bv_omega

theorem spqrSendSavedRegs_eq_sp0 (s0 : State) :
    spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 =
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
      ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
      ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
      ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
      ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
      ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) := by
  unfold spqrSendSavedRegs
  simp only [BitVec.ofNat_eq_ofNat, sp_sub_8064_add_7968, sp_sub_8064_add_7976,
    sp_sub_8064_add_7984, sp_sub_8064_add_7992, sp_sub_8064_add_8000, sp_sub_8064_add_8008,
    sp_sub_8064_add_8016, sp_sub_8064_add_8024, sp_sub_8064_add_8032, sp_sub_8064_add_8040,
    sp_sub_8064_add_8048, sp_sub_8064_add_8056]

/-- Epilogue (`+4632 -> s0.lr`, `0x31a74..0x31a94`):
    adds `0x1000 + 0xf20 = 0x1f20` (`7968`) to `sp = s0.sp - 0x1f80`, restores `x19..x30`
    from `s0.sp - 96`, and executes `ret`. -/
theorem spqr_send_epilogue_4632 {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendEntry b + 4632#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x1f20 ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ stackAt s0.sp spqrSendStack ∗ Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s.trace) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  rw [← fnAddr_spqrSend_eq b ext] at hpc
  spqr_send_fetches_range b (Rust.withPanics ext) 4632 36
  dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_session::HookRng>" = entry
  examples_hide_fetches
  rw [spqrSendSavedRegs_eq_sp0 s0]
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have hrest := stack_restore_spqrSend s0.sp s0
    rw [spqrSendSavedRegs_eq_sp0 s0] at hrest
    refine Entails.trans
      (Entails.of_eq (show _ =
        (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
         memRegion (s0.sp - 0x1f80#64) 0x1f20 ∗
         (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
          ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
          ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
          ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∗ Rest by ac_rfl))
      (sepConj_mono_left hrest)
  · wp_done

@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_3968_add_608 (sp0 : BitVec 64) :
    (sp0 - 3968#64) + 608#64 = (sp0 - 8064#64) + 0x1260#64 := by bv_omega

theorem memRegion_7968_split_probes (sp0 : BitVec 64) :
    memRegion (sp0 - 0x1f80#64) 0x1f20 =
      (∃∗ v0 : BitVec 64, ((sp0 - 0x1f80#64) ↦₆₄ v0)) ∗
      memRegion (sp0 - 8056#64) 3864 ∗
      (∃∗ v_probe : BitVec 64, ((sp0 - 4192#64) ↦₆₄ v_probe)) ∗
      memRegion (sp0 - 4184#64) 4088 := by
  rw [ProofLib.memRegion_split' (b := sp0 - 0x1f80#64) (n := 0xf20) (k := 4096)
        (b' := sp0 - 4192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 0x1f80#64) (n := 8) (k := 3864)
        (b' := sp0 - 8056#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 4192#64) (n := 8) (k := 4088)
        (b' := sp0 - 4184#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp0 - 0x1f80#64),
      ProofLib.memRegion_eight (sp0 - 4192#64),
      sepConj_assoc]

theorem probes_entails_memRegion_7968 (sp0 v0 v_probe : BitVec 64) :
    ((sp0 - 0x1f80#64) ↦₆₄ v0) ∗
      memRegion (sp0 - 8056#64) 3864 ∗
      ((sp0 - 4192#64) ↦₆₄ v_probe) ∗
      memRegion (sp0 - 4184#64) 4088 ⊢
      memRegion (sp0 - 0x1f80#64) 0x1f20 := by
  rw [ProofLib.memRegion_split' (b := sp0 - 0x1f80#64) (n := 0xf20) (k := 4096)
        (b' := sp0 - 4192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 0x1f80#64) (n := 8) (k := 3864)
        (b' := sp0 - 8056#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 4192#64) (n := 8) (k := 4088)
        (b' := sp0 - 4184#64) rfl (by bv_omega) (by decide),
      sepConj_assoc]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion (sp0 - 0x1f80#64) v0)
    (sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (sp0 - 4192#64) v_probe)))

theorem optChainPBAt_none_entails_memRegion_80' (A : RustAlloc) (a : BitVec 64) :
    ProtoRepr.optChainPBAt A a none ⊢ memRegion a 80 := by
  unfold ProtoRepr.optChainPBAt
  rw [ProofLib.memRegion_split a 8 72 (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion a LibsignalTripleRatchetRepr.noneCap)

theorem memRegion_rejoin_60_80 (fsp : BitVec 64) :
    memRegion fsp 0x60 ∗ memRegion (fsp + 0x60#64) 80 ∗ memRegion (fsp + 0xb0#64) (0x1f20 - 0xb0) =
      memRegion fsp 0x1f20 := by
  rw [← ProofLib.memRegion_split' (b := fsp + 0x60#64) (n := 80) (k := 0x1f20 - 0xb0)
        (b' := fsp + 0xb0#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := fsp) (n := 0x60) (k := 0x1f20 - 0x60)
        (b' := fsp + 0x60#64) rfl rfl (by decide)]

/-! ## Prologue (`+0..+76`, `0x3085c..0x308a8`) -/

/-- Prologue (`+0 -> +76`, `0x3085c -> 0x308a8`):
    saves `x19..x30` at `s0.sp - 96`, sets `x29 = s0.sp - 96`, `sp = s0.sp - 0x1f80`,
    `x19 = ret`, `x0 = stV`, `x8 = x21 = x26 = sp + 0x1260`, and probes `[s0.sp - 4192]` and `[sp]`. -/
theorem spqr_send_prologue {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 : State) (ret stV : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = spqrSendEntry b)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ret)
    (hx1 : s0.readReg64 .x1 = stV) :
    SepWP (tripleRatchetProgAtExt b ext)
      (spqrSendEntry b + 76#64) s0
      (stackAt s0.sp spqrSendStack ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢
          stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
          memRegion (s0.sp - 0x1f80#64) 0x1f20 ∗
          spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest) ∧
        s1.sp = s0.sp - 0x1f80#64 ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        s1.readReg64 .x19 = ret ∧
        s1.readReg64 .x0 = stV ∧
        s1.readReg64 .x8 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
        s1.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
        s1.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
        s1.trace = s0.trace ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s0) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hsp4192_align : ((s0.sp - 4192#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 4192#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  rw [← fnAddr_spqrSend_eq b ext] at hpc ⊢
  spqr_send_fetches_range b (Rust.withPanics ext) 0 76
  dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_session::HookRng>" = entry
  examples_hide_fetches
  wp_conv_pre =>
    rw [stackAt_spqrSend_eq_callee_and_frame s0.sp,
        sp_sub_8064_add_7968 s0.sp,
        ProofLib.memRegion_cells (s0.sp - 96#64) 12 (by decide),
        memRegion_7968_split_probes s0.sp]
  cells_unfold
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro w0
  apply ProofLib.SepWP.exists_left; intro w1
  apply ProofLib.SepWP.exists_left; intro w2
  apply ProofLib.SepWP.exists_left; intro w3
  apply ProofLib.SepWP.exists_left; intro w4
  apply ProofLib.SepWP.exists_left; intro w5
  apply ProofLib.SepWP.exists_left; intro w6
  apply ProofLib.SepWP.exists_left; intro w7
  apply ProofLib.SepWP.exists_left; intro w8
  apply ProofLib.SepWP.exists_left; intro w9
  apply ProofLib.SepWP.exists_left; intro w10
  apply ProofLib.SepWP.exists_left; intro w11
  apply ProofLib.SepWP.exists_left; intro v_probe
  apply ProofLib.SepWP.exists_left; intro v0
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · rw [spqrSendSavedRegs_eq_sp0 s0]
    have hfsp := probes_entails_memRegion_7968 s0.sp 0#64 0#64
    refine Entails.trans
      (Entails.of_eq (show _ =
        (((s0.sp - 0x1f80#64) ↦₆₄ 0#64) ∗
         memRegion (s0.sp - 8056#64) 3864 ∗
         ((s0.sp - 4192#64) ↦₆₄ 0#64) ∗
         memRegion (s0.sp - 4184#64) 4088) ∗
        (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
         (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
          ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
          ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
          ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
         Rest) by ac_rfl))
      (Entails.trans (sepConj_mono_left hfsp) (Entails.of_eq (by ac_rfl)))
  · wp_done

/-! ## Shared Cleanup Epilogues (`+4608` and `+904`) -/

@[local simp, local arm64_norm, local wp_norm]
theorem fsp_add_30_add_30 (fsp : BitVec 64) :
    (fsp + 0x30#64) + 0x30#64 = fsp + 0x60#64 := by bv_omega

theorem stackAt_spqrSendCallee_split_dropStack48 (fsp : BitVec 64) :
    stackAt fsp spqrSendCalleeStack =
      memRegion (fsp - 123008#64) (spqrSendCalleeStack - dropStack48) ∗
      stackAt fsp dropStack48 :=
  ProofLib.stackAt_split_bottom fsp dropStack48 (spqrSendCalleeStack - dropStack48) (by decide)

theorem stackAt_spqrSendCallee_split_allocHook (fsp : BitVec 64) :
    stackAt fsp spqrSendCalleeStack =
      memRegion (fsp - 123008#64) (spqrSendCalleeStack - allocHookStack) ∗
      stackAt fsp allocHookStack :=
  ProofLib.stackAt_split_bottom fsp allocHookStack (spqrSendCalleeStack - allocHookStack) (by decide)

theorem cap_add_one_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  bv_omega

def chainPBRestAt (A : RustAlloc) (a cap ptr : BitVec 64) (ch : ChainPB) : SepProp :=
  ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
    vecBuf A chainEpochPBSize 8 (fun ep addr => ProtoRepr.chainEpochPBAt A addr ep) cap ptr ch.links ∗
    rustBytesVecAt A (a + 0x18#64) ch.nextRoot ∗
    ((a + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
    ((a + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
    ProtoRepr.optChainParamsPBAt (a + 0x40#64) ch.params ∗
    ((a + 0x4c#64) ↦₃₂ ch.direction)

theorem vecBuf_chainEpochPB_cap_lt (A : RustAlloc) (cap ptr : BitVec 64) (links : List ChainEpochPB) :
    vecBuf A chainEpochPBSize 8 (fun ep addr => ProtoRepr.chainEpochPBAt A addr ep) cap ptr links ⊢
      ⌜cap.toNat < 2 ^ 63⌝ ∗
      vecBuf A chainEpochPBSize 8 (fun ep addr => ProtoRepr.chainEpochPBAt A addr ep) cap ptr links := by
  unfold vecBuf
  apply Entails.pure_left; intro hp
  have hlt : cap.toNat < 2 ^ 63 := by
    have hmul := hp.2.1
    have hsz : chainEpochPBSize = 112 := rfl
    rw [hsz] at hmul
    omega
  exact Entails.pure_right hlt (Entails.pure_right hp (Entails.refl _))

theorem chainPBAt_entails_first_word (A : RustAlloc) (a : BitVec 64) (ch : ChainPB) :
    ProtoRepr.chainPBAt A a ch ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cap.toNat < 2 ^ 63⌝ ∗
        (a ↦₆₄ cap) ∗
        chainPBRestAt A a cap ptr ch := by
  unfold ProtoRepr.chainPBAt ProtoRepr.chainLinksVecAt vecOf vecAt vecHeader chainPBRestAt
  simp only [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  refine Entails.trans
    (sepConj_mono_left (sepConj_mono_right (vecBuf_chainEpochPB_cap_lt A cap ptr ch.links))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem first_word_entails_chainPBAt (A : RustAlloc) (a cap ptr : BitVec 64) (ch : ChainPB) :
    (a ↦₆₄ cap) ∗ chainPBRestAt A a cap ptr ch ⊢ ProtoRepr.chainPBAt A a ch := by
  unfold ProtoRepr.chainPBAt ProtoRepr.chainLinksVecAt vecOf vecAt vecHeader chainPBRestAt
  simp only [sepExists_sepConj_left]
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  exact Entails.of_eq (by ac_rfl)

/-- Shared `st.chain` drop + register-restore epilogue (`+4608 -> s0.lr`, `0x31a5c..0x31a94`):
    drops `ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) optCh` (calling `0x35530`
    `dropProtoSpqrChainName` when `some`), rejoins `memRegion (s0.sp - 0x1f80#64) 0x1f20`,
    and runs `spqr_send_epilogue_4632`. -/
theorem spqr_send_chain_drop_epilogue_4608 {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdrop : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropProtoSpqrChainName)
      (dropProtoSpqrChainSpec A))
    (s0 s : State) (optCh : Option ChainPB) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendEntry b + 4608#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x60 ∗
        ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) optCh ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x1f20 - 0xb0) ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ stackAt s0.sp spqrSendStack ∗ A.pool ∗ Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s.trace) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hdrop_raw : subroutine_ok (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#1]"))
      (dropProtoSpqrChainSpec A) := Drop.sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#1]")) (b := b) (X := Rust.withPanics ext)
      spqrSend_fnOff dropProtoSpqrChain_fnOff (by decide))
    hdrop
  refine EncoderFromPb.seq_clean
    (mid := spqrSendEntry b + 4632#64)
    (P_mid :=
      stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
      memRegion (s0.sp - 0x1f80#64) 0x1f20 ∗
      spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
      (A.pool ∗ Rest))
    (Q := fun sm => sm.sp = s0.sp - 0x1f80#64 ∧ sm.trace = s.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · rw [← fnAddr_spqrSend_eq b ext] at hpc ⊢
    spqr_send_fetches_range b (Rust.withPanics ext) 4608 24
    dsimp only [tripleRatchetProgAtExt, spqrSendName, dropProtoSpqrChainSpec,
      chainPBSize, BitVec.ofNat_eq_ofNat] at hpc hdrop_raw ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::send::<libsignal_session::HookRng>" = entry
    examples_hide_fetches
    generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align ⊢
    cases optCh with
    | none =>
      have hnone : ProtoRepr.optChainPBAt A (fsp + 96#64) none =
          (((fsp + 96#64) ↦₆₄ LibsignalTripleRatchetRepr.noneCap) ∗
           memRegion ((fsp + 96#64) + 8#64) 72) := rfl
      wp_conv_pre => rw [hnone]
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hch := optChainPBAt_none_entails_memRegion_80' A (fsp + 96#64)
        rw [hnone] at hch
        refine Entails.trans
          (Entails.of_eq (show _ =
            ((fsp + 96#64) ↦₆₄ LibsignalTripleRatchetRepr.noneCap ∗
             memRegion ((fsp + 96#64) + 8#64) 72) ∗
            (memRegion fsp 96 ∗
             memRegion (fsp + 176#64) 7792 ∗
             stackAt fsp spqrSendCalleeStack ∗
             spqrSendSavedRegs fsp s0 ∗
             A.pool ∗ Rest) by ac_rfl)) ?_
        refine Entails.trans (sepConj_mono_left hch) ?_
        rw [← memRegion_rejoin_60_80 fsp]
        exact Entails.of_eq (by ac_rfl)
      · wp_done
    | some ch =>
      have hsome : ProtoRepr.optChainPBAt A (fsp + 96#64) (some ch) =
          ProtoRepr.chainPBAt A (fsp + 96#64) ch := rfl
      wp_conv_pre => rw [hsome]
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
          (chainPBAt_entails_first_word A (fsp + 96#64) ch)))) ?_
      wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro cap
      apply ProofLib.SepWP.exists_left; intro ptr
      wp_focus_pure; intro hcap_lt
      have hne_none := cap_add_one_beq_zero_false hcap_lt
      wp_steps
      refine SepWP.weaken_pre
        (Entails.trans
          (Entails.of_eq (show _ =
            ((fsp + 96#64) ↦₆₄ cap ∗
             chainPBRestAt A (fsp + 96#64) cap ptr ch) ∗
            (stackAt fsp spqrSendCalleeStack ∗
             memRegion fsp 96 ∗
             memRegion (fsp + 176#64) 7792 ∗
             spqrSendSavedRegs fsp s0 ∗
             A.pool ∗ Rest) by ac_rfl))
          (sepConj_mono_left (first_word_entails_chainPBAt A (fsp + 96#64) cap ptr ch))) ?_
      wp_conv_pre => rw [stackAt_spqrSendCallee_split_dropStack48 fsp]
      wp_call hdrop_raw ⟨fsp + 96#64, ch⟩
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [hsp, stackAt_spqrSendCallee_split_dropStack48 fsp,
            ← memRegion_rejoin_60_80 fsp]
        exact Entails.of_eq (by ac_rfl)
      · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, htr2, hvregs2⟩
    have hep := spqr_send_epilogue_4632 (ext := ext) s0 s2 (A.pool ∗ Rest) hsp0_align hpc2 hrun2 hsp2
    refine SepWP.mono hep ?_
    intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩
    refine ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f.trans htr2⟩

theorem versionNegotiationPBTailAt_entails_memRegion_32 (a16 : BitVec 64) (v : VersionNegotiationPB) :
    DecodeState.versionNegotiationPBTailAt a16 v ⊢ memRegion a16 32 := by
  unfold DecodeState.versionNegotiationPBTailAt
  have hcp : ProtoRepr.optChainParamsPBAt (a16 + 8#64) v.chainParams ⊢ memRegion (a16 + 8#64) 12 := by
    cases v.chainParams with
    | none =>
      unfold ProtoRepr.optChainParamsPBAt
      dsimp only
      rw [ProofLib.memRegion_split' (b := a16 + 8#64) (n := 4) (k := 8)
            (b' := (a16 + 8#64) + 4#64) rfl rfl (by decide)]
      exact sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion _ _)
    | some cp =>
      unfold ProtoRepr.optChainParamsPBAt ProtoRepr.chainParamsPBAt
      dsimp only
      have ha8 : ((a16 + 8#64) + 4#64) + 4#64 = (a16 + 8#64) + 8#64 := by bv_omega
      rw [ha8,
          ProofLib.memRegion_split' (b := a16 + 8#64) (n := 4) (k := 8)
            (b' := (a16 + 8#64) + 4#64) rfl rfl (by decide),
          ProofLib.memRegion_split' (b := (a16 + 8#64) + 4#64) (n := 4) (k := 4)
            (b' := (a16 + 8#64) + 8#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (ProofLib.pointsTo32_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo32_entails_memRegion _ _)
          (ProofLib.pointsTo32_entails_memRegion _ _))
  rw [ProofLib.memRegion_split' (b := a16) (n := 8) (k := 24) (b' := a16 + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a16 + 8#64) (n := 12) (k := 12) (b' := a16 + 20#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a16 + 20#64) (n := 4) (k := 8) (b' := a16 + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a16 + 24#64) (n := 4) (k := 4) (b' := a16 + 28#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono hcp
      (sepConj_mono (ProofLib.pointsTo32_entails_memRegion _ _)
        (sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion _ _))))

theorem optVersionNegotiationPBTail_cleanup_entails (A : RustAlloc) (a30 w0 w1 : BitVec 64)
    (optVn : Option VersionNegotiationPB) :
    (a30 ↦₆₄ w0) ∗ ((a30 + 8#64) ↦₆₄ w1) ∗
      DecodeState.optVersionNegotiationPBTailAt A w0 w1 (a30 + 16#64) optVn ⊢
      if BitVec.slt w0 1#64 then
        memRegion a30 48
      else
        ⌜0 < w0.toNat ∧ w0.toNat < 2 ^ 63 ∧ w1 ≠ 0⌝ ∗
        ((a30 + 8#64) ↦₆₄ w1) ∗
        memRegion a30 8 ∗
        memRegion (a30 + 16#64) 32 ∗
        A.live w1 w0.toNat 1 ∗
        memRegion w1 w0.toNat := by
  cases optVn with
  | none =>
    unfold DecodeState.optVersionNegotiationPBTailAt
    have hpull :
        ((a30 ↦₆₄ w0) ∗ ((a30 + 8#64) ↦₆₄ w1) ∗ ⌜w0 = LibsignalTripleRatchetRepr.noneCap⌝ ∗
          memRegion (a30 + 16#64) 32) =
        ⌜w0 = LibsignalTripleRatchetRepr.noneCap⌝ ∗
          ((a30 ↦₆₄ w0) ∗ ((a30 + 8#64) ↦₆₄ w1) ∗ memRegion (a30 + 16#64) 32) := by ac_rfl
    rw [hpull]
    apply Entails.pure_left; intro hw0
    subst hw0
    have hslt : BitVec.slt LibsignalTripleRatchetRepr.noneCap 1#64 = true := by decide
    simp only [hslt, ↓reduceIte]
    rw [ProofLib.memRegion_split' (b := a30) (n := 8) (k := 40) (b' := a30 + 8#64) rfl rfl (by decide),
        ProofLib.memRegion_split' (b := a30 + 8#64) (n := 8) (k := 32) (b' := a30 + 16#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))
  | some v =>
    unfold DecodeState.optVersionNegotiationPBTailAt vecU8Heap
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (versionNegotiationPBTailAt_entails_memRegion_32 (a30 + 16#64) v)))) ?_
    have hpull :
        ((a30 ↦₆₄ w0) ∗ ((a30 + 8#64) ↦₆₄ w1) ∗ memRegion (a30 + 16#64) 32 ∗
         ⌜v.authKey.length ≤ w0.toNat ∧ w0.toNat < 2 ^ 63 ∧ w1 ≠ 0⌝ ∗
         (if w0 = 0 then emp
          else A.live w1 w0.toNat 1 ∗ (w1 ↦ₛ v.authKey) ∗
            memRegion (w1 + BitVec.ofNat 64 v.authKey.length) (w0.toNat - v.authKey.length))) =
        ⌜v.authKey.length ≤ w0.toNat ∧ w0.toNat < 2 ^ 63 ∧ w1 ≠ 0⌝ ∗
          ((a30 ↦₆₄ w0) ∗ ((a30 + 8#64) ↦₆₄ w1) ∗ memRegion (a30 + 16#64) 32 ∗
           (if w0 = 0 then emp
            else A.live w1 w0.toNat 1 ∗ (w1 ↦ₛ v.authKey) ∗
              memRegion (w1 + BitVec.ofNat 64 v.authKey.length) (w0.toNat - v.authKey.length))) := by ac_rfl
    rw [hpull]
    apply Entails.pure_left; rintro ⟨hlen_le, hcap_lt, hptr_ne⟩
    by_cases hw0 : w0 = 0#64
    · subst hw0
      have hslt : BitVec.slt 0#64 1#64 = true := by decide
      have h0eq : (0#64 : BitVec 64) = 0 := rfl
      simp only [h0eq, hslt, ↓reduceIte, sepConj_emp]
      rw [ProofLib.memRegion_split' (b := a30) (n := 8) (k := 40) (b' := a30 + 8#64) rfl rfl (by decide),
          ProofLib.memRegion_split' (b := a30 + 8#64) (n := 8) (k := 32) (b' := a30 + 16#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))
    · have hw0_pos : 0 < w0.toNat := by bv_omega
      have hslt : BitVec.slt w0 1#64 = false := by
        revert hw0 hcap_lt
        bv_bits
      have hw0' : w0 ≠ 0 := hw0
      simp only [hw0', hslt, Bool.false_eq_true, ↓reduceIte]
      apply Entails.pure_right ⟨hw0_pos, hcap_lt, hptr_ne⟩
      have hbuf : (w1 ↦ₛ v.authKey) ∗
          memRegion (w1 + BitVec.ofNat 64 v.authKey.length) (w0.toNat - v.authKey.length) ⊢
          memRegion w1 w0.toNat := by
        have hsplit : w0.toNat = v.authKey.length + (w0.toNat - v.authKey.length) := by omega
        conv_rhs => rw [hsplit]
        rw [ProofLib.memRegion_split w1 v.authKey.length (w0.toNat - v.authKey.length) (by omega)]
        exact sepConj_mono_left (ProofLib.pointsToBytes_entails_memRegion w1 v.authKey)
      have ha30 := ProofLib.pointsTo64_entails_memRegion a30 w0
      refine Entails.trans
        (Entails.of_eq (show _ =
          (a30 ↦₆₄ w0) ∗
          (((w1 ↦ₛ v.authKey) ∗
            memRegion (w1 + BitVec.ofNat 64 v.authKey.length) (w0.toNat - v.authKey.length)) ∗
           (((a30 + 8#64) ↦₆₄ w1) ∗ memRegion (a30 + 16#64) 32 ∗ A.live w1 w0.toNat 1)) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono ha30 (sepConj_mono_left hbuf)) ?_
      exact Entails.of_eq (by ac_rfl)

theorem memRegion_rejoin_30_48 (fsp : BitVec 64) :
    memRegion fsp 0x30 ∗ memRegion (fsp + 0x30#64) 48 = memRegion fsp 0x60 := by
  rw [← ProofLib.memRegion_split' (b := fsp) (n := 0x30) (k := 48)
        (b' := fsp + 0x30#64) rfl rfl (by decide)]

theorem memRegion_rejoin_30_8_8_32 (fsp w1 : BitVec 64) :
    memRegion fsp 0x30 ∗ memRegion (fsp + 0x30#64) 8 ∗
      ((fsp + 0x38#64) ↦₆₄ w1) ∗ memRegion (fsp + 0x40#64) 32 ⊢
      memRegion fsp 0x60 := by
  rw [← memRegion_rejoin_30_48 fsp,
      ProofLib.memRegion_split' (b := fsp + 0x30#64) (n := 8) (k := 40)
        (b' := fsp + 0x38#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x38#64) (n := 8) (k := 32)
        (b' := fsp + 0x40#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (fsp + 0x38#64) w1)))

/-- Shared `st.version_negotiation.auth_key` dealloc + `st.chain` drop + register-restore epilogue
    (`+904 -> s0.lr`, `0x30be4..0x30bf4 -> 0x31a5c..0x31a94`):
    loads `w1` from `[sp + 0x38]`, calls `__rust_dealloc(w1, w0.toNat, 1)`, and jumps to `+4608`. -/
theorem spqr_send_vn_chain_drop_epilogue_904 {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (hdrop : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropProtoSpqrChainName)
      (dropProtoSpqrChainSpec A))
    (s0 s : State) (w0 w1 : BitVec 64) (optCh : Option ChainPB) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendEntry b + 904#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hx23 : s.readReg64 .x23 = w0)
    (hw0_pos : 0 < w0.toNat)
    (hw0_lt : w0.toNat < 2 ^ 63)
    (hw1_ne : w1 ≠ 0)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x30#64) 8 ∗
        (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x40#64) 32 ∗
        A.live w1 w0.toNat 1 ∗
        memRegion w1 w0.toNat ∗
        ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) optCh ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x1f20 - 0xb0) ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ stackAt s0.sp spqrSendStack ∗ A.pool ∗ Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s.trace) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hdealloc_raw : subroutine_ok (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := Drop.sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      spqrSend_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  refine EncoderFromPb.seq_clean
    (mid := spqrSendEntry b + 4608#64)
    (P_mid :=
      stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
      memRegion (s0.sp - 0x1f80#64) 0x60 ∗
      ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) optCh ∗
      memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x1f20 - 0xb0) ∗
      spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
      A.pool ∗ Rest)
    (Q := fun sm => sm.sp = s0.sp - 0x1f80#64 ∧ sm.trace = s.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · rw [← fnAddr_spqrSend_eq b ext] at hpc ⊢
    spqr_send_fetches_range b (Rust.withPanics ext) 904 20
    dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hpc hdealloc_raw ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::send::<libsignal_session::HookRng>" = entry
    examples_hide_fetches
    generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align ⊢
    wp_steps
    wp_conv_pre => rw [stackAt_spqrSendCallee_split_allocHook fsp]
    wp_call hdealloc_raw (w1, w0.toNat, 1)
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · rw [hsp, stackAt_spqrSendCallee_split_allocHook fsp]
      have h60 := memRegion_rejoin_30_8_8_32 fsp w1
      refine Entails.trans
        (Entails.of_eq (show _ =
          (memRegion fsp 48 ∗
           memRegion (fsp + 48#64) 8 ∗
           ((fsp + 56#64) ↦₆₄ w1) ∗
           memRegion (fsp + 64#64) 32) ∗
          (memRegion (fsp - 123008#64) (spqrSendCalleeStack - allocHookStack) ∗
           stackAt fsp allocHookStack ∗
           ProtoRepr.optChainPBAt A (fsp + 96#64) optCh ∗
           memRegion (fsp + 176#64) 7792 ∗
           spqrSendSavedRegs fsp s0 ∗
           A.pool ∗ Rest) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left h60) ?_
      exact Entails.of_eq (by ac_rfl)
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, htr2, hvregs2⟩
    have hep := spqr_send_chain_drop_epilogue_4608 hdrop s0 s2 optCh Rest hsp0_align hpc2 hrun2 hsp2
    refine SepWP.mono hep ?_
    intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩
    refine ⟨hPf, hsp_f, hcc_f, htr_f.trans htr2⟩

end CryptoVerification.SpqrV1.Top.Send
